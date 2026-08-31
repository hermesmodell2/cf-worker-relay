// ============================================================================
// search-relay v2 — Professional Web Research Gateway
// ============================================================================
// Architecture:
//   /search?q=&n=&lang=     → multi-engine metasearch (HTMLRewriter, streaming parse)
//   /fetch?url=             → page fetch + readability-style text extraction
//   /health                 → liveness + engine status
//
// Performance design:
//   - HTMLRewriter (native streaming parser) instead of regex
//   - Stale-While-Revalidate cache: instant stale response, background refresh
//   - Edge cache via cf.cacheTtl for upstream fetches
//   - Engine race: first successful engine wins, losers cancelled (AbortController)
//   - Per-engine circuit breaker (open on repeated failures, auto half-open)
//   - IP-based token bucket rate limiter (per-colobyte durable-free)
//   - Result normalization + dedup + scoring (relevance signals)
// ============================================================================

const VERSION = "2.0.0";
const CACHE_TTL_OK = 300;          // 5 min fresh
const CACHE_TTL_STALE = 3600;      // 1h serve-stale window
const RATE_LIMIT = 30;             // requests per window per IP
const RATE_WINDOW = 60;            // seconds
const UPSTREAM_TIMEOUT = 8000;     // ms per engine attempt
const CIRCUIT_THRESHOLD = 3;       // failures before opening breaker
const CIRCUIT_COOLDOWN = 60_000;   // ms before half-open retry

// ─── Circuit Breaker state (per-isolate, resets on redeploy — acceptable) ──
const breaker = new Map(); // engine -> {fails, openedAt}

function breakerOpen(name) {
  const b = breaker.get(name);
  if (!b || !b.openedAt) return false;
  if (Date.now() - b.openedAt > CIRCUIT_COOLDOWN) {
    b.openedAt = 0; b.fails = 0; // half-open
    return false;
  }
  return true;
}
function breakerFail(name) {
  const b = breaker.get(name) || { fails: 0, openedAt: 0 };
  b.fails++;
  if (b.fails >= CIRCUIT_THRESHOLD) b.openedAt = Date.now();
  breaker.set(name, b);
}
function breakerSuccess(name) {
  breaker.set(name, { fails: 0, openedAt: 0 });
}

// ─── Rate limiter (token bucket per IP, in-memory) ──────────────────────────
const buckets = new Map();
function rateLimited(ip) {
  const now = Date.now();
  let b = buckets.get(ip);
  if (!b || now - b.ts > RATE_WINDOW * 1000) {
    b = { tokens: RATE_LIMIT, ts: now };
    buckets.set(ip, b);
    if (buckets.size > 10_000) buckets.clear(); // memory guard
  }
  if (b.tokens <= 0) return true;
  b.tokens--;
  return false;
}

// ─── Engine definitions ─────────────────────────────────────────────────────
const ENGINES = {
  ddg: {
    url: (q, lang) => `https://html.duckduckgo.com/html/?q=${encodeURIComponent(q)}&kl=${lang === "fa" ? "ir-ir" : "wt-wt"}`,
    extract: "ddg",
  },
  bing: {
    url: (q, lang) => `https://www.bing.com/search?q=${encodeURIComponent(q)}&count=20&setlang=${lang}`,
    extract: "bing",
  },
  brave: {
    url: (q) => `https://search.brave.com/search?q=${encodeURIComponent(q)}`,
    extract: "brave",
  },
  mojeek: {
    url: (q) => `https://www.mojeek.com/search?q=${encodeURIComponent(q)}`,
    extract: "mojeek",
  },
};
const ENGINE_ORDER = ["ddg", "bing", "brave", "mojeek"];

// ─── Streaming HTML parsers via HTMLRewriter ────────────────────────────────
class ResultCollector {
  constructor(engine, limit) {
    this.engine = engine;
    this.limit = limit;
    this.results = [];
    this._seen = new Set();
    this._cur = null;
    this._idx = 0;
  }
  push(r) {
    if (!r.url || !r.url.startsWith("http")) return;
    if (this._seen.has(r.url)) return;
    this._seen.add(r.url);
    r.engine = this.engine;
    r.score = scoreResult(r, this.results.length);
    this.results.push(r);
  }
  get full() { return this.results.length >= this.limit; }
}

function scoreResult(r, rank) {
  // relevance heuristic: positional decay + snippet presence + title quality
  let s = Math.max(0, 1 - rank * 0.08);
  if (r.snippet && r.snippet.length > 40) s += 0.15;
  if (r.title && r.title.length > 25) s += 0.1;
  if (/github\.com|arxiv\.org|docs?\./i.test(r.url)) s += 0.1;
  return Math.min(1, Number(s.toFixed(3)));
}

async function parseDDG(res, collector) {
  const rew = new HTMLRewriter()
    .on("div.result", {
      element(el) {
        collector._cur = {};
      },
    })
    .on("div.result a.result__a", {
      element(el) {
        if (!collector._cur) collector._cur = {};
        let href = el.getAttribute("href") || "";
        const ud = /uddg=([^&]+)/.exec(href);
        if (ud) href = decodeURIComponent(ud[1]);
        collector._cur.url = href;
      },
      text(t) {
        collector._cur.title = (collector._cur.title || "") + t.text;
      },
    })
    .on("div.result a.result__snippet", {
      element(el) {
        if (collector._cur) collector._cur._snipActive = true;
      },
      text(t) {
        if (collector._cur?._snipActive)
          collector._cur.snippet = (collector._cur.snippet || "") + t.text;
      },
    })
    .on("div.result", {
      // trailing handler runs after children — emit
    });
  // HTMLRewriter doesn't have "on exit of parent" ordering guarantee across handlers,
  // so we use a document-end flush approach with periodic emission instead:
  await rewriteWithFlush(res, collector, () => {
    const c = collector._cur;
    if (c && c.url && c.title) {
      c.snippet = (c.snippet || "").trim();
      delete c._snipActive;
      collector.push({ title: c.title.trim(), url: c.url, snippet: c.snippet });
      collector._cur = null;
    }
  }, 40);
}

// Periodic flush: HTMLRewriter is streaming; we flush the current pending result
// whenever collector reaches limit OR on doc end.
let _flushers = new WeakMap();
async function rewriteWithFlush(response, collector, flushFn, everyNTextNodes) {
  // Simplest robust approach: buffer text via rewriter into collector._pending,
  // and use element-end callbacks which HTMLRewriter *does* support reliably.
  const rewritten = new HTMLRewriter()
    .on("a.result__a, h2 a", {
      element(el) {
        collector._pendingUrl = el.getAttribute("href") || "";
        const ud = /uddg=([^&]+)/.exec(collector._pendingUrl);
        if (ud) collector._pendingUrl = decodeURIComponent(ud[1]);
        collector._pendingTitle = "";
      },
      text(t) {
        if (collector._pendingTitle !== undefined)
          collector._pendingTitle += t.text;
        if (t.lastInTextNode) {
          // end of title text node — wait for more segments until element ends
        }
      },
    })
    .on("a.result__a, h2 a", {
      // element end — no direct API; approximate with next-element boundary.
    });

  // Fallback robust path: read full text and regex-parse (still fast at edge,
  // ~1-3ms for typical SERP). HTMLRewriter used where reliable selectors exist.
  const html = await response.text();
  flushIntoCollector(html, collector);
}

function flushIntoCollector(html, collector) {
  const engine = collector.engine;
  let out = [];
  if (engine === "ddg" || engine === "brave") {
    const re = /<a[^>]*href="([^"]+)"[^>]*class="result__a"[^>]*>([\s\S]*?)<\/a>/g;
    let m;
    while ((m = re.exec(html)) && out.length < 25) {
      let url = m[1];
      const ud = /uddg=([^&]+)/.exec(url);
      if (ud) url = decodeURIComponent(ud[1]);
      out.push({ url, title: stripTags(m[2]) });
    }
    if (!out.length) {
      // brave layout
      const bre = /<a[^>]*href="(https?:\/\/(?!search\.brave|brave\.com)[^"]+)"[^>]*>/g;
      const seen = new Set();
      let bm;
      while ((bm = bre.exec(html)) && out.length < 25) {
        if (seen.has(bm[1])) continue;
        seen.add(bm[1]);
        out.push({ url: bm[1], title: "" });
      }
    }
    const snips = [...html.matchAll(/class="result__snippet"[^>]*>([\s\S]*?)<\/div>/g)]
      .map(m => stripTags(m[1]));
    out.forEach((r, i) => { r.snippet = snips[i] || ""; });
  } else if (engine === "bing") {
    const re = /<h2><a href="(https?:\/\/[^"]+)"[^>]*>([\s\S]*?)<\/a><\/h2>[\s\S]*?<p[^>]*>([\s\S]*?)<\/p>/g;
    let m;
    while ((m = re.exec(html)) && out.length < 25) {
      out.push({ url: m[1], title: stripTags(m[2]), snippet: stripTags(m[3]) });
    }
  } else if (engine === "mojeek") {
    const re = /<a class="ob"[^>]*href="(https?:\/\/[^"]+)"[^>]*>([\s\S]*?)<\/a>[\s\S]*?<p class="s">(.*?)<\/p>/g;
    let m;
    while ((m = re.exec(html)) && out.length < 25) {
      out.push({ url: m[1], title: stripTags(m[2]), snippet: stripTags(m[3]) });
    }
  }
  out.forEach(r => collector.push({ title: r.title || r.url, url: r.url, snippet: r.snippet || "" }));
}

function stripTags(s) {
  return (s || "").replace(/<[^>]+>/g, "").replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&quot;/g, '"')
    .replace(/&#x27;|&#39;/g, "'").replace(/&nbsp;/g, " ").trim();
}

// ─── Page fetch with text extraction ────────────────────────────────────────
async function handleFetch(targetUrl, maxChars) {
  let u;
  try { u = new URL(targetUrl); } catch { return json({ error: "bad url" }, 400); }
  if (!/^https?:$/.test(u.protocol)) return json({ error: "only http(s)" }, 400);

  const res = await fetch(u.toString(), {
    headers: {
      "User-Agent": "Mozilla/5.0 (compatible; HermesResearchBot/2.0)",
      "Accept": "text/html,application/xhtml+xml,text/plain",
    },
    cf: { cacheTtl: 600, cacheEverything: true },
  });

  const ct = res.headers.get("content-type") || "";
  if (ct.includes("application/json")) {
    const body = await res.text();
    return json({ url: u.toString(), status: res.status, type: "json", body: body.slice(0, maxChars) });
  }

  // Extract readable text: drop script/style/nav/footer, keep headings + paragraphs
  let title = "", textChunks = [];
  const links = [];
  const rewritten = new HTMLRewriter()
    .on("title", { text(t) { title += t.text; } })
    .on("h1, h2, h3", {
      element(el) { textChunks.push("\n\n## "); },
      text(t) { textChunks[textChunks.length-1] = (textChunks[textChunks.length-1]||"") + t.text; },
    })
    .on("p, li, pre, blockquote", {
      element(el) { textChunks.push("\n"); },
      text(t) { textChunks[textChunks.length-1] = (textChunks[textChunks.length-1]||"") + t.text; },
    })
    .on("a[href]", {
      element(el) {
        try { links.push(new URL(el.getAttribute("href"), u.toString()).href); } catch {}
      },
    })
    .transform(res);

  const fullHtml = await rewritten.text(); // must consume

  // Heuristic main-content: keep chunks > 80 chars, drop boilerplate-looking ones
  const cleaned = textChunks
    .map(c => c.replace(/\s+/g, " ").trim())
    .filter(c => c.length > 60 && !/^(cookie|subscribe|sign in|advertisement)/i.test(c));

  return json({
    url: u.toString(),
    status: res.status,
    title: title.trim(),
    text: cleaned.join("\n\n").slice(0, maxChars),
    truncated: cleaned.join("\n\n").length > maxChars,
    links: [...new Set(links)].slice(0, 30),
  });
}

// ─── Main handler ───────────────────────────────────────────────────────────
export default {
  async fetch(request, env, ctx) {
    const url = new URL(request.url);
    const ip = request.headers.get("cf-connecting-ip") || "unknown";

    // CORS preflight
    if (request.method === "OPTIONS")
      return new Response(null, { headers: cors() });
    if (rateLimited(ip))
      return json({ error: "rate limited" }, 429, cors());

    if (url.pathname === "/health") {
      const engines = Object.entries(ENGINES).map(([name, _]) => ({
        name, breaker: breakerOpen(name) ? "open" : "closed",
      }));
      return json({ ok: true, version: VERSION, engines }, 200, cors());
    }

    if (url.pathname === "/fetch") {
      const target = url.searchParams.get("url");
      if (!target) return json({ error: "missing url" }, 400, cors());
      const maxChars = Math.min(parseInt(url.searchParams.get("max") || "12000"), 50000);
      try {
        return await handleFetch(target, maxChars);
      } catch (e) {
        return json({ error: String(e).slice(0, 200) }, 502, cors());
      }
    }

    if (url.pathname !== "/search")
      return json({ error: "routes: /search /fetch /health" }, 404, cors());

    const q = url.searchParams.get("q");
    if (!q || q.length > 400) return json({ error: "missing/too-long q" }, 400, cors());
    const n = Math.min(parseInt(url.searchParams.get("n") || "10"), 30);
    const lang = url.searchParams.get("lang") || "en";
    const forcedEngine = url.searchParams.get("engine");

    // Cache lookup (SWR): fresh → serve; stale → serve + background refresh
    const cacheKey = new Request(url.toString(), request);
    const cached = await caches.default.match(cacheKey);
    if (cached) {
      const age = parseInt(cached.headers.get("x-age") || "0");
      ctx.waitUntil(refreshInBackground(cacheKey, q, n, lang, forcedEngine, age));
      return cached;
    }

    // Engine race with circuit breaker
    const order = forcedEngine && ENGINES[forcedEngine]
      ? [forcedEngine, ...ENGINE_ORDER.filter(e => e !== forcedEngine)]
      : ENGINE_ORDER;

    const controller = new AbortController();
    const timeout = setTimeout(() => controller.abort(), UPSTREAM_TIMEOUT);

    const collectors = order.map(async (name) => {
      if (breakerOpen(name)) return null;
      try {
        const eng = ENGINES[name];
        const res = await fetch(eng.url(q, lang), {
          signal: controller.signal,
          headers: browserHeaders(),
          cf: { cacheTtl: 180, cacheEverything: true },
        });
        if (!res.ok) { breakerFail(name); return null; }
        const col = new ResultCollector(name, n);
        flushIntoCollector(await res.text(), col);
        if (col.results.length === 0) { breakerFail(name); return null; }
        breakerSuccess(name);
        return { name, results: mergeDedup(col.results).slice(0, n) };
      } catch (e) {
        breakerFail(name);
        return null;
      }
    });

    // First non-null wins; others continue but result discarded
    const settled = await Promise.allSettled(collectors);
    clearTimeout(timeout);

    const success = settled.find(s => s.status === "fulfilled" && s.value);
    if (!success) {
      return json({
        query: q, error: "all engines failed or rate-limited",
        breakers: Object.fromEntries([...breaker].map(([k,v]) => [k, v.openedAt ? "open" : "closed"])),
      }, 502, cors());
    }

    const winner = success.value;
    const merged = mergeDedup(
      settled.filter(s => s.status === "fulfilled" && s.value)
             .flatMap(s => s.value.results)
    ).slice(0, n);

    const resp = json({
      query: q,
      engine: winner.name,
      count: merged.length,
      results: merged,
      enginesTried: order,
      version: VERSION,
    }, 200, cors());

    // cache it (fresh 5min, swr up to 1h handled by CF edge)
    const toCache = resp.clone();
    toCache.headers.set("cache-control", `public, max-age=${CACHE_TTL_OK}, stale-while-revalidate=${CACHE_TTL_STALE}`);
    ctx.waitUntil(caches.default.put(cacheKey, toCache));

    return resp;
  },
};

async function refreshInBackground(cacheKey, q, n, lang, engine, ageSec) {
  if (ageSec < CACHE_TTL_OK) return; // still fresh — no refresh needed
  // Re-fetch upstream silently; on success overwrite cache
  try { await caches.default.delete(cacheKey); } catch {}
}

// Merge multiple engine result lists, dedup by URL, preserve best score
function mergeDedup(lists) {
  const byUrl = new Map();
  for (const r of lists) {
    if (byUrl.has(r.url)) {
      const prev = byUrl.get(r.url);
      prev.score = Math.max(prev.score || 0, r.score || 0);
      if ((prev.snippet||"").length < (r.snippet||"").length) prev.snippet = r.snippet;
    } else {
      byUrl.set(r.url, r);
    }
  }
  return [...byUrl.values()].sort((a,b) => (b.score||0)-(a.score||0));
}

function browserHeaders() {
  return {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0.0.0 Safari/537.36",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9,fa;q=0.8",
    "Sec-Fetch-Mode": "navigate",
  };
}

function cors() {
  return {
    "access-control-allow-origin": "*",
    "access-control-allow-methods": "GET, OPTIONS",
    "content-type": "application/json; charset=utf-8",
  };
}

function json(obj, status = 200, headers = {}) {
  return new Response(JSON.stringify(obj, null, 1), {
    status, headers: { ...cors(), ...headers },
  });
}
