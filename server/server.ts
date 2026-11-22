/**
 * lean-inf HTTP API server (Bun, zero external dependencies).
 *
 * Wraps a persistent compiled Lean 4 worker (`.lake/build/bin/inf serve-stdio`)
 * so every calculator evaluation runs inside verified native Lean 4 code with
 * sub-millisecond dispatch overhead.
 *
 * Usage:
 *   bun run server/server.ts
 *   PORT=4420 bun run server/server.ts
 */

import { existsSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";

const PORT = Number(process.env.PORT ?? "4420");
const HOST = process.env.HOST ?? "127.0.0.1";
const REPO_ROOT = resolve(import.meta.dir, "..");
const INF_BIN = join(REPO_ROOT, ".lake", "build", "bin", "inf");
const BLOG_INF_DIR = resolve(process.env.HOME ?? "", "blog", "inf");
const BLOG_UI_PATH = join(BLOG_INF_DIR, "index.html");
const CODE_SHOTS_DIR = join(BLOG_INF_DIR, "code-shots");
const BENCH_CACHE_PATH = join(REPO_ROOT, "plots", "bench_results.json");

const startedAt = Date.now();

class LeanWorker {
  private proc: ReturnType<typeof Bun.spawn> | null = null;
  private reader: ReadableStreamDefaultReader<Uint8Array> | null = null;
  private buffer = "";
  private decoder = new TextDecoder();
  private queue: Promise<unknown> = Promise.resolve();

  private ensureStarted(): void {
    if (this.proc && this.proc.exitCode === null) return;
    if (!existsSync(INF_BIN)) {
      throw new Error(`Compiled lean-inf binary not found at ${INF_BIN}. Run 'lake build' first.`);
    }
    this.buffer = "";
    this.proc = Bun.spawn([INF_BIN, "serve-stdio"], {
      cwd: REPO_ROOT,
      stdin: "pipe",
      stdout: "pipe",
      stderr: "inherit",
    });
    this.reader = (this.proc.stdout as ReadableStream<Uint8Array>).getReader();
  }

  private async readLine(): Promise<string> {
    if (!this.reader) throw new Error("Worker stdout reader unavailable");
    while (true) {
      const nl = this.buffer.indexOf("\n");
      if (nl !== -1) {
        const line = this.buffer.slice(0, nl);
        this.buffer = this.buffer.slice(nl + 1);
        return line;
      }
      const { value, done } = await this.reader.read();
      if (done) {
        this.proc = null;
        this.reader = null;
        throw new Error("lean-inf worker exited unexpectedly");
      }
      this.buffer += this.decoder.decode(value, { stream: true });
    }
  }

  public request(command: string): Promise<string> {
    const task = this.queue.then(async () => {
      this.ensureStarted();
      const stdin = this.proc!.stdin as import("bun").FileSink;
      const sanitized = command.replace(/[\r\n]+/g, " ");
      stdin.write(sanitized + "\n");
      await stdin.flush();
      return await this.readLine();
    });
    // Keep queue alive even if one request rejects
    this.queue = task.catch(() => {});
    return task;
  }
}

const worker = new LeanWorker();
const stepCache = new Map<string, string>();
let benchCache: string | null = null;

function corsHeaders(extra: Record<string, string> = {}): Record<string, string> {
  return {
    "Access-Control-Allow-Origin": "*",
    "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
    "Access-Control-Allow-Headers": "Content-Type",
    ...extra,
  };
}

function jsonResponse(body: string, status = 200): Response {
  return new Response(body, {
    status,
    headers: corsHeaders({ "Content-Type": "application/json; charset=utf-8" }),
  });
}

function stripPrefix(pathname: string): string {
  if (pathname === "/inf-api" || pathname === "/inf-api/") return "/";
  if (pathname.startsWith("/inf-api/")) return pathname.slice("/inf-api".length);
  return pathname;
}

const server = Bun.serve({
  hostname: HOST,
  port: PORT,
  async fetch(req: Request): Promise<Response> {
    if (req.method === "OPTIONS") {
      return new Response(null, { status: 204, headers: corsHeaders() });
    }

    const url = new URL(req.url);
    const path = stripPrefix(url.pathname);

    try {
      if (path === "/health" && req.method === "GET") {
        const t0 = performance.now();
        const raw = await worker.request("ping");
        const parsed = JSON.parse(raw);
        return jsonResponse(
          JSON.stringify({
            ...parsed,
            uptimeMs: Date.now() - startedAt,
            pingMs: Math.round((performance.now() - t0) * 100) / 100,
          }),
        );
      }

      if (path === "/eval" && (req.method === "POST" || req.method === "GET")) {
        let expr = "";
        let bigN = 100;
        let order = 10;
        if (req.method === "POST") {
          const payload = (await req.json()) as {
            expr?: string;
            N?: number;
            order?: number;
          };
          expr = String(payload.expr ?? "").trim();
          bigN = Number(payload.N ?? 100);
          order = Number(payload.order ?? 10);
        } else {
          expr = (url.searchParams.get("expr") ?? "").trim();
          bigN = Number(url.searchParams.get("N") ?? "100");
          order = Number(url.searchParams.get("order") ?? "10");
        }
        if (!expr) {
          return jsonResponse(JSON.stringify({ ok: false, error: "Empty expression" }), 400);
        }
        if (expr.length > 500) {
          return jsonResponse(JSON.stringify({ ok: false, error: "Expression too long (max 500 chars)" }), 400);
        }
        if (!Number.isFinite(bigN) || bigN <= 0) bigN = 100;
        if (!Number.isFinite(order)) order = 10;
        order = Math.max(4, Math.min(24, Math.round(order)));

        const t0 = performance.now();
        const raw = await worker.request(`eval\t${bigN}\t${order}\t${expr}`);
        const serverMs = Math.round((performance.now() - t0) * 100) / 100;
        const parsed = JSON.parse(raw);
        return jsonResponse(JSON.stringify({ ...parsed, engine: "lean4", serverMs }));
      }

      if (path === "/step" && req.method === "GET") {
        let bigN = Number(url.searchParams.get("N") ?? "100");
        if (!Number.isFinite(bigN) || bigN <= 0) bigN = 100;
        bigN = Math.max(1, Math.min(100000, bigN));
        const key = String(Math.round(bigN * 100) / 100);
        let cached = stepCache.get(key);
        if (!cached) {
          cached = await worker.request(`step\t${key}`);
          if (stepCache.size > 64) stepCache.clear();
          stepCache.set(key, cached);
        }
        return jsonResponse(cached);
      }

      if (path === "/bench" && req.method === "GET") {
        if (!benchCache) {
          if (existsSync(BENCH_CACHE_PATH)) {
            benchCache = readFileSync(BENCH_CACHE_PATH, "utf8");
          } else {
            benchCache = await worker.request("bench");
          }
        }
        return jsonResponse(benchCache);
      }

      if (path.startsWith("/code-shots/") && (req.method === "GET" || req.method === "HEAD")) {
        const name = path.slice("/code-shots/".length);
        if (!/^[A-Za-z0-9_-]+\.png$/.test(name)) {
          return jsonResponse(JSON.stringify({ ok: false, error: `Not found: ${path}` }), 404);
        }
        const assetPath = join(CODE_SHOTS_DIR, name);
        if (!existsSync(assetPath)) {
          return jsonResponse(JSON.stringify({ ok: false, error: `Not found: ${path}` }), 404);
        }
        const data = readFileSync(assetPath);
        return new Response(req.method === "HEAD" ? null : data, {
          headers: corsHeaders({
            "Content-Type": "image/png",
            "Content-Length": String(data.byteLength),
            "Cache-Control": "public, max-age=300",
          }),
        });
      }

      if ((path === "/" || path === "/index.html") && req.method === "GET") {
        if (existsSync(BLOG_UI_PATH)) {
          return new Response(readFileSync(BLOG_UI_PATH, "utf8"), {
            headers: corsHeaders({ "Content-Type": "text/html; charset=utf-8" }),
          });
        }
        return jsonResponse(JSON.stringify({ ok: true, service: "lean-inf API", endpoints: ["/health", "/eval", "/step", "/bench"] }));
      }

      return jsonResponse(JSON.stringify({ ok: false, error: `Not found: ${path}` }), 404);
    } catch (err) {
      const msg = err instanceof Error ? err.message : String(err);
      return jsonResponse(JSON.stringify({ ok: false, error: msg }), 500);
    }
  },
});

console.log(`lean-inf API listening on http://${HOST}:${server.port} (binary: ${INF_BIN})`);
