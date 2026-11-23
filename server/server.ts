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

import { timingSafeEqual } from "node:crypto";
import { existsSync, readFileSync } from "node:fs";
import { join, resolve } from "node:path";

/** Load key=value pairs from server/.env without overriding explicit env vars or logging secrets. */
function loadDotEnv(envPath: string): void {
  if (!existsSync(envPath)) return;
  const content = readFileSync(envPath, "utf8");
  for (const rawLine of content.split(/\r?\n/)) {
    const line = rawLine.trim();
    if (!line || line.startsWith("#")) continue;
    const eq = line.indexOf("=");
    if (eq <= 0) continue;
    const key = line.slice(0, eq).trim();
    let val = line.slice(eq + 1).trim();
    if (
      (val.startsWith("\"") && val.endsWith("\"")) ||
      (val.startsWith("'") && val.endsWith("'"))
    ) {
      val = val.slice(1, -1);
    }
    if (!process.env[key]) {
      process.env[key] = val;
    }
  }
}

loadDotEnv(join(import.meta.dir, ".env"));

const PORT = Number(process.env.PORT ?? "4420");
const HOST = process.env.HOST ?? "127.0.0.1";
const REPO_ROOT = resolve(import.meta.dir, "..");
const INF_BIN = join(REPO_ROOT, ".lake", "build", "bin", "inf");
const BLOG_INF_DIR = resolve(process.env.HOME ?? "", "blog", "inf");
const BLOG_UI_PATH = join(BLOG_INF_DIR, "index.html");
const CODE_SHOTS_DIR = join(BLOG_INF_DIR, "code-shots");
const BENCH_CACHE_PATH = join(REPO_ROOT, "plots", "bench_results.json");
const OCR_MAX_BODY_BYTES = 2 * 1024 * 1024;
const EVAL_MAX_BODY_BYTES = 32 * 1024;
const OCR_OVERALL_BUDGET_MS = 17_000;
const OCR_PER_MODEL_TIMEOUT_MS = 7_500;
const WORKER_DEFAULT_TIMEOUT_MS = 5_000;
const WORKER_BENCH_TIMEOUT_MS = 120_000;
const OCR_RATE_LIMIT_MAX = 30;
const OCR_RATE_LIMIT_WINDOW_MS = 60_000;
const ocrRequestTimestamps: number[] = [];

function clampBigN(raw: unknown): number {
  const n = Number(raw ?? 100);
  if (!Number.isFinite(n) || n <= 0) return 100;
  return Math.max(1e-6, Math.min(1e12, n));
}

const OCR_SYSTEM_PROMPT = `You are a high-precision mathematical handwriting OCR engine for the lean-inf Levi-Civita calculator (nonstandard analysis / infinitesimals & infinities in Lean 4).
Your job is to transcribe the handwritten mathematical expression in the image into a single valid ASCII lean-inf calculator expression.

STRICT GRAMMAR (LeanInf/Parser.lean):
- Constants & auto plot variable:
  - H : infinite unit (map handwritten ∞, ω, H to H)
  - eps : infinitesimal 1/H (map handwritten ε, ϵ, dx, eps to eps)
  - x : free plot variable (KEEP free variable x verbatim for functions of x, e.g. 1/(1+exp(-H*x)), dstep(x), x^2 + eps!)
  - pi : 3.14159... (map π to pi)
  - e : Euler's number
- Operators: +  -  *  /  ^  unary -  parentheses (...)  comparisons == != < <= > >=  statements separated by ;  assignments a = expr  function defs f(x) = body
- Built-in functions:
  sin, cos, tan, exp, ln, log, sqrt, abs, std, sign, signum, lead, order,
  coeff(x, e), trunc(x, n), eval(x, N),
  diff(expr, var, point), deriv(fnName, point),
  step(x), dstep(x), ddstep(x),
  isinf, isfinite, isinfsm

MANDATORY REWRITE RULES:
1. Stacked fractions: write (numerator)/(denominator), or simple 1/(1+exp(-H*x)) without extra outer parens when clear.
2. Exponents MUST use ASCII ^ with parentheses around negative or compound exponents: e.g. (1 + eps)^(-1), H^(1/2), eps^3, (1 + eps)^(1/eps). NEVER output Unicode superscripts or LaTeX.
3. ALWAYS write explicit * between adjacent identifiers (e.g. H*x, H*eps, NOT Hx, Heps, or Hε).
4. Radicals: sqrt(A) for square root, (A)^(1/n) for nth root.
5. Derivatives at a point: d/dx (E) |_{x=a} -> diff(E, x, a); f(x) = E; f'(a) -> f(x) = E; deriv(f, a).
6. Nonstandard step / Dirac delta: ONLY map explicit symbols L_H(x), Θ(x), u(x), step(x) -> step(x); δ(x), L'_H(x), dstep(x) -> dstep(x); δ'(x), L''_H(x), ddstep(x) -> ddstep(x). NEVER collapse an explicit logistic formula like 1/(1+e^(-Hx)) or 1/(1+exp(-Hx)) into step(x) — transcribe it faithfully as 1/(1+exp(-H*x)) keeping x!
7. Exponential notation: ALWAYS rewrite e^(...) -> exp(...) (e.g., 1/(1+e^(-Hx)) -> 1/(1+exp(-H*x))).
8. Output ONLY valid JSON matching the schema: { "expr": "...", "confidence": 0.0-1.0, "note": "" }. Never include LaTeX commands, dollar signs, backticks, or prose inside expr.`;

const SUPERSCRIPT_MAP: Record<string, string> = {
  "⁰": "0",
  "¹": "1",
  "²": "2",
  "³": "3",
  "⁴": "4",
  "⁵": "5",
  "⁶": "6",
  "⁷": "7",
  "⁸": "8",
  "⁹": "9",
  "⁺": "+",
  "⁻": "-",
  "⁽": "(",
  "⁾": ")",
};

/** Rewrites `e^(...)` (with arbitrarily nested parens) and `e^<atom>` (including nested `^`) to `exp(...)`. */
function rewriteEToExp(input: string): string {
  const s = input;
  let out = "";
  let i = 0;
  while (i < s.length) {
    const isWordBoundaryBefore = i === 0 || !/[A-Za-z0-9_]/.test(s[i - 1]);
    if (s[i] === "e" && isWordBoundaryBefore) {
      let j = i + 1;
      while (j < s.length && s[j] === " ") j++;
      if (j < s.length && s[j] === "^") {
        j++;
        while (j < s.length && s[j] === " ") j++;
        // Handle e^(...) as well as e^-(...) / e^+(...)
        let signPrefix = "";
        if (j + 1 < s.length && (s[j] === "-" || s[j] === "+") && s[j + 1] === "(") {
          signPrefix = s[j];
          j++;
        }
        if (j < s.length && s[j] === "(") {
          let depth = 1;
          let k = j + 1;
          while (k < s.length && depth > 0) {
            if (s[k] === "(") depth++;
            else if (s[k] === ")") depth--;
            k++;
          }
          if (depth === 0) {
            const inner = rewriteEToExp(s.slice(j + 1, k - 1));
            out += signPrefix ? `exp(${signPrefix}(${inner}))` : `exp(${inner})`;
            i = k;
            continue;
          }
        } else if (j < s.length) {
          // Capture `^` inside unparenthesized exponents (e.g. e^-H*x^2 -> exp(-H*x^2))
          const m = s.slice(j).match(/^([+-]?[A-Za-z0-9_.*^]+)/);
          if (m) {
            out += `exp(${m[1]})`;
            i = j + m[1].length;
            continue;
          }
        }
      }
    }
    out += s[i];
    i++;
  }
  return out;
}

function sanitizeLeanInfExpr(raw: string): string {
  let s = raw.trim();
  // Strip accidental markdown fences, backticks, and LaTeX math delimiters
  s = s.replace(/^```[a-zA-Z]*\s*/g, "").replace(/\s*```$/g, "");
  s = s.replace(/`/g, "");
  s = s.replace(/^\$\$|\$\$$/g, "").replace(/^\$|\$$/g, "");
  s = s.replace(/^\\\(|\\\)$/g, "").replace(/^\\\[|\\\]$/g, "");

  // Common LaTeX fallbacks if Gemini ever leaks LaTeX
  s = s.replace(/\\frac\s*\{([^{}]+)\}\s*\{([^{}]+)\}/g, "(($1)/($2))");
  s = s.replace(/\\sqrt\s*\{([^{}]+)\}/g, "sqrt($1)");
  s = s.replace(/\\(?:cdot|times)/g, "*");
  s = s.replace(/\\(?:varepsilon|epsilon)/g, "eps");
  s = s.replace(/\\infty/g, "H");
  s = s.replace(/\\pi/g, "pi");
  s = s.replace(/\\left|\\right/g, "");

  // Separate adjacent identifier + Greek epsilon before replacing epsilon -> eps
  s = s.replace(/([A-Za-z])([εϵɛ])/g, "$1*eps");
  s = s.replace(/([εϵɛ])([A-Za-z])/g, "eps*$2");

  // Unicode symbol normalization
  s = s
    .replace(/[−–—‒]/g, "-")
    .replace(/[×·⋅∙]/g, "*")
    .replace(/[÷⁄∕]/g, "/")
    .replace(/≤/g, "<=")
    .replace(/≥/g, ">=")
    .replace(/≠/g, "!=")
    .replace(/[∞ω]/g, "H")
    .replace(/[εϵɛ]/g, "eps")
    .replace(/π/g, "pi")
    .replace(/（/g, "(")
    .replace(/）/g, ")")
    .replace(/［/g, "[")
    .replace(/］/g, "]");

  // Radicals
  s = s.replace(/√\s*\(([^()]+)\)/g, "sqrt($1)");
  s = s.replace(/√\s*([A-Za-z0-9_.]+)/g, "sqrt($1)");

  // Superscript runs: e.g. x² -> x^2, (1+eps)⁻¹ -> (1+eps)^(-1)
  s = s.replace(/([⁺⁻⁰¹²³⁴⁵⁶⁷⁸⁹⁽⁾]+)/g, (run) => {
    const mapped = Array.from(run)
      .map((ch) => SUPERSCRIPT_MAP[ch] ?? ch)
      .join("");
    if (mapped.startsWith("(") && mapped.endsWith(")")) {
      return `^${mapped}`;
    }
    if (mapped.includes("-") || mapped.includes("+")) {
      return `^(${mapped})`;
    }
    return `^${mapped}`;
  });

  // Normalize e^(...) -> exp(...) (handles nested parens like 1/(1+e^(-H*(x-0.5))))
  s = rewriteEToExp(s);

  // Catch accidental concatenation of H / eps / x
  s = s.replace(/\bHeps\b/g, "H*eps");
  s = s.replace(/\bepsH\b/g, "eps*H");
  s = s.replace(/\bHx\b/g, "H*x");
  s = s.replace(/\bxH\b/g, "x*H");
  s = s.replace(/\bhx\b/g, "h*x");
  s = s.replace(/\bxeps\b/g, "x*eps");
  s = s.replace(/\bepsx\b/g, "eps*x");

  // Collapse whitespace
  s = s.replace(/\s+/g, " ").trim();
  return s;
}

function verifyInfPadToken(provided: string | null): boolean {
  const expected = process.env.INFPAD_OCR_TOKEN ?? "";
  if (!expected || !provided) return false;
  const a = Buffer.from(provided, "utf8");
  const b = Buffer.from(expected, "utf8");
  if (a.length !== b.length) return false;
  return timingSafeEqual(a, b);
}

function checkOcrRateLimit(): boolean {
  const now = Date.now();
  while (ocrRequestTimestamps.length > 0 && now - ocrRequestTimestamps[0] > OCR_RATE_LIMIT_WINDOW_MS) {
    ocrRequestTimestamps.shift();
  }
  if (ocrRequestTimestamps.length >= OCR_RATE_LIMIT_MAX) {
    return false;
  }
  ocrRequestTimestamps.push(now);
  return true;
}

interface GeminiOcrResult {
  expr: string;
  confidence: number;
  note: string;
  model: string;
  ocrMs: number;
}

async function callGeminiVisionOcr(imageBase64: string, mimeType: string): Promise<GeminiOcrResult> {
  const apiKey = process.env.GEMINI_API_KEY ?? "";
  if (!apiKey) {
    throw new Error("Server OCR is not configured (missing GEMINI_API_KEY in server/.env)");
  }

  const primaryModel = (process.env.GEMINI_OCR_MODEL ?? "gemini-flash-lite-latest").trim() || "gemini-flash-lite-latest";
  const candidateModels = [
    primaryModel,
    "gemini-flash-lite-latest",
    "gemini-3.5-flash-lite",
    "gemini-flash-latest",
    "gemini-2.5-flash",
  ];
  const modelsToTry = Array.from(new Set(candidateModels));

  const cleanBase64 = imageBase64.replace(/^data:[^;]+;base64,/, "").replace(/\s+/g, "");
  const overallStart = performance.now();
  let lastErr = "Gemini OCR request failed";

  for (const model of modelsToTry) {
    const remainingBudgetMs = OCR_OVERALL_BUDGET_MS - (performance.now() - overallStart);
    if (remainingBudgetMs < 1500) {
      lastErr = `${lastErr} (overall ${OCR_OVERALL_BUDGET_MS}ms OCR budget exhausted)`;
      break;
    }
    const perModelTimeoutMs = Math.max(1500, Math.min(OCR_PER_MODEL_TIMEOUT_MS, Math.floor(remainingBudgetMs)));
    const t0 = performance.now();
    const url = `https://generativelanguage.googleapis.com/v1beta/models/${encodeURIComponent(model)}:generateContent`;

    const buildBody = (includeMinimalThinking: boolean) => ({
      system_instruction: {
        parts: [{ text: OCR_SYSTEM_PROMPT }],
      },
      contents: [
        {
          role: "user",
          parts: [
            {
              text: "Transcribe the handwritten mathematical expression in this image into a single valid ASCII lean-inf calculator expression.",
            },
            {
              inline_data: {
                mime_type: mimeType,
                data: cleanBase64,
              },
            },
          ],
        },
      ],
      generationConfig: {
        temperature: 0.0,
        maxOutputTokens: 256,
        responseMimeType: "application/json",
        responseSchema: {
          type: "OBJECT",
          properties: {
            expr: { type: "STRING" },
            confidence: { type: "NUMBER" },
            note: { type: "STRING" },
          },
          required: ["expr", "confidence", "note"],
        },
        ...(includeMinimalThinking ? { thinkingConfig: { thinkingLevel: "minimal" } } : {}),
      },
    });

    let res: Response;
    try {
      res = await fetch(url, {
        method: "POST",
        headers: {
          "Content-Type": "application/json",
          "x-goog-api-key": apiKey,
        },
        signal: AbortSignal.timeout(perModelTimeoutMs),
        body: JSON.stringify(buildBody(true)),
      });

      if (res.status === 400) {
        const errPreview = await res.text();
        if (/thinking/i.test(errPreview)) {
          const retryRemaining = Math.max(1500, Math.floor(OCR_OVERALL_BUDGET_MS - (performance.now() - overallStart)));
          res = await fetch(url, {
            method: "POST",
            headers: {
              "Content-Type": "application/json",
              "x-goog-api-key": apiKey,
            },
            signal: AbortSignal.timeout(Math.min(OCR_PER_MODEL_TIMEOUT_MS, retryRemaining)),
            body: JSON.stringify(buildBody(false)),
          });
        } else {
          lastErr = `Gemini API (${model}) HTTP 400: ${errPreview.slice(0, 240)}`;
          continue;
        }
      }
    } catch (err) {
      lastErr = `Gemini API (${model}) network/timeout error: ${err instanceof Error ? err.message : String(err)}`;
      continue;
    }

    if (!res.ok) {
      const errText = await res.text();
      lastErr = `Gemini API (${model}) HTTP ${res.status}: ${errText.slice(0, 240)}`;
      if (res.status === 404 || res.status === 429 || res.status >= 500) {
        continue;
      }
      throw new Error(lastErr);
    }

    const data = (await res.json()) as {
      candidates?: Array<{
        content?: { parts?: Array<{ text?: string }> };
      }>;
    };
    const ocrMs = Math.round((performance.now() - t0) * 100) / 100;
    const rawText = data.candidates?.[0]?.content?.parts?.map((p) => p.text ?? "").join("").trim() ?? "";
    if (!rawText) {
      lastErr = `Gemini API (${model}) returned empty content`;
      continue;
    }

    let expr = rawText;
    let confidence = 0.9;
    let note = "";
    try {
      const parsed = JSON.parse(rawText) as { expr?: unknown; confidence?: unknown; note?: unknown };
      expr = typeof parsed.expr === "string" ? parsed.expr : "";
      confidence = typeof parsed.confidence === "number" && Number.isFinite(parsed.confidence)
        ? Math.max(0, Math.min(1, parsed.confidence))
        : 0.9;
      note = typeof parsed.note === "string" ? parsed.note : "";
    } catch {
      expr = rawText;
      note = "Fallback non-JSON parse";
    }

    return { expr, confidence, note, model, ocrMs };
  }

  throw new Error(lastErr);
}

const startedAt = Date.now();

class LeanWorker {
  private proc: ReturnType<typeof Bun.spawn> | null = null;
  private reader: ReadableStreamDefaultReader<Uint8Array> | null = null;
  private buffer = "";
  private decoder = new TextDecoder();
  private queue: Promise<unknown> = Promise.resolve();

  private resetIfCurrent(proc: ReturnType<typeof Bun.spawn>): void {
    if (this.proc === proc) {
      this.proc = null;
      this.reader = null;
      this.buffer = "";
    }
  }

  private killAndReset(proc: ReturnType<typeof Bun.spawn>, reader: ReadableStreamDefaultReader<Uint8Array>): void {
    try {
      proc.kill("SIGKILL");
    } catch {
      // ignore if already exited
    }
    try {
      void reader.cancel();
    } catch {
      // ignore reader cancel failure
    }
    this.resetIfCurrent(proc);
  }

  private ensureStarted(): { proc: ReturnType<typeof Bun.spawn>; reader: ReadableStreamDefaultReader<Uint8Array> } {
    if (this.proc && this.proc.exitCode === null && this.reader) {
      return { proc: this.proc, reader: this.reader };
    }
    if (!existsSync(INF_BIN)) {
      throw new Error(`Compiled lean-inf binary not found at ${INF_BIN}. Run 'lake build' first.`);
    }
    this.buffer = "";
    const proc = Bun.spawn([INF_BIN, "serve-stdio"], {
      cwd: REPO_ROOT,
      stdin: "pipe",
      stdout: "pipe",
      stderr: "inherit",
    });
    const reader = (proc.stdout as ReadableStream<Uint8Array>).getReader();
    this.proc = proc;
    this.reader = reader;
    return { proc, reader };
  }

  private async readLine(
    proc: ReturnType<typeof Bun.spawn>,
    reader: ReadableStreamDefaultReader<Uint8Array>,
  ): Promise<string> {
    while (true) {
      if (this.proc !== proc) {
        throw new Error("lean-inf worker was recycled");
      }
      const nl = this.buffer.indexOf("\n");
      if (nl !== -1) {
        const line = this.buffer.slice(0, nl);
        this.buffer = this.buffer.slice(nl + 1);
        return line;
      }
      const { value, done } = await reader.read();
      if (done) {
        this.resetIfCurrent(proc);
        throw new Error("lean-inf worker exited unexpectedly");
      }
      if (this.proc !== proc) {
        throw new Error("lean-inf worker was recycled");
      }
      this.buffer += this.decoder.decode(value, { stream: true });
    }
  }

  public request(command: string, timeoutMs = WORKER_DEFAULT_TIMEOUT_MS): Promise<string> {
    const task = this.queue.then(async () => {
      const { proc, reader } = this.ensureStarted();
      const stdin = proc.stdin as import("bun").FileSink;
      const sanitized = command.replace(/[\r\n]+/g, " ");
      let timer: ReturnType<typeof setTimeout> | null = null;
      const timeoutPromise = new Promise<never>((_, reject) => {
        timer = setTimeout(() => {
          this.killAndReset(proc, reader);
          reject(new Error(`Lean 4 worker timed out after ${timeoutMs} ms and was respawned`));
        }, timeoutMs);
      });
      try {
        stdin.write(sanitized + "\n");
        await stdin.flush();
        return await Promise.race([this.readLine(proc, reader), timeoutPromise]);
      } catch (err) {
        if (this.proc === proc && proc.exitCode !== null) {
          this.resetIfCurrent(proc);
        }
        throw err;
      } finally {
        if (timer !== null) clearTimeout(timer);
      }
    });
    // Keep queue alive even if one request rejects or times out
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
    "Access-Control-Allow-Headers": "Content-Type, X-InfPad-Token",
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
            ocrConfigured: Boolean(process.env.GEMINI_API_KEY && process.env.INFPAD_OCR_TOKEN),
            uptimeMs: Date.now() - startedAt,
            pingMs: Math.round((performance.now() - t0) * 100) / 100,
          }),
        );
      }

      if (path === "/ocr-eval" && req.method === "POST") {
        if (!verifyInfPadToken(req.headers.get("x-infpad-token"))) {
          return jsonResponse(
            JSON.stringify({ ok: false, error: "Unauthorized: invalid or missing X-InfPad-Token" }),
            401,
          );
        }

        if (!checkOcrRateLimit()) {
          return jsonResponse(
            JSON.stringify({ ok: false, error: "Rate limit exceeded (max 30 OCR requests/minute)" }),
            429,
          );
        }

        const contentLengthHeader = req.headers.get("content-length");
        if (contentLengthHeader && Number(contentLengthHeader) > OCR_MAX_BODY_BYTES) {
          return jsonResponse(
            JSON.stringify({ ok: false, error: "Payload too large (max 2 MB)" }),
            413,
          );
        }

        const rawBody = await req.text();
        if (Buffer.byteLength(rawBody, "utf8") > OCR_MAX_BODY_BYTES) {
          return jsonResponse(
            JSON.stringify({ ok: false, error: "Payload too large (max 2 MB)" }),
            413,
          );
        }

        let payload: {
          imageBase64?: unknown;
          mimeType?: unknown;
          N?: unknown;
          order?: unknown;
        };
        try {
          payload = JSON.parse(rawBody);
        } catch {
          return jsonResponse(JSON.stringify({ ok: false, error: "Invalid JSON body" }), 400);
        }

        const imageBase64 = typeof payload.imageBase64 === "string" ? payload.imageBase64.trim() : "";
        if (!imageBase64) {
          return jsonResponse(JSON.stringify({ ok: false, error: "Missing imageBase64" }), 400);
        }

        const mimeTypeRaw = typeof payload.mimeType === "string" ? payload.mimeType.trim() : "image/png";
        const allowedMimes = new Set(["image/png", "image/jpeg", "image/webp"]);
        const mimeType = allowedMimes.has(mimeTypeRaw) ? mimeTypeRaw : "image/png";

        const bigN = clampBigN(payload.N);
        let order = Number(payload.order ?? 10);
        if (!Number.isFinite(order)) order = 10;
        order = Math.max(4, Math.min(24, Math.round(order)));

        const ocr = await callGeminiVisionOcr(imageBase64, mimeType);
        const recognizedExpr = ocr.expr.trim();
        const normalizedExpr = sanitizeLeanInfExpr(recognizedExpr);

        if (!normalizedExpr) {
          return jsonResponse(
            JSON.stringify({
              ok: false,
              error: "No mathematical expression recognized in ink image",
              recognizedExpr,
              normalizedExpr: "",
              confidence: ocr.confidence,
              note: ocr.note,
              model: ocr.model,
              ocrMs: ocr.ocrMs,
              serverMs: 0,
              ocr: {
                expr: "",
                rawExpr: recognizedExpr,
                confidence: ocr.confidence,
                note: ocr.note,
                model: ocr.model,
                ocrMs: ocr.ocrMs,
              },
              eval: {
                ok: false,
                input: "",
                error: "No mathematical expression recognized",
                engine: "lean4",
                serverMs: 0,
              },
            }),
          );
        }

        if (normalizedExpr.length > 500) {
          return jsonResponse(
            JSON.stringify({
              ok: false,
              error: "Recognized expression too long (max 500 chars)",
              recognizedExpr,
              normalizedExpr: normalizedExpr.slice(0, 500),
              ocrMs: ocr.ocrMs,
              serverMs: 0,
            }),
            400,
          );
        }

        const tEval0 = performance.now();
        const rawEval = await worker.request(`eval\t${bigN}\t${order}\t${normalizedExpr}`);
        const serverMs = Math.round((performance.now() - tEval0) * 100) / 100;
        const evalPayload = { ...JSON.parse(rawEval), engine: "lean4", serverMs };

        return jsonResponse(
          JSON.stringify({
            ok: Boolean(evalPayload.ok),
            recognizedExpr,
            normalizedExpr,
            confidence: ocr.confidence,
            note: ocr.note,
            model: ocr.model,
            ocrMs: ocr.ocrMs,
            serverMs,
            ocr: {
              expr: normalizedExpr,
              rawExpr: recognizedExpr,
              confidence: ocr.confidence,
              note: ocr.note,
              model: ocr.model,
              ocrMs: ocr.ocrMs,
            },
            eval: evalPayload,
          }),
        );
      }

      if (path === "/eval" && (req.method === "POST" || req.method === "GET")) {
        let expr = "";
        let bigN = 100;
        let order = 10;
        if (req.method === "POST") {
          const contentLengthHeader = req.headers.get("content-length");
          if (contentLengthHeader && Number(contentLengthHeader) > EVAL_MAX_BODY_BYTES) {
            return jsonResponse(JSON.stringify({ ok: false, error: "Payload too large (max 32 KB)" }), 413);
          }
          const rawBody = await req.text();
          if (Buffer.byteLength(rawBody, "utf8") > EVAL_MAX_BODY_BYTES) {
            return jsonResponse(JSON.stringify({ ok: false, error: "Payload too large (max 32 KB)" }), 413);
          }
          let payload: { expr?: unknown; N?: unknown; order?: unknown };
          try {
            payload = JSON.parse(rawBody);
          } catch {
            return jsonResponse(JSON.stringify({ ok: false, error: "Invalid JSON body" }), 400);
          }
          if (!payload || typeof payload !== "object") {
            return jsonResponse(JSON.stringify({ ok: false, error: "Invalid JSON object" }), 400);
          }
          expr = String(payload.expr ?? "").trim();
          bigN = clampBigN(payload.N);
          order = Number(payload.order ?? 10);
        } else {
          expr = (url.searchParams.get("expr") ?? "").trim();
          bigN = clampBigN(url.searchParams.get("N"));
          order = Number(url.searchParams.get("order") ?? "10");
        }
        if (!expr) {
          return jsonResponse(JSON.stringify({ ok: false, error: "Empty expression" }), 400);
        }
        if (expr.length > 500) {
          return jsonResponse(JSON.stringify({ ok: false, error: "Expression too long (max 500 chars)" }), 400);
        }
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
            benchCache = await worker.request("bench", WORKER_BENCH_TIMEOUT_MS);
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
