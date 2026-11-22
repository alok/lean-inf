# `lean-inf` Revitalization & Theorem Talk Spec

## Goals
1. **Revitalize `lean-inf`** (`~/lean-inf`):
   - Pin `lean-toolchain` to `leanprover/lean4:v4.36.0` (stable, installed locally) with zero errors, zero warnings (`linter.missingDocs` + `doc.verso` clean), zero `sorry`.
   - Fix latent bugs in original code:
     - `Std.HashMap` `BEq` (`ys.getD k v == v` returned `true` on missing keys → `ys.get? k == some v`).
     - `LeviCivitaNum.signum` sorted ascending (`exp₁ < exp₂`), reading the smallest infinitesimal instead of dominant largest exponent (`exp₁ > exp₂`).
     - `String.data` compatibility on Lean 4.36+.
     - Non-pure `Inv LeviCivitaNum` stub returning `0`.
     - Stub `Parser.lean` (`"1+ε"` returned `1 + H`, everything else failed).
   - Keep the original naive HashMap `LeviCivitaNum` operational as the reference baseline for differential testing and benchmarking.

2. **Verified Fast Representation & Refactors (`zero sorry`, `#print axioms` clean)**:
   - `SortedLC`: strictly descending by exponent `Array (Rat × Rat)` with nonzero coefficients (`WF` invariant proven preserved by all ops).
   - Semantic spec `coeffOf : List (Rat × Rat) → Rat → Rat`.
   - Verified refactors with machine-checked equivalence theorems:
     1. `signum` / `leadingTerm`: `O(n log n)` sort → `O(1)` head lookup.
     2. `add` / `sub`: HashMap + `filterZeros` → `O(n + m)` two-pointer sorted merge with zero-pruning.
     3. `mul`:
        - `mulTree`: balanced binary tree merge of sorted shifted runs (`O(nm log n)`, zero hashing), proven equivalent to `mulNaive`.
        - `mulKaratsuba`: verified dense Karatsuba (`O(n^1.585)`) with exact arithmetic-progression grid detection + fallback to `mulTree`, proven equivalent to `mulNaive` with zero `sorry`!
     4. `powFast`: `O(k)` linear loop → `O(log k)` binary exponentiation, proven equivalent to `powNaive`.
     5. `invNewton`: `O(N^2)` recomputed geometric series → `O(log N)` Newton-Raphson (`y_{k+1} = y_k(2 - x y_k)`), with formal proof of quadratic residual squaring `1 - x y_{k+1} = (1 - x y_k)^2`.

3. **Full Calculator Engine, Test Suite & Benchmarks (`lake exe inf`)**:
   - Complete recursive-descent parser & evaluator: `H`, `ε`/`eps`/`d`, `pi`, `e`, arithmetic, implicit mul, rational/integer powers, comparisons, `std`, `sign`, `abs`, `lead`, `order`, `coeff`, `exp`, `ln`, `sin`, `cos`, `sqrt`, `step`, `dstep`, `ddstep`, `deriv`, `eval(expr, N)`, variable bindings (`a = 6*7; a+5`), function definitions (`f x = x^2; f(f(2))`).
   - CLI modes: `eval <expr>`, `repl`, `test`, `bench`, `step-demo [--N <float>] [--json]`, `serve-stdio` (persistent JSON-line worker for the web server).
   - Comprehensive differential & unit test suite (100+ tests: naive vs fast equivalence, algebraic laws, Crowell `Test.js` corpus, step-function & finite evaluation).

4. **Step Function → Dirac Delta & Finite Evaluation (`H ↦ N`)**:
   - Nonstandard logistic step `L_H(x) = 1 / (1 + exp(-H * x))`.
   - Pure Levi-Civita AD via second-order infinitesimal `η = ε²` (so `H·η = ε` is finite-taylor-expandable!):
     - `x = 0`: `L_H(0) = 1/2`, `L'_H(0) = (1/4) H` (`D_{ε²} L_H(0) = 1/4 H - 1/48 ε + ...`).
     - `x = c·ε`: `L'_H(c·ε) = σ'(c) H + O(ε)` where `σ'(c) = e^{-c} / (1 + e^{-c})^2`.
     - Appreciable `x ≠ 0`: `L_H(x) = 1` (`x > 0`) or `0` (`x < 0`), `L'_H(x) = 0`.
     - Second derivative (dipole): `D²_{ε²} L_H(c·ε) = σ''(c) H² + ...`.
     - Hyperfinite Riemann integral check: `∑ σ'(c_k) H · (Δc · ε) = ∑ σ'(c_k) Δc ≈ 1`.
   - Finite specialization `evalAt(a, N) = ∑ c_i · N^{q_i}` replacing `H ↦ N`, `ε ↦ 1/N`, and `x = c·ε ↦ c/N`.
   - High-resolution plots generated directly from `lake exe inf` JSON output.

5. **Web App Attached to `~/blog` + Local Lean 4 Server**:
   - `~/lean-inf/server/server.ts` (Bun HTTP server wrapping persistent `lake exe inf serve-stdio` on `127.0.0.1:4420`, with LaunchAgent plist & Tailscale Funnel `/inf-api` route without disturbing `/` `site-editor`).
   - `~/blog/inf/index.html`: interactive Calculator REPL + Step Function `H ↦ N` Live Plotter + Verified Refactors & Benchmarks view; connects to live Lean 4 server when reachable and falls back seamlessly to a faithful client-side JS mirror when offline.
   - Linked cleanly from `~/blog` (`_config.yml` or nav / `Papers.md` / `2024-09-28` post) without breaking Verso/GwernPort checks.

6. **Theorem Whiteboard Talk Prep + Allume Boards + Dev Guide**:
   - `~/lean-inf/docs/theorem-whiteboard-talk.md`: complete whiteboard script, talking points, drawings, demo list, and tough Q&A.
   - `~/lean-inf/docs/dev-guide.md`: deep manual-reconstruction developer guide per user preference.
   - Organized Allume workspace boards under root board (`/`).
