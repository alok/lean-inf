# `lean-inf`

**Compute with infinities (`H`) and infinitesimals (`ε = 1/H`) in Lean 4 — with zero-`sorry` verified fast algorithms, discontinuous automatic differentiation, and a live calculator web app.**

## Highlights

- **Exact Levi-Civita arithmetic** with rational exponents and rational coefficients (`H * ε = 1`, `2H + 1 > 2H`, `ε² < ε < √ε < 1 < H`).
- **Zero-`sorry` verified refactors** (`FastLC` vs original naive HashMap `LeviCivitaNum`, `#print axioms` clean — only `[propext, Classical.choice, Quot.sound]`):
  - `O(1)` `signumFast` vs `O(n log n)` sort (**311× – 540× faster**)
  - `O(n + m)` two-pointer sorted merge addition (`addMerge`)
  - Verified **Karatsuba** multiplication (`O(n^1.585)`) + balanced-tree sparse fallback (`mulTree`) (**5.8× faster at n=512**)
  - `O(log k)` binary exponentiation (`powFast`) (**4.3× faster at k=48**)
  - `O(log N)` quadratically convergent **Newton-Raphson** inversion (`newton_order_doubles`) (**13.8× faster at order=40**)
- **Step function → Dirac delta via pure Levi-Civita AD** (`LeanInf/StepFunction.lean`): differentiates `L_H(x) = 1 / (1 + e^{-Hx})` automatically with step `ε²` (yielding `(1/4)H - (1/48)ε + ...` at `x = 0` and hyperfinite area `≈ 1.000`), plus **finite specialization** `evalFinite` (`H ↦ N`, `ε ↦ 1/N`).
- **122-test differential & expression suite** (`lake exe inf test`) covering Crowell's `Test.js`, algebraic laws, naive-vs-fast equivalence, and step-function AD.
- **Live HTTP API & Blog Calculator** (`server/server.ts`, `~/blog/inf/index.html`).

## Quick Start

```bash
lake build
.lake/build/bin/inf test                   # 122/122 differential & expression tests
.lake/build/bin/inf bench                  # Naive HashMap vs Verified FastLC benchmarks
.lake/build/bin/inf step-demo --N 100      # Step function -> Dirac delta & H -> 100 eval
.lake/build/bin/inf eval "dstep(0)" --N 100
.lake/build/bin/inf repl                   # Interactive calculator
uv run scripts/generate_plots.py           # Regenerate plots from Lean 4 JSON
bun run server/server.ts                   # Start Lean 4 HTTP API on 127.0.0.1:4420
```

## Documentation

- [Theorem Whiteboard Talk Guide](docs/theorem-whiteboard-talk.md)
- [Build-It-Yourself Developer Guide](docs/dev-guide.md)
- [Specification](docs/SPEC.md)
