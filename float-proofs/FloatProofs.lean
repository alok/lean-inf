import FloatProofs.Convert
import FloatProofs.EvalFinite
import FloatProofs.Sigmoid
import FloatProofs.DiracBridge
import FloatProofs.Homomorphism

/-!
# FloatProofs — Verified IEEE-754 Binary64 & Native Float Bridge for `LeanInf`

Zero-`sorry`, zero-`native_decide` proofs connecting `LeanInf.FastLC` to actual IEEE-754
`Binary64` and Lean's native `Float` via `FloatLib`:
- `FloatProofs.Convert` (T1): Single-rounding `ratToBinary64` half-ULP + `MixedError` + lossless
  `Binary64 ↪ FastLC` `stdPart` round-trip.
- `FloatProofs.EvalFinite` (T2): End-to-end `H ↦ N` bounds for left-to-right `evalFiniteB64`,
  Ogita–Rump–Oishi `TwoSum` compensated `evalFiniteSum2`, and single-rounding `evalFiniteExactSum`.
- `FloatProofs.Sigmoid` (T3): Unconditional overflow-free `[0, 1]` & `< 4u` `sigmoidB64` plus
  auto-generated `roundoff mixed` bounds directly on Lean's native `Float`.
- `FloatProofs.DiracBridge` (T4): Symbolic-to-float Dirac delta peak bridge at `x = 0` +
  kernel-checked `float_decide` certification at `N = 100`.
- `FloatProofs.Homomorphism` (T5): Exact `evalExactInt` ring homomorphism + commutative-diagram
  float bound + kernel-checked `float_decide` catastrophic-cancellation separation.
-/
