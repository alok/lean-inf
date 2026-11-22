import LeanInf.VerifiedRefactor

namespace LeanInf
namespace StepFunction

open FastLC

/-- Exact closed-form logistic function `σ(u) = 1 / (1 + e^(-u))` on `Float`. -/
def sigmoidFloat (u : Float) : Float :=
  if u ≥ 0.0 then
    let e := Float.exp (-u)
    1.0 / (1.0 + e)
  else
    let e := Float.exp u
    e / (1.0 + e)

/-- Exact closed-form first derivative `σ'(u) = σ(u)(1 - σ(u))` on `Float`. -/
def sigmoidDerivFloat (u : Float) : Float :=
  let s := sigmoidFloat u
  s * (1.0 - s)

/-- Exact closed-form second derivative `σ''(u) = σ(u)(1 - σ(u))(1 - 2σ(u))` on `Float`. -/
def sigmoidDeriv2Float (u : Float) : Float :=
  let s := sigmoidFloat u
  s * (1.0 - s) * (1.0 - 2.0 * s)

/-- Nonstandard logistic approximation to the Heaviside step function:
    `L_H(x) = 1 / (1 + exp(-H * x))`, where `H = ε⁻¹` is the fixed unlimited scale parameter.

    - In the infinitesimal transition layer (`x = c·ε + O(ε^{>1})`, including `x = 0`),
      `-H * x` is finite, so `exp(-H * x)` and `1 / (1 + exp(-H * x))` are computed purely
      via Levi-Civita Taylor series and Newton-Raphson inversion.
    - For appreciable `x > 0`, `-H * x` is negative infinite, so `exp(-H * x)` is
      super-exponentially infinitesimal (`< ε^k` for all standard `k`), yielding `1`.
    - For appreciable `x < 0`, `-H * x` is positive infinite, so `exp(-H * x)` is
      super-exponentially infinite (`> H^k` for all standard `k`), yielding `0`. -/
def logisticStep (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let negHx := -(FastLC.infH * x)
  if negHx.isFinite then
    let ex ← FastLC.expOrder negHx order
    FastLC.invNewton ((1 : FastLC) + ex) order
  else if negHx.signum < 0 then
    return (1 : FastLC)
  else
    return (0 : FastLC)

/-- Second-order infinitesimal step `η = ε²` used for differentiating `L_H(x)`.
    Crucially `H · ε² = ε` is still infinitesimal, so `L_H(x ± ε²)` stays inside the
    analytic convergence radius of `exp` around `-H · x`. -/
def eps2 : FastLC := FastLC.mono (-2) 1

/-- Pure Levi-Civita forward difference quotient `(L_H(x + ε²) - L_H(x)) / ε²`.
    Computes the Dirac delta without any hand-coded derivative rule! -/
def logisticDerivForward (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let y1 ← logisticStep (x + eps2) order
  let y0 ← logisticStep x order
  return ((y1 - y0) * FastLC.mono 2 1).truncate order

/-- Pure Levi-Civita central difference quotient `(L_H(x + ε²) - L_H(x - ε²)) / (2ε²)`.
    Cancels the `O(1)` bias so at `x = 0` it yields `(1/4)H - (1/48)ε + (1/480)ε³ - ...`. -/
def logisticDerivCentral (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let yPlus ← logisticStep (x + eps2) order
  let yMinus ← logisticStep (x - eps2) order
  return ((yPlus - yMinus) * FastLC.mono 2 (mkRat 1 2)).truncate order

/-- Pure Levi-Civita second difference quotient
    `(L_H(x + ε²) - 2 L_H(x) + L_H(x - ε²)) / ε⁴`, yielding the dipole moment `σ''(c) H² + ...`. -/
def logisticDeriv2Central (x : FastLC) (order : Nat := 12) : Except String FastLC := do
  let yPlus ← logisticStep (x + eps2) order
  let yMid ← logisticStep x order
  let yMinus ← logisticStep (x - eps2) order
  let two : FastLC := 2
  return ((yPlus - two * yMid + yMinus) * FastLC.mono 4 1).truncate order

/-- Closed-form nonstandard derivative `L'_H(x) = H · exp(-H x) / (1 + exp(-H x))²`
    for direct comparison with the automatic difference quotient. -/
def logisticDerivClosed (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let negHx := -(FastLC.infH * x)
  if negHx.isFinite then
    let ex ← FastLC.expOrder negHx order
    let denom := ((1 : FastLC) + ex) * ((1 : FastLC) + ex)
    let invDenom ← FastLC.invNewton denom order
    return (FastLC.infH * ex * invDenom).truncate order
  else
    return (0 : FastLC)

/-- One evaluation sample on the relative transition grid `x = c · ε`, paired with its
    finite specialization under `H ↦ N, ε ↦ 1/N` (`x_N = c / N`). -/
structure StepSample where
  /-- Dimensionless coordinate `c` (so `x = c · ε`, and `x_N = c / N`). -/
  c : Rat
  /-- Nonstandard input `x = c · ε`. -/
  xLC : FastLC
  /-- Finite input `x_N = c / N`. -/
  xFinite : Float
  /-- Exact Levi-Civita value `L_H(c · ε)`. -/
  stepLC : FastLC
  /-- Finite specialization `evalFinite(L_H(c · ε), N)`. -/
  stepFinite : Float
  /-- Classical `L_N(c / N) = σ(c)` for cross-checking. -/
  stepClassical : Float
  /-- Pure Levi-Civita AD derivative `D_sym L_H(c · ε)`. -/
  derivLC : FastLC
  /-- Finite specialization `evalFinite(D_sym L_H(c · ε), N)`. -/
  derivFinite : Float
  /-- Exact classical `L'_N(c / N) = N · σ'(c)`. -/
  derivClassical : Float
  /-- Pure Levi-Civita 2nd derivative `D² L_H(c · ε)` (dipole). -/
  deriv2LC : FastLC
  /-- Finite specialization `evalFinite(D² L_H(c · ε), N)`. -/
  deriv2Finite : Float
  /-- Exact classical `L''_N(c / N) = N² · σ''(c)`. -/
  deriv2Classical : Float

/-- Evaluate the nonstandard step function and its first two Levi-Civita derivatives at
    `x = c · ε`, then specialize every Levi-Civita result at finite `H ↦ bigN`. -/
def evalSampleAt (c : Rat) (bigN : Float) (order : Nat := 8) : Except String StepSample := do
  let xLC := FastLC.mono (-1) c
  let cf := FastLC.ratToFloat c
  let xF := cf / bigN
  let sLC ← logisticStep xLC order
  let dLC ← logisticDerivCentral xLC order
  let d2LC ← logisticDeriv2Central xLC (order + 2)
  return {
    c
    xLC
    xFinite := xF
    stepLC := sLC
    stepFinite := sLC.evalFinite bigN
    stepClassical := sigmoidFloat cf
    derivLC := dLC
    derivFinite := dLC.evalFinite bigN
    derivClassical := bigN * sigmoidDerivFloat cf
    deriv2LC := d2LC
    deriv2Finite := d2LC.evalFinite bigN
    deriv2Classical := bigN * bigN * sigmoidDeriv2Float cf
  }

/-- Evaluate a uniform grid of `c ∈ [-maxC, maxC]` with step `dc` and compute the
    hyperfinite Riemann integral `∑ L'_H(c_k · ε) · (dc · ε)` directly in `FastLC`
    (demonstrating `H · ε = 1` cancellation yielding unit area `≈ 1`). -/
def computeStepGrid (bigN : Float := 100.0) (halfSteps : Nat := 32) (stepDen : Nat := 4) :
    Except String (Array StepSample × FastLC) := do
  let dc : Rat := mkRat 1 stepDen
  let dxLC : FastLC := FastLC.mono (-1) dc
  let mut samples : Array StepSample := #[]
  let mut riemannArea : FastLC := 0
  let total := 2 * halfSteps + 1
  for i in [:total] do
    let k : Int := Int.ofNat i - Int.ofNat halfSteps
    let c : Rat := mkRat k stepDen
    let s ← evalSampleAt c bigN 8
    samples := samples.push s
    riemannArea := (riemannArea + s.derivLC * dxLC).truncate 6
  return (samples, riemannArea)

private def escapeJson (s : String) : String :=
  let rec go (acc : String) : List Char → String
    | [] => acc
    | '"' :: rest => go (acc ++ "\\\"") rest
    | '\\' :: rest => go (acc ++ "\\\\") rest
    | '\n' :: rest => go (acc ++ "\\n") rest
    | c :: rest => go (acc.push c) rest
  go "" s.toList

/-- Render the full step-function demo and finite specialization at `H ↦ bigN` as JSON. -/
def stepDemoJSON (bigN : Float := 100.0) (halfSteps : Nat := 32) (stepDen : Nat := 4) :
    Except String String := do
  let (samples, areaLC) ← computeStepGrid bigN halfSteps stepDen
  let deriv0 ← logisticDerivCentral 0 10
  let derivClosed0 ← logisticDerivClosed 0 10
  let derivPos ← logisticDerivCentral 1 8
  let derivNeg ← logisticDerivCentral (-1) 8
  let sampleJsons := samples.toList.map fun s =>
    "{" ++
    s!"\"c\":{FastLC.ratToFloat s.c}," ++
    s!"\"x_lc\":\"{escapeJson s.xLC.pretty}\"," ++
    s!"\"x_finite\":{s.xFinite}," ++
    s!"\"step_lc\":\"{escapeJson (s.stepLC.truncate 4).prettyApprox}\"," ++
    s!"\"step_finite\":{s.stepFinite}," ++
    s!"\"step_classical\":{s.stepClassical}," ++
    s!"\"deriv_lc\":\"{escapeJson (s.derivLC.truncate 4).prettyApprox}\"," ++
    s!"\"deriv_exact_lc\":\"{escapeJson (s.derivLC.truncate 4).pretty}\"," ++
    s!"\"deriv_finite\":{s.derivFinite}," ++
    s!"\"deriv_classical\":{s.derivClassical}," ++
    s!"\"deriv2_lc\":\"{escapeJson (s.deriv2LC.truncate 4).prettyApprox}\"," ++
    s!"\"deriv2_finite\":{s.deriv2Finite}," ++
    s!"\"deriv2_classical\":{s.deriv2Classical}" ++
    "}"
  return "{" ++
    s!"\"N\":{bigN}," ++
    s!"\"eps\":{1.0 / bigN}," ++
    s!"\"deriv_at_0_exact\":\"{escapeJson deriv0.pretty}\"," ++
    s!"\"deriv_at_0_closed\":\"{escapeJson derivClosed0.pretty}\"," ++
    s!"\"deriv_at_0_finite\":{deriv0.evalFinite bigN}," ++
    s!"\"deriv_at_pos1\":\"{escapeJson derivPos.pretty}\"," ++
    s!"\"deriv_at_neg1\":\"{escapeJson derivNeg.pretty}\"," ++
    s!"\"riemann_area_lc\":\"{escapeJson areaLC.prettyApprox}\"," ++
    s!"\"riemann_area_finite\":{areaLC.evalFinite bigN}," ++
    "\"samples\":[" ++ String.intercalate "," sampleJsons ++ "]" ++
    "}"

end StepFunction
end LeanInf
