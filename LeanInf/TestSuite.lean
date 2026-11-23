import LeanInf.LeviCivitaNum
import LeanInf.VerifiedRefactor
import LeanInf.StepFunction
import LeanInf.Parser

namespace LeanInf.TestSuite

open LeanInf

/-- Result of a single named test case. -/
structure TestResult where
  /-- Category name for grouped reporting. -/
  group : String
  /-- Human-readable test description. -/
  name : String
  /-- Whether the assertion succeeded. -/
  passed : Bool
  /-- Diagnostic detail on failure (or concise observed value on success). -/
  detail : String

private def check (group name : String) (ok : Bool) (detail : String := "") : TestResult :=
  { group, name, passed := ok, detail }

private def checkEvalEq (group expr expectedExpr : String) (order : Nat := 10) : TestResult :=
  match Calc.evalString expr order, Calc.evalString expectedExpr order with
  | .ok v1, .ok v2 =>
    check group s!"{expr} == {expectedExpr}" (v1 == v2)
      s!"got {v1}, expected {v2}"
  | .error e, _ => check group s!"{expr} == {expectedExpr}" false s!"eval error: {e}"
  | _, .error e => check group s!"{expr} == {expectedExpr}" false s!"expected error: {e}"

private def checkEvalBool (group expr : String) (expected : Bool) (order : Nat := 10) : TestResult :=
  match Calc.evalString expr order with
  | .ok (.bool b) =>
    check group s!"{expr} -> {expected}" (b == expected) s!"got {b}"
  | .ok other =>
    check group s!"{expr} -> {expected}" false s!"expected bool, got {other}"
  | .error e =>
    check group s!"{expr} -> {expected}" false s!"error: {e}"

private def checkEvalError (group expr : String) (order : Nat := 10) : TestResult :=
  match Calc.evalString expr order with
  | .error msg => check group s!"{expr} errors" true s!"error as expected: {msg}"
  | .ok v => check group s!"{expr} errors" false s!"expected error, got {v}"

private def checkApproxFloat (group name : String) (actual expected tol : Float) : TestResult :=
  let diff := (actual - expected).abs
  check group name (diff ≤ tol) s!"actual={actual}, expected={expected}, diff={diff}"

/-- Deterministic dense polynomial `(1 + c1*ε + c2*ε^2 + ...)` of `n` terms for differential tests. -/
def makeDenseSeries (n : Nat) (seed : Int) : FastLC :=
  let terms : TermList := (List.range n).map fun k =>
    let num : Int := ((Int.ofNat k * 7 + seed) % 11) - 5
    let c : Rat := mkRat (if num == 0 then 1 else num) (k % 3 + 1)
    (-(Int.ofNat k : Rat), c)
  FastLC.ofTerms terms

/-- Deterministic sparse rational-exponent series for differential tests. -/
def makeSparseSeries (n : Nat) (seed : Int) : FastLC :=
  let terms : TermList := (List.range n).map fun k =>
    let expNum : Int := Int.ofNat n * 3 - Int.ofNat (k * k + 2 * k)
    let expDen : Nat := (k % 4) + 1
    let cNum : Int := ((Int.ofNat k * 5 + seed) % 9) - 4
    let c : Rat := mkRat (if cNum == 0 then 2 else cNum) (k % 2 + 1)
    (mkRat expNum expDen, c)
  FastLC.ofTerms terms

/-- Run the complete `lean-inf` test suite. -/
def runAllTests : Array TestResult := Id.run do
  let mut r : Array TestResult := #[]

  -- Group 1: Bug-fix regressions (HashMap BEq, signum sort direction, pure/non-pure Inv)
  let g1 := "Regressions"
  let m1 : Std.HashMap Rat Rat := Std.HashMap.singleton 1 5
  let m2 : Std.HashMap Rat Rat := Std.HashMap.singleton 2 7
  r := r.push (check g1 "HashMap BEq rejects distinct keys with same size" (!(m1 == m2)) s!"m1==m2 is {m1 == m2}")
  let hMinusEps : LeviCivitaNum := lc[H, -ε]
  r := r.push (check g1 "LeviCivitaNum.signum(H - ε) == 1 (dominant H beats -ε)" (hMinusEps.signum == 1) s!"got {hMinusEps.signum}")
  let negHPlusEps : LeviCivitaNum := lc[-H, ε]
  r := r.push (check g1 "LeviCivitaNum.signum(-H + ε) == -1" (negHPlusEps.signum == -1) s!"got {negHPlusEps.signum}")
  let invNonPure : LeviCivitaNum := (lc[1, -ε])⁻¹
  let prodNonPure := ((FastLC.ofLeviCivitaNum (lc[1, -ε] * invNonPure)).truncateRel 6)
  r := r.push (check g1 "LeviCivitaNum non-pure inverse (1-ε)*(1-ε)⁻¹ == 1 (rel order 6)" (prodNonPure == 1) s!"got {prodNonPure}")

  -- Group 2: Differential equivalence — Legacy HashMap Naive vs Verified FastLC (mulTree & Karatsuba)
  let g2 := "Differential (Naive vs FastLC)"
  for sz in [1, 4, 12, 16, 20, 32] do
    let aFast := makeDenseSeries sz 3
    let bFast := makeDenseSeries sz 7
    let aNaive := aFast.toLeviCivitaNum
    let bNaive := bFast.toLeviCivitaNum
    let prodFast := aFast * bFast
    let prodSparse := FastLC.mulSparse aFast bFast
    let prodNaive := FastLC.ofLeviCivitaNum (LeviCivitaNum.mulNaive aNaive bNaive)
    r := r.push (check g2 s!"Dense mul size={sz}: FastLC(Karatsuba) == HashMap Naive"
      (prodFast == prodNaive) s!"terms fast={prodFast.terms.length}, naive={prodNaive.terms.length}")
    r := r.push (check g2 s!"Dense mul size={sz}: FastLC(Karatsuba) == FastLC(mulTree)"
      (prodFast == prodSparse) s!"terms fast={prodFast.terms.length}, sparse={prodSparse.terms.length}")
    let sumFast := aFast + bFast
    let sumNaive := FastLC.ofLeviCivitaNum (aNaive + bNaive)
    r := r.push (check g2 s!"Dense add size={sz}: FastLC == HashMap Naive"
      (sumFast == sumNaive) s!"terms={sumFast.terms.length}")
    r := r.push (check g2 s!"Dense signum size={sz}: O(1) FastLC == O(n log n) Naive"
      (aFast.signum == aNaive.signum) s!"fast={aFast.signum}, naive={aNaive.signum}")

  for sz in [5, 16, 24] do
    let aSp := makeSparseSeries sz 1
    let bSp := makeSparseSeries sz 4
    let prodFast := aSp * bSp
    let prodNaive := FastLC.ofLeviCivitaNum (LeviCivitaNum.mulNaive aSp.toLeviCivitaNum bSp.toLeviCivitaNum)
    r := r.push (check g2 s!"Sparse rational-exp mul size={sz}: FastLC == HashMap Naive"
      (prodFast == prodNaive) s!"terms={prodFast.terms.length}")

  -- Binary exponentiation vs naive power
  let basePoly := FastLC.ofTerms [(1, 1), (0, -2), (-1, mkRat 1 3)]
  for k in [0, 1, 2, 5, 8, 11] do
    let pFast := basePoly.powFast k
    let pNaive := basePoly.powNaive k
    let pLegacy := FastLC.ofLeviCivitaNum (LeviCivitaNum.powNaive basePoly.toLeviCivitaNum k)
    r := r.push (check g2 s!"pow k={k}: powFast == powNaive == legacy"
      (pFast == pNaive && pFast == pLegacy) s!"terms={pFast.terms.length}")

  -- Newton inversion accuracy check: x * invNewton(x, 12) = 1 up to order 12
  for expr in ["1 - ε", "1 + 2ε - 3ε^2", "2H + 1 - ε", "3ε + 5ε^2 - ε^3"] do
    match Calc.evalFastLC expr 12 with
    | .ok x =>
      match FastLC.invNewton x 12 with
      | .ok invX =>
        let resid := ((x * invX) - 1).truncate 10
        let ok := match resid.leadingTerm with
          | none => true
          | some (e, _) => e ≤ -10
        r := r.push (check g2 s!"Newton inv accuracy for ({expr})" ok s!"residual={resid}")
      | .error e =>
        r := r.push (check g2 s!"Newton inv accuracy for ({expr})" false e)
    | .error e =>
      r := r.push (check g2 s!"Newton inv accuracy for ({expr})" false e)

  -- Group 3: Arithmetic & Calculator Expression Suite (Crowell Test.js + extended)
  let g3 := "Arithmetic Expressions"
  let eqCases : List (String × String) := [
    ("2 + 2", "4"),
    ("1 + ε", "1 + d"),
    ("1 / ε", "H"),
    ("1 / H", "ε"),
    ("H * ε", "1"),
    ("ε + ε", "2 * ε"),
    ("2ε + 3ε", "5ε"),
    ("(1 + ε)(1 - ε)", "1 - ε^2"),
    ("(H + 1)(H - 1)", "H^2 - 1"),
    ("a = 6 * 7; a + 5", "47"),
    ("f x = x^2; f(f(2))", "16"),
    ("f(x) = x^3 + 2x; f(3)", "33"),
    ("std([(2 + ε)^4 - 2^4] / ε)", "32"),
    ("[(2 + ε)^4 - 2^4] / ε", "32 + 24ε + 8ε^2 + ε^3"),
    ("std(diff(x^4, x, 2))", "32"),
    ("f(x) = x^5; std(deriv(f, 2))", "80"),
    ("trunc(1 / (1 - ε), 5)", "1 + ε + ε^2 + ε^3 + ε^4"),
    ("trunc(exp(ε), 5)", "1 + ε + (1/2)ε^2 + (1/6)ε^3 + (1/24)ε^4"),
    ("trunc(sin(ε), 6)", "ε - (1/6)ε^3 + (1/120)ε^5"),
    ("trunc(cos(ε), 6)", "1 - (1/2)ε^2 + (1/24)ε^4"),
    ("trunc(ln(1 + ε), 4)", "ε - (1/2)ε^2 + (1/3)ε^3 - (1/4)ε^4"),
    ("trunc(exp(ln(1 + ε)), 6)", "1 + ε"),
    ("trunc([sqrt(ε + ε^2)]^2, 6)", "ε + ε^2"),
    ("sqrt(ε)^2", "ε"),
    ("sqrt(H)^2", "H"),
    ("ε^(1/2) + 1 - ε^(1/2)", "1"),
    ("abs(-H + 3)", "H - 3"),
    ("sign(H - 1000000)", "1"),
    ("sign(-ε)", "-1"),
    ("lead(3H^2 - 5H + 7 - ε)", "3H^2"),
    ("order(3H^2 - 5H + 7)", "2"),
    ("order(5ε^3 + ε^4)", "-3"),
    ("coeff(3H^2 + 5 - 7ε, -1)", "-7")
  ]
  for (lhs, rhs) in eqCases do
    r := r.push (checkEvalEq g3 lhs rhs 10)

  let boolCases : List (String × Bool) := [
    ("1 < 3", true),
    ("1 > 3", false),
    ("ε > 0", true),
    ("ε < 0", false),
    ("ε < -1", false),
    ("-ε > -1", true),
    ("ε < 10^-10", true),
    ("ε^2 < ε", true),
    ("sqrt(ε) > ε", true),
    ("2 * ε > ε", true),
    ("H > 1000000", true),
    ("2 * H > H", true),
    ("2 * H + 1 > 2 * H", true),
    ("H^2 > H", true),
    ("H - ε > 0", true),
    ("isinf(H)", true),
    ("isinf(1 / ε)", true),
    ("isfinite(3 + 2ε)", true),
    ("isfinite(H)", false),
    ("isinfsm(ε)", true),
    ("isinfsm((1 - cos(ε)) / ε)", true),
    ("isinfsm(sqrt(H + 1) - sqrt(H - 1))", true),
    ("zzz = 1; zzz == 1", true)
  ]
  for (expr, expected) in boolCases do
    r := r.push (checkEvalBool g3 expr expected 10)

  -- Check `(1 + ε)^(1/ε)` standard part ≈ e = 2.718281828...
  match Calc.evalFastLC "(1 + ε)^(1/ε)" 8 with
  | .ok val =>
    match val.stdPart with
    | some st =>
      r := r.push (checkApproxFloat g3 "std((1 + ε)^(1/ε)) ≈ e" (FastLC.ratToFloat st) 2.718281828 1e-5)
    | none =>
      r := r.push (check g3 "std((1 + ε)^(1/ε)) ≈ e" false s!"not finite: {val}")
  | .error e =>
    r := r.push (check g3 "std((1 + ε)^(1/ε)) ≈ e" false e)

  -- Expected error cases
  for bad in ["1 / 0", "ε / 0", "exp(H)", "ln(-1)", "sqrt(-1)", "std(H)"] do
    r := r.push (checkEvalError g3 bad)

  -- Group 4: Step Function -> Dirac Delta & Finite Evaluation (H -> N)
  let g4 := "Step Function & Finite Eval"
  r := r.push (checkEvalEq g4 "step(0)" "1/2" 10)
  r := r.push (checkEvalEq g4 "step(1)" "1" 10)
  r := r.push (checkEvalEq g4 "step(-1)" "0" 10)
  r := r.push (checkEvalEq g4 "dstep(1)" "0" 10)
  r := r.push (checkEvalEq g4 "dstep(-1)" "0" 10)
  r := r.push (checkEvalEq g4 "lead(dstep(0))" "(1/4)H" 10)
  r := r.push (checkEvalEq g4 "coeff(dstep(0), 1)" "1/4" 10)
  r := r.push (checkEvalEq g4 "coeff(dstep(0), -1)" "-1/48" 10)
  r := r.push (checkEvalEq g4 "ddstep(0)" "0" 12)
  r := r.push (checkEvalBool g4 "ddstep(-ε) > 0" true 12)
  r := r.push (checkEvalBool g4 "ddstep(ε) < 0" true 12)
  r := r.push (checkEvalBool g4 "isinf(dstep(0))" true 10)
  r := r.push (checkEvalBool g4 "isinf(dstep(ε))" true 10)

  -- Finite specialization H -> 100 and H -> 1000
  match StepFunction.logisticDerivCentral 0 10 with
  | .ok d0 =>
    r := r.push (checkApproxFloat g4 "evalFinite(dstep(0), 100) ≈ 25.0" (d0.evalFinite 100.0) 25.0 0.001)
    r := r.push (checkApproxFloat g4 "evalFinite(dstep(0), 1000) ≈ 250.0" (d0.evalFinite 1000.0) 250.0 0.001)
  | .error e =>
    r := r.push (check g4 "evalFinite(dstep(0), N)" false e)

  match StepFunction.evalSampleAt 1 100.0 8 with
  | .ok s1 =>
    r := r.push (checkApproxFloat g4 "At x = ε (x_100 = 0.01): finite AD matches N*σ'(1) ≈ 19.6612"
      s1.derivFinite s1.derivClassical 0.01)
  | .error e =>
    r := r.push (check g4 "At x = ε finite AD" false e)

  match StepFunction.computeStepGrid 100.0 32 4 with
  | .ok (_, areaLC) =>
    r := r.push (check g4 "Hyperfinite Riemann integral ∑ L'_H(c_k ε)(dc·ε) is finite (H·ε = 1)"
      areaLC.isFinite s!"area={areaLC.prettyApprox}")
    r := r.push (checkApproxFloat g4 "Hyperfinite Riemann integral of Dirac delta ≈ 1.0"
      (areaLC.evalFinite 100.0) 1.0 0.002)
  | .error e =>
    r := r.push (check g4 "Hyperfinite Riemann integral" false e)

  -- Group 5: Glued Math Implicit Mul, Safe Logistic Div & Free-Variable `x` Function Plotting
  let g5 := "Glued Tokens & Function Plot (`x`)"
  r := r.push (checkEvalEq g5 "Hε" "1" 10)
  r := r.push (checkEvalEq g5 "Heps" "1" 10)
  r := r.push (checkEvalEq g5 "1/(1+exp(-H))" "1" 10)
  r := r.push (checkEvalEq g5 "1/(1+exp(H))" "0" 10)
  r := r.push (checkEvalEq g5 "1/(1+exp(-H*0))" "1/2" 10)
  r := r.push (checkEvalEq g5 "hx = 5; hx + 1" "6" 10)
  r := r.push (checkEvalEq g5 "hx(t) = t^2; hx(3)" "9" 10)

  -- Glued `Hx`, `xH`, `εx`, `xeps`, `hx` parse with free variable `x`
  for exprStr in ["1/(1+exp(-Hx))", "1/(1+exp(-H*x))", "-Hx", "xH", "εx", "xeps", "hx",
                  "dstep(x)", "x^2 + eps", "1/(1+exp(-H*(x-0.5)))"] do
    match Calc.parseExpr exprStr with
    | .ok e =>
      r := r.push (check g5 s!"hasFreeVar '{exprStr}' == true" (Calc.hasFreeVar e "x") s!"expr={repr e}")
    | .error err =>
      r := r.push (check g5 s!"parse '{exprStr}'" false err)

  -- Bound `x` in `diff` and `fnDef` must remain scalar (`hasFreeVar == false`, `kind: "num"`)
  for scalarStr in ["diff(x^4, x, 2)", "f(x) = x^2; f(3)", "x = 3; x + 1"] do
    match Calc.parseExpr scalarStr with
    | .ok e =>
      let j := Calc.evalToJson scalarStr 100.0 10
      let isScalar := !(Calc.hasFreeVar e "x") && (j.splitOn "\"kind\":\"num\"").length ≥ 2
      r := r.push (check g5 s!"bound x stays scalar kind=\"num\": {scalarStr}" isScalar j)
    | .error err =>
      r := r.push (check g5 s!"parse scalar '{scalarStr}'" false err)

  -- Full end-to-end check of `1/(1+exp(-Hx))` probes & Float step plot
  let logJson100 := Calc.evalToJson "1/(1+exp(-Hx))" 100.0 10
  let logJson1000 := Calc.evalToJson "1/(1+exp(-Hx))" 1000.0 10
  r := r.push (check g5 "1/(1+exp(-Hx)) JSON returns kind=\"fn\" with probes & plot"
    ((logJson100.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
     (logJson100.splitOn "\"exact\":\"f(-1) = 0,  f(0) = 1/2,  f(1) = 1\"").length ≥ 2 &&
     (logJson100.splitOn "\"x_label\":\"ε²\",\"ok\":true,\"exact\":\"1/2 + (1/4)ε - (1/48)ε³").length ≥ 2 &&
     (logJson100.splitOn "\"zoom_points\":[").length ≥ 2 &&
     (logJson100.splitOn "NaN").length == 1 &&
     (logJson1000.splitOn "NaN").length == 1)
    logJson100)

  -- Verify Float sampler produces exact step shape on `1/(1+exp(-Hx))` at N = 100 and N = 1000
  match Calc.parseExpr "1/(1+exp(-Hx))" with
  | .ok logExpr =>
    match Calc.evalExprFloat logExpr 100.0 (-1.0),
          Calc.evalExprFloat logExpr 100.0 0.0,
          Calc.evalExprFloat logExpr 100.0 1.0,
          Calc.evalExprFloat logExpr 1000.0 (-1.0),
          Calc.evalExprFloat logExpr 1000.0 1.0 with
    | some yL, some yM, some yR, some yL1k, some yR1k =>
      r := r.push (check g5 "1/(1+exp(-Hx)) Float sampler step shape at N=100 & N=1000 (zero NaN)"
        (yL < 1e-6 && (yM - 0.5).abs < 1e-12 && yR > 1.0 - 1e-6 &&
         yL1k < 1e-6 && yR1k > 1.0 - 1e-6)
        s!"N=100: ({yL},{yM},{yR}), N=1000: ({yL1k},{yR1k})")
    | _, _, _, _, _ =>
      r := r.push (check g5 "1/(1+exp(-Hx)) Float sampler step shape" false "returned none")
  | .error err =>
    r := r.push (check g5 "parse 1/(1+exp(-Hx))" false err)

  -- Verify `1/(1+exp(-H*x))`, `dstep(x)`, `x^2 + eps`, `1/(1+exp(-H*(x-0.5)))` emit valid kind="fn"
  for fnExpr in ["1/(1+exp(-H*x))", "dstep(x)", "x^2 + eps", "1/(1+exp(-H*(x-0.5)))"] do
    let j := Calc.evalToJson fnExpr 100.0 10
    let ok := (j.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
              (j.splitOn "\"points\":[[").length ≥ 2 &&
              (j.splitOn "NaN").length == 1
    r := r.push (check g5 s!"kind=\"fn\" with valid plot points: {fnExpr}" ok)

  -- Group 6: Dual-Audit Math Regressions, Float Bridge, LeviCivitaNum Inverse & DoS Caps
  let g6 := "Audit Regressions & DoS Hardening"
  r := r.push (checkEvalEq g6 "(1 - eps^2) / (1 - eps)" "1 + eps" 10)
  r := r.push (checkEvalBool g6 "(H^2 - 1) / (H - 1) == H + 1" true 10)
  r := r.push (checkEvalEq g6 "ln(exp(eps))" "eps" 10)
  -- No garbage tail at ε¹⁰..ε¹² for `ln(1+eps+eps^2/2)` or at ε¹⁰ for `cos(eps+eps^2)`
  match Calc.evalFastLC "ln(1 + eps + eps^2 / 2)" 10 with
  | .ok v =>
    r := r.push (check g6 "ln(1+eps+eps^2/2) has zero garbage tail at ε¹⁰..ε¹²"
      (v.coeff (-10) == 0 && v.coeff (-11) == 0 && v.coeff (-12) == 0 && v.coeff (-3) == mkRat (-1) 6)
      s!"got {v}")
  | .error err => r := r.push (check g6 "ln(1+eps+eps^2/2)" false err)
  match Calc.evalFastLC "cos(eps + eps^2)" 10 with
  | .ok v =>
    r := r.push (check g6 "cos(eps+eps^2) has zero garbage tail at ε¹⁰"
      (v.coeff (-10) == 0 && v.coeff (-2) == mkRat (-1) 2 && v.coeff (-3) == (-1 : Rat))
      s!"got {v}")
  | .error err => r := r.push (check g6 "cos(eps+eps^2)" false err)
  -- `det_52`: `(1+eps)^(1/eps)` ε⁹ coefficient ≈ -1.083047 (not -0.811219)
  match Calc.evalFastLC "(1 + eps)^(1 / eps)" 10 with
  | .ok v =>
    let c9 := FastLC.ratToFloat (v.coeff (-9))
    r := r.push (checkApproxFloat g6 "det_52: coeff((1+eps)^(1/eps), -9) ≈ -1.083047" c9 (-1.083047) 1e-4)
  | .error err => r := r.push (check g6 "det_52 (1+eps)^(1/eps)" false err)
  -- Exact dyadic `ratOfFloat` & finite `expOrder` guard
  match Calc.evalFastLC "exp(25)" 10 with
  | .ok v =>
    r := r.push (checkApproxFloat g6 "exp(25) ≈ 72004899337.39 (no UInt64 saturation)"
      (v.evalFinite 100.0) 72004899337.38588 1.0)
  | .error err => r := r.push (check g6 "exp(25)" false err)
  r := r.push (checkEvalBool g6 "exp(-25) == 0" false 10)
  r := r.push (checkEvalError g6 "exp(710)" 10)
  r := r.push (checkEvalEq g6 "eval(H^3, 10000)" "1000000000000" 10)
  -- `e^u` desugaring & optional 4th `diff` step argument
  let eLogJson := Calc.evalToJson "1/(1+e^(-Hx))" 100.0 10
  r := r.push (check g6 "1/(1+e^(-Hx)) desugars to exp & matches 1/(1+exp(-Hx)) probes"
    ((eLogJson.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
     (eLogJson.splitOn "\"exact\":\"f(-1) = 0,  f(0) = 1/2,  f(1) = 1\"").length ≥ 2 &&
     (eLogJson.splitOn "NaN").length == 1)
    eLogJson)
  r := r.push (checkEvalEq g6 "diff(1/(1+exp(-Hx)), x, 0, eps^2)" "dstep(0)" 10)
  -- DoS exponent / power caps return clean errors instantly
  for dos in ["1e999999999", "2^1000000000", "9^9^9", "(1+H)^100000", "(1+eps)^99999"] do
    r := r.push (checkEvalError g6 dos 10)
  -- JSON control-char escaping & non-finite `bigN` guard
  let tabJson := Calc.evalToJson "1\t+\t1" (1.0 / 0.0) 10
  r := r.push (check g6 "evalToJson escapes \\t and guards non-finite bigN"
    ((tabJson.splitOn "\\t").length ≥ 3 &&
     (tabJson.splitOn "inf").length == 1 &&
     (tabJson.splitOn "\"eval_N\":100").length ≥ 2)
    tabJson)
  -- `LeviCivitaNum.expandUnitInverse` matches `FastLC.invNewton` on sparse `1/(1 + ε + ε²)`
  let lcSparse := lc[1, ε, ε^2]
  let invLegacy := FastLC.ofLeviCivitaNum (LeviCivitaNum.invOrder lcSparse 10)
  match Calc.evalFastLC "1 / (1 + eps + eps^2)" 10 with
  | .ok invFast =>
    r := r.push (check g6 "LeviCivitaNum.invOrder(1+ε+ε², 10) == FastLC.invNewton"
      (invLegacy == invFast) s!"legacy={invLegacy}, fast={invFast}")
  | .error err => r := r.push (check g6 "invOrder sparse check" false err)

  -- Group 7: Generic Plotter (finite_projection, scale_hint, y/z single-var, fn2, fn3)
  let g7 := "7. Generic Plotter (finite_projection, scale_hint, fn2, fn3)"
  -- Constant finite projections & scale_curve
  let h2Json := Calc.evalToJson "H^2" 100.0 10
  r := r.push (check g7 "H^2 emits finite_projection + loglog + scale_curve"
    ((h2Json.splitOn "\"kind\":\"num\"").length ≥ 2 &&
     (h2Json.splitOn "\"plot_decision\":\"finite_projection\"").length ≥ 2 &&
     (h2Json.splitOn "\"scale_hint\":\"loglog\"").length ≥ 2 &&
     (h2Json.splitOn "\"finite_y\":10000").length ≥ 2 &&
     (h2Json.splitOn "\"scale_curve\":[[1.000000,1.000000]").length ≥ 2 &&
     (h2Json.splitOn "NaN").length == 1)
    h2Json)
  let c42Json := Calc.evalToJson "42" 100.0 10
  r := r.push (check g7 "42 emits finite_projection + linear"
    ((c42Json.splitOn "\"plot_decision\":\"finite_projection\"").length ≥ 2 &&
     (c42Json.splitOn "\"scale_hint\":\"linear\"").length ≥ 2 &&
     (c42Json.splitOn "\"finite_y\":42").length ≥ 2)
    c42Json)
  let negH2Json := Calc.evalToJson "-H^2" 100.0 10
  r := r.push (check g7 "-H^2 emits finite_projection + symlog"
    ((negH2Json.splitOn "\"plot_decision\":\"finite_projection\"").length ≥ 2 &&
     (negH2Json.splitOn "\"scale_hint\":\"symlog\"").length ≥ 2 &&
     (negH2Json.splitOn "\"finite_y\":-10000").length ≥ 2)
    negH2Json)
  let dstep0Json := Calc.evalToJson "dstep(0)" 100.0 10
  r := r.push (check g7 "dstep(0) emits finite_projection + scale_curve"
    ((dstep0Json.splitOn "\"kind\":\"num\"").length ≥ 2 &&
     (dstep0Json.splitOn "\"plot_decision\":\"finite_projection\"").length ≥ 2 &&
     (dstep0Json.splitOn "\"scale_curve\":[[").length ≥ 2)
    dstep0Json)
  let h1000Json := Calc.evalToJson "H^1000" 100.0 10
  r := r.push (check g7 "H^1000 at N=100 emits skip_nonfinite + plot_reason and omits plot"
    ((h1000Json.splitOn "\"kind\":\"num\"").length ≥ 2 &&
     (h1000Json.splitOn "\"plot_decision\":\"skip_nonfinite\"").length ≥ 2 &&
     (h1000Json.splitOn "\"plot_reason\":").length ≥ 2 &&
     (h1000Json.splitOn "\"plot\":{").length == 1)
    h1000Json)
  -- Single-var generalization (`x`, `y`, `z`) & adaptive `scale_hint`
  let sinYJson := Calc.evalToJson "sin(y) + eps" 100.0 10
  r := r.push (check g7 "sin(y) + eps emits kind=\"fn\", var=\"y\", linear"
    ((sinYJson.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
     (sinYJson.splitOn "\"var\":\"y\"").length ≥ 2 &&
     (sinYJson.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (sinYJson.splitOn "\"scale_hint\":\"linear\"").length ≥ 2)
    sinYJson)
  let stepZJson := Calc.evalToJson "1/(1+exp(-Hz))" 100.0 10
  r := r.push (check g7 "1/(1+exp(-Hz)) emits kind=\"fn\", var=\"z\", linear, exact probes"
    ((stepZJson.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
     (stepZJson.splitOn "\"var\":\"z\"").length ≥ 2 &&
     (stepZJson.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (stepZJson.splitOn "\"scale_hint\":\"linear\"").length ≥ 2 &&
     (stepZJson.splitOn "\"exact\":\"f(-1) = 0,  f(0) = 1/2,  f(1) = 1\"").length ≥ 2)
    stepZJson)
  let stepXJson := Calc.evalToJson "1/(1+exp(-Hx))" 100.0 10
  r := r.push (check g7 "1/(1+exp(-Hx)) keeps linear scale_hint and plot_decision=\"plot\""
    ((stepXJson.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (stepXJson.splitOn "\"scale_hint\":\"linear\"").length ≥ 2)
    stepXJson)
  let dstepXJson := Calc.evalToJson "dstep(x)" 100.0 10
  r := r.push (check g7 "dstep(x) keeps linear scale_hint for sharp Dirac spike"
    ((dstepXJson.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (dstepXJson.splitOn "\"scale_hint\":\"linear\"").length ≥ 2)
    dstepXJson)
  let exp10xJson := Calc.evalToJson "exp(10*x)" 100.0 10
  r := r.push (check g7 "exp(10*x) emits symlog scale_hint"
    ((exp10xJson.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
     (exp10xJson.splitOn "\"scale_hint\":\"symlog\"").length ≥ 2)
    exp10xJson)
  let skipFnJson := Calc.evalToJson "H^1000 + x" 100.0 10
  r := r.push (check g7 "H^1000 + x at N=100 keeps exact probes and emits skip_nonfinite"
    ((skipFnJson.splitOn "\"ok\":true").length ≥ 2 &&
     (skipFnJson.splitOn "\"kind\":\"fn\"").length ≥ 2 &&
     (skipFnJson.splitOn "\"plot_decision\":\"skip_nonfinite\"").length ≥ 2 &&
     (skipFnJson.splitOn "\"plot\":{").length == 1)
    skipFnJson)
  -- 2-var (`fn2`) heatmap & pole handling
  let fn2Json := Calc.evalToJson "x^2 + y^2" 100.0 10
  r := r.push (check g7 "x^2 + y^2 emits kind=\"fn2\", 21x21 grid, z_min=0, z_max=2, 6 probes"
    ((fn2Json.splitOn "\"kind\":\"fn2\"").length ≥ 2 &&
     (fn2Json.splitOn "\"vars\":[\"x\",\"y\"]").length ≥ 2 &&
     (fn2Json.splitOn "\"grid_size\":21").length ≥ 2 &&
     (fn2Json.splitOn "\"z_min\":0").length ≥ 2 &&
     (fn2Json.splitOn "\"z_max\":2").length ≥ 2 &&
     (fn2Json.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (fn2Json.splitOn "\"x_label\":\"(0,0)\"").length ≥ 2 &&
     (fn2Json.splitOn "\"x_label\":\"(0,ε)\"").length ≥ 2)
    fn2Json)
  let pole2Json := Calc.evalToJson "1/(x^2 + y^2)" 100.0 10
  r := r.push (check g7 "1/(x^2 + y^2) emits null pole cleanly without NaN/inf"
    ((pole2Json.splitOn "\"kind\":\"fn2\"").length ≥ 2 &&
     (pole2Json.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (pole2Json.splitOn ",null,").length ≥ 2 &&
     (pole2Json.splitOn "NaN").length == 1 &&
     (pole2Json.splitOn ",inf").length == 1 &&
     (pole2Json.splitOn ":inf").length == 1 &&
     (pole2Json.splitOn "-inf").length == 1)
    pole2Json)
  let xzJson := Calc.evalToJson "z + x" 100.0 10
  r := r.push (check g7 "z + x canonicalizes vars to [\"x\",\"z\"]"
    ((xzJson.splitOn "\"kind\":\"fn2\"").length ≥ 2 &&
     (xzJson.splitOn "\"vars\":[\"x\",\"z\"]").length ≥ 2)
    xzJson)
  let gluedXYJson := Calc.evalToJson "xy + eps" 100.0 10
  r := r.push (check g7 "glued xy + eps splits cleanly into kind=\"fn2\" vars [\"x\",\"y\"]"
    ((gluedXYJson.splitOn "\"kind\":\"fn2\"").length ≥ 2 &&
     (gluedXYJson.splitOn "\"vars\":[\"x\",\"y\"]").length ≥ 2 &&
     (gluedXYJson.splitOn "\"x_label\":\"(1,0)\",\"ok\":true,\"exact\":\"ε\"").length ≥ 2)
    gluedXYJson)
  -- 3-var (`fn3`) slices
  let fn3Json := Calc.evalToJson "x + y + z" 100.0 10
  r := r.push (check g7 "x + y + z emits kind=\"fn3\", 13x13x9 slices, z_min=-3, z_max=3, 6 probes"
    ((fn3Json.splitOn "\"kind\":\"fn3\"").length ≥ 2 &&
     (fn3Json.splitOn "\"vars\":[\"x\",\"y\",\"z\"]").length ≥ 2 &&
     (fn3Json.splitOn "\"grid_size\":13").length ≥ 2 &&
     (fn3Json.splitOn "\"slice_values\":[-1,-0.750000,-0.500000,-0.250000,0,0.250000,0.500000,0.750000,1]").length ≥ 2 &&
     (fn3Json.splitOn "\"z_min\":-3").length ≥ 2 &&
     (fn3Json.splitOn "\"z_max\":3").length ≥ 2 &&
     (fn3Json.splitOn "\"plot_decision\":\"plot\"").length ≥ 2 &&
     (fn3Json.splitOn "\"x_label\":\"(0,0,0)\"").length ≥ 2 &&
     (fn3Json.splitOn "\"x_label\":\"(ε,ε,ε)\"").length ≥ 2)
    fn3Json)
  -- Bound y/z remain scalar kind="num"
  let boundYZJson := Calc.evalToJson "y = 3; z = 4; y + z" 100.0 10
  r := r.push (check g7 "bound y and z stay scalar kind=\"num\" with exact=\"7\""
    ((boundYZJson.splitOn "\"kind\":\"num\"").length ≥ 2 &&
     (boundYZJson.splitOn "\"exact\":\"7\"").length ≥ 2)
    boundYZJson)

  return r

/-- Print a formatted test report and return `true` iff every test passed. -/
def runAndPrint : IO Bool := do
  let results := runAllTests
  let mut passed := 0
  let mut failed := 0
  let mut lastGroup := ""
  for t in results do
    if t.group != lastGroup then
      IO.println s!"\n=== {t.group} ==="
      lastGroup := t.group
    if t.passed then
      passed := passed + 1
      IO.println s!"  [PASS] {t.name}"
    else
      failed := failed + 1
      IO.println s!"  [FAIL] {t.name} -- {t.detail}"
  IO.println s!"\nSummary: {passed}/{results.size} passed, {failed} failed."
  return failed == 0

end LeanInf.TestSuite
