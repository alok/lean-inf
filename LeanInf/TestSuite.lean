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
