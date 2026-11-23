import LeanInf

open LeanInf

private def parseFloatArg (s : String) (default : Float) : Float :=
  match Calc.parseExpr s with
  | .ok e =>
    match Calc.evalExpr (Calc.defaultEnv 6) e with
    | .ok (.num v, _) =>
      match v.stdPart with
      | some r =>
        let f := FastLC.ratToFloat r
        if f.isNaN || f.isInf || f ≤ 0.0 then default else f
      | none => default
    | _ => default
  | _ => default

private def runStepDemo (bigN : Float) (asJson : Bool) : IO Unit := do
  if asJson then
    match StepFunction.stepDemoJSON bigN 32 4 with
    | .ok j => IO.println j
    | .error e => IO.eprintln s!"Error: {e}"
  else
    IO.println s!"=== Nonstandard Step Function L_H(x) = 1 / (1 + exp(-H*x)) ==="
    IO.println s!"Finite specialization: H ↦ N = {bigN}, ε ↦ 1/N = {1.0 / bigN}\n"
    match StepFunction.logisticDerivCentral 0 10, StepFunction.logisticDerivClosed 0 10 with
    | .ok d0, .ok dc0 =>
      IO.println s!"At x = 0:"
      IO.println s!"  L_H(0)                    = 1/2"
      IO.println s!"  Pure AD D_(ε²) L_H(0)     = {d0}"
      IO.println s!"  Closed form L'_H(0)       = {dc0}"
      IO.println s!"  Finite eval (H ↦ {bigN}) = {d0.evalFinite bigN}  (exact N/4 = {bigN / 4.0})\n"
    | _, _ => IO.eprintln "Failed computing derivative at 0"
    match StepFunction.computeStepGrid bigN 32 4 with
    | .ok (samples, areaLC) =>
      IO.println "Transition layer x = c·ε (finite x_N = c/N):"
      IO.println "   c   |   x_N    |   L_N(x_N)   |   LC Derivative L'_H(c·ε)      | evalAt(N)  | N·σ'(c)"
      IO.println "-------|----------|--------------|--------------------------------|------------|---------"
      for s in samples do
        let cf := FastLC.ratToFloat s.c
        if cf == -4.0 || cf == -2.0 || cf == -1.0 || cf == -0.5 || cf == 0.0 ||
           cf == 0.5 || cf == 1.0 || cf == 2.0 || cf == 4.0 then
          IO.println s!" {cf} | {s.xFinite} | {s.stepFinite} | {(s.derivLC.truncate 2).prettyApprox 4} | {s.derivFinite} | {s.derivClassical}"
      IO.println s!"\nHyperfinite Riemann integral ∑ L'_H(c_k·ε)·(Δc·ε) = {areaLC.prettyApprox 5}"
      IO.println s!"Finite specialization of area (H ↦ {bigN})         = {areaLC.evalFinite bigN} (exact = 1.0)"
    | .error e => IO.eprintln s!"Error: {e}"

/-- Persistent line-oriented worker for HTTP servers (`eval\t<N>\t<order>\t<expr>` or `step\t<N>`). -/
private partial def runServeStdio : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  while true do
    let line ← stdin.getLine
    if line.isEmpty then break
    let trimmed := line.trimAscii.toString
    if trimmed.isEmpty then continue
    let parts := trimmed.splitOn "\t"
    match parts with
    | "eval" :: nStr :: ordStr :: exprParts =>
      let expr := String.intercalate "\t" exprParts
      let bigN := parseFloatArg nStr 100.0
      let ord := max 4 (min 32 (ordStr.toNat?.getD 10))
      stdout.putStrLn (Calc.evalToJson expr bigN ord)
      stdout.flush
    | "step" :: nStr :: _ =>
      let bigN := parseFloatArg nStr 100.0
      match StepFunction.stepDemoJSON bigN 32 4 with
      | .ok j => stdout.putStrLn j
      | .error e => stdout.putStrLn ("{\"ok\":false,\"error\":\"" ++ Calc.escapeJsonStr e ++ "\"}")
      stdout.flush
    | ["bench"] =>
      let rows ← Bench.runAllBenchmarks
      stdout.putStrLn (Bench.rowsToJson rows)
      stdout.flush
    | ["ping"] =>
      stdout.putStrLn "{\"ok\":true,\"engine\":\"lean-inf\",\"lean\":\"4.36.0\"}"
      stdout.flush
    | _ =>
      stdout.putStrLn (Calc.evalToJson trimmed 100.0 10)
      stdout.flush

private partial def runRepl : IO Unit := do
  IO.println "lean-inf — Levi-Civita Calculator (H = infinite, ε = 1/H). Type :quit to exit."
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut env := Calc.defaultEnv 10
  while true do
    stdout.putStr "inf> "
    stdout.flush
    let line ← stdin.getLine
    if line.isEmpty then break
    let trimmed := line.trimAscii.toString
    if trimmed == ":quit" || trimmed == ":q" || trimmed == "exit" then break
    if trimmed.isEmpty then continue
    match Calc.parseExpr trimmed with
    | .error e => IO.println s!"Parse error: {e}"
    | .ok expr =>
      match Calc.evalExpr env expr with
      | .error e => IO.println s!"Error: {e}"
      | .ok (val, env') =>
        env := env'
        IO.println s!"  = {val}"

private def usage : String :=
  "lean-inf — Computable Levi-Civita Numbers in Lean 4\n" ++
  "Usage:\n" ++
  "  inf eval <expr> [--N <val>] [--order <k>] [--json]\n" ++
  "  inf test\n" ++
  "  inf bench [--json]\n" ++
  "  inf step-demo [--N <val>] [--json]\n" ++
  "  inf repl\n" ++
  "  inf serve-stdio\n"

/-- CLI entry point for the `inf` executable. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["--help"] | ["-h"] =>
    IO.println usage
    return 0
  | ["test"] =>
    let ok ← TestSuite.runAndPrint
    return if ok then 0 else 1
  | "bench" :: rest =>
    let asJson := rest.contains "--json"
    Bench.runAndPrint asJson
    return 0
  | "step-demo" :: rest =>
    let asJson := rest.contains "--json"
    let bigN :=
      match rest.dropWhile (· != "--N") with
      | "--N" :: v :: _ => parseFloatArg v 100.0
      | _ => 100.0
    runStepDemo bigN asJson
    return 0
  | ["repl"] =>
    runRepl
    return 0
  | ["serve-stdio"] =>
    runServeStdio
    return 0
  | "eval" :: expr :: rest =>
    let asJson := rest.contains "--json"
    let bigN :=
      match rest.dropWhile (· != "--N") with
      | "--N" :: v :: _ => parseFloatArg v 100.0
      | _ => 100.0
    let ord :=
      match rest.dropWhile (· != "--order") with
      | "--order" :: v :: _ => max 4 (min 32 (v.toNat?.getD 10))
      | _ => 10
    if asJson then
      IO.println (Calc.evalToJson expr bigN ord)
      return 0
    else
      match Calc.evalString expr ord with
      | .ok (.bool b) =>
        IO.println (if b then "true" else "false")
        return 0
      | .ok (.num x) =>
        IO.println s!"exact  : {x.pretty}"
        IO.println s!"approx : {x.prettyApprox}"
        IO.println s!"eval({bigN}) : {x.evalFinite bigN}"
        return 0
      | .error e =>
        IO.eprintln s!"Error: {e}"
        return 1
  | _ =>
    IO.eprintln usage
    return 1
