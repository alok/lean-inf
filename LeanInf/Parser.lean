import Std
import LeanInf.VerifiedRefactor
import LeanInf.StepFunction

namespace LeanInf.Calc

open LeanInf

/-- Calculator runtime value: either a canonical `FastLC` number or a boolean comparison result. -/
inductive CalcVal where
  /-- A Levi-Civita number. -/
  | num (v : FastLC)
  /-- A boolean comparison result (`<`, `<=`, `>`, `>=`, `==`, `!=`). -/
  | bool (b : Bool)
deriving BEq, Repr

instance : ToString CalcVal where
  toString
    | .num v => v.pretty
    | .bool b => if b then "true" else "false"

/-- Binary arithmetic and comparison operators. -/
inductive BinOp where
  /-- Addition `+`. -/ | add
  /-- Subtraction `-`. -/ | sub
  /-- Multiplication `*`. -/ | mul
  /-- Division `/`. -/ | div
  /-- Exponentiation `^`. -/ | pow
  /-- Equality `==`. -/ | eq
  /-- Inequality `!=`. -/ | ne
  /-- Less than `<`. -/ | lt
  /-- Less than or equal `<=`. -/ | le
  /-- Greater than `>`. -/ | gt
  /-- Greater than or equal `>=`. -/ | ge
deriving BEq, Repr

/-- Calculator expression AST. -/
inductive Expr where
  /-- Numeric Levi-Civita literal. -/ | lit (v : FastLC)
  /-- Variable reference. -/ | var (name : String)
  /-- Unary negation. -/ | neg (e : Expr)
  /-- Binary operation. -/ | bin (op : BinOp) (l r : Expr)
  /-- Function call `f(arg1, ...)`. -/ | call (name : String) (args : List Expr)
  /-- Variable assignment `name = rhs`. -/ | assign (name : String) (rhs : Expr)
  /-- Unary function definition `name(param) = body`. -/ | fnDef (name : String) (param : String) (body : Expr)
  /-- Semicolon-separated statement sequence. -/ | seq (stmts : List Expr)
deriving Repr

/-- Lexer token. -/
inductive Token where
  /-- Rational numeric literal. -/ | num (r : Rat)
  /-- Identifier (`H`, `ε`, `x`, `sin`, ...). -/ | ident (s : String)
  /-- `+`. -/ | plus
  /-- `-`. -/ | minus
  /-- `*`. -/ | star
  /-- `/`. -/ | slash
  /-- `^`. -/ | caret
  /-- `(`, `[`, or `{`. -/ | lparen
  /-- `)`, `]`, or `}`. -/ | rparen
  /-- `,`. -/ | comma
  /-- `;`. -/ | semi
  /-- `=`. -/ | eq
  /-- `==`. -/ | eqEq
  /-- `!=`. -/ | bangEq
  /-- `<`. -/ | lt
  /-- `<=`. -/ | le
  /-- `>`. -/ | gt
  /-- `>=`. -/ | ge
  /-- End of input. -/ | eof
deriving BEq, Repr

private def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c == 'ε' || c == 'π'

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == 'ε' || c == 'π'

private def parseNatDigits (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

private def lexNumber (chars : List Char) : Rat × List Char :=
  let (intPart, rest1) := chars.span Char.isDigit
  let (fracPart, rest2) :=
    match rest1 with
    | '.' :: more =>
      let (fd, r) := more.span Char.isDigit
      (fd, r)
    | _ => ([], rest1)
  let baseNum := parseNatDigits (intPart ++ fracPart)
  let baseScale : Int := -(Int.ofNat fracPart.length)
  let (expShift, rest3) : Int × List Char :=
    match rest2 with
    | 'e' :: '+' :: d :: more | 'E' :: '+' :: d :: more =>
      if d.isDigit then
        let (ed, r) := (d :: more).span Char.isDigit
        (Int.ofNat (parseNatDigits ed), r)
      else (0, rest2)
    | 'e' :: '-' :: d :: more | 'E' :: '-' :: d :: more =>
      if d.isDigit then
        let (ed, r) := (d :: more).span Char.isDigit
        (-(Int.ofNat (parseNatDigits ed)), r)
      else (0, rest2)
    | 'e' :: d :: more | 'E' :: d :: more =>
      if d.isDigit then
        let (ed, r) := (d :: more).span Char.isDigit
        (Int.ofNat (parseNatDigits ed), r)
      else (0, rest2)
    | _ => (0, rest2)
  let totalExp : Int := baseScale + expShift
  let rat : Rat :=
    if totalExp ≥ 0 then
      mkRat (Int.ofNat (baseNum * Nat.pow 10 totalExp.toNat)) 1
    else
      mkRat (Int.ofNat baseNum) (Nat.pow 10 totalExp.natAbs)
  (rat, rest3)

/-- Tokenize a calculator input string into a list of tokens. -/
partial def tokenize (input : String) : Except String (List Token) :=
  let rec go (acc : List Token) : List Char → Except String (List Token)
    | [] => .ok (acc.reverse ++ [.eof])
    | c :: rest =>
      if c.isWhitespace then go acc rest
      else if c.isDigit || (c == '.' && match rest with | d :: _ => d.isDigit | _ => false) then
        let (r, rem) := lexNumber (c :: rest)
        go (.num r :: acc) rem
      else if isIdentStart c then
        let (idChars, rem) := (c :: rest).span isIdentChar
        go (.ident (String.ofList idChars) :: acc) rem
      else
        match c, rest with
        | '+', _ => go (.plus :: acc) rest
        | '-', _ => go (.minus :: acc) rest
        | '*', _ => go (.star :: acc) rest
        | '×', _ => go (.star :: acc) rest
        | '·', _ => go (.star :: acc) rest
        | '/', _ => go (.slash :: acc) rest
        | '^', _ => go (.caret :: acc) rest
        | '(', _ | '[', _ | '{', _ => go (.lparen :: acc) rest
        | ')', _ | ']', _ | '}', _ => go (.rparen :: acc) rest
        | ',', _ => go (.comma :: acc) rest
        | ';', _ => go (.semi :: acc) rest
        | '=', '=' :: more => go (.eqEq :: acc) more
        | '=', _ => go (.eq :: acc) rest
        | '!', '=' :: more => go (.bangEq :: acc) more
        | '<', '=' :: more => go (.le :: acc) more
        | '<', _ => go (.lt :: acc) rest
        | '>', '=' :: more => go (.ge :: acc) more
        | '>', _ => go (.gt :: acc) rest
        | _, _ => .error s!"Unexpected character '{c}'"
  go [] input.toList

private structure PState where
  tokens : List Token

private abbrev ParserM := StateT PState (Except String)

private def peek : ParserM Token := do
  match (← get).tokens with
  | t :: _ => return t
  | [] => return .eof

private def peek2 : ParserM (Token × Token) := do
  match (← get).tokens with
  | t1 :: t2 :: _ => return (t1, t2)
  | [t1] => return (t1, .eof)
  | [] => return (.eof, .eof)

private def peek3 : ParserM (Token × Token × Token) := do
  match (← get).tokens with
  | t1 :: t2 :: t3 :: _ => return (t1, t2, t3)
  | [t1, t2] => return (t1, t2, .eof)
  | [t1] => return (t1, .eof, .eof)
  | [] => return (.eof, .eof, .eof)

private def bump : ParserM Token := do
  let st ← get
  match st.tokens with
  | t :: rest =>
    set ({ tokens := rest } : PState)
    return t
  | [] => return .eof

private def expect (tok : Token) (msg : String) : ParserM Unit := do
  let t ← bump
  if t != tok then throw msg

private def isImplicitMulStart : Token → Bool
  | .lparen | .ident _ => true
  | _ => false

private def isKnownPrefixFn (name : String) : Bool :=
  ["sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "std", "sign", "signum",
   "lead", "order", "step", "dstep", "ddstep", "isinf", "isfinite", "isinfsm"].contains name

mutual
  private partial def parseProgram : ParserM Expr := do
    let first ← parseStmt
    let mut stmts := [first]
    while (← peek) == .semi do
      let _ ← bump
      if (← peek) == .eof then break
      let next ← parseStmt
      stmts := stmts ++ [next]
    match stmts with
    | [single] => return single
    | many => return .seq many

  private partial def parseStmt : ParserM Expr := do
    let (t1, t2, t3) ← peek3
    -- Function definition: `f(x) = body`
    match t1, t2, t3 with
    | .ident fn, .lparen, .ident param =>
      let saved ← get
      let _ ← bump; let _ ← bump; let _ ← bump
      let (t4, t5) ← peek2
      if t4 == .rparen && t5 == .eq then
        let _ ← bump; let _ ← bump
        let body ← parseComparison
        return .fnDef fn param body
      else
        set saved
    -- Function definition without parens: `f x = body`
    | .ident fn, .ident param, .eq =>
      let _ ← bump; let _ ← bump; let _ ← bump
      let body ← parseComparison
      return .fnDef fn param body
    -- Variable assignment: `a = expr`
    | .ident name, .eq, _ =>
      let _ ← bump; let _ ← bump
      let rhs ← parseComparison
      return .assign name rhs
    | _, _, _ => pure ()
    parseComparison

  private partial def parseComparison : ParserM Expr := do
    let mut lhs ← parseAdd
    while true do
      match (← peek) with
      | .eqEq => let _ ← bump; lhs := .bin .eq lhs (← parseAdd)
      | .bangEq => let _ ← bump; lhs := .bin .ne lhs (← parseAdd)
      | .lt => let _ ← bump; lhs := .bin .lt lhs (← parseAdd)
      | .le => let _ ← bump; lhs := .bin .le lhs (← parseAdd)
      | .gt => let _ ← bump; lhs := .bin .gt lhs (← parseAdd)
      | .ge => let _ ← bump; lhs := .bin .ge lhs (← parseAdd)
      | _ => break
    return lhs

  private partial def parseAdd : ParserM Expr := do
    let mut lhs ← parseMul
    while true do
      match (← peek) with
      | .plus => let _ ← bump; lhs := .bin .add lhs (← parseMul)
      | .minus => let _ ← bump; lhs := .bin .sub lhs (← parseMul)
      | _ => break
    return lhs

  private partial def parseMul : ParserM Expr := do
    let mut lhs ← parseUnary
    while true do
      match (← peek) with
      | .star => let _ ← bump; lhs := .bin .mul lhs (← parseUnary)
      | .slash => let _ ← bump; lhs := .bin .div lhs (← parseUnary)
      | t =>
        if isImplicitMulStart t then
          lhs := .bin .mul lhs (← parsePow)
        else
          break
    return lhs

  private partial def parseUnary : ParserM Expr := do
    match (← peek) with
    | .minus => let _ ← bump; return .neg (← parseUnary)
    | .plus => let _ ← bump; parseUnary
    | _ => parsePow

  private partial def parsePow : ParserM Expr := do
    let base ← parsePrimary
    if (← peek) == .caret then
      let _ ← bump
      let exp ← parseUnary
      return .bin .pow base exp
    else
      return base

  private partial def parsePrimary : ParserM Expr := do
    match (← bump) with
    | .num r => return .lit (FastLC.ofRat r)
    | .lparen =>
      let e ← parseComparison
      expect .rparen "Expected closing parenthesis"
      return e
    | .ident name =>
      if (← peek) == .lparen then
        let _ ← bump
        let mut args : List Expr := []
        if (← peek) != .rparen then
          args := [← parseComparison]
          while (← peek) == .comma do
            let _ ← bump
            args := args ++ [← parseComparison]
        expect .rparen "Expected ')' after function arguments"
        return .call name args
      else if isKnownPrefixFn name then
        -- Support Crowell-style prefix calls like `sqrt d` or `cos sin d`
        match (← peek) with
        | .num _ | .ident _ | .lparen | .minus =>
          let arg ← parseUnary
          return .call name [arg]
        | _ => return .var name
      else
        return .var name
    | tok => throw s!"Unexpected token: {repr tok}"
end

/-- Parse a calculator string into an `Expr`. -/
def parseExpr (input : String) : Except String Expr := do
  let toks ← tokenize input
  let (e, st) ← (parseProgram).run { tokens := toks }
  match st.tokens with
  | [.eof] | [] => return e
  | extra :: _ => throw s!"Unexpected trailing token: {repr extra}"

/-- Mutable evaluation environment holding variables, user functions, and truncation order. -/
structure Env where
  /-- Bound Levi-Civita variables. -/
  vars : Std.HashMap String FastLC := Std.HashMap.emptyWithCapacity
  /-- User-defined unary functions `f(param) = body`. -/
  fns : Std.HashMap String (String × Expr) := Std.HashMap.emptyWithCapacity
  /-- Series truncation order for inversion and transcendentals. -/
  order : Nat := 10

/-- Default calculator environment with standard constants `H`, `ε`, `eps`, `d`, `pi`, `e`. -/
def defaultEnv (order : Nat := 10) : Env :=
  let m : Std.HashMap String FastLC := Std.HashMap.emptyWithCapacity
    |>.insert "H" FastLC.infH
    |>.insert "h" FastLC.infH
    |>.insert "ε" FastLC.infEps
    |>.insert "eps" FastLC.infEps
    |>.insert "d" FastLC.infEps
    |>.insert "pi" (FastLC.ofRat (FastLC.ratOfFloat 3.141592653589793))
    |>.insert "π" (FastLC.ofRat (FastLC.ratOfFloat 3.141592653589793))
    |>.insert "e" (FastLC.ofRat (FastLC.ratOfFloat 2.718281828459045))
  { vars := m, fns := Std.HashMap.emptyWithCapacity, order }

private def expectNum : CalcVal → Except String FastLC
  | .num v => .ok v
  | .bool b => .error s!"Expected a Levi-Civita number, got boolean '{b}'"

/-- Evaluate an `Expr` in an `Env`, returning the computed `CalcVal` and updated `Env`. -/
partial def evalExpr (env : Env) : Expr → Except String (CalcVal × Env)
  | .lit v => .ok (.num v, env)
  | .var name =>
    match env.vars.get? name with
    | some v => .ok (.num v, env)
    | none => .error s!"Undefined variable '{name}'"
  | .neg e => do
    let (v, env') ← evalExpr env e
    let n ← expectNum v
    return (.num (-n), env')
  | .assign name rhs => do
    let (v, env') ← evalExpr env rhs
    let n ← expectNum v
    let env'' :=
      if name == "order" || name == "levi_civita_n" then
        let newOrd :=
          match n.stdPart with
          | some r => max 2 (min 64 r.num.toNat)
          | none => env'.order
        { env' with vars := env'.vars.insert name n, order := newOrd }
      else
        { env' with vars := env'.vars.insert name n }
    return (.num n, env'')
  | .fnDef name param body =>
    let env' := { env with fns := env.fns.insert name (param, body) }
    .ok (.num 0, env')
  | .seq stmts => do
    let mut curEnv := env
    let mut lastVal : CalcVal := .num 0
    for s in stmts do
      let (v, nextEnv) ← evalExpr curEnv s
      lastVal := v
      curEnv := nextEnv
    return (lastVal, curEnv)
  | .bin op l r => do
    let (lv, env1) ← evalExpr env l
    let (rv, env2) ← evalExpr env1 r
    let ln ← expectNum lv
    let rn ← expectNum rv
    match op with
    | .add => return (.num (ln + rn), env2)
    | .sub => return (.num (ln - rn), env2)
    | .mul => return (.num (ln * rn), env2)
    | .div =>
      let q ← FastLC.divNewton ln rn env2.order
      return (.num q, env2)
    | .pow =>
      match rn.stdPart with
      | some expRat =>
        if rn == FastLC.ofRat expRat then
          let p ← FastLC.powRatOrder ln expRat env2.order
          return (.num p, env2)
        else
          -- General `a^b = exp(b * ln(a))` when `b` has infinitesimal parts
          let la ← FastLC.lnOrder ln env2.order
          let p ← FastLC.expOrder (rn * la) env2.order
          return (.num p, env2)
      | none =>
        -- Exponent is infinite (e.g. `(1 + ε)^(1/ε)` = `exp((1/ε) * ln(1 + ε))`)
        let la ← FastLC.lnOrder ln env2.order
        let p ← FastLC.expOrder (rn * la) env2.order
        return (.num p, env2)
    | .eq => return (.bool (ln == rn), env2)
    | .ne => return (.bool (ln != rn), env2)
    | .lt => return (.bool ((ln - rn).signum < 0), env2)
    | .le => return (.bool ((ln - rn).signum ≤ 0), env2)
    | .gt => return (.bool ((ln - rn).signum > 0), env2)
    | .ge => return (.bool ((ln - rn).signum ≥ 0), env2)
  | .call name args =>
    -- Special syntactic forms: `diff(expr, var, at)` and `deriv(fnName, at)`
    if name == "diff" then
      match args with
      | [body, .var param, atExpr] => do
        let (atVal, env1) ← evalExpr env atExpr
        let x0 ← expectNum atVal
        let (y1, _) ← evalExpr { env1 with vars := env1.vars.insert param (x0 + FastLC.infEps) } body
        let (y0, _) ← evalExpr { env1 with vars := env1.vars.insert param x0 } body
        let d := ((← expectNum y1) - (← expectNum y0)) * FastLC.infH
        return (.num (d.truncate env1.order), env1)
      | _ => .error "Usage: diff(expr, var, point), e.g., diff(x^4, x, 2)"
    else if name == "deriv" then
      match args with
      | [.var fnName, atExpr] => do
        let (atVal, env1) ← evalExpr env atExpr
        let x0 ← expectNum atVal
        match env1.fns.get? fnName with
        | some (param, body) =>
          let (y1, _) ← evalExpr { env1 with vars := env1.vars.insert param (x0 + FastLC.infEps) } body
          let (y0, _) ← evalExpr { env1 with vars := env1.vars.insert param x0 } body
          let d := ((← expectNum y1) - (← expectNum y0)) * FastLC.infH
          return (.num (d.truncate env1.order), env1)
        | none => .error s!"Undefined function '{fnName}' in deriv({fnName}, ...)"
      | _ => .error "Usage: deriv(f, x0), e.g., f(x) = x^3; deriv(f, 2)"
    else do
      -- Evaluate arguments eagerly
      let mut curEnv := env
      let mut evalArgs : List FastLC := []
      for a in args do
        let (v, nextEnv) ← evalExpr curEnv a
        evalArgs := evalArgs ++ [← expectNum v]
        curEnv := nextEnv
      match name, evalArgs with
      | "std", [x] =>
        match x.stdPart with
        | some r => return (.num (FastLC.ofRat r), curEnv)
        | none => .error "Infinite Levi-Civita number has no standard part"
      | "sign", [x] | "signum", [x] =>
        return (.num (FastLC.ofRat (mkRat x.signum 1)), curEnv)
      | "abs", [x] => return (.num x.abs, curEnv)
      | "lead", [x] =>
        match x.leadingTerm with
        | some (e, c) => return (.num (FastLC.mono e c), curEnv)
        | none => return (.num 0, curEnv)
      | "order", [x] =>
        match x.order with
        | some e => return (.num (FastLC.ofRat e), curEnv)
        | none => .error "0 has no finite order"
      | "coeff", [x, eVal] =>
        match eVal.stdPart with
        | some eRat => return (.num (FastLC.ofRat (x.coeff eRat)), curEnv)
        | none => .error "coeff exponent must be a standard rational"
      | "trunc", [x, nVal] =>
        match nVal.stdPart with
        | some r => return (.num (x.truncate r.num.toNat), curEnv)
        | none => .error "trunc count must be a standard natural number"
      | "exp", [x] =>
        return (.num (← FastLC.expOrder x curEnv.order), curEnv)
      | "ln", [x] | "log", [x] =>
        return (.num (← FastLC.lnOrder x curEnv.order), curEnv)
      | "sin", [x] =>
        return (.num (← FastLC.sinOrder x curEnv.order), curEnv)
      | "cos", [x] =>
        return (.num (← FastLC.cosOrder x curEnv.order), curEnv)
      | "tan", [x] =>
        let s ← FastLC.sinOrder x curEnv.order
        let c ← FastLC.cosOrder x curEnv.order
        return (.num (← FastLC.divNewton s c curEnv.order), curEnv)
      | "sqrt", [x] =>
        return (.num (← FastLC.sqrtOrder x curEnv.order), curEnv)
      | "step", [x] =>
        return (.num (← StepFunction.logisticStep x curEnv.order), curEnv)
      | "dstep", [x] =>
        return (.num (← StepFunction.logisticDerivCentral x curEnv.order), curEnv)
      | "ddstep", [x] =>
        return (.num (← StepFunction.logisticDeriv2Central x (curEnv.order + 2)), curEnv)
      | "eval", [x, nVal] =>
        match nVal.stdPart with
        | some r =>
          let bigN := FastLC.ratToFloat r
          if bigN ≤ 0.0 then .error "Finite substitution N must be positive"
          else
            let approx := x.evalFinite bigN
            return (.num (FastLC.ofRat (FastLC.ratOfFloat approx 100000000)), curEnv)
        | none => .error "Finite substitution N must be a standard positive number"
      | "isinf", [x] => return (.bool x.isInfinite, curEnv)
      | "isfinite", [x] => return (.bool x.isFinite, curEnv)
      | "isinfsm", [x] | "isinfinitesimal", [x] => return (.bool x.isInfinitesimal, curEnv)
      | fnName, [arg] =>
        match curEnv.fns.get? fnName with
        | some (param, body) =>
          let fnEnv := { curEnv with vars := curEnv.vars.insert param arg }
          let (res, _) ← evalExpr fnEnv body
          return (res, curEnv)
        | none => .error s!"Unknown function '{fnName}'"
      | fnName, _ =>
        .error s!"Unknown function '{fnName}' or wrong argument count"

/-- Convenience one-shot evaluation of a calculator expression string. -/
def evalString (input : String) (order : Nat := 10) : Except String CalcVal := do
  let expr ← parseExpr input
  let (val, _) ← evalExpr (defaultEnv order) expr
  return val

/-- Evaluate an expression expecting a `FastLC` result. -/
def evalFastLC (input : String) (order : Nat := 10) : Except String FastLC := do
  expectNum (← evalString input order)

private def escapeJsonStr (s : String) : String :=
  let rec go (acc : String) : List Char → String
    | [] => acc
    | '"' :: rest => go (acc ++ "\\\"") rest
    | '\\' :: rest => go (acc ++ "\\\\") rest
    | '\n' :: rest => go (acc ++ "\\n") rest
    | '\r' :: rest => go (acc ++ "\\r") rest
    | c :: rest => go (acc.push c) rest
  go "" s.toList

/-- Evaluate an expression and serialize rich result metadata as JSON for the web app API. -/
def evalToJson (input : String) (bigN : Float := 100.0) (order : Nat := 10) : String :=
  match evalString input order with
  | .error err =>
    "{" ++
    "\"ok\":false," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"error\":\"{escapeJsonStr err}\"" ++
    "}"
  | .ok (.bool b) =>
    let bStr := if b then "true" else "false"
    "{" ++
    "\"ok\":true," ++
    "\"kind\":\"bool\"," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"exact\":\"{bStr}\"," ++
    s!"\"approx\":\"{bStr}\"," ++
    s!"\"value\":{bStr}" ++
    "}"
  | .ok (.num x) =>
    let stdJson :=
      match x.stdPart with
      | some r => s!"\"{escapeJsonStr (FastLC.ofRat r).pretty}\""
      | none => "null"
    let leadJson :=
      match x.leadingTerm with
      | some (e, c) =>
        s!"\"{escapeJsonStr (FastLC.mono e c).pretty}\""
      | none => "\"0\""
    let termsJson := x.terms.map fun (e, c) =>
      "{" ++
      s!"\"exp\":\"{escapeJsonStr (toString e)}\"," ++
      s!"\"exp_f\":{FastLC.ratToFloat e}," ++
      s!"\"coeff\":\"{escapeJsonStr (toString c)}\"," ++
      s!"\"coeff_f\":{FastLC.ratToFloat c}" ++
      "}"
    let evalN := x.evalFinite bigN
    let evalNJson := if evalN.isNaN || evalN.isInf then "null" else s!"{evalN}"
    let kindTag :=
      if x.isZero then "zero"
      else if x.isInfinite then "infinite"
      else if x.isInfinitesimal then "infinitesimal"
      else "finite"
    "{" ++
    "\"ok\":true," ++
    "\"kind\":\"num\"," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"exact\":\"{escapeJsonStr x.pretty}\"," ++
    s!"\"approx\":\"{escapeJsonStr x.prettyApprox}\"," ++
    s!"\"regime\":\"{kindTag}\"," ++
    s!"\"sign\":{x.signum}," ++
    s!"\"dominant\":{leadJson}," ++
    s!"\"std_part\":{stdJson}," ++
    s!"\"term_count\":{x.terms.length}," ++
    s!"\"eval_N\":{bigN}," ++
    s!"\"eval_finite\":{evalNJson}," ++
    "\"terms\":[" ++ String.intercalate "," termsJson ++ "]" ++
    "}"

end LeanInf.Calc
