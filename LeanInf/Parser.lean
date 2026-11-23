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

private def lexNumber (chars : List Char) : Except String (Rat × List Char) :=
  let (intPart, rest1) := chars.span Char.isDigit
  let (fracPart, rest2) :=
    match rest1 with
    | '.' :: more =>
      let (fd, r) := more.span Char.isDigit
      (fd, r)
    | _ => ([], rest1)
  if intPart.length + fracPart.length > 500 then
    .error "Numeric literal exceeds 500 digits"
  else
    let baseNum := parseNatDigits (intPart ++ fracPart)
    let baseScale : Int := -(Int.ofNat fracPart.length)
    let (expShift, expTooLarge, rest3) : Int × Bool × List Char :=
      match rest2 with
      | 'e' :: '+' :: d :: more | 'E' :: '+' :: d :: more =>
        if d.isDigit then
          let (ed, r) := (d :: more).span Char.isDigit
          if ed.length > 6 then (0, true, r)
          else (Int.ofNat (parseNatDigits ed), false, r)
        else (0, false, rest2)
      | 'e' :: '-' :: d :: more | 'E' :: '-' :: d :: more =>
        if d.isDigit then
          let (ed, r) := (d :: more).span Char.isDigit
          if ed.length > 6 then (0, true, r)
          else (-(Int.ofNat (parseNatDigits ed)), false, r)
        else (0, false, rest2)
      | 'e' :: d :: more | 'E' :: d :: more =>
        if d.isDigit then
          let (ed, r) := (d :: more).span Char.isDigit
          if ed.length > 6 then (0, true, r)
          else (Int.ofNat (parseNatDigits ed), false, r)
        else (0, false, rest2)
      | _ => (0, false, rest2)
    let totalExp : Int := baseScale + expShift
    if expTooLarge || totalExp.natAbs > 400 then
      .error "Numeric literal exponent exceeds limit (|exp| ≤ 400)"
    else
      let rat : Rat :=
        if totalExp ≥ 0 then
          mkRat (Int.ofNat (baseNum * Nat.pow 10 totalExp.toNat)) 1
        else
          mkRat (Int.ofNat baseNum) (Nat.pow 10 totalExp.natAbs)
      .ok (rat, rest3)

/-- Tokenize a calculator input string into a list of tokens. -/
partial def tokenize (input : String) : Except String (List Token) :=
  let rec go (acc : List Token) : List Char → Except String (List Token)
    | [] => .ok (acc.reverse ++ [.eof])
    | c :: rest =>
      if c.isWhitespace then go acc rest
      else if c.isDigit || (c == '.' && match rest with | d :: _ => d.isDigit | _ => false) then do
        let (r, rem) ← lexNumber (c :: rest)
        go (.num r :: acc) rem
      else if isIdentStart c then
        let (idChars, rem) := (c :: rest).span isIdentChar
        go (.ident (String.ofList idChars) :: acc) rem
      else
        match c, rest with
        | '+', _ => go (.plus :: acc) rest
        | '-', _ => go (.minus :: acc) rest
        | '−', _ => go (.minus :: acc) rest
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
      match base with
      | .var "e" => return .call "exp" [exp]
      | _ => return .bin .pow base exp
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

private def builtinIdentNames : List String :=
  [ "H", "h", "ε", "eps", "d", "pi", "π", "e", "x", "y", "z"
  , "sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "std"
  , "sign", "signum", "lead", "order", "coeff", "trunc", "eval"
  , "step", "dstep", "ddstep", "diff", "deriv"
  , "isinf", "isfinite", "isinfsm", "isinfinitesimal", "levi_civita_n" ]

private def splitGluedMathIdent (s : String) : Option (List String) :=
  if s.length < 2 || builtinIdentNames.contains s then none
  else
    let rec go (acc : List String) : List Char → Option (List String)
      | [] =>
        if acc.length ≥ 2 then some acc.reverse else none
      | 'e' :: 'p' :: 's' :: rest => go ("eps" :: acc) rest
      | 'p' :: 'i' :: rest => go ("pi" :: acc) rest
      | c :: rest =>
        if c == 'H' || c == 'h' || c == 'ε' || c == 'π' || c == 'x' || c == 'y' || c == 'z' || c == 'd' then
          go (String.singleton c :: acc) rest
        else
          none
    go [] s.toList

private partial def collectDefinedNames (toks : List Token) : List String :=
  let rec goDiffParam (depth : Nat) (commas : Nat) : List Token → Option String
    | [] => none
    | .lparen :: rest => goDiffParam (depth + 1) commas rest
    | .rparen :: rest =>
      if depth == 0 then none else goDiffParam (depth - 1) commas rest
    | .comma :: (.ident p) :: .comma :: _ =>
      if depth == 0 && commas == 0 then some p else none
    | .comma :: rest =>
      goDiffParam depth (if depth == 0 then commas + 1 else commas) rest
    | _ :: rest => goDiffParam depth commas rest
  let rec go (atStmtStart : Bool) (acc : List String) : List Token → List String
    | [] => acc
    | .semi :: rest => go true acc rest
    | .ident "diff" :: .lparen :: rest =>
      let acc' := match goDiffParam 0 0 rest with
        | some p => p :: acc
        | none => acc
      go false acc' rest
    | .ident fn :: .lparen :: .ident param :: .rparen :: .eq :: rest =>
      if atStmtStart then go false (fn :: param :: acc) rest
      else go false acc (.lparen :: .ident param :: .rparen :: .eq :: rest)
    | .ident fn :: .ident param :: .eq :: rest =>
      if atStmtStart then go false (fn :: param :: acc) rest
      else go false acc (.ident param :: .eq :: rest)
    | .ident name :: .eq :: rest =>
      if atStmtStart then go false (name :: acc) rest
      else go false acc (.eq :: rest)
    | _ :: rest => go false acc rest
  go true [] toks

private def expandGluedTokens (toks : List Token) : List Token :=
  let defined := collectDefinedNames toks
  let rec intersperseStar : List String → List Token
    | [] => []
    | [a] => [.ident a]
    | a :: rest => .ident a :: .star :: intersperseStar rest
  let rec go (acc : List Token) : List Token → List Token
    | [] => acc.reverse
    | .ident name :: rest =>
      let followedByCall := match rest with | .lparen :: _ => true | _ => false
      if followedByCall || defined.contains name then
        go (.ident name :: acc) rest
      else
        match splitGluedMathIdent name with
        | some parts => go ((intersperseStar parts).reverse ++ acc) rest
        | none => go (.ident name :: acc) rest
    | tok :: rest => go (tok :: acc) rest
  go [] toks

/-- Parse a calculator string into an `Expr`. -/
def parseExpr (input : String) : Except String Expr := do
  let rawToks ← tokenize input
  let toks := expandGluedTokens rawToks
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

private def matchExpScaled : Expr → Option (Option Expr × Expr)
  | .call "exp" [u] => some (none, u)
  | .bin .mul b (.call "exp" [u]) => some (some b, u)
  | .bin .mul (.call "exp" [u]) b => some (some b, u)
  | .neg inner =>
    match matchExpScaled inner with
    | some (none, u) => some (some (.lit (-1)), u)
    | some (some b, u) => some (some (.neg b), u)
    | none => none
  | _ => none

private def matchLogisticDen : Expr → Option (Expr × Option Expr × Expr)
  | .bin .add l r =>
    match matchExpScaled r with
    | some (b?, u) => some (l, b?, u)
    | none =>
      match matchExpScaled l with
      | some (b?, u) => some (r, b?, u)
      | none => none
  | .bin .sub l r =>
    match matchExpScaled r with
    | some (none, u) => some (l, some (.lit (-1)), u)
    | some (some b, u) => some (l, some (.neg b), u)
    | none =>
      match matchExpScaled l with
      | some (b?, u) => some (.neg r, b?, u)
      | none => none
  | _ => none

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
  | .bin .div l r => do
    -- Safe logistic division: handle `num / (a + b * exp(u))` and `num / (a + b * exp(u))^k`
    -- when `u` is infinite (`u < 0` => `exp(u)` super-exponentially infinitesimal,
    -- `u > 0` => `exp(u)` super-exponentially infinite), while keeping standalone `exp(H)` an error.
    let logisticHandled : Option (CalcVal × Env) ←
      match matchLogisticDen r with
      | some (aExpr, bExpr?, uExpr) =>
        let (lv, env1) ← evalExpr env l
        let ln ← expectNum lv
        let (uv, env2) ← evalExpr env1 uExpr
        let un ← expectNum uv
        if un.isInfinite then
          let (av, env3) ← evalExpr env2 aExpr
          let an ← expectNum av
          let (bn, env4) ←
            match bExpr? with
            | some bExpr =>
              let (bv, e4) ← evalExpr env3 bExpr
              pure (← expectNum bv, e4)
            | none => pure ((1 : FastLC), env3)
          if bn.isZero then
            let q ← FastLC.divNewton ln an env4.order
            pure (some (.num q, env4))
          else if un.signum < 0 then
            let q ← FastLC.divNewton ln an env4.order
            pure (some (.num q, env4))
          else
            pure (some (.num 0, env4))
        else
          pure none
      | none =>
        match r with
        | .bin .pow baseE expE =>
          match matchLogisticDen baseE with
          | some (aExpr, bExpr?, uExpr) =>
            let (lv, env1) ← evalExpr env l
            let ln ← expectNum lv
            let (uv, env2) ← evalExpr env1 uExpr
            let un ← expectNum uv
            if un.isInfinite then
              let (av, env3) ← evalExpr env2 aExpr
              let an ← expectNum av
              let (bn, env4) ←
                match bExpr? with
                | some bExpr =>
                  let (bv, e4) ← evalExpr env3 bExpr
                  pure (← expectNum bv, e4)
                | none => pure ((1 : FastLC), env3)
              let (ev, env5) ← evalExpr env4 expE
              let en ← expectNum ev
              match en.stdPart with
              | some expRat =>
                if en == FastLC.ofRat expRat && expRat > 0 && !bn.isZero then
                  if un.signum < 0 then
                    let ak ← FastLC.powRatOrder an expRat env5.order
                    let q ← FastLC.divNewton ln ak env5.order
                    pure (some (.num q, env5))
                  else
                    pure (some (.num 0, env5))
                else
                  pure none
              | none => pure none
            else
              pure none
          | none => pure none
        | _ => pure none
    match logisticHandled with
    | some res => return res
    | none =>
      let (lv, env1) ← evalExpr env l
      let (rv, env2) ← evalExpr env1 r
      let ln ← expectNum lv
      let rn ← expectNum rv
      let q ← FastLC.divNewton ln rn env2.order
      return (.num q, env2)
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
          let la ← FastLC.lnOrder ln (env2.order + 1)
          let prod := (rn * la).truncateRel (env2.order + 1)
          let p ← FastLC.expOrder prod env2.order
          return (.num p, env2)
      | none =>
        -- Exponent is infinite (e.g. `(1 + ε)^(1/ε)` = `exp((1/ε) * ln(1 + ε))`):
        -- lift `lnOrder` by `ceil(max(0, rn.order)) + 1` so multiplying by `H^extra` keeps all
        -- terms through `ε^(order - 1)` exact (fixes `det_52`).
        let extra : Nat :=
          match rn.order with
          | some e =>
            if e > 0 then
              let ceilE : Int := if e.den == 1 then e.num else e.num / (Int.ofNat e.den) + 1
              min 32 ceilE.toNat
            else 0
          | none => 0
        let la ← FastLC.lnOrder ln (env2.order + extra + 1)
        let prod := (rn * la).truncateRel (env2.order + 1)
        let p ← FastLC.expOrder prod env2.order
        return (.num p, env2)
    | .eq => return (.bool (ln == rn), env2)
    | .ne => return (.bool (ln != rn), env2)
    | .lt => return (.bool ((ln - rn).signum < 0), env2)
    | .le => return (.bool ((ln - rn).signum ≤ 0), env2)
    | .gt => return (.bool ((ln - rn).signum > 0), env2)
    | .ge => return (.bool ((ln - rn).signum ≥ 0), env2)
  | .call name args =>
    -- Special syntactic forms: `diff(expr, var, at [, step])` and `deriv(fnName, at)`
    if name == "diff" then
      match args with
      | [body, .var param, atExpr] => do
        let (atVal, env1) ← evalExpr env atExpr
        let x0 ← expectNum atVal
        let (y1, _) ← evalExpr { env1 with vars := env1.vars.insert param (x0 + FastLC.infEps) } body
        let (y0, _) ← evalExpr { env1 with vars := env1.vars.insert param x0 } body
        let d := ((← expectNum y1) - (← expectNum y0)) * FastLC.infH
        return (.num (d.truncate env1.order), env1)
      | [body, .var param, atExpr, stepExpr] => do
        let (atVal, env1) ← evalExpr env atExpr
        let x0 ← expectNum atVal
        let (stepVal, env2) ← evalExpr env1 stepExpr
        let hVal ← expectNum stepVal
        if hVal.isZero then
          throw "diff step size must be nonzero"
        let (yPlus, _) ← evalExpr { env2 with vars := env2.vars.insert param (x0 + hVal) } body
        let (yMinus, _) ← evalExpr { env2 with vars := env2.vars.insert param (x0 - hVal) } body
        let num := (← expectNum yPlus) - (← expectNum yMinus)
        let d ← FastLC.divNewton num ((2 : FastLC) * hVal) env2.order
        return (.num d, env2)
      | _ => .error "Usage: diff(expr, var, point [, step]), e.g., diff(x^4, x, 2)"
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
        | some r => return (.num (x.truncateRel r.num.toNat), curEnv)
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

private def hexDigit (n : Nat) : Char :=
  match n % 16 with
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3'
  | 4 => '4' | 5 => '5' | 6 => '6' | 7 => '7'
  | 8 => '8' | 9 => '9' | 10 => 'a' | 11 => 'b'
  | 12 => 'c' | 13 => 'd' | 14 => 'e' | _ => 'f'

/-- Escape a string for safe embedding inside a JSON string literal (RFC 8259),
    including `\"`, `\\`, `\n`, `\r`, `\t`, and all control characters `< 0x20`. -/
def escapeJsonStr (s : String) : String :=
  let rec go (acc : String) : List Char → String
    | [] => acc
    | '"' :: rest => go (acc ++ "\\\"") rest
    | '\\' :: rest => go (acc ++ "\\\\") rest
    | '\n' :: rest => go (acc ++ "\\n") rest
    | '\r' :: rest => go (acc ++ "\\r") rest
    | '\t' :: rest => go (acc ++ "\\t") rest
    | c :: rest =>
      let code := c.toNat
      if code < 0x20 then
        let esc := "\\u00" ++ String.singleton (hexDigit (code / 16)) ++ String.singleton (hexDigit code)
        go (acc ++ esc) rest
      else
        go (acc.push c) rest
  go "" s.toList

mutual
  private def hasFreeVarAux (v : String) (bound : List String) (e : Expr) : Bool :=
    match e with
    | .lit _ => false
    | .var name => name == v && !(bound.contains name)
    | .neg inner => hasFreeVarAux v bound inner
    | .bin _ l r => hasFreeVarAux v bound l || hasFreeVarAux v bound r
    | .assign _ rhs => hasFreeVarAux v bound rhs
    | .fnDef _ param body => hasFreeVarAux v (param :: bound) body
    | .call "diff" [body, .var param, atExpr] =>
      hasFreeVarAux v (param :: bound) body || hasFreeVarAux v bound atExpr
    | .call "diff" [body, .var param, atExpr, stepExpr] =>
      hasFreeVarAux v (param :: bound) body || hasFreeVarAux v bound atExpr || hasFreeVarAux v bound stepExpr
    | .call _ args => hasFreeVarList v bound args
    | .seq stmts => hasFreeVarSeq v bound stmts
  termination_by sizeOf e

  private def hasFreeVarList (v : String) (bound : List String) (es : List Expr) : Bool :=
    match es with
    | [] => false
    | e :: rest => hasFreeVarAux v bound e || hasFreeVarList v bound rest
  termination_by sizeOf es

  private def hasFreeVarSeq (v : String) (bound : List String) (stmts : List Expr) : Bool :=
    match stmts with
    | [] => false
    | s :: rest =>
      match s with
      | .assign name rhs => hasFreeVarAux v bound rhs || hasFreeVarSeq v (name :: bound) rest
      | .fnDef _ param body => hasFreeVarAux v (param :: bound) body || hasFreeVarSeq v bound rest
      | other => hasFreeVarAux v bound other || hasFreeVarSeq v bound rest
  termination_by sizeOf stmts
end

/-- Check whether `v` appears as a free variable in `e`, respecting binders (`assign`, `fnDef`,
    `diff` parameter, and sequential `seq` bindings). -/
def hasFreeVar (e : Expr) (v : String := "x") : Bool :=
  hasFreeVarAux v [] e

-- TODO: add t later
private def plotVarCandidates : List String := ["x", "y", "z"]

/-- Collect distinct free plotting variables from `["x", "y", "z"]` in canonical order (`x`, `y`, `z`). -/
def freePlotVars (e : Expr) : List String :=
  plotVarCandidates.filter fun v => hasFreeVar e v

private def isFiniteFloat (f : Float) : Bool :=
  !f.isNaN && !f.isInf

private structure FloatEnv where
  vars : Std.HashMap String Float
  fns : Std.HashMap String (String × Expr)
  bigN : Float

private def defaultFloatEnvVars (bigN : Float) (bindings : List (String × Float)) : FloatEnv :=
  let effN := if isFiniteFloat bigN && bigN > 0.0 then bigN else 100.0
  let base : Std.HashMap String Float := Std.HashMap.emptyWithCapacity
    |>.insert "H" effN
    |>.insert "h" effN
    |>.insert "ε" (1.0 / effN)
    |>.insert "eps" (1.0 / effN)
    |>.insert "d" (1.0 / effN)
    |>.insert "pi" 3.141592653589793
    |>.insert "π" 3.141592653589793
    |>.insert "e" 2.718281828459045
  let m := bindings.foldl (init := base) fun acc (k, v) => acc.insert k v
  { vars := m, fns := Std.HashMap.emptyWithCapacity, bigN := effN }

private partial def evalExprFloatAux (fEnv : FloatEnv) : Expr → Option (Float × FloatEnv)
  | .lit v => some (v.evalFinite fEnv.bigN, fEnv)
  | .var name =>
    match fEnv.vars.get? name with
    | some v => some (v, fEnv)
    | none => none
  | .neg inner => do
    let (v, env1) ← evalExprFloatAux fEnv inner
    return (-v, env1)
  | .assign name rhs => do
    let (v, env1) ← evalExprFloatAux fEnv rhs
    return (v, { env1 with vars := env1.vars.insert name v })
  | .fnDef name param body =>
    some (0.0, { fEnv with fns := fEnv.fns.insert name (param, body) })
  | .seq stmts => do
    let mut curEnv := fEnv
    let mut lastVal := 0.0
    for s in stmts do
      let (v, nextEnv) ← evalExprFloatAux curEnv s
      lastVal := v
      curEnv := nextEnv
    return (lastVal, curEnv)
  | .bin .div l r => do
    -- Overflow-safe IEEE-754 logistic division: handles `u > 700` without `Inf / Inf = NaN`
    let logisticRes : Option (Float × FloatEnv) :=
      match matchLogisticDen r with
      | some (aExpr, bExpr?, uExpr) => do
        let (lv, env1) ← evalExprFloatAux fEnv l
        let (uv, env2) ← evalExprFloatAux env1 uExpr
        if uv > 700.0 then
          let (bn, env3) ←
            match bExpr? with
            | some bE => evalExprFloatAux env2 bE
            | none => some (1.0, env2)
          if bn != 0.0 then some (0.0, env3) else none
        else if uv < -700.0 then
          let (av, env3) ← evalExprFloatAux env2 aExpr
          if av == 0.0 then none else some (lv / av, env3)
        else
          none
      | none => none
    match logisticRes with
    | some res => return res
    | none =>
      let (lv, env1) ← evalExprFloatAux fEnv l
      let (rv, env2) ← evalExprFloatAux env1 r
      if rv == 0.0 then none
      else return (lv / rv, env2)
  | .bin op l r => do
    let (lv, env1) ← evalExprFloatAux fEnv l
    let (rv, env2) ← evalExprFloatAux env1 r
    match op with
    | .add => return (lv + rv, env2)
    | .sub => return (lv - rv, env2)
    | .mul => return (lv * rv, env2)
    | .div => if rv == 0.0 then none else return (lv / rv, env2)
    | .pow => return (Float.pow lv rv, env2)
    | .eq => return (if lv == rv then 1.0 else 0.0, env2)
    | .ne => return (if lv != rv then 1.0 else 0.0, env2)
    | .lt => return (if lv < rv then 1.0 else 0.0, env2)
    | .le => return (if lv ≤ rv then 1.0 else 0.0, env2)
    | .gt => return (if lv > rv then 1.0 else 0.0, env2)
    | .ge => return (if lv ≥ rv then 1.0 else 0.0, env2)
  | .call name args =>
    if name == "diff" then
      match args with
      | [body, .var param, atExpr] => do
        let (x0, env1) ← evalExprFloatAux fEnv atExpr
        let h := max 1e-6 (min 1e-4 (1.0 / (env1.bigN * env1.bigN)))
        let (y1, _) ← evalExprFloatAux { env1 with vars := env1.vars.insert param (x0 + h) } body
        let (y0, _) ← evalExprFloatAux { env1 with vars := env1.vars.insert param (x0 - h) } body
        return ((y1 - y0) / (2.0 * h), env1)
      | [body, .var param, atExpr, stepExpr] => do
        let (x0, env1) ← evalExprFloatAux fEnv atExpr
        let (hRaw, env2) ← evalExprFloatAux env1 stepExpr
        let h := if isFiniteFloat hRaw && hRaw.abs > 1e-12 then hRaw.abs
                 else max 1e-6 (min 1e-4 (1.0 / (env2.bigN * env2.bigN)))
        let (y1, _) ← evalExprFloatAux { env2 with vars := env2.vars.insert param (x0 + h) } body
        let (y0, _) ← evalExprFloatAux { env2 with vars := env2.vars.insert param (x0 - h) } body
        return ((y1 - y0) / (2.0 * h), env2)
      | _ => none
    else if name == "deriv" then
      match args with
      | [.var fnName, atExpr] => do
        let (x0, env1) ← evalExprFloatAux fEnv atExpr
        let (param, body) ← env1.fns.get? fnName
        let h := max 1e-6 (min 1e-4 (1.0 / (env1.bigN * env1.bigN)))
        let (y1, _) ← evalExprFloatAux { env1 with vars := env1.vars.insert param (x0 + h) } body
        let (y0, _) ← evalExprFloatAux { env1 with vars := env1.vars.insert param (x0 - h) } body
        return ((y1 - y0) / (2.0 * h), env1)
      | _ => none
    else do
      let mut curEnv := fEnv
      let mut evalArgs : List Float := []
      for a in args do
        let (v, nextEnv) ← evalExprFloatAux curEnv a
        evalArgs := evalArgs ++ [v]
        curEnv := nextEnv
      match name, evalArgs with
      | "exp", [u] => return (Float.exp u, curEnv)
      | "ln", [u] | "log", [u] => if u > 0.0 then return (Float.log u, curEnv) else none
      | "sin", [u] => return (Float.sin u, curEnv)
      | "cos", [u] => return (Float.cos u, curEnv)
      | "tan", [u] => return (Float.tan u, curEnv)
      | "sqrt", [u] => if u ≥ 0.0 then return (Float.sqrt u, curEnv) else none
      | "abs", [u] => return (u.abs, curEnv)
      | "sign", [u] | "signum", [u] =>
        return (if u > 0.0 then 1.0 else if u < 0.0 then -1.0 else 0.0, curEnv)
      | "std", [u] | "lead", [u] => return (u, curEnv)
      | "trunc", [u, _] | "eval", [u, _] => return (u, curEnv)
      | "step", [u] => return (StepFunction.sigmoidFloat (curEnv.bigN * u), curEnv)
      | "dstep", [u] => return (curEnv.bigN * StepFunction.sigmoidDerivFloat (curEnv.bigN * u), curEnv)
      | "ddstep", [u] =>
        return (curEnv.bigN * curEnv.bigN * StepFunction.sigmoidDeriv2Float (curEnv.bigN * u), curEnv)
      | fnName, [arg] =>
        match curEnv.fns.get? fnName with
        | some (param, body) =>
          let (res, _) ← evalExprFloatAux { curEnv with vars := curEnv.vars.insert param arg } body
          return (res, curEnv)
        | none => none
      | _, _ => none

/-- Fast native `Float` evaluator for plotting an `Expr` at `H ↦ bigN`, `ε ↦ 1/bigN`, and arbitrary
    free variable bindings `bindings`. -/
def evalExprFloatVars (expr : Expr) (bigN : Float) (bindings : List (String × Float)) : Option Float :=
  match evalExprFloatAux (defaultFloatEnvVars bigN bindings) expr with
  | some (y, _) => if isFiniteFloat y then some y else none
  | none => none

/-- Fast native `Float` evaluator for plotting an `Expr` at `H ↦ bigN`, `ε ↦ 1/bigN`, `x ↦ xVal`. -/
def evalExprFloat (expr : Expr) (bigN : Float) (xVal : Float) : Option Float :=
  evalExprFloatVars expr bigN [("x", xVal)]

private def cleanFloat (x : Float) : Float :=
  if x == 0.0 then 0.0 else x

private def formatCleanNum (x : Float) : String :=
  if isFiniteFloat x && x == x.round && x.abs < 1e12 then
    if x < 0.0 then s!"-{(-x).toUInt64}" else s!"{x.toUInt64}"
  else
    s!"{cleanFloat x}"

private def dedupSortedFloats (xs : List Float) (tol : Float := 1e-12) : List Float :=
  let rec go (prev : Option Float) (acc : List Float) : List Float → List Float
    | [] => acc.reverse
    | x :: rest =>
      match prev with
      | some p =>
        if (x - p).abs ≤ tol then go prev acc rest
        else go (some x) (x :: acc) rest
      | none => go (some x) (x :: acc) rest
  go none [] xs

private def yBounds (pts : Array (Float × Float)) : Float × Float :=
  if pts.isEmpty then (0.0, 1.0)
  else
    let ys := (pts.map Prod.snd).qsort (fun a b => a < b)
    let lo := ys[0]!
    let hi := ys[ys.size - 1]!
    let fullRange := hi - lo
    if fullRange.abs < 1e-12 then (lo - 1.0, hi + 1.0)
    else if ys.size ≥ 20 then
      let i05 := (ys.size * 5) / 100
      let i95 := min (ys.size - 1) ((ys.size * 95) / 100)
      let p05 := ys[i05]!
      let p95 := ys[i95]!
      let span90 := p95 - p05
      if span90 > 0.0 && fullRange > 50.0 * span90 then
        let pad := 0.25 * span90
        (p05 - pad, p95 + pad)
      else
        (lo, hi)
    else
      (lo, hi)

private def jsonFloatOrNull (f : Float) : String :=
  if isFiniteFloat f then s!"{cleanFloat f}" else "null"

private def formatPointsJson (pts : Array (Float × Float)) : String :=
  "[" ++ String.intercalate "," (pts.toList.map fun (x, y) => s!"[{cleanFloat x},{cleanFloat y}]") ++ "]"

private def formatOptFloatArrayJson (vals : Array (Option Float)) : String :=
  "[" ++ String.intercalate "," (vals.toList.map fun v =>
    match v with
    | some f => jsonFloatOrNull f
    | none => "null") ++ "]"

private def formatStringArrayJson (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map fun s => s!"\"{escapeJsonStr s}\"") ++ "]"

private def scaleHintForCurve (pts : Array (Float × Float)) : String :=
  if pts.size < 2 then "linear"
  else
    let ys := pts.map Prod.snd
    let allPos := ys.all fun y => y > 0.0
    if allPos then
      let sorted := ys.qsort (fun a b => a < b)
      let lo := sorted[0]!
      let hi := sorted[sorted.size - 1]!
      if lo > 0.0 && hi / lo ≥ 1000.0 then "loglog" else "linear"
    else
      let posAbs := (ys.filterMap fun y =>
        let a := y.abs
        if a > 0.0 then some a else none).qsort (fun a b => a < b)
      if posAbs.isEmpty then "linear"
      else
        let lo := posAbs[0]!
        let hi := posAbs[posAbs.size - 1]!
        if hi / lo ≥ 1000.0 then "symlog" else "linear"

private def scaleHintForMacro (pts : Array (Float × Float)) : String :=
  if pts.size < 2 then "linear"
  else
    let ys := pts.map Prod.snd
    let maxAbs := ys.foldl (init := 0.0) fun m y => max m y.abs
    if maxAbs == 0.0 then "linear"
    else
      let zeroFloor := maxAbs * 1e-9
      let allStrictlyPosY := ys.all fun y => y > zeroFloor
      let allPosX := pts.all fun (x, _) => x > 0.0
      let sigAbs := (ys.filterMap fun y =>
        let a := y.abs
        if a > zeroFloor then some a else none).qsort (fun a b => a < b)
      if sigAbs.isEmpty then "linear"
      else
        let minSig := sigAbs[0]!
        let medSig := sigAbs[sigAbs.size / 2]!
        if allStrictlyPosY && (maxAbs / max minSig 1e-15) ≥ 1000.0 then
          if allPosX then
            let xs := (pts.map Prod.fst).qsort (fun a b => a < b)
            let minX := xs[0]!
            let maxX := xs[xs.size - 1]!
            if maxX / max minX 1e-15 ≥ 100.0 then "loglog" else "symlog"
          else "symlog"
        else if (maxAbs / max medSig 1e-6) ≥ 1000.0 then
          "symlog"
        else
          "linear"

private def scaleHintForValues (vals : Array (Option Float)) : String :=
  let finiteVals := vals.filterMap id
  if finiteVals.size < 2 then "linear"
  else
    let maxAbs := finiteVals.foldl (init := 0.0) fun m z => max m z.abs
    if maxAbs == 0.0 then "linear"
    else
      let zeroFloor := maxAbs * 1e-9
      let sigAbs := (finiteVals.filterMap fun z =>
        let a := z.abs
        if a > zeroFloor then some a else none).qsort (fun a b => a < b)
      if sigAbs.isEmpty then "linear"
      else
        let medSig := sigAbs[sigAbs.size / 2]!
        if (maxAbs / max medSig 1e-6) ≥ 1000.0 then "symlog" else "linear"

private def zRangeOfFinite (vals : Array Float) : Float × Float :=
  if vals.isEmpty then (0.0, 1.0)
  else
    let first := vals[0]!
    vals.foldl (init := (first, first)) fun (lo, hi) v => (min lo v, max hi v)

private def evalSingleProbe (baseEnv : Env) (expr : Expr) (effN : Float)
    (lbl : String) (bindings : List (String × FastLC)) : String × Option String × String :=
  let vars' := bindings.foldl (init := baseEnv.vars) fun acc (k, v) => acc.insert k v
  let pEnv := { baseEnv with vars := vars' }
  match evalExpr pEnv expr with
  | .ok (.num v, _) =>
    let evalN := v.evalFinite effN
    let evalNJson := jsonFloatOrNull evalN
    let regime :=
      if v.isZero then "zero"
      else if v.isInfinite then "infinite"
      else if v.isInfinitesimal then "infinitesimal"
      else "finite"
    let item :=
      "{" ++
      s!"\"x_label\":\"{escapeJsonStr lbl}\"," ++
      "\"ok\":true," ++
      s!"\"exact\":\"{escapeJsonStr v.pretty}\"," ++
      s!"\"approx\":\"{escapeJsonStr v.prettyApprox}\"," ++
      s!"\"regime\":\"{regime}\"," ++
      s!"\"eval_finite\":{evalNJson}" ++
      "}"
    (lbl, some v.pretty, item)
  | .ok (.bool b, _) =>
    let bStr := if b then "true" else "false"
    let item :=
      "{" ++
      s!"\"x_label\":\"{escapeJsonStr lbl}\"," ++
      "\"ok\":true," ++
      s!"\"exact\":\"{bStr}\"," ++
      s!"\"approx\":\"{bStr}\"," ++
      "\"regime\":\"bool\"," ++
      "\"eval_finite\":null" ++
      "}"
    (lbl, some bStr, item)
  | .error err =>
    let item :=
      "{" ++
      s!"\"x_label\":\"{escapeJsonStr lbl}\"," ++
      "\"ok\":false," ++
      s!"\"error\":\"{escapeJsonStr err}\"" ++
      "}"
    (lbl, none, item)

private def fnProbePoints : List (String × FastLC) :=
  [ ("-1", (-1 : FastLC))
  , ("-ε", -FastLC.infEps)
  , ("0", (0 : FastLC))
  , ("ε²", FastLC.mono (-2) 1)
  , ("ε", FastLC.infEps)
  , ("1", (1 : FastLC)) ]

private def fn2ProbePoints : List (String × FastLC × FastLC) :=
  [ ("(0,0)", (0 : FastLC), (0 : FastLC))
  , ("(1,0)", (1 : FastLC), (0 : FastLC))
  , ("(0,1)", (0 : FastLC), (1 : FastLC))
  , ("(-1,-1)", (-1 : FastLC), (-1 : FastLC))
  , ("(ε,0)", FastLC.infEps, (0 : FastLC))
  , ("(0,ε)", (0 : FastLC), FastLC.infEps) ]

private def fn3ProbePoints : List (String × FastLC × FastLC × FastLC) :=
  [ ("(0,0,0)", (0 : FastLC), (0 : FastLC), (0 : FastLC))
  , ("(1,0,0)", (1 : FastLC), (0 : FastLC), (0 : FastLC))
  , ("(0,1,0)", (0 : FastLC), (1 : FastLC), (0 : FastLC))
  , ("(0,0,1)", (0 : FastLC), (0 : FastLC), (1 : FastLC))
  , ("(ε,0,0)", FastLC.infEps, (0 : FastLC), (0 : FastLC))
  , ("(ε,ε,ε)", FastLC.infEps, FastLC.infEps, FastLC.infEps) ]

private def evalFnToJson (input : String) (expr : Expr) (varName : String)
    (bigN : Float) (order : Nat) : String :=
  let effN := if isFiniteFloat bigN && bigN > 0.0 then bigN else 100.0
  let baseEnv := defaultEnv order
  -- A. Exact Lean 4 FastLC probes at 6 key points
  let probeRes := fnProbePoints.map fun (lbl, xLC) =>
    evalSingleProbe baseEnv expr effN lbl [(varName, xLC)]
  let probesJson := "[" ++ String.intercalate "," (probeRes.map fun (_, _, j) => j) ++ "]"
  let preferred := ["-1", "0", "1"].filterMap fun target =>
    match probeRes.find? (fun (l, _, _) => l == target) with
    | some (_, some exStr, _) => some s!"f({target}) = {exStr}"
    | _ => none
  let exactSummary :=
    if preferred.length == 3 then
      String.intercalate ",  " preferred
    else
      let anyOk := probeRes.filterMap fun (l, exOpt, _) =>
        exOpt.map fun exStr => s!"f({l}) = {exStr}"
      let picked := anyOk.take 3
      if picked.isEmpty then s!"f({varName})" else String.intercalate ",  " picked
  -- B. Macro plot points in [-1, 1] (101 uniform + 61 cluster in [-10/N, 10/N], sorted & deduped)
  let uniformXs : Array Float := (Array.range 101).map fun i =>
    -1.0 + 2.0 * (Float.ofNat i) / 100.0
  let clusterSpan := min 1.0 (10.0 / effN)
  let clusterXs : Array Float := (Array.range 61).map fun i =>
    -clusterSpan + 2.0 * clusterSpan * (Float.ofNat i) / 60.0
  let combinedXs := (uniformXs ++ clusterXs).qsort (fun a b => a < b)
  let macroXs := dedupSortedFloats combinedXs.toList
  let macroPts : Array (Float × Float) := macroXs.foldl (init := #[]) fun acc t =>
    match evalExprFloatVars expr effN [(varName, t)] with
    | some y => acc.push (t, y)
    | none => acc
  let (yMin, yMax) := yBounds macroPts
  -- C. Micro transition-layer points in [-8/N, 8/N] (81 uniform)
  let zoomHalf := 8.0 / effN
  let zoomPts : Array (Float × Float) := (Array.range 81).foldl (init := #[]) fun acc i =>
    let t := -zoomHalf + 2.0 * zoomHalf * (Float.ofNat i) / 80.0
    match evalExprFloatVars expr effN [(varName, t)] with
    | some y => acc.push (t, y)
    | none => acc
  let (zyMin, zyMax) := yBounds zoomPts
  let anyProbeOk := probeRes.any fun (_, exOpt, _) => exOpt.isSome
  if !anyProbeOk && macroPts.isEmpty then
    -- All probes failed and Float sampler produced zero points (e.g. undefined variable `foo + x`)
    let firstErr :=
      match evalExpr { baseEnv with vars := baseEnv.vars.insert varName (0 : FastLC) } expr with
      | .error e => e
      | .ok _ => "Unable to evaluate function expression"
    "{" ++
    "\"ok\":false," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"error\":\"{escapeJsonStr firstErr}\"" ++
    "}"
  else if macroPts.size < 2 then
    let reason := s!"fewer than 2 finite samples for f({varName}) at H ↦ {formatCleanNum effN}"
    "{" ++
    "\"ok\":true," ++
    "\"kind\":\"fn\"," ++
    s!"\"var\":\"{escapeJsonStr varName}\"," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"exact\":\"{escapeJsonStr exactSummary}\"," ++
    s!"\"approx\":\"f({escapeJsonStr varName}) at H ↦ {formatCleanNum effN}\"," ++
    "\"regime\":\"function\"," ++
    s!"\"eval_N\":{formatCleanNum effN}," ++
    "\"plot_decision\":\"skip_nonfinite\"," ++
    s!"\"plot_reason\":\"{escapeJsonStr reason}\"," ++
    "\"scale_hint\":\"linear\"," ++
    s!"\"probes\":{probesJson}" ++
    "}"
  else
    let sHint := scaleHintForMacro macroPts
    "{" ++
    "\"ok\":true," ++
    "\"kind\":\"fn\"," ++
    s!"\"var\":\"{escapeJsonStr varName}\"," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"exact\":\"{escapeJsonStr exactSummary}\"," ++
    s!"\"approx\":\"f({escapeJsonStr varName}) at H ↦ {formatCleanNum effN}\"," ++
    "\"regime\":\"function\"," ++
    s!"\"eval_N\":{formatCleanNum effN}," ++
    "\"plot_decision\":\"plot\"," ++
    s!"\"scale_hint\":\"{sHint}\"," ++
    s!"\"probes\":{probesJson}," ++
    "\"plot\":{" ++
      s!"\"var\":\"{escapeJsonStr varName}\"," ++
      s!"\"scale_hint\":\"{sHint}\"," ++
      "\"x_min\":-1,\"x_max\":1," ++
      s!"\"y_min\":{cleanFloat yMin},\"y_max\":{cleanFloat yMax}," ++
      s!"\"points\":{formatPointsJson macroPts}," ++
      s!"\"zoom_x_min\":{cleanFloat (-zoomHalf)},\"zoom_x_max\":{cleanFloat zoomHalf}," ++
      s!"\"zoom_y_min\":{cleanFloat zyMin},\"zoom_y_max\":{cleanFloat zyMax}," ++
      s!"\"zoom_points\":{formatPointsJson zoomPts}" ++
    "}" ++
    "}"

private def evalFn2ToJson (input : String) (expr : Expr) (v1 v2 : String)
    (bigN : Float) (order : Nat) : String :=
  let effN := if isFiniteFloat bigN && bigN > 0.0 then bigN else 100.0
  let baseEnv := defaultEnv order
  let probeRes := fn2ProbePoints.map fun (lbl, aLC, bLC) =>
    evalSingleProbe baseEnv expr effN lbl [(v1, aLC), (v2, bLC)]
  let probesJson := "[" ++ String.intercalate "," (probeRes.map fun (_, _, j) => j) ++ "]"
  let okProbes := probeRes.filterMap fun (l, exOpt, _) =>
    exOpt.map fun exStr => s!"f{l} = {exStr}"
  let exactSummary :=
    let picked := okProbes.take 3
    if picked.isEmpty then s!"f({v1},{v2})" else String.intercalate ",  " picked
  -- 21x21 row-major grid: v2 outer (row 0 = -1 .. row 20 = +1), v1 inner (col 0 = -1 .. col 20 = +1)
  let gridSize : Nat := 21
  let coords : Array Float := (Array.range gridSize).map fun i =>
    -1.0 + 2.0 * (Float.ofNat i) / (Float.ofNat (gridSize - 1))
  let gridVals : Array (Option Float) := Id.run do
    let mut out : Array (Option Float) := Array.mkEmpty (gridSize * gridSize)
    for c2 in coords do
      for c1 in coords do
        out := out.push (evalExprFloatVars expr effN [(v1, c1), (v2, c2)])
    return out
  let finiteVals := gridVals.filterMap id
  let anyProbeOk := probeRes.any fun (_, exOpt, _) => exOpt.isSome
  if !anyProbeOk && finiteVals.isEmpty then
    let firstErr :=
      let vMap := baseEnv.vars.insert v1 (0 : FastLC) |>.insert v2 (0 : FastLC)
      match evalExpr { baseEnv with vars := vMap } expr with
      | .error e => e
      | .ok _ => "Unable to evaluate 2-variable function expression"
    "{" ++
    "\"ok\":false," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"error\":\"{escapeJsonStr firstErr}\"" ++
    "}"
  else
    let varsJson := formatStringArrayJson [v1, v2]
    let sHint := scaleHintForValues gridVals
    if finiteVals.size < 2 then
      let reason := s!"fewer than 2 finite grid samples for f({v1},{v2}) at H ↦ {formatCleanNum effN}"
      "{" ++
      "\"ok\":true," ++
      "\"kind\":\"fn2\"," ++
      s!"\"vars\":{varsJson}," ++
      s!"\"input\":\"{escapeJsonStr input}\"," ++
      s!"\"exact\":\"{escapeJsonStr exactSummary}\"," ++
      s!"\"approx\":\"f({escapeJsonStr v1},{escapeJsonStr v2}) at H ↦ {formatCleanNum effN}\"," ++
      "\"regime\":\"function\"," ++
      s!"\"eval_N\":{formatCleanNum effN}," ++
      "\"plot_decision\":\"skip_nonfinite\"," ++
      s!"\"plot_reason\":\"{escapeJsonStr reason}\"," ++
      s!"\"scale_hint\":\"{sHint}\"," ++
      s!"\"probes\":{probesJson}" ++
      "}"
    else
      let (zMin, zMax) := zRangeOfFinite finiteVals
      "{" ++
      "\"ok\":true," ++
      "\"kind\":\"fn2\"," ++
      s!"\"vars\":{varsJson}," ++
      s!"\"input\":\"{escapeJsonStr input}\"," ++
      s!"\"exact\":\"{escapeJsonStr exactSummary}\"," ++
      s!"\"approx\":\"f({escapeJsonStr v1},{escapeJsonStr v2}) at H ↦ {formatCleanNum effN}\"," ++
      "\"regime\":\"function\"," ++
      s!"\"eval_N\":{formatCleanNum effN}," ++
      "\"plot_decision\":\"plot\"," ++
      s!"\"scale_hint\":\"{sHint}\"," ++
      s!"\"grid_size\":{gridSize}," ++
      "\"x_min\":-1,\"x_max\":1,\"y_min\":-1,\"y_max\":1," ++
      s!"\"z_min\":{cleanFloat zMin},\"z_max\":{cleanFloat zMax}," ++
      s!"\"values\":{formatOptFloatArrayJson gridVals}," ++
      s!"\"probes\":{probesJson}" ++
      "}"

private def fn3SliceValues : Array Float :=
  #[-1.0, -0.75, -0.5, -0.25, 0.0, 0.25, 0.5, 0.75, 1.0]

private def evalFn3ToJson (input : String) (expr : Expr) (v1 v2 v3 : String)
    (bigN : Float) (order : Nat) : String :=
  let effN := if isFiniteFloat bigN && bigN > 0.0 then bigN else 100.0
  let baseEnv := defaultEnv order
  let probeRes := fn3ProbePoints.map fun (lbl, aLC, bLC, cLC) =>
    evalSingleProbe baseEnv expr effN lbl [(v1, aLC), (v2, bLC), (v3, cLC)]
  let probesJson := "[" ++ String.intercalate "," (probeRes.map fun (_, _, j) => j) ++ "]"
  let okProbes := probeRes.filterMap fun (l, exOpt, _) =>
    exOpt.map fun exStr => s!"f{l} = {exStr}"
  let exactSummary :=
    let picked := okProbes.take 3
    if picked.isEmpty then s!"f({v1},{v2},{v3})" else String.intercalate ",  " picked
  -- 9 z-slices, each a 13x13 row-major grid in (v1, v2)
  let gridSize : Nat := 13
  let coords : Array Float := (Array.range gridSize).map fun i =>
    -1.0 + 2.0 * (Float.ofNat i) / (Float.ofNat (gridSize - 1))
  let sliceGrids : Array (Array (Option Float)) := fn3SliceValues.map fun c3 => Id.run do
    let mut out : Array (Option Float) := Array.mkEmpty (gridSize * gridSize)
    for c2 in coords do
      for c1 in coords do
        out := out.push (evalExprFloatVars expr effN [(v1, c1), (v2, c2), (v3, c3)])
    return out
  let allVals : Array (Option Float) := sliceGrids.foldl (init := #[]) fun acc g => acc ++ g
  let finiteVals := allVals.filterMap id
  let anyProbeOk := probeRes.any fun (_, exOpt, _) => exOpt.isSome
  if !anyProbeOk && finiteVals.isEmpty then
    let firstErr :=
      let vMap := baseEnv.vars.insert v1 (0 : FastLC)
        |>.insert v2 (0 : FastLC)
        |>.insert v3 (0 : FastLC)
      match evalExpr { baseEnv with vars := vMap } expr with
      | .error e => e
      | .ok _ => "Unable to evaluate 3-variable function expression"
    "{" ++
    "\"ok\":false," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"error\":\"{escapeJsonStr firstErr}\"" ++
    "}"
  else
    let varsJson := formatStringArrayJson [v1, v2, v3]
    let sHint := scaleHintForValues allVals
    let sliceValsJson :=
      "[" ++ String.intercalate "," (fn3SliceValues.toList.map formatCleanNum) ++ "]"
    if finiteVals.size < 2 then
      let reason := s!"fewer than 2 finite grid samples for f({v1},{v2},{v3}) at H ↦ {formatCleanNum effN}"
      "{" ++
      "\"ok\":true," ++
      "\"kind\":\"fn3\"," ++
      s!"\"vars\":{varsJson}," ++
      s!"\"input\":\"{escapeJsonStr input}\"," ++
      s!"\"exact\":\"{escapeJsonStr exactSummary}\"," ++
      s!"\"approx\":\"f({escapeJsonStr v1},{escapeJsonStr v2},{escapeJsonStr v3}) at H ↦ {formatCleanNum effN}\"," ++
      "\"regime\":\"function\"," ++
      s!"\"eval_N\":{formatCleanNum effN}," ++
      "\"plot_decision\":\"skip_nonfinite\"," ++
      s!"\"plot_reason\":\"{escapeJsonStr reason}\"," ++
      s!"\"scale_hint\":\"{sHint}\"," ++
      s!"\"probes\":{probesJson}" ++
      "}"
    else
      let (zMin, zMax) := zRangeOfFinite finiteVals
      let slicesJson :=
        "[" ++ String.intercalate "," (sliceGrids.toList.map formatOptFloatArrayJson) ++ "]"
      "{" ++
      "\"ok\":true," ++
      "\"kind\":\"fn3\"," ++
      s!"\"vars\":{varsJson}," ++
      s!"\"input\":\"{escapeJsonStr input}\"," ++
      s!"\"exact\":\"{escapeJsonStr exactSummary}\"," ++
      s!"\"approx\":\"f({escapeJsonStr v1},{escapeJsonStr v2},{escapeJsonStr v3}) at H ↦ {formatCleanNum effN}\"," ++
      "\"regime\":\"function\"," ++
      s!"\"eval_N\":{formatCleanNum effN}," ++
      "\"plot_decision\":\"plot\"," ++
      s!"\"scale_hint\":\"{sHint}\"," ++
      s!"\"grid_size\":{gridSize}," ++
      "\"x_min\":-1,\"x_max\":1,\"y_min\":-1,\"y_max\":1," ++
      s!"\"z_min\":{cleanFloat zMin},\"z_max\":{cleanFloat zMax}," ++
      s!"\"slice_values\":{sliceValsJson}," ++
      s!"\"slices\":{slicesJson}," ++
      s!"\"probes\":{probesJson}" ++
      "}"

private def buildConstantScaleCurve (x : FastLC) (effN evalN : Float) : Array (Float × Float) :=
  let nMax := max 10000.0 effN
  let raw : Array (Float × Float) := (Array.range 25).foldl (init := #[]) fun acc i =>
    let nVal :=
      if i == 0 then 1.0
      else if i == 24 then nMax
      else Float.pow nMax ((Float.ofNat i) / 24.0)
    let yVal := x.evalFinite nVal
    if isFiniteFloat nVal && isFiniteFloat yVal then acc.push (nVal, yVal) else acc
  if raw.size < 2 && isFiniteFloat effN && effN > 1.0 && isFiniteFloat evalN then
    let hasEffN := raw.any fun (n, _) => (n - effN).abs ≤ 1e-9 * effN
    if hasEffN then raw
    else (raw.push (effN, evalN)).qsort (fun a b => a.1 < b.1)
  else
    raw

/-- Evaluate an expression and serialize rich result metadata as JSON for the web app API. -/
def evalToJson (input : String) (bigN : Float := 100.0) (order : Nat := 10) : String :=
  match parseExpr input with
  | .error err =>
    "{" ++
    "\"ok\":false," ++
    s!"\"input\":\"{escapeJsonStr input}\"," ++
    s!"\"error\":\"{escapeJsonStr err}\"" ++
    "}"
  | .ok expr =>
    match freePlotVars expr with
    | [v] => evalFnToJson input expr v bigN order
    | [v1, v2] => evalFn2ToJson input expr v1 v2 bigN order
    | [v1, v2, v3] => evalFn3ToJson input expr v1 v2 v3 bigN order
    | _ =>
      match evalExpr (defaultEnv order) expr with
      | .error err =>
        "{" ++
        "\"ok\":false," ++
        s!"\"input\":\"{escapeJsonStr input}\"," ++
        s!"\"error\":\"{escapeJsonStr err}\"" ++
        "}"
      | .ok (.bool b, _) =>
        let bStr := if b then "true" else "false"
        "{" ++
        "\"ok\":true," ++
        "\"kind\":\"bool\"," ++
        s!"\"input\":\"{escapeJsonStr input}\"," ++
        s!"\"exact\":\"{bStr}\"," ++
        s!"\"approx\":\"{bStr}\"," ++
        s!"\"value\":{bStr}" ++
        "}"
      | .ok (.num x, _) =>
        let stdJson :=
          match x.stdPart with
          | some r => s!"\"{escapeJsonStr (FastLC.ofRat r).pretty}\""
          | none => "null"
        let leadJson :=
          match x.leadingTerm with
          | some (e, c) =>
            s!"\"{escapeJsonStr (FastLC.mono e c).pretty}\""
          | none => "\"0\""
        let effN := if isFiniteFloat bigN && bigN > 0.0 then bigN else 100.0
        let termsJson := x.terms.map fun (e, c) =>
          "{" ++
          s!"\"exp\":\"{escapeJsonStr (toString e)}\"," ++
          s!"\"exp_f\":{jsonFloatOrNull (FastLC.ratToFloat e)}," ++
          s!"\"coeff\":\"{escapeJsonStr (toString c)}\"," ++
          s!"\"coeff_f\":{jsonFloatOrNull (FastLC.ratToFloat c)}" ++
          "}"
        let evalN := x.evalFinite effN
        let evalNJson := jsonFloatOrNull evalN
        let kindTag :=
          if x.isZero then "zero"
          else if x.isInfinite then "infinite"
          else if x.isInfinitesimal then "infinitesimal"
          else "finite"
        let plotSuffix :=
          if isFiniteFloat evalN then
            let scaleCurve := buildConstantScaleCurve x effN evalN
            let sHint := scaleHintForCurve scaleCurve
            let flatPts : Array (Float × Float) := #[(-1.0, evalN), (0.0, evalN), (1.0, evalN)]
            let (pyMin, pyMax) :=
              if scaleCurve.isEmpty then (evalN - 1.0, evalN + 1.0)
              else yBounds scaleCurve
            ",\"plot_decision\":\"finite_projection\"," ++
            s!"\"scale_hint\":\"{sHint}\"," ++
            "\"plot\":{" ++
              s!"\"finite_y\":{cleanFloat evalN}," ++
              "\"x_min\":-1,\"x_max\":1," ++
              s!"\"y_min\":{cleanFloat pyMin},\"y_max\":{cleanFloat pyMax}," ++
              s!"\"points\":{formatPointsJson flatPts}," ++
              s!"\"scale_curve\":{formatPointsJson scaleCurve}," ++
              s!"\"scale_hint\":\"{sHint}\"" ++
            "}"
          else
            ",\"plot_decision\":\"skip_nonfinite\"," ++
            "\"plot_reason\":\"finite projection overflows Float64 at H ↦ N\""
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
        s!"\"eval_N\":{cleanFloat effN}," ++
        s!"\"eval_finite\":{evalNJson}," ++
        "\"terms\":[" ++ String.intercalate "," termsJson ++ "]" ++
        plotSuffix ++
        "}"

end LeanInf.Calc
