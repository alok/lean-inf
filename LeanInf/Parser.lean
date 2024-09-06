import LeanInf.Basic
import LeanInf.LeviCivitaNum
namespace LeviCivitaNum.Parser
/-! This module contains the parser for the calculator. -/

inductive Expr
  | Number (value : LeviCivitaNum)
  | InfiniteUnit
  | Plus (left right : Expr)
  | Minus (left right : Expr)
  | Mul (left right : Expr)
  | Div (left right : Expr)
  | Pow (left right : Expr)
  | Assign (ident: String) (right : Expr)
  | LParen | RParen
deriving Repr, BEq

def interpreter: Expr -> Except String LeviCivitaNum
  | .Number n => .ok n
  | .InfiniteUnit => .ok lc[H]
  | .Plus left right => do
    .ok ((<-interpreter left) + (<-interpreter right))
  | .Minus left right => do
    .ok ((<-interpreter left) - (<-interpreter right))
  | .Mul left right => do
    .ok ((<-interpreter left) * (<-interpreter right))
  | .Div left right => do
    .ok ((<-interpreter left) / (<-interpreter right))
  | .Assign _ident right => do
    let right <- interpreter right
    .ok (right)
  | x => panic! s!"Not implemented: {x}"

def parser: String -> Except String Expr
  | "1+ε" => .ok (Expr.Plus (Expr.Number 1) (Expr.InfiniteUnit))
  | _ => .error "Not implemented"

def parseAssignment (s:String) : Except String Expr:=do
  let xs := s.split (· == '=')
  let ident := xs[0]!
  let rest := xs[1]!
  let expr <- parser rest
  return .Assign ident expr

def testCases := #[
  "1+d",
  "(1+d)(1-d)",
  "1",
  "((1))",
  "(3.2+d)(-d)",
  "-d",
  " a - d",
  "a = 3; a - d"
  ]

def allTogether (s : String) : Except String LeviCivitaNum := do
  let expr <- parser s
  let result <- interpreter expr
  return result

end LeviCivitaNum.Parser
