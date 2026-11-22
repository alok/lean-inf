import Lean
import Lean.Parser
import Std

open Lean.Parser
open Lean Elab Command
open Parser

/-- Check if a natural number is even. -/
def _root_.Nat.isEven (n : Nat) : Bool := n % 2 == 0

/-- Check if a natural number is odd. -/
def _root_.Nat.isOdd (n : Nat) : Bool := n % 2 == 1

/-- Check if an integer is even. -/
def _root_.Int.isEven (n : Int) : Bool := n % 2 == 0

/-- Check if an integer is odd. -/
def _root_.Int.isOdd (n : Int) : Bool := n % 2 == 1

/-- Find the maximum element in an array by a given key function. -/
def _root_.Array.maxBy? {a b : Type _} [Ord b] [Max b] [LT b] [DecidableRel (@LT.lt b _)]
    (xs : Array a) (f : a → b) : Option a :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some v =>
      match compare (f x) (f v) with
      | .lt => acc
      | _  => some x

namespace Array

namespace Notation

/-- Syntax category for array comprehension clauses. -/
declare_syntax_cat compClause

/-- Comprehension iterator clause. -/
syntax "for " term " in " term : compClause

/-- Guard clause syntax. -/
syntax ifClause := "if " term

/-- Filtered comprehension iterator clause. -/
syntax "for " term " in " term " if " term : compClause

/-- Array comprehension notation. -/
syntax "#[" term " | " compClause,* "]" : term

/-- Semantics for array comprehension notation. -/
macro_rules
  | `(#[$t | for $x in $xs]) => `(($xs).map (fun $x ↦ $t))
  | `(#[$t | for $x in $xs if $p]) => `(Id.run do
    let mut out := #[]
    for $x in $xs do
      if $p then out := out.push $t
    return out)

end Notation

/-- Flatten an array of arrays. -/
def join {α} (xss : Array (Array α)) : Array α := Id.run do
  let mut out := #[]
  for xs in xss do
    out := out ++ xs
  out

/-- Compute the sum of all elements in an array (renamed to avoid conflict with core). -/
def sum' [Add a] [Zero a] (arr : Array a) : a :=
  arr.foldr Add.add 0

/-- Compute the product of all elements in an array. -/
def prod' [Mul a] [One a] (arr : Array a) : a :=
  arr.foldr Mul.mul 1

/-- Cartesian product of two arrays. -/
protected def cartProd (xs : Array a) (ys : Array b) : Array (a × b) := Id.run do
  let mut out := #[]
  for x in xs do
    for y in ys do
      out := out.push (x, y)
  out

/-- Filter an array of values using a parallel array of booleans. -/
protected def filterBy (xs : Array a) (bs : Array Bool) : Array a := Id.run do
  let mut out := #[]
  for (x, b) in xs.zip bs do
    if b then out := out.push x
  return out

/-- Join an array of strings with a separator. -/
protected def intersperse (separator : String) (array : Array String) : String := Id.run do
  let mut out := ""
  for _h : i in [:array.size] do
    if i > 0 then out := out ++ separator
    out := out ++ array[i]
  return out

end Array

namespace Std.HashMap

variable {K V : Type}
variable [Hashable K] [BEq K]

/-- Extensional equality on `Std.HashMap`.
    Fixes the original `getD k v == v` bug that returned `true` on missing keys. -/
instance [BEq V] : BEq (Std.HashMap K V) where
  beq xs ys :=
    xs.size == ys.size && xs.all (fun k v => ys.get? k == some v)

/-- Display a map as `#{ k ↦ v, ... }`. -/
instance [Repr K] [Repr V] : Repr (Std.HashMap K V) where
  reprPrec m _ :=
    let entries := m.toArray.map (fun (k, v) => s!"{repr k} ↦ {repr v}")
    "#{" ++ String.intercalate ", " entries.toList ++ "}"

instance [ToString K] [ToString V] : ToString (Std.HashMap K V) where
  toString m := Id.run do
    let mut out := #[]
    for (k, v) in m do
      out := out.push s!"{k} ↦ {v}"
    "#{" ++ String.intercalate ", " out.toList ++ "}"

/-- Create a new `Std.HashMap` with a single key-value pair. -/
def singleton (k : K) (v : V) : Std.HashMap K V :=
  Std.HashMap.emptyWithCapacity.insert k v

/-- Merge two maps with a combining function. Values from {lit}`other` are combined with
    existing ones via {lit}`f`. -/
def mergeWith (m : Std.HashMap K V) (other : Std.HashMap K V) (f : K → V → V → V) :
    Std.HashMap K V :=
  other.toList.foldl (fun r (p : K × V) =>
    let k := p.1; let v := p.2
    match r.get? k with
    | none => r.insert k v
    | some vprev => r.insert k (f k vprev v)) m

end Std.HashMap

/-- Unwrap an option, returning the contained value if {lit}`some`, or a default value otherwise. -/
def _root_.Option.unwrapOr [Inhabited a] (val : Option a) (default : a := Inhabited.default) : a :=
  val.getD default

/-- Construct an empty list. -/
def _root_.List.empty : List a := []
