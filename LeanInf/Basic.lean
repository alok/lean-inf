import Lean
import Lean.Parser
import Std

open Lean.Parser
open Lean Elab Command
open Parser


/-- {lean}`Nat.isEven`: Check if a natural number is even -/
def _root_.Nat.isEven (n : Nat) : Bool := n % 2 == 0

/-- {lean}`Nat.isOdd`: Check if a natural number is odd -/
def _root_.Nat.isOdd (n : Nat) : Bool := n % 2 == 1

/-- {lean}`Int.isEven`: Check if an integer is even -/
def _root_.Int.isEven (n : Int) : Bool := n % 2 == 0
/-- {lean}`Int.isOdd`: Check if an integer is odd -/
def _root_.Int.isOdd (n : Int) : Bool := n % 2 == 1

/-- Find the maximum element in an array by a given function -/
def _root_.Array.maxBy? {a b : Type _} [Ord b] [Max b] [LT b] [DecidableRel (@LT.lt b _)] (xs : Array a) (f : a → b) : Option a :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some v =>
      match compare (f x) (f v) with
      | .lt => acc
      | _  => some x  -- Keep the last element in case of equality

#eval #[1,2,3].maxBy? (fun (x : Nat) => x)

namespace Array

namespace Notation

/-- {lean}`Lean.Parser.Category.compClause` Array comprehension notation -/
declare_syntax_cat compClause

/-- for x in xs -/
syntax "for " term " in " term : compClause

/-- if x -/
syntax ifClause := "if " term
/-- special case for x in xs if pred x-/
syntax "for " term " in " term " if " term : compClause
/-- `#[x | for x in xs]` -/
syntax "#[" term " | " compClause,* "]" : term
/-- Semantics for Array comprehension notation.-/
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

#eval #[x | for x in #[1,2,3] if x > 2]
#eval #[#[x | for x in #[1,2,3] ] | for _ in #[1,2,3]]

private def dropWhile (array : Array a) (predicate : a → Bool) : Array a :=
  match array.findIdx? (!predicate ·) with
  | none => #[]
  | some i => array[i:]

/-- Compute the sum of all elements in an array (renamed to avoid conflict with core). -/
def sum' [Add a] [Zero a] (arr : Array a) : a :=
  arr.foldr Add.add 0

/-- Compute the product of all elements in an array. -/
def prod' [Mul a] [One a] (arr : Array a) : a :=
  arr.foldr Mul.mul 1

/-- Cartesian product of 2 arrays. Example of the list comprehension notation's flexibility. -/
protected def cartProd (xs : Array a) (ys : Array b) : Array (a × b) := Id.run do
  let mut out := #[]
  for x in xs do
    for y in ys do
      out := out.push (x, y)
  out

/-- Filters a list of values based on a list of booleans. -/
protected def filterBy (xs: Array a) (bs: Array Bool) : Array a := Id.run do
  let mut out := #[]
  for (x, b) in xs.zip bs do
    if b then out := out.push x
  return out

/-- Inserts the {lit}`separator` between the elements of the array. TODO this is List.intersperse-/
protected def intersperse (separator : String) (array : Array String) : String := Id.run do
  let mut out := ""
  for _h: i in [:array.size] do
    if i > 0 then out := out ++ separator
    out := out ++ array[i]
  return out

#eval Array.sum' #[1, 2, 3, 4] = 10
#eval Array.sum' #[] = 0
#eval Array.prod' #[1, 2, 3, 4] = 24
#eval Array.prod' #[] = 1

#eval #[2 | for _ in [1,2]]
#eval #[x | for (x, _) in [(1,2),(3,4)]]
#eval (Id.run do
  let mut out := #[]
  for x in Array.range 5 do
    for y in Array.range 5 do
      if x + y ≤ 3 then out := out.push (x, y)
  out)
#eval #[x| for x in #[1,2,3]]
-- #eval #[4 | if 1 < 0] = #[]
-- #eval #[4 | if 1 < 3] = #[4]
#eval (Id.run do
  let mut out := #[]
  for x in Array.range 5 do
    for y in Array.range 5 do
      if x + y ≤ 3 then out := out.push (x, y)
  out)
#eval #[1,2,3].filterBy #[true, false, true]
#eval #[].dropWhile (fun x => x < 0)

end Array

namespace Std.HashMap

variable {K V : Type}
variable [Hashable K] [BEq K]

-- Note: `all` and `any` are now provided by Std.HashMap in newer versions

-- TODO this may break?
instance [BEq V]: BEq (Std.HashMap K V) where
  beq xs ys :=
    xs.size == ys.size && xs.all (fun k v => ys.getD k v == v)


/-- Display as #\{ a ↦ b, c ↦ d \} -/
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



/-- Creates a new HashMap with a single key-value pair. -/
def singleton (k: K) (v : V) : Std.HashMap K V := Std.HashMap.emptyWithCapacity.insert k v

/-- Merge two maps with a combining function. Values from {lit}`other` are combined with existing ones via {lit}`f`.
    Implemented as a fold over {lit}`other.toList` to make equational reasoning straightforward. -/
def mergeWith (m : Std.HashMap K V) (other : Std.HashMap K V) (f : K → V → V → V) : Std.HashMap K V :=
  other.toList.foldl (fun r (p : K × V) =>
    let k := p.1; let v := p.2
    match r.get? k with
    | none => r.insert k v
    | some vprev => r.insert k (f k vprev v)) m


end Std.HashMap

/-- Unwraps an option, returning the contained value if it is {lit}`some`, or a default value if it is {lit}`none`. -/
def _root_.Option.unwrapOr [Inhabited a] (val: Option a) (default : a := Inhabited.default) : a :=
  val.getD default

#eval (some 3).unwrapOr
#eval none.unwrapOr 2

/-- Construct a new empty list. -/
def _root_.List.empty: List a := []

-- Rational-specific experiments removed for nightly compatibility.
