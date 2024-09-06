import Lean
import Lean.Parser
import Std
import Batteries
import Mathlib
open Lean.Parser
open Parser


/-- Check if a natural number is even -/
def _root_.Nat.isEven (n : Nat) : Bool := n % 2 == 0
/-- Check if a natural number is odd -/
def _root_.Nat.isOdd (n : Nat) : Bool := n % 2 == 1
/-- Check if an integer is even -/
def _root_.Int.isEven (n : Int) : Bool := n % 2 == 0
/-- Check if an integer is odd -/
def _root_.Int.isOdd (n : Int) : Bool := n % 2 == 1


def _root_.Array.maxBy? [Ord b] [Max b] [LT b] [DecidableRel (@LT.lt b _)] (xs : Array a) (f : a → b) : Option a :=
  xs.foldl (init := none) fun acc x =>
    match acc with
    | none => some x
    | some v =>
      match compare (f x) (f v) with
      | .lt => acc
      | _  => some x  -- Keep the last element in case of equality

#eval #[1,2,3].maxBy? (fun x => x)




namespace Array

namespace Notation
/-- Array comprehension notation -/
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
  -- TODO
  | `(#[$t | for $x in $xs if $p]) => `(Id.run do
    let mut out := #[]
    for $x in $xs do
      if $p then out := out.push $t
    return out)
  | `(#[$t | $c, $cs,*]) => `(Array.join #[#[$t | $cs,*] | $c ])
end Notation

#eval #[x | for x in #[1,2,3] if x > 2]
#eval #[#[x | for x in #[1,2,3] ] | for _ in #[1,2,3]]

private def dropWhile (array : Array a) (predicate : a → Bool) : Array a :=
  match array.findIdx? (!predicate ·) with
  | none => #[]
  | some i => array[i:]

/-- Compute the sum of all elements in an array. -/
private def sum [Add a] [Zero a] (arr : Array a) : a :=
  arr.foldr Add.add 0

/-- Compute the product of all elements in an array. -/
private def prod [Mul a] [One a] (arr : Array a) : a :=
  arr.foldr Mul.mul 1

/-- Cartesian product of 2 arrays. Example of the list comprehension notation's flexibility. -/
protected def cartProd (xs : Array a) (ys : Array b) : Array (a × b) := #[(x, y) | for x in xs, for y in ys]

/-- Filters a list of values based on a list of booleans. -/
protected def filterBy (xs: Array a) (bs: Array Bool) : Array a := Id.run do
  let mut out := #[]
  for (x, b) in xs.zip bs do
    if b then out := out.push x
  return out

/-- Inserts the `separator` between the elements of the array. TODO this is List.intersperse-/
protected def intersperse (separator : String) (array : Array String) : String := Id.run do
  let mut out := ""
  for _h: i in [:array.size] do
    if i > 0 then out := out ++ separator
    out := out ++ array[i]
  return out

#eval #[1, 2, 3, 4].sum = 10
#eval #[].sum = 0
#eval #[1, 2, 3, 4].prod = 24
#eval #[].prod = 1

#eval #[2 | for _ in [1,2]]
#eval #[x | for (x, _) in [(1,2),(3,4)]]
#eval #[(x, y) | for x in Array.range 5, for y in Array.range 5 if x + y <= 3]
#eval #[#[1],#[1,2]].join
#eval #[x| for x in #[1,2,3]]
#eval (#[#[2],#[3]]|>.join)
-- #eval #[4 | if 1 < 0] = #[]
-- #eval #[4 | if 1 < 3] = #[4]
#eval #[(x, y) | for x in Array.range 5, for y in Array.range 5 if x + y <= 3]
#eval #[1,2,3].filterBy #[true, false, true]
#eval #[].dropWhile (fun x => x < 0)

end Array

namespace Std.HashMap

variable {K V : Type}
variable [Hashable K] [BEq K]

/--
Checks if all key-value pairs in a `HashMap` satisfy a given predicate.

This function applies the given predicate `f` to each key-value pair in the `HashMap`.
It returns `true` if all pairs satisfy the predicate, and `false` otherwise.
-/
def all (xs: Std.HashMap K V) (f: K → V → Bool) : Bool :=
  xs.fold (fun acc k v => acc && f k v) (init := true)

/--
Checks if any key-value pairs in a `HashMap` satisfy a given predicate.

This function applies the given predicate `f` to each key-value pair in the `HashMap`.
It returns `true` if any pair satisfies the predicate, and `false` otherwise.

-- TODO does this short circuit? make test case
-/
def any (xs: Std.HashMap K V) (f: K → V → Bool) : Bool :=
  xs.fold (fun acc k v => acc || f k v) (init := false)

-- TODO this may break?
instance [BEq V]: BEq (Std.HashMap K V) where
  beq xs ys :=
    xs.size == ys.size && xs.all (fun k v => ys.getD k v == v)


/-- Display as #{ a ↦ b, c ↦ d }-/
instance [Repr K] [Repr V] : Repr (Std.HashMap K V) where
  reprPrec m _ :=
    let entries := m.toArray.map (fun (k, v) => s!"{repr k} ↦ {repr v}")
    "#{" ++ entries.intersperse ", " ++ "}"

instance [ToString K] [ToString V] : ToString (Std.HashMap K V) where
  toString m := Id.run do
    let mut out := #[]
    for (k, v) in m do
      out := out.push s!"{k} ↦ {v}"
    "#{" ++ out.intersperse ", " ++ "}"



/-- This function creates a new `HashMap` with a single key-value pair, using the given `k` and `v` as the key and value respectively. -/
def singleton (k: K) (v : V) : Std.HashMap K V := Std.HashMap.empty.insert k v

/-- Syntax category for `HashMap` items separated by the $\maps$ symbol -/
syntax hashMapItem := term " ↦ " term

/-- Syntax for a `HashMap` like `#{1 ↦ 2}` -/
syntax "#{" hashMapItem,* ","? "}" : term

/-- Semantics for `HashMap` notation.-/
macro_rules
  | `(#{}) => `(Std.HashMap.empty) -- 0
  | `(#{$k ↦ $v}) => `(Std.HashMap.singleton $k $v) -- 1
  -- `mergeWith` instead of `.insert` is to ensure left to right order for insertion.
  | `(#{$k ↦ $v, $ks,*}) => `(#{$k ↦ $v}.mergeWith (f := fun _ _v₁ v₂ => v₂) (other := #{$ks,*} )) -- n

#eval (((1:Nat) - (2:Int)) :Int)
-- Example usages
#eval #{1 ↦ 2}
#eval #{1 ↦ 1, 2 ↦ 2}
#eval #{}.insert 2 2.0
#eval toString #{1 ↦ 1, 2 ↦ 2}
#eval #{1 ↦ 1, 2 ↦ 2}.map ((fun x => x + 1):Nat->_->Nat)

end Std.HashMap

/-- Unwraps an option, returning the contained value if it is `some`, or a default value if it is `none`. -/
def _root_.Option.unwrapOr [Inhabited a] (val: Option a) (default : a := Inhabited.default) : a :=
  val.getD default

#eval (some 3).unwrapOr
#eval none.unwrapOr 2

/-- Construct a new empty list. -/
def _root_.List.empty: List a := []

/-- Local notation for creating a rational number. -/
local notation a "÷" b => Lean.mkRat (num := a) (den := b)

/-- TODO these instances aren't equal? `Lean.Rat` and `ℚ`-/
instance : Hashable Lean.Rat  where hash r := hash (hash r.num, hash r.den)
instance : Hashable ℚ where hash r := hash (hash r.num, hash r.den)

-- #eval hash (1 ÷ 4) == hash (Lean.mkRat 5 20)
-- #eval (1 ÷ 2) < (3 ÷ 4:Lean.Rat)
#eval (1/2) == (3/4)
#eval (1/2) = (3/4)
#eval (1/2) ≥ (3/4)
#eval (1/2) ≤ (3/4)
#eval toString #{1 ↦ 1, 2 ↦ 2}
