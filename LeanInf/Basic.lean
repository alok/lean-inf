import Lean
import Lean.Parser
import Mathlib
open Lean.Parsec
open Parser

namespace Array

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

#eval #[x | for x in #[1,2,3] if x > 2]
#eval #[#[x | for x in #[1,2,3] ] | for _ in #[1,2,3]]

private def dropWhile (xs : Array a) (p : a → Bool) : Array a :=
  match xs.findIdx? (fun x => !p x) with
  | none => #[]
  | some i => xs[i:]

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


namespace Lean.HashMap

/--
Checks if all key-value pairs in a `HashMap` satisfy a given predicate.

This function applies the given predicate `f` to each key-value pair in the `HashMap`.
It returns `true` if all pairs satisfy the predicate, and `false` otherwise.
-/
def _root_.Lean.HashMap.all [Hashable K][BEq K][BEq V] (xs: Lean.HashMap K V) (f: K → V → Bool) : Bool :=
  xs.fold (fun acc k v => acc && f k v) true

/--
Checks if any key-value pairs in a `HashMap` satisfy a given predicate.

This function applies the given predicate `f` to each key-value pair in the `HashMap`.
It returns `true` if any pair satisfies the predicate, and `false` otherwise.

-- TODO does this short circuit? make test case
-/
def _root_.Lean.HashMap.any [Hashable K][BEq K][BEq V] (xs: Lean.HashMap K V) (f: K → V → Bool) : Bool :=
  xs.fold (fun acc k v => acc || f k v) false

-- TODO this may break?
instance [Hashable K][BEq K][BEq V] : BEq (Lean.HashMap K V) where
  beq xs ys :=
    xs.size == ys.size && xs.all (fun k v => ys.findD k v == v)


/-- Maps both keys and values of a `HashMap` using a given function.

This function applies the given function `f` to each key-value pair in the `HashMap`,
allowing for both keys and values to be transformed. It returns a new `HashMap` with
the transformed key-value pairs.

TODO(alok): is this just an endofunctor? should it return a hashmap and keep the shape?
-/
def map [BEq K] [Hashable K] [BEq K'] [Hashable K'] (f : K → V → (K' × V')) (m : Lean.HashMap K V) : Lean.HashMap K' V' := Id.run do
  let mut result := .empty
  for (k, v) in m do
    let (k', v') := f k v
    result := result.insert k' v'
  return result

/--Display as #{ a ↦ b, c ↦ d }-/
instance [Hashable a] [BEq a] [Repr a] [Repr b]: Repr (Lean.HashMap a b) where
  reprPrec m _ :=
    let entries := m.toArray.map (fun (k, v) => s!"{repr k} ↦ {repr v}")
    "#{" ++ entries.intersperse ", " ++ "}"

instance [ToString a] [ToString b] [BEq a] [Hashable a] : ToString (Lean.HashMap a b) where
  toString m := Id.run do
    let mut out := #[]
    for (k, v) in m do
      out := out.push s!"{k} ↦ {v}"
    "#{" ++ out.intersperse ", " ++ "}"

/-- Filters a `HashMap` based on a given predicate.

This function applies the given predicate `f` to each key-value pair in the `HashMap`.
It returns a new `HashMap` with the key-value pairs that satisfy the predicate.
-/
def filter [BEq a] [Hashable a] (xs: Lean.HashMap a b) (f: a → b → Bool) : Lean.HashMap a b :=
  Id.run do
    let mut result := .empty
    for (k, v) in xs do
      if f k v then
        result := result.insert k v
    return result

/-- Maps the values of a `HashMap` using a given function.

This function applies the given function `f` to each value in the `HashMap`,
keeping the keys unchanged.
-/
def mapValues [BEq k] [Hashable k] (f : v → v') (xs : Lean.HashMap k v) : Lean.HashMap k v' :=
  xs.map ((·, f ·))

/-- This function creates a new `HashMap` with a single key-value pair, using the given `k` and `v` as the key and value respectively. -/
def singleton [BEq K] [Hashable K] (k:K) (v : V) : Lean.HashMap K V := Lean.HashMap.empty.insert k v

/-- Syntax category for `HashMap` items separated by the $\maps$ symbol -/
syntax hashMapItem := term " ↦ " term

/-- Syntax for a `HashMap` like `#{1 ↦ 2}` -/
syntax "#{" hashMapItem,* ","? "}" : term

/-- Semantics for `HashMap` notation.-/
macro_rules
  | `(#{}) => `(Lean.HashMap.empty) -- 0
  | `(#{$k ↦ $v}) => `(Lean.HashMap.singleton $k $v) -- 1
  -- `mergeWith` instead of `.insert` is to ensure left to right order for insertion.
  | `(#{$k ↦ $v, $ks,*}) => `(#{$k ↦ $v}.mergeWith (fun _ _ v => v) #{$ks,*}) -- n

#eval (((1:Nat) - (2:Int)) :Int)
-- Example usages
#eval (#{}: Lean.HashMap Int Int)
#eval #{1 ↦ 2}
#eval #{1 ↦ 1, 2 ↦ 2}
#eval #{}.insert 2 2.0
#eval toString #{1 ↦ 1, 2 ↦ 2}
#eval #{1 ↦ 1, 2 ↦ 2}.mapValues (· + 1)

end Lean.HashMap

namespace Option
/-- Unwraps an option, returning the contained value if it is `some`, or a default value if it is `none`. -/
def unwrapOr [Inhabited a] (val: Option a) (default : a := Inhabited.default) : a :=
  val.getD default

#eval (some 3).unwrapOr
#eval none.unwrapOr 2

end Option

namespace List

/-- Construct a new empty list. -/
def empty: List a := []

end List

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
