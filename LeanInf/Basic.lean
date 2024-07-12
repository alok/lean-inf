import Lean
import Mathlib


namespace Array


-- List comprehension notation
declare_syntax_cat compClause
syntax "for " term " in " term : compClause
syntax "if " term : compClause

syntax "[" term " | " compClause,* "]" : term
syntax "#[" term " | " compClause,* "]" : term

macro_rules
  | `(#[$t | for $x in $xs]) => `(($xs).map (λ $x ↦ $t))
  | `(#[$t | if $x]) => `(if $x then #[ $t ] else #[])
  | `(#[$t | $c, $cs,*]) => `(Array.join #[#[$t | $cs,*] | $c ])
  | `([$t | for $x in $xs]) => `(($xs).map (λ $x ↦ $t))
  | `([$t | if $x]) => `(if $x then [ $t ] else [])
  | `([$t | $c, $cs,*]) => `(List.join [[$t | $cs,*] | $c ])

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

/--
  Filters a list of values based on a list of booleans.
-/
protected def filterBy (xs: Array a) (bs: Array Bool) : Array a := Id.run do
  let mut out := #[]
  for (x, b) in xs.zip bs do
    if b then out := out.push x
  return out

protected def intercalate (separator : String) (xs : Array String) : String := Id.run do
  let mut out := ""
  for i in [:xs.size] do
    if i > 0 then out := out ++ separator
    out := out ++ xs[i]!
  return out


#eval #[1, 2, 3, 4].sum = 10
#eval #[].sum = 0
#eval #[1, 2, 3, 4].prod = 24
#eval #[].prod = 1



#eval #[2 | for _ in [1,2]]
#eval #[x | for (x, _) in [(1,2),(3,4)]]
#eval #[(x, y) | for x in Array.range 5, for y in Array.range 5, if x + y <= 3]
#eval #[#[1],#[1,2]].join = #[1, 1, 2]
#eval #[x| for x in #[1,2,3]] = #[1, 2, 3]
#eval (#[#[2],#[3]]|>.join) = #[2, 3]
#eval #[4 | if 1 < 0] = #[]
#eval #[4 | if 1 < 3] = #[4]
#eval #[(x, y) | for x in Array.range 5, for y in Array.range 5, if x + y <= 3] = #[(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (3, 0)]

#eval #[1,2,3].filterBy #[true, false, true] = #[1, 3]
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
    "#{" ++ entries.intercalate ", " ++ "}"

instance [ToString a] [ToString b] [BEq a] [Hashable a] : ToString (Lean.HashMap a b) where
  toString m := Id.run do
    let mut out := #[]
    for (k, v) in m do
      out := out.push s!"{k} ↦ {v}"
    "#{" ++ out.intercalate ", " ++ "}"


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
  -- `mergeWith` is to ensure left to right order for insertion.
  | `(#{$k ↦ $v, $ks,*}) => `(#{$k ↦ $v}.mergeWith (fun _ _ v => v) #{$ks,*}) -- n



-- Example usages
#eval (#{}: Lean.HashMap Int Int)
#eval #{1 ↦ 2 }
#eval #{1 ↦ 1, 2 ↦ 2}
#eval #{}.insert 2 2.0
#eval toString #{1 ↦ 1, 2 ↦ 2}
#eval #{1 ↦ 1, 2 ↦ 2}.mapValues (· + 1)

end Lean.HashMap





/-- Unwraps an option, returning the contained value if it is `some`, or a default value if it is `none`. -/
def _root_.Option.unwrapOr [Inhabited a] (val: Option a) (default : a := Inhabited.default) : a :=
  val.getD default

#eval (some 3).unwrapOr
#eval none.unwrapOr 2


/-- Construct a new empty list. -/
def _root_.List.empty: List a := []

notation a "÷" b => Rat.mk' (num := a) (den := b)


instance : Hashable Rat where hash (r: ℚ) := hash (r.num, hash r.den)

#synth Ord Float
#eval (1 ÷ 2) < (3 ÷ 4:Rat)
#eval (1/2) == (3/4)
#eval (1/2) = (3/4)
#eval (1/2) ≥ (3/4)
#eval (1/2) ≤ (3/4)
