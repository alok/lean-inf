import Lean
import Mathlib

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

def _root_.Array.dropWhile (xs : Array a) (p : a → Bool) : Array a :=
  match xs.findIdx? (fun x => !p x) with
  | none => #[]
  | some i => xs[i:]

namespace Array

/-- Compute the sum of all elements in an array. -/
protected def sum [Add a] [Zero a] (arr : Array a) : a :=
  arr.foldr Add.add 0

/-- Compute the product of all elements in an array. -/
protected def prod [Mul a] [One a] (arr : Array a) : a :=
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

/-- The [p-norm](https://en.wikipedia.org/wiki/Lp_space#The_p-norm) of a vector `v`

The p-norm is defined as:

$\|v\|_p = \left(\sum_{i=1}^n |v_i|^p\right)^{1/p}$

where `v = (v_1, ..., v_n)` is a vector and `p ≥ 1` is a real number.
-/
protected def pNorm (p : Float := 2) (v : Array Float) : Float := Id.run do
  let mut sum := 0
  for _h: i in [:v.size] do
    sum := sum + (v[i] ^ p)
  return sum ^ (1 / p)

/-- The most common norm. A special case of `pNorm` where `p = 2`-/
protected abbrev norm2 (v : Array Float) : Float := v.pNorm (p := 2)
protected abbrev norm (v : Array Float) : Float := v.norm2

end Array

namespace Option

/--
  Unwraps an option, returning the contained value if it is `some`, or a default value if it is `none`.
-/
def unwrapOr [Inhabited a] (val: Option a) (default : a := Inhabited.default) : a :=
  if let some v := val then v else default

end Option

namespace List

/-- Construct a new empty list. -/
protected def empty: List a := []

end List

namespace Float

abbrev ERROR_TOLERANCE : Float := 1e-6

protected abbrev distance (x y : Float) : Float := #[x - y].norm
protected abbrev near (x y : Float) (tol : Float := ERROR_TOLERANCE) : Bool := x.distance y < tol

end Float

namespace Rat

instance : Hashable Rat where hash (r: ℚ) := hash (r.num, hash r.den)

end Rat

namespace Lean.HashMap

instance [Hashable a] [BEq a] [Repr a] [Repr b]: Repr (Lean.HashMap a b) where
  reprPrec m _ :=
    let entries := m.toArray.map (fun (k, v) => s!"{repr k} ↦ {repr v}")
    "{" ++ entries.intercalate ", " ++ "}"

instance [Repr a] [Repr b] [BEq a] [Hashable a] : ToString (Lean.HashMap a b) where
  toString m := s!"{repr m}"

end Lean.HashMap

@[inherit_doc Lean.HashMap.ofList]
def hm! [BEq a] [Hashable a] (x : List (a × b)) : Lean.HashMap a b := Lean.HashMap.ofList x

/-- Generates sequences of {-1,1} of length n that sum to k with non-negative partial sums. -/
def G (n : Nat) (k : Int) : Array (Array Int) := Id.run do
  let mut result := #[]
  let mut stack := #[(0, 0, (#[] : Array Int))]

  while stack.size > 0 do
    let (length, sum, current) := stack.back
    stack := stack.pop

    if length == n then
      if sum == k then
        result := result.push current
    else
      -- Try adding 1
      let partialSum1 := current.foldl (· + ·) 0 + 1
      if partialSum1 >= 0 then
        stack := stack.push (length + 1, sum + 1, current.push 1)

      -- Try adding -1
      let partialSum2 := current.sum - 1
      if partialSum2 >= 0 && sum - 1 >= -(n - length - 1) then
        stack := stack.push (length + 1, sum - 1, current.push (-1))

  return result

#eval #[1, 2, 3, 4].sum = 10
#eval #[].sum = 0
#eval #[1, 2, 3, 4].prod = 24
#eval #[].prod = 1

#eval G 2 0  = #[#[1, -1]]
#eval G 3 0  = #[]
#eval G 4 0  = #[#[1, -1, 1, -1], #[1, 1, -1, -1]]

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

#eval hm! [(1,1),(2,1)]

#eval #[1.0, 2.0, 3.0].pNorm
