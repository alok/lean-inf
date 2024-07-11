import Mathlib
import LeanInf.Basic
import Mathlib.Algebra.DirectSum.Ring

open scoped DirectSum

-- set_option diagnostics true

/-- A generic polynomial represented as an array of coefficients.

In `Poly'`, the coefficients are stored in the array in the order of increasing degree.
-/
@[deprecated "Use `Polynomial'` instead, it supports the necessary non-integer exponents"]
structure Poly' (S) [Semiring S] [Inhabited S] where
  coeffs : Array S
deriving Repr

-- TODO make repr with custom var symbol

namespace Poly'


variable {S : Type} [Semiring S] [Inhabited S] [BEq S]

instance [ToString S]: ToString (Poly' S) where
  toString p := Id.run do
    let mut terms := #[]
    for (i, c) in p.coeffs.toList.enum do
      if c != 0 then
      -- TODO what was up with dependent elimination?
        let isOne := c == 1
        let term := match i, isOne with
          | 0, _ => s!"{c}"
          | 1, true => "x"
          | 1, false => s!"{c}x"
          | i, true => s!"x^{i}"
          | i, false => s!"{c}x^{i}"
        terms := terms.push term
    if terms.isEmpty then
      return "0"
    else
      return terms.intercalate " + "

#eval toString <| Poly'.mk (#[1, 2, 3]) -- "1 + 2x + 3x^2"

/-- Create a polynomial from a list of coefficients. -/
def fromList (l : List S) : Poly' S :=
  ⟨l.toArray⟩

/-- Create a polynomial from a dictionary of coefficients. Keys are the degrees. Values are the coefficients. -/
def fromDict (d: Lean.HashMap Nat S) : Poly' S := Id.run do
  let mut coeffs := Array.mkArray d.size 0
  for (i, c) in d do
    have h: i < coeffs.size := sorry
    coeffs := coeffs.set ⟨i, h⟩ c
  return ⟨coeffs⟩

/-- Remove all zero components from a polynomial. -/
def removeZeros (p : Poly' S) : Poly' S :=
  ⟨p.coeffs.filter (· != 0)⟩

/-- Get the degree of the polynomial. -/
def degree (p : Poly' S) : Nat := Id.run do
  let nonZero := p.removeZeros
  return nonZero.coeffs.size - 1


#eval #[1, 2, 3, 4, 50, 0,2].dropWhile (· ≠ 0) -- #[1, 2, 3, 4, 5]
/-- Trim trailing zero coefficients. -/
def trim (p : Poly' S) : Poly' S :=
  let trimmed := p.coeffs.reverse.dropWhile (· == 0)
  ⟨trimmed.reverse⟩

/-- Add two polynomials. -/
def add (p q : Poly' S) : Poly' S :=
  let maxSize := max p.coeffs.size q.coeffs.size
  let padded1 := p.coeffs.append (Array.mkArray (maxSize - p.coeffs.size) 0)
  let padded2 := q.coeffs.append (Array.mkArray (maxSize - q.coeffs.size) 0)
  ⟨padded1.zipWith padded2 (· + ·)⟩
#eval toString (add (fromList [1, 2, 3]) (fromList [4, 5, 6]))
-- TODO finish
/-- Convolution of two arrays. -/
def convolve (xs ys : Array S) : Array S := Id.run do
  let m := xs.size
  let n := ys.size
  let mut result := Array.mkArray (m + n - 1) 0
  for i in [:m] do
      for j in [:n] do
        let k := i + j
        have h : k < result.size :=  by sorry
        -- exact h'
        -- if h : k < result.size then
        result := result.set ⟨k, h⟩ (result[k] + xs[i]! * ys[j]!)
    return result

#eval convolve #[1, 2, 3] #[4, 5, 6] -- #[4, 13, 28, 27, 18]
/-- Multiply two polynomials. -/
def mul (p q : Poly' S) : Poly' S :=
  ⟨convolve p.coeffs q.coeffs⟩
#eval mul (fromList [1, 2, 3]) (fromList [4, 5, 6]) -- Poly'.mk #[4, 13, 28, 27, 18]

/-- Evaluate a polynomial at a given point. -/
def eval [HPow S Nat S] (p : Poly' S) (x : S) : S :=
  let foldWithIndex (init : S) (f : Nat → S → S → S) (arr : Array S) : S :=
    (arr.foldl (init := (0, init)) (fun (i, acc) x => (i+1, f i acc x))).2
  foldWithIndex 0 (fun i acc coeff => acc + coeff * (x ^ i)) p.coeffs

#eval Poly'.eval (fromList [1, 2, 3]) 2 -- 17

instance : Add (Poly' S) := ⟨add⟩
instance : Mul (Poly' S) := ⟨mul⟩
instance : Zero (Poly' S) := ⟨⟨#[]⟩⟩

end Poly'

def Poly'.fromArray {S : Type} [Semiring S] [Inhabited S] (xs : Array S) : Poly' S :=
  ⟨xs⟩

-- Tests
#eval Poly'.fromList [1, 2, 3] -- Poly'.mk #[1, 2, 3]
#eval Poly'.fromList [1, 2, 3] + Poly'.fromList [4, 5, 6] -- Poly'.mk #[5, 7, 9]
#eval Poly'.fromList [1, 2] * Poly'.fromList [3, 4] -- Poly'.mk #[3, 10, 8]

def p : Poly' Nat := Poly'.fromList [1, 2, 3]
#eval p.eval 2 -- 17
