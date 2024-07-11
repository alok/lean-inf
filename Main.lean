import Mathlib
import Lean.Data.Parsec
import Batteries.Lean.HashMap
import Lean.Data.HashMap
import LeanInf.Basic
import Lean.Util.Path
import Lean.Data.Rat
-- open Lean.Parsec
import LeanInf.Poly
import Mathlib.Algebra.Order.Group.Abs
#eval Array.intercalate ", " #[s!"a", s!"b", s!"c"]
#eval let a:= (Lean.HashMap.ofList [(1, 1), (2, 2)]); (a, s!"{a}")



-- TODO rm? too overlapping-/
local instance [Neg a] [Add a] : Sub a where
  sub x y := x + (-y)

@[inherit_doc Float]
abbrev Coeff := Float
@[inherit_doc Rat]
abbrev Exponent := Rat


/-- A term in a polynomial. Given as `(Coeff, Exponent)`. -/
abbrev Term := Coeff × Exponent

/-- A map from exponents to coefficients -/
abbrev CoeffMap := Lean.HashMap Exponent Coeff  -- TODO use RbMap instead bc sorted?


structure Polynomial' where
  coeffs : CoeffMap := .empty
deriving Repr, Inhabited

def Polynomial'.ofList (l : List Term) : Polynomial' := Id.run do
  let mut result := .empty
  for (coeff, exp) in l do
    let existingCoeff := result.findD exp 0
    result := result.insert exp (existingCoeff + coeff)
  return ⟨result⟩

/-- Create a `Polynomial'` from a list of tuples -/
notation "p[" t "]" => Polynomial'.ofList t

#eval p[[(1,2)]]
instance : Zero Polynomial' where
  zero := p[[]]

instance : One Polynomial' where
  one := p[[(0, 1)]]

def Polynomial'.empty : Polynomial' := Zero.zero

namespace Format

private def digitToSuperscript (c : Char) : Char :=
  match c with
  | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
  | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | '9' => '⁹'
  | _ => c

/-- Converts digits 0-9 to their superscript Unicode equivalents, leaving other characters unchanged. Handles negative signs properly. -/
def toSuperscript (s : String) : String :=
  let rec go (acc : String) (chars : List Char) : String :=
    match chars with
    | [] => acc
    | '-' :: rest => go (acc ++ "⁻") rest
    | c :: rest => go (acc.push (digitToSuperscript c)) rest
  go "" s.data

private def sortTerms (terms : Array (Exponent × Coeff)) : Array (Exponent × Coeff) :=
  terms.qsort (fun (a, _) (b, _) =>
    if a < 0 && b < 0 then a > b
    else if a < 0 then true
    else if b < 0 then false
    else a < b)

instance : ToString Polynomial' where
  toString p := Id.run do
    let terms := sortTerms (p.coeffs.toArray)
      |>.map fun (exp, coeff) =>
        match exp with
        | 0 => s!"{coeff}"
        | 1 => s!"{coeff}ε"
        | _ => s!"{coeff}ε{Format.toSuperscript (toString exp)}"
    return terms.intercalate " + "

end Format

instance : Add Polynomial' where
  add p q := Id.run do
    let mut result := p.coeffs

    for (exp, coeff) in q.coeffs do
      let existingCoeff := result.findD exp 0
      result := result.insert exp (existingCoeff + coeff)
    return ⟨result⟩

#eval toString (p[[(1, 2), (2, 3)]] + p[[(1, 1), (3, 4)]])

#eval  p[[(1,2),(-1,2)]]


def Polynomial'.partition (poly: Polynomial') : (Coeff × CoeffMap × CoeffMap) := Id.run do
  let mut (std, infinite, infinitesimal) := (0, .empty, .empty)

  for (exp, coeff) in poly.coeffs do
    if exp == 0 then
      std := coeff
    else if exp > 0 then
      infinite := infinite.insert exp coeff
    else
      infinitesimal := infinitesimal.insert exp coeff

  return (std, infinite, infinitesimal)

/-- Maps both keys and values of a `HashMap` using a given function.

This function applies the given function `f` to each key-value pair in the `HashMap`,
allowing for both keys and values to be transformed. It returns a new `HashMap` with
the transformed key-value pairs.
-/
def Lean.HashMap.map [BEq k] [Hashable k] [BEq k'] [Hashable k'] (f : k → v → (k' × v')) (m : Lean.HashMap k v) : Lean.HashMap k' v' := Id.run do
  let mut result := .empty
  for (k, v) in m do
    let (newKey, newValue) := f k v
    result := result.insert newKey newValue
  return result

/-- Maps the values of a HashMap using a given function.

This function applies the given function `f` to each value in the HashMap,
keeping the keys unchanged.
-/
def Lean.HashMap.mapValues [BEq k] [Hashable k] (f : v → v') (m : Lean.HashMap k v) : Lean.HashMap k v' :=
  Lean.HashMap.map (fun k v => (k, f v)) m

instance : Neg Polynomial' where
  neg p := ⟨p.coeffs.mapValues (-·)⟩

instance : Sub Polynomial' where
  sub p q := p + (-q)

-- Test cases
#eval toString (-p[[(1, 2), (2, 3)]])  -- Should output: "-2ε - 3ε²"
#eval toString (p[[(1, 2), (2, 3)]] - p[[(1, 1), (2, 1)]])  -- Should output: "ε + 2ε²"

#eval #[1,2,3].map toString |>.intercalate "+"

#eval do
  let (std, infinite, infinitesimal) := Polynomial'.partition (Polynomial'.mk (hm! [(1, 1), (2, -1),(0,3),(3,0)]))
  (s!"std: {std}", s!"infinite: {infinite}", s!"infinitesimal: {infinitesimal}")

instance : Mul Polynomial' where
  mul p q := Id.run do
    let mut result := Polynomial'.empty
    for (expP, coeffP) in p.coeffs do
      for (expQ, coeffQ) in q.coeffs do
        let newExp := expP + expQ
        let newCoeff := coeffP * coeffQ
        let term := ⟨hm! [(newExp, newCoeff)]⟩
        result := result + term
    return result

-- epsilon
#eval toString p[[(1,1)]]

#eval toString  (p[[(1,1), (0, 1)]] ) -- e
#eval toString p[[(1,-1), (0, 1)]] -- 1/e
#eval toString (p[[(1,1), (0, 1)]] * p[[(1,-1), (0, 1)]]) -- e * 1/e = 1
#eval Format.toSuperscript s!"{-1}"

--TODO this should not use oflist but add the terms first
#eval toString (Polynomial'.mk (hm! [(2, 1), (-1, 3), (0, 1)]))  -- Should output
#eval toString (Polynomial'.mk (hm! [(1, 1), (2,4),(2,5), (3, 1), (4, 1), (5, 1), (6, 1), (7, 1), (8, 1), (9, 1), (0, 1)]))  -- Should output: "x + x² + x³ + x⁴ + x⁵ + x⁶ + x⁷ + x⁸ + x⁹ + ¹"

-- TODO use polynomial repr instead of raw hashmaps



structure LeviCivitaNum where -- extends Field
  /-- the standard part of the Levi-Civita number -/
  std : Coeff := 0
  /-- the infinitely big (more properly, unlimited) part of the number -/
  infinite : Polynomial' := .empty
  /-- the infinitesimal part of the number -/
  infinitesimal : Polynomial' := .empty


instance : Repr LeviCivitaNum where
  reprPrec x _ := Id.run do
    let parts := #[
      toString x.infinite,
      if x.std != 0 then toString x.std else "0",
      toString x.infinitesimal
    ]
    let nonEmptyParts := parts.filter (· ≠ "")
    return nonEmptyParts.reverse.intercalate " + "

instance : ToString LeviCivitaNum where
  toString lc := s!"{repr lc}"

instance : Add LeviCivitaNum where
  add x y := {std := x.std + y.std, infinite := x.infinite + y.infinite, infinitesimal := x.infinitesimal + y.infinitesimal}

instance : Coe Coeff LeviCivitaNum where
  coe c := {std := c}


instance : OfNat LeviCivitaNum n where
  ofNat := match n with
    | 0 =>  {std := 0 }
    | 1 => {std := 1}
    | _ => {std := n.toFloat}


def LeviCivitaNum.zero : LeviCivitaNum := 0
instance : Zero LeviCivitaNum where zero := 0
#eval (0 : LeviCivitaNum)

def LeviCivitaNum.one : LeviCivitaNum := 1
instance : One LeviCivitaNum where one := 1

def LeviCivitaNum.ε : LeviCivitaNum := ⟨0, Polynomial'.empty, ⟨hm! [(1, 1)]⟩⟩
#eval (.ε : LeviCivitaNum)



instance : Coe Term LeviCivitaNum where
  coe term := Id.run do
    let (coeff, exp) := term
    let mut out : LeviCivitaNum := {std := 0, infinite := Polynomial'.empty, infinitesimal := Polynomial'.empty}
    return match cmp exp 0 with
      | .eq => ↑coeff
      | .gt => {out with infinite := Polynomial'.mk (hm! [(exp, coeff)])}
      | .lt => {out with infinitesimal := Polynomial'.mk (hm! [(exp, coeff)])}


/-- Create a `LeviCivitaNum` from a list of tuples representing the coefficients and exponents of the polynomial -/
def LeviCivitaNum.ofList (l : List Term) : LeviCivitaNum := l.foldr (fun t acc => acc + t) 0
/-- Create a `LeviCivitaNum` from an array of tuples representing the coefficients and exponents of the polynomial -/
def LeviCivitaNum.ofArray (l : Array (Coeff × Exponent)) : LeviCivitaNum := l.foldr (fun t acc => acc + (↑t)) 0
        -- TODO debug why this was broken (poly addition)
      -- infinitesimal := infinitesimal + Polynomial'.mk (hm! [(exp, existingCoeff + coeff)])


#eval LeviCivitaNum.ofList [(1, 1)]

/-- Create a `LeviCivitaNum` from a list of tuples -/
notation "lc[" t "]" => LeviCivitaNum.ofList t

#eval lc[[(-1, 2), (1, 2)]]
#eval lc[[(1, 3), (-1, 2)]]


/-- Create a `LeviCivitaNum` from an array of tuples -/
notation "lc#[" t "]" => LeviCivitaNum.ofArray t

/-- Create a `Lean.HashMap` from a list of tuples -/
notation "hm[" t "]" => Lean.HashMap.ofList t


instance : Neg LeviCivitaNum where
  neg x := {std := -x.std, infinite := -x.infinite, infinitesimal := -x.infinitesimal}


-- instance : Sub LeviCivitaNum where
--   sub x y := x + (-y)
#synth Sub LeviCivitaNum

#eval do
  let p1 := p[[(1, 2), (2, 3)]]
  let p2 := p[[(1, 1), (3, 4)]]
  let p3 := p1 * p2

  (s!"p1 = {toString p1}",
  s!"p2 = {toString p2}",
  s!"p1 * p2 = {toString p3}")

-- Example usage and test
#eval toString (Polynomial'.mk (hm! [(1, 2), (2, 3)]) * Polynomial'.mk (hm! [(1, 1), (3, 4)]))

instance [BEq k][Hashable k] : Append (Lean.HashMap k v) where
  append x y := Id.run do
    let mut result := x
    for (k, v) in y do
      result := result.insert k v
    return result

#eval (hm! [(1, 1), (2, 2)] ++ hm! [(1, 2), (2, 3)]: Lean.HashMap ℕ ℕ)

instance : Mul LeviCivitaNum where
  mul x y := Id.run do
    -- Create a singleton HashMap for the standard part
    let xStd : CoeffMap := hm! [(0, x.std)]
    let yStd : CoeffMap := hm! [(0, y.std)]

    /- Merge all coefficients into a single Polynomial'

    Note that because the exponents (keys) are disjoint, we can just append the coefficients
    -/
    let xPoly : Polynomial' := ⟨xStd ++ x.infinite.coeffs ++ x.infinitesimal.coeffs⟩
    let yPoly : Polynomial' := ⟨yStd ++ y.infinite.coeffs ++ y.infinitesimal.coeffs⟩

    -- Multiply the polynomials
    let resultPoly := xPoly * yPoly
    -- Helper function to partition a HashMap into three parts

    -- Use the helper function to partition the result
    let (std, infinite, infinitesimal) := resultPoly.partition

    return { std := std, infinite := ⟨infinite⟩, infinitesimal := ⟨infinitesimal⟩ }


-- TODO fix
#eval lc[[(-1, 1), (1, 1)]] * lc[[(-1, 1), (1, 1)]]
#eval lc[[(1, 2), (3, 4)]] * lc[[(1, 2), (3, 4)]]


def Polynomial'.mapCoeffs (f : Coeff → Coeff) (p : Polynomial') : Polynomial' :=
  ⟨p.coeffs.mapValues f⟩

/-- Compute the absolute value of a `LeviCivitaNum`-/
def LeviCivitaNum.abs (x : LeviCivitaNum) : LeviCivitaNum := {std := x.std, infinite := x.infinite.mapCoeffs Float.abs , infinitesimal := x.infinitesimal.mapCoeffs Float.abs}


/--
Expand a Taylor series for a LeviCivita number. `t` is a list of coefficients for the Taylor series.

TODO what does this do?
-/
def LeviCivitaNum.expand (x : LeviCivitaNum) (t : List Coeff) : LeviCivitaNum := Id.run do
  let mut s := LeviCivitaNum.zero
  let mut pow := LeviCivitaNum.one
  for coeff in t do
    let term := (lc[[(coeff, 0)]]) * pow
    s := s + term
    pow := pow * x
  return s



-- Test the expand function
#eval LeviCivitaNum.expand lc[[(1, 1)]] [1, 1, 1/2, 1/6]  -- Should approximate e^x


-- instance : Inv LeviCivitaNum where


/-- d represents epsilon since it's easier to type.-/
def testCases : List (String × Option LeviCivitaNum) := [
  ("1+d", some lc[[(1, 1)]]),
  ("1/d", some lc[[(1, -1)]]),
  ("d+d", some lc[[(2, 1)]]),
  ("d^2", some lc[[(1, 2)]]),
  ("sqrt d", some lc[[(1, 1/2)]]),
  ("2+2", some lc[[(4, 0)]]),
  ("2d", none),
  ("1+d", some lc[[(1, 1)]]),
  ("1/d", some lc[[(1, -1)]]),
  ("d+d", some lc[[(2, 1)]]),
  ("a=6*7;a+5", some lc[[(47, 0)]]),
  ("zzz=1;zzz==1", some lc[[(1, 0)]]),
  ("f x=x^2;f(f(2))", some lc[[(16, 0)]]),
  ("sqrt(-1)", none),  -- Complex numbers not supported
  ("((1+i)/(sqrt 2))^8", none),  -- Complex numbers not supported
  ("(1+d)^pi", none),  -- Result is not a simple LeviCivita number
  ("d^pi", none),
  ("[sqrt(d+d^2)]^2", some lc[[(1, 1), (1, 2)]])
]


def main : IO Unit := do
  IO.println <| (System.FilePath.mk ".././")

#eval main
