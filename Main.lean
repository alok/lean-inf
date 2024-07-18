import Mathlib
import Lean.Data.Parsec
import Batteries.Lean.HashMap
import Lean.Data.HashMap

import Lean.Util.Path
import Lean.Data.Rat
import LeanInf.Basic

def _root_.Array.maxBy? [Ord b][Max b][LT b][DecidableRel (@LT.lt b _)] (xs : Array a) (f : a → b) : Option a := Id.run do
  let mut max : Option a := none
  let mut maxVal : Option b := none

  for x in xs do
    if let some mv ← maxVal then
      if f x < mv then
        max := some x
        maxVal := some (f x)
  return max

-- TODO rm? too overlapping-/
instance [Neg a] [Add a] : Sub a where
  sub x y := x + (-y)

@[inherit_doc Float]
abbrev Coeff := Float
@[inherit_doc Rat]
abbrev Exponent := Rat

/-- A term in a polynomial. Given as `(Coeff, Exponent)`. -/
abbrev Term := Coeff × Exponent

/-- A map from exponents to coefficients -/
abbrev CoeffMap := Lean.HashMap Exponent Coeff  -- TODO use RbMap instead bc sorted?

/-- A polynomial, represented as a `HashMap` from exponents to coefficients -/
structure Polynomial' where
  coeffs : CoeffMap := default
deriving Repr, Inhabited

instance : BEq Polynomial' where
  beq p q :=
    -- remove zeros so empty polynomials are handled
    let p' := p.coeffs.filter (fun _ v => v != 0)
    let q' := q.coeffs.filter (fun _ v => v != 0)
    p' == q'


namespace Polynomial'

/-- Add two polynomials by adding their coefficients together -/
instance : Add Polynomial' where
  add p q := Id.run do
    let mut result := p.coeffs
    for (exp, coeff) in q.coeffs do
      let existingCoeff := result.findD exp 0
      result := result.insert exp (existingCoeff + coeff)
    return ⟨result⟩

/-- Negates a polynomial by negating its coefficients -/
instance : Neg Polynomial' where neg p := ⟨p.coeffs.map (fun exp coeff => (exp, -coeff))⟩

#eval Polynomial'.mk #{0 ↦ 1, 1 ↦ 2} + Polynomial'.mk #{-1 ↦ 1, 1 ↦ 2}

/-- The empty polynomial, that is, the constant `0`. -/
def empty : Polynomial' := ⟨.empty⟩

/--  TODO: bad idea? Any real number can be represented as a polynomial with a single term. By the way, this also uses that 0^0 is 1 (since the constant term is x^0) -/
instance : Coe Coeff Polynomial' where
  coe c := ⟨#{0 ↦ c}⟩

/-- Create a `Polynomial'` from a natural 'iiiinttcsdgh'ber -/
instance : OfNat Polynomial' n where ofNat := match n with
  | 0 => .empty
  | 1 => ⟨#{0 ↦ 1}⟩
  | _ => ⟨#{0 ↦ n.toFloat}⟩

/-- For decimal and scientific numbers (e.g., `1.23`, `3.12e10`).

    Examples:
    - `OfScientific.ofScientific 123 true 2`    represents `1.23`
    - `OfScientific.ofScientific 121 false 100` represents `121e100`
-/
instance : OfScientific Polynomial' where
  ofScientific mantissa exponentSign decimalExponent := ⟨#{0 ↦ .ofScientific mantissa exponentSign decimalExponent}⟩

#eval Polynomial'.empty == (⟨#{0.0 ↦ 0}⟩ : Polynomial')
#eval Polynomial'.empty
#eval (1 : Polynomial') == (⟨#{0 ↦ 1}⟩ : Polynomial')

/-- Create a `Polynomial'` from a list of tuples -/
def ofList (l : List Term) : Polynomial' := Id.run do
  let mut result := .empty
  for (coeff, exp) in l do
    let existingCoeff := result.findD exp 0
    result := result.insert exp (existingCoeff + coeff)
  return ⟨result⟩

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
      |>.filter (fun (_, coeff) => coeff != 0)  -- Filter out zero terms
      |>.map fun (exp, coeff) =>
        match exp with
        | 0 => s!"{coeff}"
        | 1 => s!"{coeff}H"
        | -1 => s!"{coeff}ε"
        | n =>
            let unit := if n > 0 then "H" else "ε"
            let exp := Format.toSuperscript (toString (if exp > 0 then exp else -exp))
            s!"{coeff}{unit}{exp}"
    let nonZeroTerms := terms.filter (· ≠ "0")  -- Remove "0" terms
    return if nonZeroTerms.isEmpty then "0" else nonZeroTerms.intersperse " + "

#eval Format.toSuperscript s!"{-1}"

end Format

namespace Notation

/-- Syntax category for infinitesimal or hyperreal units -/
declare_syntax_cat infUnit

/-- Syntax for representing ε (epsilon) or H as infinitesimal or hyperfinite units -/
syntax "ε" : infUnit
syntax "H" : infUnit

/-- Syntax category for polynomial items-/
declare_syntax_cat polyItem

/-- Syntax for representing ε or H as a standalone polynomial item
    Examples: `ε`, `H` -/
syntax infUnit : polyItem

syntax "-" infUnit : polyItem

/-- Syntax for representing a term multiplied by ε or H as a standalone polynomial item
    Examples:
    - `2ε`, `3H`
    - `xε`, `yH` where `x` and `y` are variables -/
syntax term infUnit : polyItem

/-- Syntax for representing ε or H raised to a power as a standalone polynomial item
    Examples:
    - `ε^2`, `H^3`
    - `ε^n`, `H^m` where `n` and `m` are variables -/
syntax infUnit "^" term : polyItem
syntax "-" infUnit "^" term : polyItem
/-- Syntax for representing a standalone term as a polynomial item
    Examples:
    - `1`
    - `x` where `x` is a variable
    - `2.5` for a floating-point number -/
syntax term : polyItem

/-- Syntax for representing a term multiplied by ε or H raised to a power as a standalone polynomial item
    Examples:
    - `2ε^3`, `3H^2`
    - `xε^n`, `yH^m` where `x`, `y`, `n`, and `m` are variables -/
syntax term infUnit "^" term : polyItem

/-- Syntax for a polynomial like `p[1, 2ε, 3ε^2]` -/
syntax "p[" polyItem,* "]" : term

/--Semantics for polynomial notation.-/
macro_rules
  | `(p[]) => `(Polynomial'.empty)
  | `(p[ε]) => `(Polynomial'.mk #{-1 ↦ 1})
  | `(p[-ε]) => `(Polynomial'.mk #{-1 ↦ -1})
  | `(p[H]) => `(Polynomial'.mk #{1 ↦ 1})
  | `(p[-H]) => `(Polynomial'.mk #{1 ↦ -1})
  | `(p[$coeff:term ε]) => `(Polynomial'.mk #{-1 ↦ $coeff})
  | `(p[$coeff:term H]) => `(Polynomial'.mk #{1 ↦ $coeff})
  | `(p[ε^$exp]) => `(p[1ε^$exp])
  | `(p[-ε^$exp]) => `(p[-1ε^$exp])
  | `(p[H^$exp]) => `(p[1H^$exp])
  | `(p[-H^$exp]) => `(p[-1H^$exp])
  | `(p[$coeff:term ε^$exp]) => `(Polynomial'.mk #{-$exp ↦ $coeff})
  | `(p[$coeff:term H^$exp]) => `(Polynomial'.mk #{$exp ↦ $coeff})
  | `(p[$x:polyItem, $xs,*]) => `(p[$x] + p[$xs,*])
  | `(p[$coeff:term]) => `(Polynomial'.mk #{0 ↦ $coeff})

#eval toString <| p[]
#eval toString <| p[ε]
#eval toString <| p[-ε]
#eval toString <| p[H]
#eval toString <| p[-H]
#eval toString <| p[-3H^3]
#eval toString <| p[-ε^3]
#eval toString <| p[1ε]
#eval toString <| p[1ε, 3H]
#eval Id.run do
  let x := 2
  (p[x ε], p[4*x ε^2])
#eval  p[1, 2 ε, 3ε^2]

end Notation
end Polynomial'

#eval toString <| p[ 2ε, 3ε^2, 0 ε] + p[ 2ε, 3ε^2,4H^2]
#eval p[0 ε].coeffs.toArray.filter (fun (_, coeff) => coeff != 0)

def Polynomial'.norm (p : Polynomial') : Polynomial' := ⟨p.coeffs.mapValues (fun coeff => if coeff ==  0 then 0 else 1)⟩

instance : Mul Polynomial' where
  mul p q := Id.run do
    let mut result := Polynomial'.empty
    for (expP, coeffP) in p.coeffs do
      for (expQ, coeffQ) in q.coeffs do
        let newExp := expP + expQ
        let newCoeff := coeffP * coeffQ
        let term := ⟨#{newExp ↦ newCoeff}⟩
        result := result + term
    return result

#eval toString (Polynomial'.mk #{2 ↦ 1, -1 ↦ 3, 0 ↦ 1})  -- Should output
#eval toString (Polynomial'.mk #{1 ↦ 1, 2 ↦ 4, 2 ↦ 5, 3 ↦ 1, 4 ↦ 1, 5 ↦ 1, 6 ↦ 1, 7 ↦ 1, 8 ↦ 1, 9 ↦ 1, 0 ↦ 1})  -- Should output: "x + x² + x³ + x⁴ + x⁵ + x⁶ + x⁷ + x⁸ + x⁹ + ¹"

-- TODO use polynomial repr instead of raw hashmaps

/-- A number in the Levi-Civita number system.
    The number is represented as a polynomial in the standard part and the infinitesimal part.
    The standard part is a polynomial in the standard base 10 number system, and the infinitesimal part is a polynomial in the infinitesimal base 10 number system.
    The infinitesimal part is represented as a polynomial in the infinitesimal number system, which is a system of infinitesimally small numbers.
-/
structure LeviCivitaNum where
  std : Coeff := default
  infinitesimal : Polynomial' := default
  infinite : Polynomial' := default

  /-- To ensure coeffs are in terms of `H`. -/
  _pf_infinitesimal_keys_negative : infinitesimal.coeffs.all (fun exp _ => exp < 0) := by sorry
  /-- To ensure coeffs are in terms of `H`. -/
  _pf_infinite_keys_positive : infinite.coeffs.all (fun exp _ => exp > 0) := by sorry
deriving Repr

instance : BEq LeviCivitaNum where
  beq x y := x.std == y.std && x.infinitesimal == y.infinitesimal && x.infinite == y.infinite

namespace LeviCivitaNum

/-- 0 -/
def zero : LeviCivitaNum := {}

instance : Zero LeviCivitaNum where zero := zero

/-- 1-/
def one : LeviCivitaNum := {std := 1}
instance : One LeviCivitaNum where one := one


instance : Repr LeviCivitaNum where
  reprPrec x _ := #[toString x.infinite, toString x.std, toString x.infinitesimal].intersperse " + "

def _root_.LeviCivitaNum.ε : LeviCivitaNum := {infinitesimal := ⟨#{-1 ↦ 1}⟩}
def _root_.LeviCivitaNum.H : LeviCivitaNum := {infinite := ⟨#{1 ↦ 1}⟩}

instance : Add LeviCivitaNum where
  add x y := {
    std := x.std + y.std
    infinitesimal := x.infinitesimal + y.infinitesimal
    infinite := x.infinite + y.infinite
  }

instance : Neg LeviCivitaNum where
  neg x := {
    std := -x.std
    infinitesimal := -x.infinitesimal
    infinite := -x.infinite
  }

instance : Coe Coeff LeviCivitaNum where
  coe c := {
    std := c
    _pf_infinitesimal_keys_negative := by rfl
    _pf_infinite_keys_positive := by rfl
  }

instance : OfNat LeviCivitaNum n where
  ofNat := match n with
    | 0 => zero
    | 1  => one
    | _ => {std := n.toFloat, _pf_infinitesimal_keys_negative := by rfl, _pf_infinite_keys_positive := by rfl}

instance : OfScientific LeviCivitaNum where
  ofScientific mantissa exponentSign decimalExponent := {
    std := .ofScientific mantissa exponentSign decimalExponent
    _pf_infinitesimal_keys_negative := by rfl
    _pf_infinite_keys_positive := by rfl
  }

#eval (0 : LeviCivitaNum)

/-- Create a `LeviCivitaNum` from a list of tuples representing the coefficients and exponents of the polynomial -/
def ofList (l : Array Term) : LeviCivitaNum := Id.run do
  let mut (std, infinitesimal, infinite) := (0, .empty, .empty)
  for (coeff, exp) in l do
    if exp == 0 then
      std := std + coeff
    else if exp > 0 then
      let existingCoeff := infinite.coeffs.findD exp 0
      infinite := ⟨infinite.coeffs.insert exp (existingCoeff + coeff)⟩
    else
      let existingCoeff := infinitesimal.coeffs.findD exp 0
      infinitesimal := ⟨infinitesimal.coeffs.insert exp (existingCoeff + coeff)⟩
  return {std, infinitesimal, infinite}

/-- Create a `LeviCivitaNum` from an array of tuples representing the coefficients and exponents of the polynomial -/
def ofArray (l : Array (Coeff × Exponent)) : LeviCivitaNum := .ofList l

#eval LeviCivitaNum.ofList #[(1, 1)]

-- Similar syntax for LeviCivita numbers
syntax "lc[" polyItem,* "]" : term

/--Semantics for creating LeviCivitaNum from a list of terms like `lc[ε, H, ε^2, H^2]`, which equals `ε + H + ε^2 + H^2`-/
macro_rules
  | `(lc[]) => `(LeviCivitaNum.zero)
  | `(lc[ε]) => `(LeviCivitaNum.ε)
  | `(lc[-ε]) => `(lc[-1 ε^1])
  | `(lc[H]) => `(LeviCivitaNum.H)
  | `(lc[-H]) => `(lc[-1 H])
  | `(lc[$coeff:term ε]) => `({infinitesimal := ⟨#{-1 ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[$coeff:term H]) => `({infinite := ⟨#{1 ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[ε^$exp]) => `(lc[1ε^$exp])
  | `(lc[-ε^$exp]) => `(lc[-1ε^$exp])
  | `(lc[H^$exp]) => `(lc[1H^$exp])
  | `(lc[-H^$exp]) => `(lc[-1H^$exp])
  | `(lc[$coeff:term ε^$exp]) => `({ infinitesimal := ⟨#{-$exp ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[$coeff:term H^$exp]) => `({ infinite := ⟨#{$exp ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[$x:polyItem, $xs,*]) => `(lc[$x] + lc[$xs,*])
  | `(lc[$coeff:term]) => `({ std := $coeff, _pf_infinitesimal_keys_negative := by rfl, _pf_infinite_keys_positive := by rfl: LeviCivitaNum})

#eval lc[]
#eval lc[1ε]
#eval lc[3ε]
#eval lc[ε]
#eval lc[-ε]
#eval lc[-H]
#eval lc[ε^2]
#eval lc[ε^2 , H^2]
#eval lc[1ε , 2H]

open Polynomial'.Format in
instance : ToString LeviCivitaNum where
  toString x := Id.run do
    let mut terms := #[]
    -- Add infinite terms
    let infiniteTerms := sortTerms (x.infinite.coeffs.toArray)
      |>.map fun (exp, coeff) =>
        if coeff == 0 then
          ""
        else
        match exp with
        | 1 => s!"{coeff}H"
        | 0 => s!"{coeff}"
        | -1 => s!"{coeff}H⁻¹"
        | _ =>
          let unit := "H"
          let exp := toSuperscript (toString exp)
          s!"{coeff}{unit}{exp}"
    terms := terms.append infiniteTerms
    -- Add standard part if non-zero
    if x.std != 0 then
      terms := terms.push s!"{x.std}"
    -- Add infinitesimal terms
    let infinitesimalTerms := sortTerms (x.infinitesimal.coeffs.toArray)
      |>.map fun (exp, coeff) =>
        if coeff == 0 then
          ""
        else
        match exp with
        | 0 => s!"{coeff}"
        | -1 => s!"{coeff}ε"
        | _ =>
          let unit := "ε"
          let exp := toSuperscript (toString (-exp))
          s!"{coeff}{unit}{exp}"
    terms := terms.append infinitesimalTerms
    let nonEmptyParts := terms.filter (· != "")
    -- Combine all terms
    let result := nonEmptyParts.intersperse " + "
    return if result.isEmpty then "0" else result


def _root_.Polynomial'.partition (xs:Polynomial') : LeviCivitaNum := Id.run do
  let mut (std, infinitesimal, infinite) := (0, .empty, .empty)
  for (exp, coeff) in xs.coeffs do
    if exp == 0 then
      std := std + coeff
    else if exp > 0 then
      infinite := ⟨infinite.coeffs.insert exp (coeff)⟩
    else
      infinitesimal := ⟨infinitesimal.coeffs.insert exp (coeff)⟩
  return {std, infinitesimal, infinite}
-- parenthesization is fucked
#eval toString <| p[1, 2ε, 4H, 4H, 3,3ε^2].partition

instance : Mul LeviCivitaNum where
  mul x y :=
    -- split into big polynomial independent of grade, then multiply it. TODO make faster
    let x' := p[x.std] + x.infinite + x.infinitesimal
    let y' := p[y.std] + y.infinite + y.infinitesimal
    (x' * y').partition

/-- Power of a Levi-Civita number. -/
instance: HPow LeviCivitaNum ℕ LeviCivitaNum where
  hPow x n := Id.run do
    let mut (result, base, exp) := (one, x, n)
    while exp > 0 do
      if exp % 2 == 1 then -- exponentiation by squaring
        result := result * base
      base := base * base
      exp := exp / 2
    result

-- Test cases
#eval (lc[2] ^ 3 : LeviCivitaNum)  -- Should be 8
#eval (lc[ε] ^ 2 : LeviCivitaNum)  -- Should be ε^2
#eval (lc[H] ^ 3 : LeviCivitaNum)  -- Should be H^3
#eval (lc[1 , ε] ^ 2 : LeviCivitaNum)  -- Should be 1 + 2ε + ε^2
#eval (lc[2 , H] ^ 3 : LeviCivitaNum)  -- Should be 8 + 12H + 6H^2 + H^3



#eval  lc[ε]*lc[H,ε,H^2]
#eval lc[-ε, ε, H] * lc[-ε,  ε, H]
#eval lc[-ε^2,2ε^3] * lc[ε, 3H]
#eval lc[ε^2, 3ε^4] * lc[ε, 3H]
#eval 0 - p[5H]

#eval 2.0>3.4
#synth LE Coeff




/-- check if the number is a standard number. TODO is 0 a standard number?-/
def isStd (x: LeviCivitaNum) : Bool := x.infinite.coeffs.isEmpty && x.infinitesimal.coeffs.isEmpty

#eval lc[ε]
#eval lc[ε].isStd
#eval lc[ε^2].isStd
#eval lc[ε^2, H].isStd

/-- Compute the sign of a Levi-Civita number. -/
def signum (x: LeviCivitaNum) : Int :=
  let allTerms := #[(0, x.std)] ++ x.infinitesimal.coeffs.toArray ++ x.infinite.coeffs.toArray
  let sortedTerms := allTerms.qsort (fun (exp₁, _) (exp₂, _) =>  exp₁ < exp₂ )
  match sortedTerms.find? (fun (_, coeff) => coeff != 0) with
  | some (_, coeff) => if coeff > 0 then 1 else -1
  | none => 0

#eval lc[1, H, -H^2].signum  -- Should be -1
#eval lc[-ε,H,ε,H,-H^2, H^5].signum  -- Should be -1
#eval lc[ε].signum  -- Should be 1
#eval lc[-H,ε].signum  -- Should be -1
#eval lc[-ε,H].signum  -- Should be 1
#eval lc[-2,ε,H].signum  -- Should be 1

/-- TODO this doesn't work and fails to synthesize Decidable (a :LCN) -> Decidable (b :LCN) -> Prop, which is not what we want.
We want (a < b) to be decidable. -/
instance : LT LeviCivitaNum where
  lt x y := (x - y).signum == (-1:Int)

#eval ((1:LeviCivitaNum) - (2:LeviCivitaNum)).signum
#eval 1<2
#eval lc[1] < lc[2]
#eval lc[ε] < lc[2ε]
#eval lc[H] < lc[2H]
#eval lc[-H] < lc[H]

#eval (lc[ε] - lc[2ε]).signum
#eval (lc[H] - lc[2H]).signum
#eval (lc[-H] - lc[H]).signum

def abs (x : LeviCivitaNum) : LeviCivitaNum :=
  {
    std := Float.abs x.std
    infinitesimal := ⟨x.infinitesimal.coeffs.map (fun exp coeff => (exp, Float.abs coeff))⟩
    infinite := ⟨x.infinite.coeffs.map (fun exp coeff => (exp, Float.abs coeff))⟩
  }

#eval abs lc[-ε]
#eval abs lc[-H,2,-4]

def expand (x : LeviCivitaNum) (t : List Coeff) : LeviCivitaNum := Id.run do
  let mut s := zero
  let mut pow := one
  for coeff in t do
    let term := (↑coeff : LeviCivitaNum) * pow
    s := s + term
    pow := pow * x
  return s

/-- Truncate a Levi-Civita number to a certain grade. Negative will clip infinitesimals, positive will clip unlimited terms too.-/
def truncate (x: LeviCivitaNum) (n: Int) : LeviCivitaNum :=
  {
    std := if n <= 0 then x.std else 0
    infinitesimal := ⟨x.infinitesimal.coeffs.filter (fun exp _ => exp <= n)⟩
    infinite := ⟨x.infinite.coeffs.filter (fun exp _ => exp <= n)⟩
  }


def Term.abs (x: (Exponent × Coeff)) : (Exponent × Coeff) := (x.1, Float.abs x.2)
#eval  ((1,2):(Exponent × Coeff))
instance : LT (Exponent × Coeff) where
  lt x y := match x, y with
  | (exp₁, coeff₁), (exp₂, coeff₂) => exp₁ < exp₂ || (exp₁ == exp₂ && coeff₁ < coeff₂)


def largestTerm (x: LeviCivitaNum) : (Exponent × Coeff) := Id.run do
  let allTerms := #[(0, x.std)] ++ x.infinitesimal.coeffs.toArray ++ x.infinite.coeffs.toArray
  let nonZeroTerms := allTerms.filter (fun (_, coeff) => coeff != 0)
  if nonZeroTerms.isEmpty then
    return default  -- Return (0, 0) if all terms are zero
  dbg_trace s!"nonZeroTerms: {nonZeroTerms}"
  let sortedTerms := nonZeroTerms.qsort (fun (exp₁, _) (exp₂, _) =>  exp₁ > exp₂ )
  dbg_trace s!"sortedTerms: {sortedTerms}"
  sortedTerms.getD 0 default
#eval lc[ε].largestTerm
#eval lc[1, 2ε, 4H, -4H, 3,3ε^2].largestTerm



instance : Inv LeviCivitaNum where
  inv x := Id.run do
    if x == 0 then -- absolute infinity in this case
      return lc[(1:Float)/(0:Float)]
    else if x.isStd then -- If x is standard, just invert it
      return { std := 1 / x.std, _pf_infinitesimal_keys_negative := by rfl, _pf_infinite_keys_positive := by rfl }
    else
      let divByTerm: (Exponent × Exponent) → (Coeff×Coeff) → (Exponent × Coeff) := fun (exp₁, exp₂) (coeff₁ , coeff₂) => (exp₁ - exp₂, coeff₁ / coeff₂)
      let (largestExp, largestCoeff) := largestTerm x
      dbg_trace ('a',largestExp, largestCoeff)
      -- Now we can invert (1 + small terms)
      let poly : Polynomial' :=
        {coeffs := x.infinitesimal.coeffs.map (fun exp coeff => divByTerm (exp, largestExp) (coeff, largestCoeff))} +
        {coeffs := x.infinite.coeffs.map (fun exp coeff => divByTerm (exp, largestExp) (coeff, largestCoeff))} +
        {coeffs := #{0 - largestExp ↦ x.std/largestCoeff}}
      dbg_trace poly
      let poly' := poly.partition
      dbg_trace poly'
      -- Taylor series for 1/(1+eps) (1 - ε + ε²  - ε³ ..)
      let invFactored := LeviCivitaNum.expand poly' [1, -1, 1, -1, 1, -1, 1, -1]

      -- Multiply by 1/largestCoeff and adjust the exponent
      return invFactored

#eval lc[Float.nan]
instance: Div LeviCivitaNum where
  div x y := x * y⁻¹

-- Test the expand function
#eval LeviCivitaNum.expand lc[1ε] [1, 1, 1/2, 1/6]  -- Should approximate e^x
#eval Inv.inv lc[ε]
/-- d represents epsilon since it's easier to type.-/
def testCases : List (String × Option LeviCivitaNum) := [
  ("1+d", some lc[1ε]),
  ("1/d", some lc[-ε]),
  ("d+d", some lc[2ε]),
  ("d^2", some lc[ε^2]),
  ("sqrt d", some lc[ε^(1/2)]),
  ("2+2", some lc[4]),
  ("2d", none),
  ("1+d", some lc[1ε]),
  ("1/d", some lc[-ε]),
  ("d+d", some lc[2ε]),
  ("a=6*7;a+5", some lc[47]),
  ("zzz=1;zzz==1", some lc[1]),
  ("f x=x^2;f(f(2))", some lc[16]),
  ("sqrt(-1)", none),  -- Complex numbers not supported
  ("((1+i)/(sqrt 2))^8", none),  -- Complex numbers not supported
  ("(1+d)^pi", none),  -- Result is not a simple LeviCivita number
  ("d^pi", none),
  ("[sqrt(d+d^2)]^2", some lc[ε^(1/2) , ε^2])
]
end LeviCivitaNum

/--entry point.-/
def main : IO Unit := do
  IO.println <| System.FilePath.mk ".././"
