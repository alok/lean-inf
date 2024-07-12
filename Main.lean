import Mathlib
import Lean.Data.Parsec
import Batteries.Lean.HashMap
import Lean.Data.HashMap

import Lean.Util.Path
import Lean.Data.Rat
import LeanInf.Basic

#eval #[s!"a", s!"b", s!"c"].intercalate ", "



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

structure Polynomial' where
  coeffs : CoeffMap := default
deriving Repr, Inhabited, BEq

namespace Polynomial'

instance : Add Polynomial' where
  add p q := Id.run do
    let mut result := p.coeffs
    for (exp, coeff) in q.coeffs do
      let existingCoeff := result.findD exp 0
      result := result.insert exp (existingCoeff + coeff)
    return ⟨result⟩

instance : Neg Polynomial' where neg p := ⟨p.coeffs.mapValues (-·)⟩


#eval Polynomial'.mk #{0 ↦ 1, 1 ↦ 2} + Polynomial'.mk #{-1 ↦ 1, 1 ↦ 2}

def empty : Polynomial' := ⟨.empty⟩

-- TODO: bad idea? Any real number can be represented as a polynomial with a single term. By the way, this also uses that 0^0 is 1 (since the constant term is x^0)
instance : Coe Coeff Polynomial' where
  coe c := {coeffs := #{0 ↦ c}}

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

#eval Polynomial'.empty == (0 : Polynomial')
#eval Polynomial'.empty
#eval (0 : Polynomial')

/-- Create a `Polynomial'` from a list of tuples -/
def ofList (l : List Term) : Polynomial' := Id.run do
  let mut result := .empty
  for (coeff, exp) in l do
    let existingCoeff := result.findD exp 0
    result := result.insert exp (existingCoeff + coeff)
  return ⟨result⟩




namespace Notation

/-- Syntax category for infinitesimal or hyperreal units -/
declare_syntax_cat infUnit

/-- Syntax for representing ε (epsilon) or H as infinitesimal or hyperreal units -/
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
  | `(p[ε]) => `(Polynomial'.mk #{1 ↦ 1})
  | `(p[-ε]) => `(Polynomial'.mk #{1 ↦ -1})
  | `(p[H]) => `(Polynomial'.mk #{-1 ↦ 1})
  | `(p[-H]) => `(Polynomial'.mk #{-1 ↦ -1})
  | `(p[$coeff:term ε]) => `(Polynomial'.mk #{1 ↦ $coeff})
  | `(p[$coeff:term H]) => `(Polynomial'.mk #{-1 ↦ $coeff})
  | `(p[ε^$exp]) => `(p[1ε^$exp])
  | `(p[-ε^$exp]) => `(p[-1ε^$exp])
  | `(p[H^$exp]) => `(p[1H^$exp])
  | `(p[-H^$exp]) => `(p[-1H^$exp])
  | `(p[$coeff:term ε^$exp]) => `(Polynomial'.mk #{$exp ↦ $coeff})
  | `(p[$coeff:term H^$exp]) => `(Polynomial'.mk #{-$exp ↦ $coeff})
  | `(p[$x:polyItem, $xs,*]) => `(p[$x] + p[$xs,*])
  | `(p[$coeff:term]) => `(Polynomial'.mk #{0 ↦ $coeff})

#eval p[]
#eval p[ε]
#eval p[-ε]
#eval p[H]
#eval p[-H]
#eval p[-3H^3]
#eval p[(-ε)^3]
#eval p[1ε]
#eval p[1ε, 3H]
#eval Id.run do
  let x := 2
  (p[x ε], p[x ε^2])
#eval  p[1, 2 ε, 3ε^2]

end Notation
end Polynomial'


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
        | 1 => s!"{coeff}ε"
        | -1 => s!"{coeff}H"
        | n => Id.run do
          let unit := if n > 0 then "ε" else "H"
          let exp := Format.toSuperscript (toString (if exp > 0 then exp else -exp))
          s!"{coeff}{unit}{exp}"
    let nonZeroTerms := terms.filter (· ≠ "0")  -- Remove "0" terms
    return if nonZeroTerms.isEmpty then "0" else nonZeroTerms.intercalate " + "

end Format

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

#eval Format.toSuperscript s!"{-1}"
#eval toString (Polynomial'.mk #{2 ↦ 1, -1 ↦ 3, 0 ↦ 1})  -- Should output
#eval toString (Polynomial'.mk #{1 ↦ 1, 2 ↦ 4, 2 ↦ 5, 3 ↦ 1, 4 ↦ 1, 5 ↦ 1, 6 ↦ 1, 7 ↦ 1, 8 ↦ 1, 9 ↦ 1, 0 ↦ 1})  -- Should output: "x + x² + x³ + x⁴ + x⁵ + x⁶ + x⁷ + x⁸ + x⁹ + ¹"

-- TODO use polynomial repr instead of raw hashmaps

structure LeviCivitaNum where -- extends Field
  /-- the standard part of the Levi-Civita number -/
  std : Coeff := 0
  /-- the infinitely big (more properly, unlimited) part of the number -/
  infinite : Polynomial' := .empty
  /-- the infinitesimal part of the number -/
  infinitesimal : Polynomial' := .empty
deriving Inhabited,BEq

instance : Repr LeviCivitaNum where
  reprPrec x _ := Id.run do
    let parts := #[
      if x.infinite != .empty then toString x.infinite else "",
      if x.std != 0 then toString x.std else "",
      if x.infinitesimal != .empty then toString x.infinitesimal else ""
    ]
    let nonEmptyParts := parts.filter (fun a => !a.isEmpty && a != "0")
    return if nonEmptyParts.isEmpty then "0" else nonEmptyParts.intercalate " + "

-- TODO this should be doable with default deriving handler for `Add`.
instance : Add LeviCivitaNum where
  add x y := {std := x.std + y.std, infinite := x.infinite + y.infinite, infinitesimal := x.infinitesimal + y.infinitesimal}

instance : Coe Coeff LeviCivitaNum where
  coe c := {std := c}

instance : OfNat LeviCivitaNum n where
  ofNat := match n with
    | 0 =>  {std := 0}
    | 1 => {std := 1}
    | _ => {std := n.toFloat}

def LeviCivitaNum.zero : LeviCivitaNum := 0
instance : Zero LeviCivitaNum where zero := 0
#eval (0 : LeviCivitaNum)

def LeviCivitaNum.one : LeviCivitaNum := 1
instance : One LeviCivitaNum where one := 1

def LeviCivitaNum.ε : LeviCivitaNum :=  {infinitesimal := ⟨#{1 ↦ 1}⟩}
/-- `H` is a hyperfinite number, synonyms are "infinitely big number" and "unlimited number".-/
def LeviCivitaNum.H : LeviCivitaNum := {infinite := ⟨#{-1 ↦ 1}⟩}
#eval (.ε : LeviCivitaNum)

instance : Coe Term LeviCivitaNum where
  coe term := Id.run do
    let (coeff, exp) := term
    let mut out : LeviCivitaNum := default
    return match cmp exp 0 with
      | .eq => ↑coeff
      | .gt => {out with infinite := ⟨#{exp ↦ coeff}⟩}
      | .lt => {out with infinitesimal := ⟨#{exp ↦ coeff}⟩}

/-- Create a `LeviCivitaNum` from a list of tuples representing the coefficients and exponents of the polynomial -/
def LeviCivitaNum.ofList (l : List Term) : LeviCivitaNum := l.foldr (fun t acc => acc + t) 0
/-- Create a `LeviCivitaNum` from an array of tuples representing the coefficients and exponents of the polynomial -/
def LeviCivitaNum.ofArray (l : Array (Coeff × Exponent)) : LeviCivitaNum := l.foldr (fun t acc => acc + (↑t)) 0
        -- TODO debug why this was broken (poly addition)
      -- infinitesimal := infinitesimal + Polynomial'.mk #{exp ↦ existingCoeff + coeff}

#eval LeviCivitaNum.ofList [(1, 1)]

-- Similar syntax for LeviCivita numbers
syntax "lc[" polyItem,* "]" : term

/--Semantics for creating LeviCivitaNum from a list of terms like `lc[ε, H, ε^2, H^2]`, which equals `ε + H + ε^2 + H^2`-/
macro_rules
  | `(lc[]) => `(LeviCivitaNum.zero)
  | `(lc[ε]) => `(LeviCivitaNum.ε)
  | `(lc[-ε]) => `({ infinitesimal := ⟨#{1 ↦ -1}⟩ : LeviCivitaNum})
  | `(lc[H]) => `(LeviCivitaNum.H)
  | `(lc[-H]) => `({ infinite := ⟨#{-1 ↦ -1}⟩ : LeviCivitaNum})
  | `(lc[$coeff:term ε]) => `({ infinitesimal := ⟨#{1 ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[$coeff:term H]) => `({ infinite := ⟨#{-1 ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[ε^$exp]) => `(lc[1ε^$exp])
  | `(lc[-ε^$exp]) => `(lc[-1ε^$exp])
  | `(lc[H^$exp]) => `(lc[1H^$exp])
  | `(lc[-H^$exp]) => `(lc[-1H^$exp])
  | `(lc[$coeff:term ε^$exp]) => `({ infinitesimal := ⟨#{$exp ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[$coeff:term H^$exp]) => `({ infinite := ⟨#{-$exp ↦ $coeff}⟩ : LeviCivitaNum})
  | `(lc[$x:polyItem, $xs,*]) => `(lc[$x] + lc[$xs,*])
  | `(lc[$coeff:term]) => `({ std := $coeff : LeviCivitaNum})

#eval lc[]
#eval lc[1ε]
#eval lc[3ε]
#eval lc[ε]
#eval lc[ε^2]
#eval lc[ε^2 , H^2]
#eval lc[1ε , 2H]

instance : Neg LeviCivitaNum where
  neg x := {std := -x.std, infinite := -x.infinite, infinitesimal := -x.infinitesimal}

-- Example usage and test
#eval toString <| p[2ε, 3ε^2] * p[1ε, 3ε^2]

-- 2e + 3e^3 * 1ε + 4ε^3
local instance [BEq k][Hashable k] : Append (Lean.HashMap k v) where
  append x y := Id.run do
    let mut result := x
    for (k, v) in y do
      result := result.insert k v
    return result

#eval #{ 1↦ 1, 2↦ 2} ++ #{1↦ 2, 2↦ 3}

private def Polynomial'.partition (poly: Polynomial') : LeviCivitaNum := Id.run do
  let mut (std, infinite, infinitesimal) := (0, p[], p[])
  for (exp, coeff) in poly.coeffs do
    if exp == 0 then
      std := std + coeff
    else if exp < 0 then
      infinite := infinite + p[coeff H^(-exp)]
    else
      infinitesimal := infinitesimal + p[coeff ε^exp]
  return {std := std, infinite := infinite, infinitesimal := infinitesimal}

instance : ToString LeviCivitaNum where
  toString x := Id.run do
    let mut terms := #[]
    -- Add infinite terms
    let infiniteTerms := Format.sortTerms (x.infinite.coeffs.toArray)
      |>.map fun (exp, coeff) =>
        if coeff == 0 then
          ""
        else
        match exp with
        | -1 => s!"{coeff}H"
        | 0 => s!"{coeff}"
        | 1 => s!"{coeff}H⁻¹"
        | _ =>
          let unit := "H"
          let exp := Format.toSuperscript (toString (-exp))
          s!"{coeff}{unit}{exp}"
    terms := terms.append infiniteTerms
    -- Add standard part if non-zero
    if x.std != 0 then
      terms := terms.push s!"{x.std}"
    -- Add infinitesimal terms
    let infinitesimalTerms := Format.sortTerms (x.infinitesimal.coeffs.toArray)
      |>.map fun (exp, coeff) =>
        if coeff == 0 then
          ""
        else
        match exp with
        | 0 => s!"{coeff}"
        | 1 => s!"{coeff}ε"
        | _ =>
          let unit := "ε"
          let exp := Format.toSuperscript (toString exp)
          s!"{coeff}{unit}{exp}"
    terms := terms.append infinitesimalTerms
    let nonEmptyParts := terms.filter (· != "")
    -- Combine all terms
    let result := nonEmptyParts.intercalate " + "
    return if result.isEmpty then "0" else result

-- parenthesization is fucked
#eval toString <| p[1, 2ε, 4H, 4H, 3,3ε^2].partition

instance : Mul LeviCivitaNum where
  mul x y :=
    /- Merge all coefficients into a single Polynomial' and use underlying polynomial multiplication, then split again.
    -/
    let x' := p[x.std] + x.infinite + x.infinitesimal
    let y' := p[y.std] + y.infinite + y.infinitesimal
    -- Multiply the polynomials
    let result := (x' * y')
    result.partition

#eval  lc[ε]*lc[H,ε,H^2]
#eval lc[-ε, ε, H] * lc[-ε,  ε, H]
#eval lc[-ε^2,2ε^3] * lc[ε, 3H]
#eval lc[ε^2, 3ε^4] * lc[ε, 3H]
#eval 0 - p[5H]

#eval 2.0>3.4
#synth LE Coeff

instance : LT LeviCivitaNum where
  lt x y :=
    let diff := x - y
    diff.std < 0 || (diff.std == 0 && diff.infinite.coeffs.any (fun  coeff exp => coeff < 0)) || (diff.std == 0 && diff.infinite.coeffs.isEmpty && diff.infinitesimal.coeffs.any (fun coeff exp => coeff < 0))

#eval (1:LeviCivitaNum) < (2:LeviCivitaNum)

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
    let term := (lc[coeff]) * pow
    s := s + term
    pow := pow * x
  return s

-- Test the expand function
#eval LeviCivitaNum.expand lc[1ε] [1, 1, 1/2, 1/6]  -- Should approximate e^x

-- instance : Inv LeviCivitaNum where


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

def main : IO Unit := do
  IO.println <| (System.FilePath.mk ".././")

#eval main
#eval main
