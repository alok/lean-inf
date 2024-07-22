import Mathlib
import Lean.Data.Parsec
import Batteries.Lean.HashMap
import Lean.Data.HashMap

import Lean.Util.Path
import Lean.Data.Rat
import LeanInf.Basic

def _root_.Array.maxBy? [Ord b] [Max b] [LT b] [DecidableRel (@LT.lt b _)] (xs : Array a) (f : a → b) : Option a :=
  xs.foldr (init:= none) fun x acc =>
    match acc with
    | none => some x
    | some v =>
      match compare (f x) (f v) with
      | .lt => acc
      | .eq|.gt  => some x  -- Keep the last element in case of equality


#eval #[1,2,3].maxBy? (fun x => x)

/-- Subtraction via addition and negation -/
local instance [Neg a] [Add a] : Sub a where
  sub x y := x + (-y)
/- Division via multiplication and inversion -/
local instance [Inv a] [Mul a]: Div a where
  div x y := x * y⁻¹
/- Inversion via dividing 1  -/
local instance [Div a] [One a]: Inv a where
  inv x := 1 / x

/-- Exponentiation via squaring. -/
local instance [Mul a][One a]: HPow a ℕ a where
  hPow x n := Id.run do
    let mut (result, base, exp) := (1, x, n)
    while exp > 0 do
      if exp % 2 == 1 then
        result := result * base
      base := base * base
      exp := exp / 2
    result

@[inherit_doc Rat]
abbrev Exponent := Rat

@[inherit_doc Rat]
abbrev Coeff := Rat

-- @[inherit_doc Float]
-- abbrev Coeff := Float

/-- A term in a polynomial. Given as `(Coeff, Exponent)`. -/

structure Term where
  coeff: Coeff
  exp: Exponent
deriving BEq, Inhabited

/-- A map from exponents to coefficients -/
abbrev CoeffMap := Lean.HashMap Exponent Coeff  -- TODO use RbMap instead bc sorted?

/-- A polynomial, represented as a `HashMap` from exponents to coefficients -/
structure Polynomial' where
  coeffs : CoeffMap := default
deriving Repr, Inhabited

def CoeffMap.toTerms (m : CoeffMap) : Array Term := Id.run do
  let mut terms := Array.mkEmpty m.size
  for (exp, coeff) in m do
    terms := terms.push {coeff, exp}
  return terms

def Polynomial'.toTerms (p : Polynomial') : Array Term := p.coeffs.toTerms
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

private def sortTerms (terms : Array Term) : Array Term :=
  terms.qsort (fun {exp:=exp₁,coeff:=coeff₁} {exp:=exp₂,coeff:=coeff₂} =>
    if exp₁ < 0 && exp₂ < 0 then
      if exp₁ ≠ exp₂ then exp₁ > exp₂ else abs coeff₁> abs coeff₂
    else if exp₁ < 0 then true
    else if exp₂ < 0 then false
    else
      if exp₁ ≠ exp₂ then exp₁ < exp₂ else abs coeff₁ < abs coeff₂)

instance : ToString Polynomial' where
  toString p := Id.run do
    let terms := p.toTerms
      |> sortTerms
      |>.filter (fun {coeff, ..} => coeff != 0)  -- Filter out zero terms
      |>.map fun {exp, coeff} =>
        match exp with
        | 0 => s!"{coeff}"
        | 1 => s!"{coeff}H"
        | -1 => s!"{coeff}ε"
        | exp =>
            let unit := if exp > 0 then "H" else "ε"
            let exp := Format.toSuperscript (toString (if exp > 0 then exp else -exp))
            s!"{coeff}{unit}{exp}"
    let nonZeroTerms := terms.filter (· ≠ "0")  -- Remove "0" terms
    return if nonZeroTerms.isEmpty then "0" else nonZeroTerms.intersperse " + "

#eval Format.toSuperscript s!"{-1}"

instance : Repr Term where
  reprPrec t _ :=
    let unit := match compare t.exp 0 with
      | .gt => "H"
      | .lt => "ε"
      | _ => ""
    let exp := Format.toSuperscript (toString (if t.exp > 0 then t.exp else -t.exp))
    s!"{t.coeff}{unit}{exp}"
end Format

instance : ToString Term where
  toString t := s!"{repr t}"

#eval (1:Nat) - (2:Nat)
#eval Float.sqrt (2/3:Float)

namespace Polynomial'

/-- Two polynomials are equal iff their coefficients are equal. -/
instance : BEq Polynomial' where
  beq p q :=
    -- remove zeros so empty polynomials are handled
    let p' := p.coeffs.filter (fun _ v => v != 0)
    let q' := q.coeffs.filter (fun _ v => v != 0)
    p' == q'

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
#eval ((2:Coeff) : Polynomial')+((2:Coeff) : Polynomial')
/-- Create a `Polynomial'` from a natural 'iiiinttcsdgh'ber -/
instance : OfNat Polynomial' n where ofNat := match n with
  | 0 => .empty
  | 1 => ⟨#{0 ↦ 1}⟩
  | _ => ⟨#{0 ↦ (n:Coeff)}⟩
#eval ((2 : Polynomial')+(2 : Polynomial'))
/-- For decimal and scientific numbers (e.g., `1.23`, `3.12e10`).

    Examples:
    - `OfScientific.ofScientific 123 true 2`    represents `1.23`
    - `OfScientific.ofScientific 121 false 100` represents `121e100`
-/
instance : OfScientific Polynomial' where
  ofScientific mantissa exponentSign decimalExponent := ⟨#{0 ↦ .ofScientific mantissa exponentSign decimalExponent}⟩
#eval (0.2341423190:Rat)
#eval Polynomial'.empty == (⟨#{0.0 ↦ 0}⟩ : Polynomial')

/--Compute the sign of a term (-1, 0, 1). -/
def signum (x: Term) : Int :=
  if x.coeff > 0 then 1 else if x.coeff < 0 then -1 else 0


#eval Polynomial'.empty
#eval (1 : Polynomial') == (⟨#{0 ↦ 1}⟩ : Polynomial')

/-- Create a `Polynomial'` from a list of tuples -/
def ofList (l : List Term) : Polynomial' := Id.run do
  let mut result := .empty
  for term in l do
    let existingCoeff := result.findD term.exp 0
    result := result.insert term.exp (existingCoeff + term.coeff)
  return ⟨result⟩



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

instance : Mul Polynomial' where
  mul p q := Id.run do
    let mut result := Polynomial'.empty
    for (expP, coeffP) in p.coeffs do
      for (expQ, coeffQ) in q.coeffs do
        let term := ⟨#{expP + expQ ↦ coeffP * coeffQ}⟩
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
  _pf_infinitesimal_keys_negative : infinitesimal.coeffs.all (fun exp _ => exp < 0) := by (first | rfl | sorry)
  /-- To ensure coeffs are in terms of `H`. -/
  _pf_infinite_keys_positive : infinite.coeffs.all (fun exp _ => exp > 0) := by (first | rfl | sorry)
deriving Repr


def LeviCivitaNum.toPoly (x: LeviCivitaNum) : Polynomial' := Id.run do
  -- concat underlying hashmaps
  let mut out := x.infinite.coeffs
  out := out.mergeWith (fun  _ v_self v_other => v_self + v_other) x.infinitesimal.coeffs
  out := out.insert 0 x.std
  return ⟨out⟩


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
  coe c := {std := c}



instance : OfNat LeviCivitaNum n where
  ofNat := match n with
    | 0 => zero
    | 1  => one
    | _ => {std := (n:Coeff)}

instance : OfScientific LeviCivitaNum where
  ofScientific mantissa exponentSign decimalExponent := {
    std := .ofScientific mantissa exponentSign decimalExponent
  }

#eval (0 : LeviCivitaNum)

#eval
  let a:= 2
  #{2↦1}.all (fun k _ => k > 0)


instance : CoeDep Term t LeviCivitaNum where
  coe := match t.coeff, compare t.exp 0 with
  | _, Ordering.gt => {infinite := ⟨ #{t.exp ↦ t.coeff}⟩:LeviCivitaNum}
  | _, Ordering.eq => {std := t.coeff}
  | _, Ordering.lt => {infinitesimal := ⟨#{-t.exp ↦ t.coeff}⟩}

/-- Create a `LeviCivitaNum` from a list of tuples representing the coefficients and exponents of the polynomial -/
def ofArray (l : Array Term) : LeviCivitaNum := Id.run do
  let mut (std, infinitesimal, infinite) := (0, .empty, .empty)
  for term in l do
    if term.exp == 0 then
      std := std + term.coeff
    else if term.exp > 0 then
      let existingCoeff := infinite.coeffs.findD term.exp 0
      infinite := ⟨infinite.coeffs.insert term.exp (existingCoeff + term.coeff)⟩
    else
      let existingCoeff := infinitesimal.coeffs.findD term.exp 0
      infinitesimal := ⟨infinitesimal.coeffs.insert term.exp (existingCoeff + term.coeff)⟩
  return {std, infinitesimal, infinite}


#eval LeviCivitaNum.ofArray #[⟨1, 1⟩]

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
  | `(lc[$coeff:term]) => `({ std := $coeff : LeviCivitaNum})

#eval lc[]
#eval lc[1ε]
#eval lc[3ε]
#eval lc[ε]
#eval lc[-ε]
#eval lc[-H]
#eval lc[ε^2]
#eval lc[ε^2, H^2]
#eval lc[1ε, 2H]

open Format in
instance : ToString LeviCivitaNum where
  toString x := Id.run do
    let mut terms := #[]
    -- Add infinite terms
    let infiniteTerms := sortTerms (x.infinite.toTerms)
      |>.map fun {exp, coeff} =>
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
    let infinitesimalTerms := sortTerms (x.infinitesimal.toTerms)
      |>.map fun {exp, coeff} =>
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

/-- Convert a polynomial to a `LeviCivitaNum` -/
def _root_.Polynomial'.toLC (xs:Polynomial') : LeviCivitaNum := Id.run do
  let mut (std, infinitesimal, infinite) := (0, .empty, .empty)
  for {exp, coeff} in xs.toTerms do
    if exp == 0 then
      std := std + coeff
    else if exp > 0 then
      infinite := ⟨infinite.coeffs.insert exp (coeff)⟩
    else
      infinitesimal := ⟨infinitesimal.coeffs.insert exp (coeff)⟩
  return {std, infinitesimal, infinite}
-- parenthesization is fucked
#eval toString <| p[1, 2ε, 4H, 4H, 3,3ε^2].toLC

instance : Mul LeviCivitaNum where
  mul x y :=
    -- split into big polynomial independent of grade, then multiply it. TODO make faster
    let x' := p[x.std] + x.infinite + x.infinitesimal
    let y' := p[y.std] + y.infinite + y.infinitesimal
    (x' * y').toLC



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

#eval  lc[ε]*lc[H,ε,H^2]
#eval lc[-ε, ε, H] * lc[-ε,  ε, H]
#eval lc[-ε^2,2ε^3] * lc[ε, 3H]
#eval lc[ε^2, 3ε^4] * lc[ε, 3H]
#eval 0 - p[5H]

#eval 2.0 > 3.4
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
instance : LE LeviCivitaNum where
  le x y := (x - y).signum == (-1:Int)

instance LT : LT LeviCivitaNum where
  lt x y  := (x-y).signum = -1

instance : DecidableRel (@LT.lt LeviCivitaNum _) :=
  fun x y =>
    if h : ((x - y).signum = -1) then
      isTrue h
    else
      isFalse (decide (h))

-- class inductive Decidable (p : Prop) where
--   /-- Prove that `p` is decidable by supplying a proof of `¬p` -/
--   | isFalse (h : Not p) : Decidable p
--   /-- Prove that `p` is decidable by supplying a proof of `p` -/
--   | isTrue (h : p) : Decidable p

#eval abs (1:Coeff)

#eval ((1:LeviCivitaNum) - (2:LeviCivitaNum)).signum
-- #synth (@LT.lt Float Float) (1.0)<(3.2)
#eval lc[1] < lc[2]
#eval lc[ε] < lc[2ε]
#eval lc[H] < lc[2H]
#eval lc[-H] < lc[-H]

#eval (lc[ε] - lc[2ε]).signum
#eval (lc[H] - lc[2H]).signum
#eval (lc[-H] - lc[H]).signum


def abs (x : LeviCivitaNum) : LeviCivitaNum :=
  let _abs : Coeff → Coeff := fun coeff => if coeff < 0 then -coeff else coeff
  {
    std := if x.std < 0 then -x.std else x.std
    infinitesimal := ⟨x.infinitesimal.coeffs.map (fun exp coeff => (exp, _abs coeff))⟩
    infinite := ⟨x.infinite.coeffs.map (fun exp coeff => (exp, _abs coeff))⟩
  }

#eval abs lc[-ε]
#eval abs lc[-H,2,-4]

/-- Expand a LeviCivitaNum using the series expansion for 1/(1+x) = 1 - x + x^2 - x^3 + ...
    This implementation uses the formula: 1/(1+ε) = Σ (-ε)^k for k=0 to n-1.
    x *must* be normalized
     -/
def expandInverse (x : LeviCivitaNum) (n : ℕ := 8) (_ok : x.infinite = 0 ∧ x.std = 1 := by sorry) : LeviCivitaNum := Id.run do
  let mut (result, εₓ) := (0, x - 1) -- since infinite part is empty, this should work
  -- dbg_trace s!"x: {x}, εₓ: {εₓ}"
  for k in [0:n] do
    let term := (-εₓ)^k
    -- dbg_trace s!"term: {term}"
    result := result + term
  return result

#eval expandInverse lc[1, -5ε] 8 sorry -- Should be approximately 1 - ε + ε^2 - ε^3
#eval expandInverse lc[0.1] 1  sorry -- Should be approximately 0.9090909090909091

/-- Expand a LeviCivitaNum using the binomial series (1+x)^a = 1 + ax + a(a-1)x^2/2! + ...
    This implementation uses the formula: (1+ε)^a = Σ (a choose k) ε^k for k=0 to n-1 -/
def expandPower (x : LeviCivitaNum) (a : Coeff) (n : Nat) : LeviCivitaNum := Id.run do
  let mut result : LeviCivitaNum := 0
  let mut term : LeviCivitaNum := 1
  let mut coeff : Coeff := 1
  for k in [0:n] do
    result := result + coeff * term
    term := term * x
    coeff := coeff * (a - k) / (k + 1)
  return result

#eval expandPower lc[0.1, ε] 2 3  -- Should be approximately 1 + 2ε + ε^2
#eval expandPower lc[0.1] 7 7  -- Should be approximately 1.21




def expand (x : LeviCivitaNum) (n : Nat) : LeviCivitaNum := Id.run do
  let mut (total , pow, sign) := (0, 1, 1)
  -- dbg_trace s!"x: {x}"
  for _ in [0:n] do
    let term := sign * pow
    total := total + term
    pow := pow * x
    sign := -sign
  return total
#eval expand lc[ε] 3
#eval lc[ε]
/-- Truncate a Levi-Civita number to a certain grade. Negative will clip infinitesimals, positive will clip unlimited terms too.-/
def truncate (x: LeviCivitaNum) (n: Int) : LeviCivitaNum :=
  {
    std := if n <= 0 then x.std else 0
    infinitesimal := ⟨x.infinitesimal.coeffs.filter (fun exp _ => exp <= n)⟩
    infinite := ⟨x.infinite.coeffs.filter (fun exp _ => exp <= n)⟩
  }


def CoeffMap.toTerms (cm: CoeffMap) : Array Term :=
  cm.toArray.map fun (exp, coeff) => { exp := exp, coeff := coeff }

def largestTerm (x: LeviCivitaNum) : Term := Id.run do
  let allTerms := #[{coeff := x.std, exp := 0}] ++ x.infinitesimal.toTerms ++ x.infinite.toTerms
  let nonZeroTerms := allTerms.filter (fun term => term.coeff != 0)
  if nonZeroTerms.isEmpty then
    return {coeff := 0, exp := 0}  -- Return (0, 0) if all terms are zero
  -- dbg_trace s!"nonZeroTerms: {nonZeroTerms}"
  let sortedTerms := nonZeroTerms.qsort (fun term₁ term₂ =>  term₁.exp > term₂.exp )
  -- dbg_trace s!"sortedTerms: {sortedTerms}"
  sortedTerms.getD 0 {coeff := 0, exp := 0}

/-- Check if a Levi-Civita number is pure. -/
def isPure (x: LeviCivitaNum) : Bool :=
  let pureStd := x.infinitesimal.coeffs.isEmpty && x.infinite.coeffs.isEmpty -- can be 0
  let pureInfinitesimal := x.std == 0 && (x.infinitesimal.coeffs.size = 1) && x.infinite.coeffs.isEmpty
  let pureInfinite := x.std == 0 && x.infinitesimal.coeffs.isEmpty && (x.infinite.coeffs.size = 1)

  pureStd || pureInfinitesimal || pureInfinite

def purePart (x: LeviCivitaNum) (h : isPure x = true ) : Term :=
  -- if pure std, return ()
  if x.infinitesimal.coeffs.isEmpty && x.infinite.coeffs.isEmpty then
    {coeff := x.std, exp := 0}
  -- if pure infinitesimal, return (infinitesimal[0], 0)
  else if x.std == 0 && x.infinite.coeffs.isEmpty && x.infinitesimal.coeffs.size = 1 then
    x.infinitesimal.toTerms[0]!
  -- if pure infinite, return (infinite[0], 0)
  else if x.std == 0 && x.infinitesimal.coeffs.isEmpty && x.infinite.coeffs.size = 1 then
    x.infinite.toTerms[0]!
  else
    {coeff := 0, exp := 0}

#eval lc[H,-H].purePart sorry


instance : Div Term where
  div x y := {exp := x.exp - y.exp, coeff := x.coeff / y.coeff}

/-- Embeds a natural number into a term by `n * H^0 = n` -/
instance : OfNat Term n where
  ofNat := {exp := 0, coeff := n}

/-- Inverts a term by appealing to division. -/
instance : Inv Term where
  inv x := (1:Term) / x

#eval (1:Term)/{exp := -1, coeff := 1} -- 1/ε

-- instance : HMul Term LeviCivitaNum LeviCivitaNum where
--   hMul t l := t * l



instance : Inv LeviCivitaNum where
  inv x := Id.run do
    if _h: isPure x then
      -- dbg_trace s!"x: {x} isPure"
      if x == 0 then
        -- dbg_trace s!"x: {x} is 0, inverse is inf"
        return lc[1/0] -- TODO this returns 0 which is wrong
      let {coeff, exp} := purePart x _h
      -- dbg_trace s!"Pure: coeff: {coeff}, exp: {exp}"
      return lc[coeff⁻¹ H^(-exp)]
    else
      let largestTerm := largestTerm x
      -- dbg_trace s!"LargestTerm: {largestTerm}"
      -- of the form largestTerm * (1 + εₓ (infinitesimals))
      let restof := x.toPoly.toTerms.map (fun t =>  t / largestTerm) |> LeviCivitaNum.ofArray
      -- dbg_trace s!"restOfFactoredTerms: {restof}"

      -- -- Now we can invert (1 + small terms) with Taylor series for 1/(1+eps)
      -- let restof.inverse :=
      -- dbg_trace s!"restof.inverse: {restof.inverse}"
      -- -- Multiply by 1/largestCoeff and adjust the exponent
      return (↑(Inv.inv largestTerm: Term)) * restof.expandInverse

-- Remove or comment out problematic evaluations
#eval lc[ε].largestTerm
#eval lc[1, 2ε, 4H, -4H, 3,3ε^2].largestTerm
-- #eval Inv.inv lc[]
-- #eval LeviCivitaNum.expand lc[1ε] [1, 1, 1/2, 1/6]


#eval Inv.inv lc[]

#eval lc[nan]
#eval Inv.inv lc[H]
#eval Inv.inv lc[1,ε]
instance: Div LeviCivitaNum where
  div x y := x * y⁻¹

-- Test the expand function
#eval LeviCivitaNum.expand lc[1ε] [1, 1, 1/2, 1/6].length  -- Should approximate e^x
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

/-- Entry point.-/
def main : IO Unit := do
  IO.println <| "Check out the calculator"
  -- TODO add printing

#eval  (p[1ε, 2ε^2, 3ε^3])
#eval lc[1,H,-1,-1]
#eval (lc[H,ε, 2ε^2, 3ε^3] : LeviCivitaNum).toPoly


-- Test cases based on the image
-- We'll use the given approximations and verify they square to the original value
-- and that their inverses are close to what's given in the image

-- Test case for √(1 + ε)
#eval let approx := lc[1, 0.5 ε, -0.125 ε^2, 0.0625 ε^3, -0.0390625 ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 + ε, 1 - 0.5ε + 0.375ε^2 - 0.3125ε^3)

-- Test case for √(1 - 0.5ε)
#eval let approx := lc[1, -0.25 ε, -0.03125 ε^2, -0.015625 ε^3, -0.009765625 ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 - 0.5ε, 1 + 0.25ε + 0.1875ε^2 + 0.15625ε^3)

-- Test case for √(1 + ε + ε^2)
#eval let approx := lc[1, 0.5 ε, 0.125 ε^2, 0.0625 ε^3, 0.0390625 ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 + ε + ε^2, 1 - 0.5 ε + 0.125 ε^2 + 0.0625 ε^3)

-- Test case for √(1 - 0.5ε + 0.375ε^2 - 0.3125ε^3)
#eval let approx := lc[1, -0.25ε, -0.03125ε^2, -0.015625ε^3, -0.009765625ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (1 - 0.5ε + 0.375ε^2 - 0.3125ε^3, 1 + 0.25ε + 0.1875ε^2 + 0.15625ε^3)

-- Test case for √(2 - 0.2813ε^3)
#eval let approx := lc[1.4142135623730950488, -0.0078125ε^3]  -- √2 - 0.0078125ε^3
      let squared := approx * approx
      dbg_trace s!"squared: {squared}"
      let inverse := 1 / approx
      (squared * inverse)
-- Should be close to (2 - 0.2813ε^3, 1/√2 + 0.00276ε^3)

-- Additional test case for √(2 + ε)
#eval let approx := lc[1.4142135623730950488, 0.3535533905932737622ε, -0.0441941738241592203ε^2, 0.0220970869120796101ε^3, -0.0138106793200497563ε^4]
      let squared := approx * approx
      let inverse := 1 / approx
      (squared, inverse)
-- Should be close to (2 + ε, 1/√2 - ε/(4√2) + 3ε^2/(32√2) - 5ε^3/(128√2))
