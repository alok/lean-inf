import LeanInf.Basic
import Init.Data.Rat
import LeanInf.CoeffLike
import LeanInf.PolyGeneric

open LeanInf

/-- Rational exponent alias for `LeviCivitaNum`. -/
abbrev Exponent := LeanInf.ExpG

/-- Exact rational coefficient alias for `LeviCivitaNum`. -/
abbrev Coeff := Rat

/-- A single term with rational exponent and rational coefficient. -/
abbrev Term := LeanInf.TermG Rat

/-- HashMap from rational exponents to rational coefficients. -/
abbrev CoeffMap := LeanInf.CoeffMapG Rat

/-- Rational polynomial backed by `Std.HashMap` (namespaced to avoid colliding with Mathlib's `Polynomial`). -/
abbrev LeanInf.Polynomial := LeanInf.PolynomialG Rat

/-- Scientific literal support for `Rat` coefficients (local to avoid typeclass diamonds with Mathlib's `ℚ`). -/
local instance : OfScientific Coeff where
  ofScientific mantissa exponentSign decimalExponent :=
    let p10 := Nat.pow 10 decimalExponent
    if exponentSign then
      mkRat (num := (Int.ofNat mantissa)) (den := p10)
    else
      mkRat (num := (Int.ofNat (mantissa * p10))) (den := 1)

local instance : Inv Coeff where
  inv := Rat.inv

namespace Format

/-- Convert ASCII digits and signs to Unicode superscripts. -/
def toSuperscript (s : String) : String :=
  PolynomialG.toSuperscript s

/-- Order terms by their exponent. -/
instance : LT Term where
  lt a b := a.exp < b.exp

instance : LE Term where
  le x y := x.exp ≤ y.exp

instance : Repr Term where
  reprPrec t _ :=
    if t.exp == 0 then s!"{t.coeff}"
    else s!"{t.coeff}{PolynomialG.fmtUnitExp t.exp}"

end Format

instance : ToString Term where
  toString t := s!"{repr t}"

namespace LeanInf.Poly

/-- Compute the sign of a term (-1, 0, or 1). -/
def signum (x : Term) : Int :=
  if x.coeff > 0 then 1 else if x.coeff < 0 then -1 else 0

/-- Create a polynomial from a list of terms, summing duplicate exponents. -/
def ofList (l : List Term) : Polynomial := Id.run do
  let mut result : CoeffMap := Std.HashMap.emptyWithCapacity
  for term in l do
    let existingCoeff := result.getD term.exp 0
    result := result.insert term.exp (existingCoeff + term.coeff)
  return PolynomialG.normalize { coeffs := result }

namespace Notation

/-- Syntax category for infinitesimal or infinite units (`ε` or `H`). -/
declare_syntax_cat infUnit

/-- Infinitesimal unit `ε = H⁻¹`. -/
syntax "ε" : infUnit

/-- Infinite hypernatural unit `H = ε⁻¹`. -/
syntax "H" : infUnit

/-- Syntax category for polynomial items inside `p[...]` and `lc[...]`. -/
declare_syntax_cat polyItem

/-- Standalone unit item (`ε`, `H`). -/
syntax infUnit : polyItem

/-- Negated unit item (`-ε`, `-H`). -/
syntax "-" infUnit : polyItem

/-- Scaled unit item (`2ε`, `3H`). -/
syntax term infUnit : polyItem

/-- Unit power item (`ε^2`, `H^3`). -/
syntax infUnit "^" term : polyItem

/-- Negated unit power item (`-ε^2`, `-H^3`). -/
syntax "-" infUnit "^" term : polyItem

/-- Scalar constant item (`1`, `2.5`). -/
syntax term : polyItem

/-- Scaled unit power item (`2ε^3`, `3H^2`). -/
syntax term infUnit "^" term : polyItem

/-- Polynomial literal notation `p[1, 2ε, 3H]`. -/
syntax "p[" polyItem,* "]" : term

/-- Semantics for polynomial literal notation. -/
macro_rules
  | `(p[]) => `(( { coeffs := (Std.HashMap.emptyWithCapacity : CoeffMap) } : Polynomial))
  | `(p[ε]) => `(( { coeffs := Std.HashMap.singleton (-1) (1 : Coeff) } : Polynomial))
  | `(p[-ε]) => `(( { coeffs := Std.HashMap.singleton (-1) ((-1) : Coeff) } : Polynomial))
  | `(p[H]) => `(( { coeffs := Std.HashMap.singleton (1 : Exponent) (1 : Coeff) } : Polynomial))
  | `(p[-H]) => `(( { coeffs := Std.HashMap.singleton (1 : Exponent) ((-1) : Coeff) } : Polynomial))
  | `(p[$coeff:term ε]) => `(( { coeffs := Std.HashMap.singleton (-1) ($coeff : Coeff) } : Polynomial))
  | `(p[$coeff:term H]) => `(( { coeffs := Std.HashMap.singleton (1 : Exponent) ($coeff : Coeff) } : Polynomial))
  | `(p[ε^$exp]) => `(p[1ε^$exp])
  | `(p[-ε^$exp]) => `(p[-1ε^$exp])
  | `(p[H^$exp]) => `(p[1H^$exp])
  | `(p[-H^$exp]) => `(p[-1H^$exp])
  | `(p[$coeff:term ε^$exp]) => `(( { coeffs := Std.HashMap.singleton (-(($exp : Exponent))) ($coeff : Coeff) } : Polynomial))
  | `(p[$coeff:term H^$exp]) => `(( { coeffs := Std.HashMap.singleton (($exp : Exponent)) ($coeff : Coeff) } : Polynomial))
  | `(p[$x:polyItem, $xs,*]) => `(p[$x] + p[$xs,*])
  | `(p[$coeff:term]) => `(( { coeffs := Std.HashMap.singleton (0 : Exponent) ($coeff : Coeff) } : Polynomial))

end Notation
end LeanInf.Poly

/-- Original HashMap-based Levi-Civita number, split into standard, infinitesimal, and infinite parts.
    Preserved as the reference baseline against which `SortedLC` is verified and benchmarked. -/
structure LeviCivitaNum where
  /-- Standard (finite, exponent 0) coefficient. -/
  std : Coeff := 0
  /-- Infinitesimal terms (strictly negative exponents of `H`, i.e., positive powers of `ε`). -/
  infinitesimal : Polynomial := 0
  /-- Infinite terms (strictly positive exponents of `H`). -/
  infinite : Polynomial := 0
deriving Repr

/-- Combine the three parts of a `LeviCivitaNum` into a single `Polynomial`. -/
def LeviCivitaNum.toPolyG (x : LeviCivitaNum) : Polynomial := Id.run do
  let mut out : CoeffMap := Std.HashMap.emptyWithCapacity
  for (e, c) in x.infinite.coeffs do
    if c != 0 then
      let prev := out.getD e 0
      out := out.insert e (prev + c)
  for (e, c) in x.infinitesimal.coeffs do
    if c != 0 then
      let prev := out.getD e 0
      out := out.insert e (prev + c)
  if x.std != 0 then
    let prev := out.getD 0 0
    out := out.insert 0 (prev + x.std)
  PolynomialG.normalize { coeffs := out }

instance : BEq LeviCivitaNum where
  beq x y := x.toPolyG == y.toPolyG

namespace LeviCivitaNum

/-- Construct a `LeviCivitaNum` from its three parts. -/
def mkParts (std : Coeff) (infinitesimal infinite : Polynomial) : LeviCivitaNum :=
  { std, infinitesimal, infinite }

/-- Construct a standard (finite) `LeviCivitaNum`. -/
def mkStd (c : Coeff) : LeviCivitaNum := mkParts c 0 0

/-- Construct a pure infinitesimal `c * H^e` (expecting `e < 0`). -/
def mkInf (e : Exponent) (c : Coeff) : LeviCivitaNum :=
  mkParts 0 { coeffs := Std.HashMap.singleton e c } 0

/-- Construct a pure infinite `c * H^e` (expecting `e > 0`). -/
def mkInfPos (e : Exponent) (c : Coeff) : LeviCivitaNum :=
  mkParts 0 0 { coeffs := Std.HashMap.singleton e c }

/-- Insert a term into the infinitesimal map. -/
def insertInfinitesimal (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum :=
  mkParts x.std { coeffs := x.infinitesimal.coeffs.insert e c } x.infinite

/-- Insert a term into the infinite map. -/
def insertInfinite (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum :=
  mkParts x.std x.infinitesimal { coeffs := x.infinite.coeffs.insert e c }

/-- Route an insertion by exponent sign (0 → std, >0 → infinite, <0 → infinitesimal). -/
def insert (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum :=
  if e == 0 then mkParts (x.std + c) x.infinitesimal x.infinite
  else if e > 0 then insertInfinite x e c
  else insertInfinitesimal x e c

/-- The additive identity `0`. -/
def zero : LeviCivitaNum := mkParts 0 0 0

instance : Zero LeviCivitaNum where zero := zero
instance : Inhabited LeviCivitaNum where default := zero

/-- The multiplicative identity `1`. -/
def one : LeviCivitaNum := mkParts 1 0 0

instance : One LeviCivitaNum where one := one

/-- The fundamental positive infinitesimal `ε = H⁻¹`. -/
def _root_.LeviCivitaNum.ε : LeviCivitaNum :=
  mkParts 0 { coeffs := Std.HashMap.singleton (-1) (1 : Coeff) } 0

/-- The fundamental positive infinite number `H = ε⁻¹`. -/
def _root_.LeviCivitaNum.H : LeviCivitaNum :=
  mkParts 0 0 { coeffs := Std.HashMap.singleton (1 : Exponent) (1 : Coeff) }

instance : Add LeviCivitaNum where
  add x y := mkParts (x.std + y.std) (x.infinitesimal + y.infinitesimal) (x.infinite + y.infinite)

instance : Neg LeviCivitaNum where
  neg x := mkParts (-x.std) (-x.infinitesimal) (-x.infinite)

instance : Coe Coeff LeviCivitaNum where
  coe c := mkParts c 0 0

instance : OfNat LeviCivitaNum n where
  ofNat := match n with
    | 0 => zero
    | 1 => one
    | _ => mkParts (((n : Nat) : Int) : Coeff) 0 0

instance : OfScientific LeviCivitaNum where
  ofScientific mantissa exponentSign decimalExponent :=
    mkParts (OfScientific.ofScientific mantissa exponentSign decimalExponent) 0 0

instance : Sub LeviCivitaNum where
  sub x y := x + (-y)

instance : CoeDep Term t LeviCivitaNum where
  coe :=
    if t.exp > 0 then mkParts 0 0 { coeffs := Std.HashMap.singleton t.exp t.coeff }
    else if t.exp = 0 then mkParts t.coeff 0 0
    else mkParts 0 { coeffs := Std.HashMap.singleton t.exp t.coeff } 0

/-- Build a `LeviCivitaNum` from an array of terms, summing duplicate exponents. -/
def ofArray (l : Array Term) : LeviCivitaNum := Id.run do
  let mut std : Coeff := 0
  let mut infinitesimal : CoeffMap := Std.HashMap.emptyWithCapacity
  let mut infinite : CoeffMap := Std.HashMap.emptyWithCapacity
  for term in l do
    if term.exp == 0 then
      std := std + term.coeff
    else if term.exp > 0 then
      let prev := infinite.getD term.exp 0
      infinite := infinite.insert term.exp (prev + term.coeff)
    else
      let prev := infinitesimal.getD term.exp 0
      infinitesimal := infinitesimal.insert term.exp (prev + term.coeff)
  return mkParts std (PolynomialG.normalize { coeffs := infinitesimal })
                     (PolynomialG.normalize { coeffs := infinite })

/-- Levi-Civita literal notation `lc[1, 2H, -3ε^2]`. -/
syntax "lc[" polyItem,* "]" : term

/-- Semantics for Levi-Civita literal notation. -/
macro_rules
  | `(lc[]) => `(LeviCivitaNum.zero)
  | `(lc[ε]) => `(LeviCivitaNum.ε)
  | `(lc[-ε]) => `(lc[-1 ε^1])
  | `(lc[H]) => `(LeviCivitaNum.H)
  | `(lc[-H]) => `(lc[-1 H])
  | `(lc[$coeff:term ε]) => `(LeviCivitaNum.mkParts 0 { coeffs := Std.HashMap.singleton (-1) ($coeff : Coeff) } 0)
  | `(lc[$coeff:term H]) => `(LeviCivitaNum.mkParts 0 0 { coeffs := Std.HashMap.singleton (1 : Exponent) ($coeff : Coeff) })
  | `(lc[ε^$exp]) => `(lc[1ε^$exp])
  | `(lc[-ε^$exp]) => `(lc[-1ε^$exp])
  | `(lc[H^$exp]) => `(lc[1H^$exp])
  | `(lc[-H^$exp]) => `(lc[-1H^$exp])
  | `(lc[$coeff:term ε^$exp]) => `(LeviCivitaNum.mkParts 0 { coeffs := Std.HashMap.singleton (-(($exp : Exponent))) ($coeff : Coeff) } 0)
  | `(lc[$coeff:term H^$exp]) => `(LeviCivitaNum.mkParts 0 0 { coeffs := Std.HashMap.singleton (($exp : Exponent)) ($coeff : Coeff) })
  | `(lc[$x:polyItem, $xs,*]) => `(lc[$x] + lc[$xs,*])
  | `(lc[$coeff:term]) => `(LeviCivitaNum.mkParts $coeff 0 0)

instance : ToString LeviCivitaNum where
  toString x := toString (x.toPolyG)

/-- Split a `Polynomial` back into a `LeviCivitaNum` by exponent sign. -/
def ofPolyG (xs : Polynomial) : LeviCivitaNum := Id.run do
  let mut std : Rat := 0
  let mut infinitesimal : CoeffMap := Std.HashMap.emptyWithCapacity
  let mut infinite : CoeffMap := Std.HashMap.emptyWithCapacity
  for (e, c) in xs.coeffs do
    if c != 0 then
      if e == 0 then std := std + c
      else if e > 0 then
        let prev := infinite.getD e 0
        infinite := infinite.insert e (prev + c)
      else
        let prev := infinitesimal.getD e 0
        infinitesimal := infinitesimal.insert e (prev + c)
  { std,
    infinitesimal := PolynomialG.normalize { coeffs := infinitesimal },
    infinite := PolynomialG.normalize { coeffs := infinite } }

/-- Original naive multiplication: converts to `Polynomial`, runs naive `O(nm)` HashMap product,
    and splits back to `LeviCivitaNum`. -/
def mulNaive (x y : LeviCivitaNum) : LeviCivitaNum :=
  ofPolyG (PolynomialG.mulNaive x.toPolyG y.toPolyG)

instance : Mul LeviCivitaNum where
  mul := mulNaive

/-- Original naive `O(k)` linear-loop natural power. -/
def powNaive (x : LeviCivitaNum) (n : Nat) : LeviCivitaNum := Id.run do
  let mut acc := (1 : LeviCivitaNum)
  let mut k := n
  while k != 0 do
    acc := acc * x
    k := k - 1
  acc

instance : HPow LeviCivitaNum Nat LeviCivitaNum where
  hPow := powNaive

/-- Check if a Levi-Civita number has only a standard (finite) part. -/
def isStd (x : LeviCivitaNum) : Bool :=
  x.infinite.isZero && x.infinitesimal.isZero

/-- Extract the dominant (largest-exponent) nonzero term, or `{coeff := 0, exp := 0}` if zero. -/
def largestTerm (x : LeviCivitaNum) : Term :=
  match x.toPolyG.leadingTerm with
  | some t => t
  | none => { coeff := 0, exp := 0 }

/-- Compute the sign (-1, 0, or 1) of a Levi-Civita number from its dominant (largest-exponent) term.
    Fixes the original ascending-sort bug where `signum` inspected the smallest infinitesimal first. -/
def signum (x : LeviCivitaNum) : Int :=
  let allTerms := x.toPolyG.toTerms
  let sortedTerms := allTerms.qsort (fun t₁ t₂ => t₁.exp > t₂.exp)
  match sortedTerms.find? (fun t => t.coeff != 0) with
  | some t => if t.coeff > 0 then 1 else -1
  | none => 0

instance : LT LeviCivitaNum where
  lt x y := (x - y).signum = -1

instance : LE LeviCivitaNum where
  le x y := (x - y).signum ≤ 0

instance : DecidableRel (@LT.lt LeviCivitaNum _) :=
  fun x y => decEq ((x - y).signum) (-1)

instance : DecidableRel (@LE.le LeviCivitaNum _) :=
  fun x y => inferInstanceAs (Decidable ((x - y).signum ≤ 0))

/-- Truncate a `LeviCivitaNum` to its `maxTerms` largest-exponent nonzero terms. -/
def truncate (x : LeviCivitaNum) (maxTerms : Nat) : LeviCivitaNum :=
  let sorted := (x.toPolyG.toTerms.filter (fun t => t.coeff != 0)).qsort (fun a b => a.exp > b.exp)
  ofArray (sorted.extract 0 maxTerms)

/-- Keep only nonzero terms with exponent `≥ minExp`. -/
def dropBelow (x : LeviCivitaNum) (minExp : Rat) : LeviCivitaNum :=
  ofArray (x.toPolyG.toTerms.filter (fun t => t.coeff != 0 && t.exp ≥ minExp))

/-- Expand `1 / (1 + δ)` via the geometric series `∑_{k=0}^{n-1} (-δ)^k` for infinitesimal `δ`,
    truncating by relative exponent `≥ -(stepD * (n - 1))` (matching `FastLC.invNewton`) so sparse
    cancellations like `1 / (1 + ε + ε²)` never retain corrupted terms beyond the loop horizon. -/
def expandUnitInverse (delta : LeviCivitaNum) (n : Nat := 10) : LeviCivitaNum := Id.run do
  if n == 0 then return zero
  let lead := delta.largestTerm
  let stepD : Rat := if lead.coeff != 0 && lead.exp < 0 then -lead.exp else 1
  let minExp : Rat := -(stepD * ((n - 1 : Nat) : Rat))
  let mut result : LeviCivitaNum := 1
  let mut power : LeviCivitaNum := 1
  let negDelta := -delta
  for _ in [1:n] do
    power := (power * negDelta).dropBelow minExp
    if power == 0 then break
    result := (result + power).dropBelow minExp
  return result

/-- Check if a Levi-Civita number has at most one nonzero term. -/
def isPure (x : LeviCivitaNum) : Bool :=
  x.toPolyG.supportSize ≤ 1

/-- Multiplicative inverse (series expansion to `order` terms for non-pure numbers). -/
def invOrder (x : LeviCivitaNum) (order : Nat := 10) : LeviCivitaNum :=
  let lead := x.largestTerm
  if lead.coeff == 0 then
    zero
  else
    let invLead : LeviCivitaNum :=
      ofArray #[{ coeff := lead.coeff⁻¹, exp := -lead.exp }]
    let normalized := x * invLead
    let delta := normalized - 1
    if delta == 0 then
      invLead
    else
      (invLead * expandUnitInverse delta order).truncate order

instance : Inv LeviCivitaNum where
  inv x := invOrder x 10

instance : Div LeviCivitaNum where
  div x y := x * y⁻¹

/-- Convert a `CoeffMap` to an array of nonzero terms. -/
def CoeffMap.toTerms (cm : CoeffMap) : Array Term := Id.run do
  let mut out := #[]
  for (exp, coeff) in cm do
    if coeff != 0 then
      out := out.push { exp, coeff }
  return out

end LeviCivitaNum
