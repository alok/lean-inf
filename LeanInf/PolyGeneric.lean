import Std
import Init.Data.Rat
import LeanInf.Basic
import LeanInf.CoeffLike

namespace LeanInf

/-- Rational exponent type for generic Levi-Civita polynomials. -/
abbrev ExpG := Rat

/-- A single term `coeff * H^exp` (with `H = ε⁻¹`). -/
structure TermG (α : Type u) where
  /-- Scalar coefficient of the term. -/
  coeff : α
  /-- Rational exponent of `H` (positive = infinite, zero = standard, negative = infinitesimal). -/
  exp   : ExpG
deriving BEq, Inhabited, Repr

/-- HashMap backing store mapping rational exponents to coefficients. -/
abbrev CoeffMapG (α : Type u) := Std.HashMap ExpG α

/-- Naive HashMap-backed polynomial over rational exponents.
    Preserved as the original reference representation for differential testing and benchmarking. -/
structure PolynomialG (α : Type u) where
  /-- Exponent-to-coefficient map. -/
  coeffs : CoeffMapG α := {}
deriving Inhabited, Repr

namespace PolynomialG
variable {α : Type u}

/-- The empty (zero) polynomial. -/
def empty {α} : PolynomialG α := { coeffs := {} }

/-- Convert a polynomial's map entries into an array of terms. -/
def toTerms (p : PolynomialG α) : Array (TermG α) := Id.run do
  let mut out := #[]
  for (e, c) in p.coeffs do
    out := out.push { coeff := c, exp := e }
  out

/-- Remove entries whose coefficient equals zero. -/
def filterZeros [BEq α] [Zero α] (m : CoeffMapG α) : CoeffMapG α := Id.run do
  let mut r : CoeffMapG α := Std.HashMap.emptyWithCapacity
  for (e, c) in m do
    if !(c == (0 : α)) then r := r.insert e c
  r

/-- Normalize by pruning zero coefficients. -/
def normalize [BEq α] [Zero α] (p : PolynomialG α) : PolynomialG α :=
  { coeffs := filterZeros p.coeffs }

/-- Equality modulo zero-coefficient entries (fixed to use `get?` rather than `getD`). -/
instance [BEq α] [Zero α] : BEq (PolynomialG α) where
  beq p q :=
    let xs := filterZeros p.coeffs
    let ys := filterZeros q.coeffs
    xs.size == ys.size &&
    xs.fold (init := true) (fun acc k v => acc && (ys.get? k == some v))

/-- Naive HashMap polynomial addition with zero pruning. -/
def addNaive [Add α] [Zero α] [BEq α] (p q : PolynomialG α) : PolynomialG α := Id.run do
  let mut r := p.coeffs
  for (e, c) in q.coeffs do
    let prev := r.getD e 0
    r := r.insert e (prev + c)
  normalize { coeffs := r }

instance [Add α] [Zero α] [BEq α] : Add (PolynomialG α) where
  add := addNaive

instance [Neg α] : Neg (PolynomialG α) where
  neg p := { coeffs := p.coeffs.map (fun _ v => -v) }

instance [Add α] [Zero α] [Sub α] [Neg α] [BEq α] : Sub (PolynomialG α) where
  sub x y := x + (-y)

/-- Original naive `O(n * m)` HashMap polynomial multiplication. -/
def mulNaive [Mul α] [Add α] [Zero α] [BEq α] (p q : PolynomialG α) : PolynomialG α := Id.run do
  let mut r : CoeffMapG α := Std.HashMap.emptyWithCapacity
  for (ep, cp) in p.coeffs do
    for (eq, cq) in q.coeffs do
      let e := ep + eq
      let prev := r.getD e 0
      r := r.insert e (prev + (cp * cq))
  normalize { coeffs := r }

instance [Mul α] [Add α] [Zero α] [BEq α] : Mul (PolynomialG α) where
  mul := mulNaive

/-- Construct a monomial with exponent {lit}`e` and coefficient {lit}`c`. -/
def mono (e : ExpG) (c : α) : PolynomialG α :=
  { coeffs := ((Std.HashMap.emptyWithCapacity : CoeffMapG α).insert e c) }

/-- Number of nonzero terms. -/
def supportSize [BEq α] [Zero α] (p : PolynomialG α) : Nat :=
  (filterZeros p.coeffs).size

/-- Check if the polynomial is identically zero (after pruning zeros). -/
def isZero [BEq α] [Zero α] (p : PolynomialG α) : Bool :=
  (filterZeros p.coeffs).size == 0

/-- Largest exponent with nonzero coefficient, if any. -/
def degree [BEq α] [Zero α] (p : PolynomialG α) : Option ExpG :=
  (filterZeros p.coeffs).fold (init := (none : Option ExpG)) (fun acc e _ =>
    match acc with
    | none => some e
    | some b => if e > b then some e else acc)

/-- Leading term (largest exponent), if any, after pruning zeros. -/
def leadingTerm [BEq α] [Zero α] (p : PolynomialG α) : Option (TermG α) :=
  (filterZeros p.coeffs).fold (init := (none : Option (TermG α))) (fun acc e c =>
    match acc with
    | none => some { coeff := c, exp := e }
    | some t => if e > t.exp then some { coeff := c, exp := e } else acc)

/-- Smallest exponent with nonzero coefficient, if any. -/
def minDegree [BEq α] [Zero α] (p : PolynomialG α) : Option ExpG :=
  (filterZeros p.coeffs).fold (init := (none : Option ExpG)) (fun acc e _ =>
    match acc with
    | none => some e
    | some b => if e < b then some e else acc)

/-- Trailing term (smallest exponent), if any, after pruning zeros. -/
def trailingTerm [BEq α] [Zero α] (p : PolynomialG α) : Option (TermG α) :=
  (filterZeros p.coeffs).fold (init := (none : Option (TermG α))) (fun acc e c =>
    match acc with
    | none => some { coeff := c, exp := e }
    | some t => if e < t.exp then some { coeff := c, exp := e } else acc)

instance [OfNat α 0] : Coe α (PolynomialG α) where
  coe a := { coeffs := (Std.HashMap.emptyWithCapacity : CoeffMapG α) |>.insert (0 : ExpG) a }

instance [OfNat α n] : OfNat (PolynomialG α) n where
  ofNat := { coeffs := ((Std.HashMap.emptyWithCapacity : CoeffMapG α).insert (0 : ExpG) (OfNat.ofNat n)) }

instance [OfScientific α] : OfScientific (PolynomialG α) where
  ofScientific m s d :=
    { coeffs := ((Std.HashMap.emptyWithCapacity : CoeffMapG α).insert (0 : ExpG) (OfScientific.ofScientific m s d : α)) }

private def digitToSuperscript (c : Char) : Char :=
  match c with
  | '0' => '⁰' | '1' => '¹' | '2' => '²' | '3' => '³' | '4' => '⁴'
  | '5' => '⁵' | '6' => '⁶' | '7' => '⁷' | '8' => '⁸' | '9' => '⁹'
  | '/' => 'ᐟ' | '-' => '⁻'
  | _ => c

/-- Convert ASCII digits, slash, and minus in a string to Unicode superscripts. -/
def toSuperscript (s : String) : String :=
  String.ofList (s.toList.map digitToSuperscript)

/-- Pretty-print a rational exponent in superscript form. -/
def fmtUnitExp (e : ExpG) : String :=
  if e == 0 then ""
  else if e == 1 then "H"
  else if e == -1 then "ε"
  else if e > 0 then s!"H{toSuperscript (toString e)}"
  else s!"ε{toSuperscript (toString (-e))}"

instance [ToString α] [BEq α] [Zero α] : ToString (PolynomialG α) where
  toString p := Id.run do
    let base := p.toTerms |>.filter (fun t => !(t.coeff == (0 : α)))
    let sorted := base.qsort (fun a b => a.exp > b.exp)
    let fmt := fun (t : TermG α) =>
      if t.exp == 0 then s!"{t.coeff}"
      else s!"{t.coeff}{fmtUnitExp t.exp}"
    let parts := (sorted.map fmt).toList
    if parts.isEmpty then "0" else String.intercalate " + " parts

end PolynomialG

end LeanInf
