import Std
import LeanInf.Basic
import LeanInf.CoeffLike

namespace LeanInf

abbrev ExpG := Std.Internal.Rat

structure TermG (α : Type u) where
  coeff : α
  exp   : ExpG
deriving BEq, Inhabited, Repr

abbrev CoeffMapG (α : Type u) := Std.HashMap ExpG α

structure PolynomialG (α : Type u) where
  coeffs : CoeffMapG α := {}
deriving Inhabited, Repr

namespace PolynomialG
variable {α : Type u}

def empty {α} : PolynomialG α := { coeffs := {} }

def toTerms (p : PolynomialG α) : Array (TermG α) := Id.run do
  let mut out := #[]
  for (e, c) in p.coeffs do
    out := out.push { coeff := c, exp := e }
  out

def filterZeros [BEq α] [Zero α] (m : CoeffMapG α) : CoeffMapG α := Id.run do
  let mut r : CoeffMapG α := Std.HashMap.emptyWithCapacity
  for (e, c) in m do
    if !(c == (0 : α)) then r := r.insert e c
  r

/-- Normalize by pruning zero coefficients. -/
def normalize [BEq α] [Zero α] (p : PolynomialG α) : PolynomialG α :=
  { coeffs := filterZeros p.coeffs }

instance [BEq α] [Zero α] : BEq (PolynomialG α) where
  beq p q :=
    let xs := filterZeros p.coeffs
    let ys := filterZeros q.coeffs
    xs.size == ys.size &&
    xs.fold (init := true) (fun acc k v => acc && (ys.getD k v == v)) &&
    ys.fold (init := true) (fun acc k v => acc && (xs.getD k v == v))

instance [Add α] [Zero α] [BEq α] : Add (PolynomialG α) where
  add p q := Id.run do
    let mut r := p.coeffs
    for (e, c) in q.coeffs do
      let prev := r.getD e 0
      r := r.insert e (prev + c)
    normalize { coeffs := r }

instance [Neg α] : Neg (PolynomialG α) where
  neg p := { coeffs := p.coeffs.map (fun _ v => -v) }

instance [Add α] [Zero α] [Sub α] [Neg α] [BEq α] : Sub (PolynomialG α) where
  sub x y := x + (-y)

instance [Mul α] [Add α] [Zero α] [BEq α] : Mul (PolynomialG α) where
  mul p q := Id.run do
    let mut r : CoeffMapG α := Std.HashMap.emptyWithCapacity
    for (ep, cp) in p.coeffs do
      for (eq, cq) in q.coeffs do
        let e := ep + eq
        let prev := r.getD e 0
        r := r.insert e (prev + (cp * cq))
    normalize { coeffs := r }

instance [OfNat α 0] : Coe α (PolynomialG α) where
  coe a := { coeffs := (Std.HashMap.emptyWithCapacity : CoeffMapG α) |>.insert (0 : ExpG) a }

instance [OfNat α n] : OfNat (PolynomialG α) n where
  ofNat := { coeffs := ((Std.HashMap.emptyWithCapacity : CoeffMapG α).insert (0 : ExpG) (OfNat.ofNat n)) }

instance [OfScientific α] : OfScientific (PolynomialG α) where
  ofScientific m s d :=
    { coeffs := ((Std.HashMap.emptyWithCapacity : CoeffMapG α).insert (0 : ExpG) (OfScientific.ofScientific m s d : α)) }

instance [ToString α] [BEq α] [Zero α] : ToString (PolynomialG α) where
  toString p :=
    let terms := p.toTerms
    let nz := terms.filter (fun t => !(t.coeff == (0 : α)))
    let strs := nz.map (fun t =>
      match t.exp with
      | 0 => s!"{t.coeff}"
      | 1 => s!"{t.coeff}H"
      | -1 => s!"{t.coeff}ε"
      | e =>
        let u := if e > 0 then "H" else "ε"
        s!"{t.coeff}{u}{e}"
    )
    let parts := strs.toList
    if parts.isEmpty then "0"
    else parts.foldl (fun acc s => if acc = "" then s else acc ++ " + " ++ s) ""

end PolynomialG

end LeanInf

-- Lightweight sanity checks for Rat-backed polynomials
#eval ((2 : LeanInf.PolynomialG Std.Internal.Rat) + (3 : LeanInf.PolynomialG Std.Internal.Rat))
#eval (toString ((1 : LeanInf.PolynomialG Std.Internal.Rat) + (1 : LeanInf.PolynomialG Std.Internal.Rat)))
