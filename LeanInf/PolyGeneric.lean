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

/-- Construct a monomial `c * u^e`. -/
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
  | _ => c

private def toSuperscript (s : String) : String :=
  let rec go (acc : String) (chars : List Char) : String :=
    match chars with
    | [] => acc
    | '-' :: rest => go (acc ++ "⁻") rest
    | c :: rest => go (acc.push (digitToSuperscript c)) rest
  go "" s.data

instance [ToString α] [BEq α] [Zero α] : ToString (PolynomialG α) where
  toString p := Id.run do
    -- Collect and prune zeros
    let base := p.toTerms |>.filter (fun t => !(t.coeff == (0 : α)))
    -- Partition by exponent sign
    let pos := base.filter (fun t => t.exp > 0)
    let zer := base.filter (fun t => t.exp == 0)
    let neg := base.filter (fun t => t.exp < 0)
    -- Sort within groups
    let pos := pos.qsort (fun a b => a.exp > b.exp)
    let neg := neg.qsort (fun a b => a.exp > b.exp) -- closer to zero first: -1, -2, ...
    -- Map to strings
    let fmt := fun (t : TermG α) =>
      match t.exp with
      | 0 => s!"{t.coeff}"
      | 1 => s!"{t.coeff}H"
      | -1 => s!"{t.coeff}ε"
      | e => if e > 0 then s!"{t.coeff}H{toSuperscript (toString e)}"
             else s!"{t.coeff}ε{toSuperscript (toString (-e))}"
    let sPos := pos.map fmt
    let sZer := zer.map fmt
    let sNeg := neg.map fmt
    let parts := (sPos ++ sZer ++ sNeg).toList
    if parts.isEmpty then "0" else
      Id.run do
        let mut acc : String := ""
        for s in parts do
          if acc == "" then acc := s else acc := acc ++ " + " ++ s
        acc

end PolynomialG

end LeanInf

-- Lightweight sanity checks for Rat-backed polynomials
#eval ((2 : LeanInf.PolynomialG Std.Internal.Rat) + (3 : LeanInf.PolynomialG Std.Internal.Rat))
#eval (toString ((1 : LeanInf.PolynomialG Std.Internal.Rat) + (1 : LeanInf.PolynomialG Std.Internal.Rat)))
