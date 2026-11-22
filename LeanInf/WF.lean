import LeanInf.PolyGeneric
import LeanInf.LeviCivitaNum

namespace LeanInf
open LeviCivitaNum

/-- Check that every exponent in an infinitesimal polynomial is strictly negative. -/
def wfNeg (p : Polynomial) : Bool :=
  p.coeffs.all (fun e _ => decide (e < 0))

/-- Check that every exponent in an infinite polynomial is strictly positive. -/
def wfPos (p : Polynomial) : Bool :=
  p.coeffs.all (fun e _ => decide (e > 0))

/-- Check that both the infinitesimal and infinite parts of a `LeviCivitaNum` satisfy their sign invariants. -/
def wfLC (x : LeviCivitaNum) : Bool := wfNeg x.infinitesimal && wfPos x.infinite

/-- Insert into the infinitesimal map and return the updated number along with its well-formedness check. -/
def insertInfinitesimalChecked (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum × Bool :=
  let y := { x with infinitesimal := { coeffs := x.infinitesimal.coeffs.insert e c } }
  (y, wfLC y)

/-- Insert into the infinite map and return the updated number along with its well-formedness check. -/
def insertInfiniteChecked (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum × Bool :=
  let y := { x with infinite := { coeffs := x.infinite.coeffs.insert e c } }
  (y, wfLC y)

/-- Negate a `LeviCivitaNum` and check that well-formedness is preserved. -/
def negChecked (x : LeviCivitaNum) : LeviCivitaNum × Bool :=
  let y : LeviCivitaNum :=
    { std := -x.std
      infinitesimal := { coeffs := x.infinitesimal.coeffs.map (fun _ v => -v) }
      infinite := { coeffs := x.infinite.coeffs.map (fun _ v => -v) } }
  (y, wfLC y)

/-- Add two `LeviCivitaNum` values via `mergeWith` and check that well-formedness is preserved. -/
def addChecked (x y : LeviCivitaNum) : LeviCivitaNum × Bool :=
  let z : LeviCivitaNum :=
    { std := x.std + y.std
      infinitesimal := { coeffs := Std.HashMap.mergeWith x.infinitesimal.coeffs y.infinitesimal.coeffs (fun _ a b => a + b) }
      infinite      := { coeffs := Std.HashMap.mergeWith x.infinite.coeffs      y.infinite.coeffs      (fun _ a b => a + b) } }
  (z, wfLC z)

end LeanInf
