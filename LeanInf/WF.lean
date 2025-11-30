import LeanInf.PolyGeneric
import LeanInf.LeviCivitaNum

namespace LeanInf
open LeviCivitaNum

-- Boolean well-formedness checks for parts
def wfNeg (p : Polynomial) : Bool :=
  p.coeffs.all (fun e _ => decide (e < 0))

def wfPos (p : Polynomial) : Bool :=
  p.coeffs.all (fun e _ => decide (e > 0))

def wfLC (x : LeviCivitaNum) : Bool := wfNeg x.infinitesimal && wfPos x.infinite

-- Checked variants that return the computed value and whether the invariant holds afterward
def insertInfinitesimalChecked (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum × Bool :=
  let y := { x with infinitesimal := { coeffs := x.infinitesimal.coeffs.insert e c } }
  (y, wfLC y)

def insertInfiniteChecked (x : LeviCivitaNum) (e : Exponent) (c : Coeff) : LeviCivitaNum × Bool :=
  let y := { x with infinite := { coeffs := x.infinite.coeffs.insert e c } }
  (y, wfLC y)

def negChecked (x : LeviCivitaNum) : LeviCivitaNum × Bool :=
  let y : LeviCivitaNum :=
    { std := -x.std
      infinitesimal := { coeffs := x.infinitesimal.coeffs.map (fun _ v => -v) }
      infinite := { coeffs := x.infinite.coeffs.map (fun _ v => -v) } }
  (y, wfLC y)

def addChecked (x y : LeviCivitaNum) : LeviCivitaNum × Bool :=
  let z : LeviCivitaNum :=
    { std := x.std + y.std
      infinitesimal := { coeffs := Std.HashMap.mergeWith x.infinitesimal.coeffs y.infinitesimal.coeffs (fun _ a b => a + b) }
      infinite      := { coeffs := Std.HashMap.mergeWith x.infinite.coeffs      y.infinite.coeffs      (fun _ a b => a + b) } }
  (z, wfLC z)

end LeanInf
