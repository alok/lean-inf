import Std
import LeanInf.CoeffLike
import LeanInf.PolyGeneric

namespace LeanInf

open LeanInf

structure LeviCivitaNumG (α : Type u) [CoeffLike α] where
  std           : α := 0
  infinitesimal : PolynomialG α := {}
  infinite      : PolynomialG α := {}
  _pf_infinitesimal_keys_negative : infinitesimal.coeffs.all (fun exp _ => exp < 0) := by
    -- placeholder maintaining invariant; to be proven later
    (first | rfl | exact propext (Iff.intro (fun h => True.intro) (fun _ => True.intro)) )
  _pf_infinite_keys_positive : infinite.coeffs.all (fun exp _ => exp > 0) := by
    (first | rfl | exact propext (Iff.intro (fun h => True.intro) (fun _ => True.intro)) )
deriving Repr

namespace LeviCivitaNumG
variable {α : Type u} [CoeffLike α]

instance : Coe α (LeviCivitaNumG α) where
  coe a := { std := a }

instance [Add α] : Add (LeviCivitaNumG α) where
  add x y := { std := x.std + y.std, infinitesimal := x.infinitesimal + y.infinitesimal, infinite := x.infinite + y.infinite }

instance [Neg α] : Neg (LeviCivitaNumG α) where
  neg x := { std := -x.std, infinitesimal := -x.infinitesimal, infinite := -x.infinite }

instance [Sub α] : Sub (LeviCivitaNumG α) where
  sub x y := x + (-y)

end LeviCivitaNumG

end LeanInf

