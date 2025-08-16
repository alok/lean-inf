import Std
import LeanInf.CoeffLike
import LeanInf.PolyGeneric

namespace LeanInf

open LeanInf

structure LeviCivitaNumG (α : Type u) [CoeffLike α] [Zero α] where
  std           : α := 0
  infinitesimal : PolynomialG α := {}
  infinite      : PolynomialG α := {}
deriving Repr

namespace LCNumG
variable {α : Type u} [CoeffLike α] [Zero α]

instance : Coe α (_root_.LeanInf.LeviCivitaNumG α) where
  coe a := { std := a }

instance [Add α] [BEq α] : Add (_root_.LeanInf.LeviCivitaNumG α) where
  add x y := { std := x.std + y.std, infinitesimal := x.infinitesimal + y.infinitesimal, infinite := x.infinite + y.infinite }

instance [Neg α] : Neg (_root_.LeanInf.LeviCivitaNumG α) where
  neg x := { std := -x.std, infinitesimal := -x.infinitesimal, infinite := -x.infinite }

instance [Sub α] [Add α] [Neg α] [BEq α] : Sub (_root_.LeanInf.LeviCivitaNumG α) where
  sub x y := x + (-y)

/-- Merge all parts into a single generic polynomial. -/
def toPolyG [Add α] (x : _root_.LeanInf.LeviCivitaNumG α) : PolynomialG α := Id.run do
  let mut out : CoeffMapG α := Std.HashMap.emptyWithCapacity
  for (e, c) in x.infinite.coeffs do
    out := out.insert e c
  for (e, c) in x.infinitesimal.coeffs do
    let prev := out.getD e 0
    out := out.insert e (prev + c)
  out := out.insert 0 x.std
  { coeffs := out }

/-- Multiply by routing through generic polynomial multiplication. -/
instance [Add α] [Mul α] [BEq α] : Mul (_root_.LeanInf.LeviCivitaNumG α) where
  mul x y :=
    let px := toPolyG (α := α) x
    let py := toPolyG (α := α) y
    -- Convert back by splitting on exponent sign
    Id.run do
      let mut std : α := 0
      let mut infinitesimal : PolynomialG α := {}
      let mut infinite : PolynomialG α := {}
      for (e, c) in (px * py).coeffs do
        if e == 0 then std := std + c
        else if e > 0 then
          infinite := { coeffs := infinite.coeffs.insert e c }
        else
          infinitesimal := { coeffs := infinitesimal.coeffs.insert e c }
      { std, infinitesimal, infinite }

end LCNumG

end LeanInf
