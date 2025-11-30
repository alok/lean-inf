import Std
import Init.Data.Rat

namespace LeanInf

/-- Minimal coefficient interface for Levi-Civita polynomials.
    Not a full field: intended to support types like {name}`Float` too. -/
class CoeffLike (α : Type u) where
  /-- Returns true if the coefficient is positive. -/
  isPos : α → Bool
  /-- Returns true if the coefficient is negative. -/
  isNeg : α → Bool

/-- Convert positive/negative flags to an integer sign (-1, 0, or 1). -/
def signInt (p n : Bool) : Int := if p then 1 else if n then -1 else 0

instance : CoeffLike Rat where
  isPos x := x > 0
  isNeg x := x < 0

instance : CoeffLike Float where
  isPos x := x > 0.0
  isNeg x := x < 0.0

-- Rat already derives `Hashable` in core (`Init.Data.Rat`).

end LeanInf
