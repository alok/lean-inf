import Std

namespace LeanInf

/-- Minimal coefficient interface for Levi-Civita polynomials.
    Not a full field: intended to support types like `Float` too. -/
class CoeffLike (α : Type u) where
  -- Optional sign query for ordering-sensitive ops (e.g., signum).
  isPos : α → Bool
  isNeg : α → Bool

def signInt (p n : Bool) : Int := if p then 1 else if n then -1 else 0

instance : CoeffLike Std.Internal.Rat where
  isPos x := x > 0
  isNeg x := x < 0

instance : CoeffLike Float where
  isPos x := x > 0.0
  isNeg x := x < 0.0

-- Hashing for rational exponents used as HashMap keys.
instance : Hashable Std.Internal.Rat where
  hash r := hash (r.num, r.den)

end LeanInf
