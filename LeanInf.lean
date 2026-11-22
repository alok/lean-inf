import LeanInf.Basic
import LeanInf.CoeffLike
import LeanInf.PolyGeneric
import LeanInf.LeviCivitaNum
import LeanInf.WF
import LeanInf.SortedLC
import LeanInf.Karatsuba
import LeanInf.VerifiedRefactor
import LeanInf.StepFunction
import LeanInf.Parser
import LeanInf.TestSuite
import LeanInf.Bench

/-!
# LeanInf — Computable Levi-Civita Numbers in Lean 4

Compute with infinities (`H`) and infinitesimals (`ε = 1/H`) using the Levi-Civita field,
with zero-`sorry` verified fast refactors (`FastLC`: `O(1)` signum, `O(n + m)` merge addition,
balanced-tree sparse multiplication, verified Karatsuba multiplication, binary exponentiation,
and quadratically convergent Newton-Raphson inversion), automatic differentiation of the
nonstandard logistic step function, finite specialization (`H ↦ N`), and a full calculator engine.
-/

namespace LeanInf

/-- Default rational polynomial type alias. -/
abbrev Polynomial := PolynomialG Rat

end LeanInf
