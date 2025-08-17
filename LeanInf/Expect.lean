import LeanInf.PolyGeneric

namespace LeanInf.Expect
open LeanInf

abbrev Rat := Std.Internal.Rat

def mono (e : ExpG) (c : Rat) : PolynomialG Rat :=
  { coeffs := ((Std.HashMap.emptyWithCapacity : CoeffMapG Rat).insert e c) }

-- Expect: 1 + 1 = 2
#eval toString ((1 : PolynomialG Rat) + (1 : PolynomialG Rat))

-- Expect: 1 + (-1) = 0, printed as "0"
#eval toString ((1 : PolynomialG Rat) + ((-1 : Rat) : PolynomialG Rat))

-- Expect: equality ignores zero terms
#eval (((1 : PolynomialG Rat) + ((-1 : Rat) : PolynomialG Rat)) == (0 : PolynomialG Rat))

-- Mixed exponents: expect both H and ε units to appear
#eval toString (mono 1 (2 : Rat) + mono (-1) (3 : Rat))

-- Expect: H * ε = constant term
#eval toString ((mono 1 (2 : Rat)) * (mono (-1) (3 : Rat)))

-- Expect: cancellation at same exponent yields 0 (due to normalize)
#eval toString ((mono 2 (1 : Rat)) + (mono 2 (-1 : Rat)))

-- LeviCivitaNum construction checks (no eval to avoid sorry-dependent paths)
-- Expect failure: missing invariant proofs when using raw record literal
#check_failure ({ std := (1 : Rat) : LeviCivitaNum })
-- Prefer helper that centralizes invariant obligations
#check (LeviCivitaNum.mkStd (1 : Rat))

end LeanInf.Expect
