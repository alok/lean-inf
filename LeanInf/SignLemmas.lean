import LeanInf.LeviCivitaNum

open LeviCivitaNum

namespace LeanInf

/-- If we insert a new coefficient into the infinitesimal map at an exponent strictly
    lower than the current leading infinitesimal exponent, the overall sign stays the same.
    This is a skeleton; we plan to discharge it with `grind` once the structure stabilizes. -/
theorem sign_preserved_by_infinitesimal_insert
    (x : LeviCivitaNum)
    (e : Exponent) (c : Coeff)
    (hneg : e < 0)
    (hle : ∀ e', x.infinitesimal.coeffs.contains e' → e ≤ e')
  : (signum x) = (signum { x with infinitesimal := ⟨x.infinitesimal.coeffs.insert e c⟩ }) := by
  -- TODO: formalize via a sorted view of exponents and `largestTerm`
  -- The `grind` tactic from the Lean reference (index map example) should automate
  -- the case analysis over the finite map structure here.
  sorry

/-- Analogous lemma for insertion into the infinite map with positive exponents. -/
theorem sign_preserved_by_infinite_insert
    (x : LeviCivitaNum)
    (e : Exponent) (c : Coeff)
    (hpos : e > 0)
    (hle : ∀ e', x.infinite.coeffs.contains e' → e ≥ e')
  : (signum x) = (signum { x with infinite := ⟨x.infinite.coeffs.insert e c⟩ }) := by
  sorry

end LeanInf

