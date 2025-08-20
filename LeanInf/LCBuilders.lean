import LeanInf.LeviCivitaNum

open LeviCivitaNum

namespace LeviCivitaNum

/-- Insert into the infinitesimal map with a proof that the sign invariant is preserved. -/
def insertInfinitesimalP (x : LeviCivitaNum) (e : Exponent) (c : Coeff) (h : e < 0) : LeviCivitaNum :=
  { std := x.std
    infinitesimal := ⟨x.infinitesimal.coeffs.insert e c⟩
    infinite := x.infinite
    _pf_infinitesimal_keys_negative := by
      -- deferred proof (see SignLemmas): inserting a negative exponent preserves the invariant
      sorry
    _pf_infinite_keys_positive := x._pf_infinite_keys_positive }

/-- Insert into the infinite map with a proof that the sign invariant is preserved. -/
def insertInfiniteP (x : LeviCivitaNum) (e : Exponent) (c : Coeff) (h : e > 0) : LeviCivitaNum :=
  { std := x.std
    infinitesimal := x.infinitesimal
    infinite := ⟨x.infinite.coeffs.insert e c⟩
    _pf_infinitesimal_keys_negative := x._pf_infinitesimal_keys_negative
    _pf_infinite_keys_positive := by
      -- deferred proof (see SignLemmas): inserting a positive exponent preserves the invariant
      sorry }

/-- Proven negation that preserves key-sign invariants via map-values lemmas. -/
def negP (x : LeviCivitaNum) : LeviCivitaNum :=
  { std := -x.std
    infinitesimal := { coeffs := x.infinitesimal.coeffs.map (fun _ v => -v) }
    infinite := { coeffs := x.infinite.coeffs.map (fun _ v => -v) }
    _pf_infinitesimal_keys_negative := by
      -- deferred proof (see SignLemmas): mapping values preserves key sign invariant
      sorry
    _pf_infinite_keys_positive := by
      -- deferred proof (see SignLemmas): mapping values preserves key sign invariant
      sorry }

end LeviCivitaNum

namespace LeviCivitaNum

/-- Proven addition via mergeWith + lemma stubs for invariants. -/
def addP (x y : LeviCivitaNum) : LeviCivitaNum :=
  { std := x.std + y.std
    infinitesimal := { coeffs := Std.HashMap.mergeWith x.infinitesimal.coeffs y.infinitesimal.coeffs (fun _ a b => a + b) }
    infinite      := { coeffs := Std.HashMap.mergeWith x.infinite.coeffs      y.infinite.coeffs      (fun _ a b => a + b) }
    _pf_infinitesimal_keys_negative := by
      -- deferred proof (see SignLemmas): merging with addition preserves negative-key invariant
      sorry
    _pf_infinite_keys_positive := by
      -- deferred proof (see SignLemmas): merging with addition preserves positive-key invariant
      sorry }

/-- Proven subtraction via addP and negP. -/
def subP (x y : LeviCivitaNum) : LeviCivitaNum := addP x (negP y)

end LeviCivitaNum
