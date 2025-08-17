import LeanInf.LeviCivitaNum
import LeanInf.SignLemmas

open LeviCivitaNum

namespace LeviCivitaNum

/-- Insert into the infinitesimal map with a proof that the sign invariant is preserved. -/
def insertInfinitesimalP (x : LeviCivitaNum) (e : Exponent) (c : Coeff) (h : e < 0) : LeviCivitaNum :=
  { std := x.std
    infinitesimal := ⟨x.infinitesimal.coeffs.insert e c⟩
    infinite := x.infinite
    _pf_infinitesimal_keys_negative := LeanInf.all_neg_insert x.infinitesimal.coeffs x._pf_infinitesimal_keys_negative e h c
    _pf_infinite_keys_positive := x._pf_infinite_keys_positive }

/-- Insert into the infinite map with a proof that the sign invariant is preserved. -/
def insertInfiniteP (x : LeviCivitaNum) (e : Exponent) (c : Coeff) (h : e > 0) : LeviCivitaNum :=
  { std := x.std
    infinitesimal := x.infinitesimal
    infinite := ⟨x.infinite.coeffs.insert e c⟩
    _pf_infinitesimal_keys_negative := x._pf_infinitesimal_keys_negative
    _pf_infinite_keys_positive := LeanInf.all_pos_insert x.infinite.coeffs x._pf_infinite_keys_positive e h c }

/-- Proven negation that preserves key-sign invariants via map-values lemmas. -/
def negP (x : LeviCivitaNum) : LeviCivitaNum :=
  { std := -x.std
    infinitesimal := { coeffs := x.infinitesimal.coeffs.map (fun _ v => -v) }
    infinite := { coeffs := x.infinite.coeffs.map (fun _ v => -v) }
    _pf_infinitesimal_keys_negative := LeanInf.all_neg_map_values x.infinitesimal.coeffs x._pf_infinitesimal_keys_negative (fun v => -v)
    _pf_infinite_keys_positive := LeanInf.all_pos_map_values x.infinite.coeffs x._pf_infinite_keys_positive (fun v => -v) }

end LeviCivitaNum

