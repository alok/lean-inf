import LeanInf.LeviCivitaNum
import LeanInf.SignLemmas

open LeviCivitaNum

namespace LeviCivitaNum

/-- Insert into the infinitesimal map with a proof that the sign invariant is preserved. -/
def insertInfinitesimalP (x : LeviCivitaNum) (e : Exponent) (c : Coeff) (h : e < 0) : LeviCivitaNum :=
  { std := x.std
    infinitesimal := ⟨x.infinitesimal.coeffs.insert e c⟩
    infinite := x.infinite
    _pf_infinitesimal_keys_negative := by
      -- inserting a negative exponent preserves the negative-keys invariant
      -- via keysNeg_insert
      refine (LeanInf.keysNeg_insert (m := x.infinitesimal.coeffs) (h := ?_ ) (e := e) (he := h) (c := c)) ?_ ?_ ?_
      · exact inferInstance
      · exact inferInstance
      · intro e' hc
        exact x._pf_infinitesimal_keys_negative e' hc
    _pf_infinite_keys_positive := x._pf_infinite_keys_positive }

/-- Insert into the infinite map with a proof that the sign invariant is preserved. -/
def insertInfiniteP (x : LeviCivitaNum) (e : Exponent) (c : Coeff) (h : e > 0) : LeviCivitaNum :=
  { std := x.std
    infinitesimal := x.infinitesimal
    infinite := ⟨x.infinite.coeffs.insert e c⟩
    _pf_infinitesimal_keys_negative := x._pf_infinitesimal_keys_negative
    _pf_infinite_keys_positive := by
      -- inserting a positive exponent preserves the positive-keys invariant via keysPos_insert
      refine (LeanInf.keysPos_insert (m := x.infinite.coeffs) (h := ?_) (e := e) (he := h) (c := c)) ?_ ?_ ?_
      · exact inferInstance
      · exact inferInstance
      · intro e' hc
        exact x._pf_infinite_keys_positive e' hc }

/-- Proven negation that preserves key-sign invariants via map-values lemmas. -/
def negP (x : LeviCivitaNum) : LeviCivitaNum :=
  { std := -x.std
    infinitesimal := { coeffs := x.infinitesimal.coeffs.map (fun _ v => -v) }
    infinite := { coeffs := x.infinite.coeffs.map (fun _ v => -v) }
    _pf_infinitesimal_keys_negative := by
      -- mapping values preserves keys; reuse negative-keys invariant
      refine (LeanInf.keysNeg_map (m := x.infinitesimal.coeffs) (h := ?_) (g := fun v => -v)) ?_ ?_ ?_
      · exact inferInstance
      · exact inferInstance
      · intro e' hc
        exact x._pf_infinitesimal_keys_negative e' hc
    _pf_infinite_keys_positive := by
      -- mapping values preserves keys; reuse positive-keys invariant
      refine (LeanInf.keysPos_map (m := x.infinite.coeffs) (h := ?_) (g := fun v => -v)) ?_ ?_ ?_
      · exact inferInstance
      · exact inferInstance
      · intro e' hc
        exact x._pf_infinite_keys_positive e' hc }

end LeviCivitaNum

namespace LeviCivitaNum

/-- Proven addition via mergeWith + lemma stubs for invariants. -/
def addP (x y : LeviCivitaNum) : LeviCivitaNum :=
  { std := x.std + y.std
    -- Use mergeAdd built as a fold over `toList` to ease invariant proofs
    infinitesimal := { coeffs := LeanInf.mergeAdd x.infinitesimal.coeffs y.infinitesimal.coeffs }
    infinite      := { coeffs := LeanInf.mergeAdd x.infinite.coeffs      y.infinite.coeffs }
    _pf_infinitesimal_keys_negative := by
      -- mergeAdd preserves negative keys when both inputs do
      refine (LeanInf.keysNeg_mergeAdd (a := x.infinitesimal.coeffs) (b := y.infinitesimal.coeffs) (ha := ?_) (hb := ?_)) ?_ ?_ ?_
      · exact inferInstance
      · exact inferInstance
      · intro e' hc; exact x._pf_infinitesimal_keys_negative e' hc
      · intro e' hc; exact y._pf_infinitesimal_keys_negative e' hc
    _pf_infinite_keys_positive := by
      -- mergeAdd preserves positive keys when both inputs do
      refine (LeanInf.keysPos_mergeAdd (a := x.infinite.coeffs) (b := y.infinite.coeffs) (ha := ?_) (hb := ?_)) ?_ ?_ ?_
      · exact inferInstance
      · exact inferInstance
      · intro e' hc; exact x._pf_infinite_keys_positive e' hc
      · intro e' hc; exact y._pf_infinite_keys_positive e' hc }

/-- Proven subtraction via addP and negP. -/
def subP (x y : LeviCivitaNum) : LeviCivitaNum := addP x (negP y)

end LeviCivitaNum
