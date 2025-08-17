import LeanInf.LeviCivitaNum
import LeanInf.Basic

open LeviCivitaNum

namespace LeanInf

/-! Lemma skeletons for sign/invariant preservation. We will discharge them using
    mvcgen/grind once structures stabilize. For now, these are placeholders to
    make proof obligations explicit and localized. -/

-- HashMap-level helpers
theorem all_neg_insert
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e < 0)) = true)
    (e : Exponent) (he : e < 0) (c : Coeff)
  : (m.insert e c).all (fun e' _ => decide (e' < 0)) = true := by
  -- grind on fold/insert once available
  sorry

theorem all_pos_insert
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e > 0)) = true)
    (e : Exponent) (he : e > 0) (c : Coeff)
  : (m.insert e c).all (fun e' _ => decide (e' > 0)) = true := by
  sorry

theorem all_neg_merge
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e < 0)) = true)
    (hb : b.all (fun e _ => decide (e < 0)) = true)
    (f : Exponent → Coeff → Coeff → Coeff)
  : (Std.HashMap.mergeWith a b f).all (fun e _ => decide (e < 0)) = true := by
  sorry

theorem all_pos_merge
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e > 0)) = true)
    (hb : b.all (fun e _ => decide (e > 0)) = true)
    (f : Exponent → Coeff → Coeff → Coeff)
  : (Std.HashMap.mergeWith a b f).all (fun e _ => decide (e > 0)) = true := by
  sorry

-- Specialized merges used in code: combining coefficients by addition
theorem all_neg_merge_add
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e < 0)) = true)
    (hb : b.all (fun e _ => decide (e < 0)) = true)
  : (Std.HashMap.mergeWith a b (fun _ x y => x + y)).all (fun e _ => decide (e < 0)) = true := by
  sorry

theorem all_pos_merge_add
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e > 0)) = true)
    (hb : b.all (fun e _ => decide (e > 0)) = true)
  : (Std.HashMap.mergeWith a b (fun _ x y => x + y)).all (fun e _ => decide (e > 0)) = true := by
  sorry

-- Mapping values does not affect key-based invariants
theorem all_neg_map_values
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e < 0)) = true)
    (g : Coeff → Coeff)
  : (m.map (fun _ v => g v)).all (fun e _ => decide (e < 0)) = true := by
  sorry

theorem all_pos_map_values
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e > 0)) = true)
    (g : Coeff → Coeff)
  : (m.map (fun _ v => g v)).all (fun e _ => decide (e > 0)) = true := by
  sorry

-- Sign preservation at the LC level (skeletons)
theorem sign_preserved_by_infinitesimal_insert
    (x : LeviCivitaNum)
    (e : Exponent) (c : Coeff)
    (hneg : e < 0)
    (hle : ∀ e', x.infinitesimal.coeffs.contains e' → e ≤ e')
  : (signum x) = (signum { x with infinitesimal := ⟨x.infinitesimal.coeffs.insert e c⟩ }) := by
  -- Will follow from ordering of exponents and first-nonzero-term reasoning
  sorry

theorem sign_preserved_by_infinite_insert
    (x : LeviCivitaNum)
    (e : Exponent) (c : Coeff)
    (hpos : e > 0)
    (hle : ∀ e', x.infinite.coeffs.contains e' → e ≥ e')
  : (signum x) = (signum { x with infinite := ⟨x.infinite.coeffs.insert e c⟩ }) := by
  sorry

end LeanInf
