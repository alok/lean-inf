import Init.Data.Rat
import Init.Data.Hashable
import Init.Data.LawfulHashable
import Init.Data.Order.Classes
import Init.Data.Order.ClassesExtra
import Init.Data.Order.Ord
import Init.Data.Order.Factories
import Init.Data.Order.FactoriesExtra
import Init.Data.Order.Lemmas
import Init.Data.Order.LemmasExtra
import LeanInf.VerifiedRefactor

/-!
# Ergonomic Lean 4.36 Typeclasses & Order Theory for `FastLC`

Zero-Mathlib, zero-`sorry` instances and verified algebraic/order lemmas for `LeanInf.FastLC`:
- Equality & hashing: `LawfulBEq`, `DecidableEq`, `Hashable`, `LawfulHashable`
- Casts & coercions: `NatCast`, `IntCast`, `Coe Nat FastLC`, `Coe Int FastLC` (alongside existing
  `OfNat FastLC n`, `Coe Rat FastLC`, `OfScientific FastLC`, `Inhabited`, `Repr`, `ToString`)
- Fast `O(n)` scalar multiplication: `SMul Nat`, `SMul Int`, `SMul Rat` / `HSMul Rat` via `scaleRat`
- Exact signum algebra (`signum_trichotomy`, `signum_neg`, `signum_add_pos`, `signum_mul`) and
  integral domain cancellation (`mul_eq_zero_iff`)
- Linear order & fast `O(min(|x|, |y|))` lexicographic `Ord`, `Min`, `Max` with all `Std` lawful
  order/ord/min/max typeclasses (`Std.IsLinearOrder`, `Std.LawfulOrderLT`, `Std.LawfulOrderBEq`,
  `Std.LawfulOrderOrd`, `Std.OrientedOrd`, `Std.TransOrd`, `Std.LawfulEqOrd`, `Std.LawfulBEqOrd`,
  `Std.LawfulOrderMin`, `Std.LawfulOrderMax`)
-/

namespace LeanInf

namespace TermList

/-! ### Fast `O(min(|xs|, |ys|))` Lexicographic Comparison on Canonical `TermList` -/

/-- Direct `O(min(|xs|, |ys|))` zero-allocation lexicographic comparison of two canonical
    strictly-descending `TermList` values in the non-Archimedean Levi-Civita order. -/
def compareFast : TermList → TermList → Ordering
  | [], [] => .eq
  | [], (_, cy) :: _ => if cy > 0 then .lt else .gt
  | (_, cx) :: _, [] => if cx > 0 then .gt else .lt
  | (ex, cx) :: rx, (ey, cy) :: ry =>
    match ratCmpFast ex ey with
    | .gt => if cx > 0 then .gt else .lt
    | .lt => if cy > 0 then .lt else .gt
    | .eq =>
      match ratCmpFast cx cy with
      | .gt => .gt
      | .lt => .lt
      | .eq => compareFast rx ry

private theorem ratCmpFast_eq {a b : Rat} (h : ratCmpFast a b = .eq) : a = b := by
  have hngt : ¬ (a > b) := by
    intro hgt
    have := (ratCmpFast_gt a b).mpr hgt
    rw [h] at this
    cases this
  have hnlt : ¬ (b > a) := by
    intro hlt
    have := (ratCmpFast_lt a b).mpr hlt
    rw [h] at this
    cases this
  grind

/-- `compareFast` agrees identically with the sign of `subFast xs ys` on canonical `WF` lists. -/
theorem compareFast_eq_signum_sub {xs ys : TermList} (hxs : WF xs) (hys : WF ys) :
    compareFast xs ys =
      let s := signumFast (subFast xs ys)
      if s < 0 then .lt else if s > 0 then .gt else .eq := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil =>
      simp [compareFast, subFast, addMerge, negFast, signumFast]
    | cons py ry =>
      rcases py with ⟨ey, cy⟩
      have hcy : cy ≠ 0 := hys.1
      have hsub : subFast [] ((ey, cy) :: ry) = (ey, -cy) :: negFast ry := by
        simp [subFast, addMerge, negFast]
      rw [hsub]
      simp only [compareFast, signumFast]
      by_cases hpos : cy > 0
      · have hneg : ¬ (-cy > 0) := by grind
        simp [hpos, hneg]
      · have hneg : -cy > 0 := by grind
        simp [hpos, hneg]
  | cons px rx ih =>
    rcases px with ⟨ex, cx⟩
    cases ys with
    | nil =>
      have hcx : cx ≠ 0 := hxs.1
      have hsub : subFast ((ex, cx) :: rx) [] = (ex, cx) :: rx := by
        simp [subFast, addMerge, negFast]
      rw [hsub]
      simp only [compareFast, signumFast]
      by_cases hpos : cx > 0 <;> simp [hpos]
    | cons py ry =>
      rcases py with ⟨ey, cy⟩
      have hsubWF : WF (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) := subFast_wf hxs hys
      simp only [compareFast]
      cases hcmpE : ratCmpFast ex ey with
      | gt =>
        have hex : ex > ey := (ratCmpFast_gt ex ey).mp hcmpE
        have hdom : ∀ e > ex, coeffOf (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) e = 0 := by
          intro e he
          rw [coeffOf_subFast, coeffOf_eq_zero_of_gt_head hxs he,
              coeffOf_eq_zero_of_gt_head hys (by grind)]
          grind
        have hhead : coeffOf (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) ex = cx := by
          rw [coeffOf_subFast, coeffOf_cons_head_of_wf hxs, coeffOf_eq_zero_of_gt_head hys hex]
          grind
        by_cases hpos : cx > 0
        · have hs : signumFast (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) = 1 :=
            (signumFast_eq_one_iff hsubWF).mpr ⟨ex, by rw [hhead]; exact hpos, hdom⟩
          simp [hpos, hs]
        · have hneg : cx < 0 := by have := hxs.1; grind
          have hs : signumFast (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) = -1 :=
            (signumFast_eq_neg_one_iff hsubWF).mpr ⟨ex, by rw [hhead]; exact hneg, hdom⟩
          simp [hpos, hs]
      | lt =>
        have hey : ey > ex := (ratCmpFast_lt ex ey).mp hcmpE
        have hdom : ∀ e > ey, coeffOf (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) e = 0 := by
          intro e he
          rw [coeffOf_subFast, coeffOf_eq_zero_of_gt_head hxs (by grind),
              coeffOf_eq_zero_of_gt_head hys he]
          grind
        have hhead : coeffOf (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) ey = -cy := by
          rw [coeffOf_subFast, coeffOf_eq_zero_of_gt_head hxs hey, coeffOf_cons_head_of_wf hys]
          grind
        by_cases hpos : cy > 0
        · have hneg : -cy < 0 := by grind
          have hs : signumFast (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) = -1 :=
            (signumFast_eq_neg_one_iff hsubWF).mpr ⟨ey, by rw [hhead]; exact hneg, hdom⟩
          simp [hpos, hs]
        · have hneg : -cy > 0 := by have := hys.1; grind
          have hs : signumFast (subFast ((ex, cx) :: rx) ((ey, cy) :: ry)) = 1 :=
            (signumFast_eq_one_iff hsubWF).mpr ⟨ey, by rw [hhead]; exact hneg, hdom⟩
          simp [hpos, hs]
      | eq =>
        have heqE : ex = ey := ratCmpFast_eq hcmpE
        subst heqE
        cases hcmpC : ratCmpFast cx cy with
        | gt =>
          have hgtC : cx > cy := (ratCmpFast_gt cx cy).mp hcmpC
          have hdom : ∀ e > ex, coeffOf (subFast ((ex, cx) :: rx) ((ex, cy) :: ry)) e = 0 := by
            intro e he
            rw [coeffOf_subFast, coeffOf_eq_zero_of_gt_head hxs he,
                coeffOf_eq_zero_of_gt_head hys he]
            grind
          have hhead : coeffOf (subFast ((ex, cx) :: rx) ((ex, cy) :: ry)) ex = cx - cy := by
            rw [coeffOf_subFast, coeffOf_cons_head_of_wf hxs, coeffOf_cons_head_of_wf hys]
          have hs : signumFast (subFast ((ex, cx) :: rx) ((ex, cy) :: ry)) = 1 :=
            (signumFast_eq_one_iff hsubWF).mpr ⟨ex, by rw [hhead]; grind, hdom⟩
          simp [hs]
        | lt =>
          have hltC : cy > cx := (ratCmpFast_lt cx cy).mp hcmpC
          have hdom : ∀ e > ex, coeffOf (subFast ((ex, cx) :: rx) ((ex, cy) :: ry)) e = 0 := by
            intro e he
            rw [coeffOf_subFast, coeffOf_eq_zero_of_gt_head hxs he,
                coeffOf_eq_zero_of_gt_head hys he]
            grind
          have hhead : coeffOf (subFast ((ex, cx) :: rx) ((ex, cy) :: ry)) ex = cx - cy := by
            rw [coeffOf_subFast, coeffOf_cons_head_of_wf hxs, coeffOf_cons_head_of_wf hys]
          have hs : signumFast (subFast ((ex, cx) :: rx) ((ex, cy) :: ry)) = -1 :=
            (signumFast_eq_neg_one_iff hsubWF).mpr ⟨ex, by rw [hhead]; grind, hdom⟩
          simp [hs]
        | eq =>
          have heqC : cx = cy := ratCmpFast_eq hcmpC
          subst heqC
          have hsubEq : subFast ((ex, cx) :: rx) ((ex, cx) :: ry) = subFast rx ry := by
            apply eq_of_wf_of_coeffOf_eq hsubWF (subFast_wf hxs.2.2 hys.2.2)
            intro e
            rw [coeffOf_subFast, coeffOf_subFast]
            simp only [coeffOf]
            split <;> grind
          rw [hsubEq]
          exact ih hxs.2.2 hys.2.2

end TermList

namespace FastLC

/-! ### Equality, Decidability & Hashing -/

/-- `BEq` on `FastLC` is lawful because canonical term lists uniquely determine elements. -/
instance : LawfulBEq FastLC where
  eq_of_beq h := (beq_iff_eq _ _).mp h
  rfl := (beq_iff_eq _ _).mpr rfl

/-- Decidable propositional equality on `FastLC` via canonical term-list comparison. -/
instance : DecidableEq FastLC := fun x y =>
  if h : x == y then isTrue ((beq_iff_eq x y).mp h)
  else isFalse fun heq => h ((beq_iff_eq x y).mpr heq)

/-- Structural hash on canonical `FastLC` term lists (enables `Std.HashMap`/`Std.HashSet`). -/
instance : Hashable FastLC where
  hash x := hash x.terms

/-- `Hashable FastLC` is lawful because `BEq FastLC` coincides with propositional equality. -/
instance : LawfulHashable FastLC where
  hash_eq _ _ h := by rw [eq_of_beq h]

/-! ### Coefficient & Rational Embedding Lemmas -/

/-- Exact coefficient of a monomial `mono e0 c`. -/
@[simp] theorem coeff_mono (e0 c e : Rat) :
    (mono e0 c).coeff e = if e0 == e then c else 0 := by
  unfold mono
  split
  · rename_i h
    have hc : c = 0 := eq_of_beq h
    subst hc
    simp [zero, coeff, TermList.coeffOf]
  · simp [coeff, TermList.coeffOf, Rat.add_zero]

/-- Exact coefficient of an embedded rational `ofRat r`. -/
@[simp] theorem coeff_ofRat (r e : Rat) :
    (ofRat r).coeff e = if (0 : Rat) == e then r else 0 :=
  coeff_mono 0 r e

/-- Exact coefficient of the infinite hypernatural unit `infH = H^1`. -/
@[simp] theorem coeff_infH (e : Rat) :
    infH.coeff e = if (1 : Rat) == e then 1 else 0 := by
  simp [infH, coeff, TermList.coeffOf, Rat.add_zero]

/-- Exact coefficient of the positive infinitesimal unit `infEps = H^(-1)`. -/
@[simp] theorem coeff_infEps (e : Rat) :
    infEps.coeff e = if (-1 : Rat) == e then 1 else 0 := by
  simp [infEps, coeff, TermList.coeffOf, Rat.add_zero]

/-- `ofRat 0 = 0`. -/
@[simp] theorem ofRat_zero : ofRat 0 = 0 := rfl

/-- `ofRat 1 = 1`. -/
@[simp] theorem ofRat_one : ofRat 1 = 1 := rfl

/-- `ofRat` preserves negation. -/
theorem ofRat_neg (r : Rat) : ofRat (-r) = -ofRat r := by
  ext e
  simp only [coeff_ofRat, coeff_neg]
  split <;> simp

/-- `ofRat` preserves addition. -/
theorem ofRat_add (a b : Rat) : ofRat (a + b) = ofRat a + ofRat b := by
  ext e
  simp only [coeff_ofRat, coeff_add]
  split <;> grind

/-- `ofRat` preserves subtraction. -/
theorem ofRat_sub (a b : Rat) : ofRat (a - b) = ofRat a - ofRat b := by
  ext e
  simp only [coeff_ofRat, coeff_sub]
  split <;> grind

/-- `ofRat` preserves multiplication. -/
theorem ofRat_mul (a b : Rat) : ofRat (a * b) = ofRat a * ofRat b := by
  ext e
  rw [coeff_ofRat, coeff_mul]
  change (if (0 : Rat) == e then a * b else 0) =
    TermList.coeffOf (TermList.mulNaiveTerms (ofRat a).terms (ofRat b).terms) e
  by_cases ha : (a == 0) = true
  · have ha0 : a = 0 := eq_of_beq ha
    subst ha0
    have hterms : (ofRat 0).terms = [] := rfl
    rw [hterms, TermList.coeffOf_mulNaiveTerms_nil]
    split <;> simp
  · have hterms : (ofRat a).terms = [(0, a)] := by
      unfold ofRat mono; simp [ha]
    rw [hterms, TermList.coeffOf_mulNaiveTerms_cons, TermList.coeffOf_mulNaiveTerms_nil, Rat.add_zero]
    have hsub : e - (0 : Rat) = e := by grind
    rw [hsub]
    change (if (0 : Rat) == e then a * b else 0) = a * (ofRat b).coeff e
    rw [coeff_ofRat]
    split <;> simp

/-- `ofRat : Rat → FastLC` is injective. -/
theorem ofRat_injective : Function.Injective ofRat := by
  intro a b h
  have h0 := congrArg (fun x : FastLC => x.coeff 0) h
  simpa [coeff_ofRat] using h0

/-! ### Natural, Integer & Rational Casts and Coercions -/

/-- Canonical embedding of natural numbers into `FastLC`. -/
instance : NatCast FastLC where
  natCast n := ofRat (n : Rat)

/-- Canonical embedding of integers into `FastLC`. -/
instance : IntCast FastLC where
  intCast i := ofRat (i : Rat)

/-- Coercion from `Nat` to `FastLC`. -/
instance : Coe Nat FastLC where
  coe n := ofRat (n : Rat)

/-- Coercion from `Int` to `FastLC`. -/
instance : Coe Int FastLC where
  coe i := ofRat (i : Rat)

/-- `OfNat.ofNat 0 = 0` on `FastLC`. -/
theorem ofNat_zero : (OfNat.ofNat 0 : FastLC) = 0 := rfl

/-- `OfNat.ofNat 1 = 1` on `FastLC`. -/
theorem ofNat_one : (OfNat.ofNat 1 : FastLC) = 1 := rfl

/-- `OfNat.ofNat (n + 1) = OfNat.ofNat n + 1` on `FastLC`. -/
theorem ofNat_succ (n : Nat) :
    (OfNat.ofNat (n + 1) : FastLC) = OfNat.ofNat n + 1 := by
  change ofRat (((n + 1 : Nat) : Int) : Rat) = ofRat (((n : Nat) : Int) : Rat) + ofRat 1
  rw [← ofRat_add]
  congr 1
  simp

/-- `Nat.cast` agrees definitionally with `OfNat.ofNat` on `FastLC`. -/
theorem ofNat_eq_natCast (n : Nat) : (OfNat.ofNat n : FastLC) = (n : FastLC) := rfl

/-- `Int.cast` on nonnegative integers agrees definitionally with `OfNat.ofNat`. -/
theorem intCast_ofNat (n : Nat) : ((OfNat.ofNat n : Int) : FastLC) = OfNat.ofNat n := rfl

/-- `Int.cast` preserves negation on `FastLC`. -/
theorem intCast_neg (i : Int) : ((-i : Int) : FastLC) = -(i : FastLC) := by
  change ofRat ((-i : Int) : Rat) = -ofRat (i : Rat)
  rw [Rat.intCast_neg, ofRat_neg]

/-! ### Verified `O(n)` Scalar Multiplication (`SMul Nat`, `SMul Int`, `SMul Rat` / `HSMul Rat`) -/

/-- Verified `O(n)` scalar multiplication of a `FastLC` by a rational `r`. -/
def scaleRat (r : Rat) (x : FastLC) : FastLC :=
  ⟨TermList.scaleTerm 0 r x.terms, TermList.scaleTerm_wf x.wf⟩

/-- Exact coefficient of `x.scaleRat r`. -/
@[simp] theorem coeff_scaleRat (r : Rat) (x : FastLC) (e : Rat) :
    (x.scaleRat r).coeff e = r * x.coeff e := by
  change TermList.coeffOf (TermList.scaleTerm 0 r x.terms) e = r * TermList.coeffOf x.terms e
  rw [TermList.coeffOf_scaleTerm]
  have hsub : e - (0 : Rat) = e := by grind
  rw [hsub]

/-- `O(n)` rational scaling agrees identically with ring multiplication by `ofRat r`. -/
theorem scaleRat_eq_ofRat_mul (r : Rat) (x : FastLC) :
    x.scaleRat r = ofRat r * x := by
  ext e
  rw [coeff_scaleRat, coeff_mul]
  unfold ofRat mono
  split
  · rename_i h
    have hr : r = 0 := eq_of_beq h
    subst hr
    simp [zero, TermList.coeffOf_mulNaiveTerms_nil]
  · rw [TermList.coeffOf_mulNaiveTerms_cons, TermList.coeffOf_mulNaiveTerms_nil, Rat.add_zero]
    have hsub : e - (0 : Rat) = e := by grind
    rw [hsub]; rfl

/-- `O(n)` natural-number scalar multiplication on `FastLC`. -/
instance : SMul Nat FastLC where
  smul n x := x.scaleRat (n : Rat)

/-- `O(n)` integer scalar multiplication on `FastLC`. -/
instance : SMul Int FastLC where
  smul i x := x.scaleRat (i : Rat)

/-- `O(n)` rational scalar multiplication on `FastLC` (also synthesizes `HSMul Rat FastLC FastLC`). -/
instance : SMul Rat FastLC where
  smul r x := x.scaleRat r

/-- Natural scalar multiplication equals multiplication by the natural cast. -/
theorem nsmul_eq_natCast_mul (n : Nat) (x : FastLC) : n • x = (n : FastLC) * x :=
  scaleRat_eq_ofRat_mul (n : Rat) x

/-- Integer scalar multiplication equals multiplication by the integer cast. -/
theorem zsmul_eq_intCast_mul (i : Int) (x : FastLC) : i • x = (i : FastLC) * x :=
  scaleRat_eq_ofRat_mul (i : Rat) x

/-- Rational scalar multiplication equals multiplication by `ofRat r`. -/
theorem qsmul_eq_ofRat_mul (r : Rat) (x : FastLC) : r • x = ofRat r * x :=
  scaleRat_eq_ofRat_mul r x

/-- Multiplication commutes with unary negation on the left. -/
theorem neg_mul (x y : FastLC) : (-x) * y = -(x * y) := by
  have h : (-x) * y + x * y = 0 := by
    rw [← add_mul, neg_add_cancel, zero_mul]
  have h2 : (-x) * y + x * y + -(x * y) = 0 + -(x * y) := congrArg (· + -(x * y)) h
  rw [add_assoc, add_neg_cancel, add_zero, zero_add] at h2
  exact h2

/-- Multiplication commutes with unary negation on the right. -/
theorem mul_neg (x y : FastLC) : x * (-y) = -(x * y) := by
  rw [mul_comm, neg_mul, mul_comm]

/-! ### Signum Algebra & Integral Domain Cancellation -/

/-- `FastLC.signum` only ever takes values in `{-1, 0, 1}`. -/
theorem signum_trichotomy (x : FastLC) :
    x.signum = -1 ∨ x.signum = 0 ∨ x.signum = 1 := by
  unfold signum TermList.signumFast
  cases x.terms with
  | nil => exact Or.inr (Or.inl rfl)
  | cons p rest =>
    rcases p with ⟨e, c⟩
    dsimp only
    split
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl

/-- `x.signum = 0` iff `x = 0`. -/
theorem signum_eq_zero_iff (x : FastLC) : x.signum = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hall := (TermList.signumFast_eq_zero_iff x.wf).mp h
    ext e
    exact hall e
  · rintro rfl
    rfl

/-- `(0 : FastLC).signum = 0`. -/
@[simp] theorem signum_zero : (0 : FastLC).signum = 0 := rfl

/-- `(1 : FastLC).signum = 1`. -/
@[simp] theorem signum_one : (1 : FastLC).signum = 1 := by decide

/-- `infH.signum = 1`. -/
@[simp] theorem signum_infH : infH.signum = 1 := by decide

/-- `infEps.signum = 1`. -/
@[simp] theorem signum_infEps : infEps.signum = 1 := by decide

/-- Exact signum of an embedded rational `ofRat r`. -/
theorem signum_ofRat (r : Rat) :
    (ofRat r).signum = if r > 0 then 1 else if r < 0 then -1 else 0 := by
  unfold signum ofRat mono
  split
  · rename_i hz
    have hr : r = 0 := eq_of_beq hz
    subst hr
    simp [zero, TermList.signumFast]
  · rename_i hnz
    have hr : r ≠ 0 := by intro h; simp [h] at hnz
    simp only [TermList.signumFast]
    by_cases hpos : r > 0
    · simp [hpos]
    · have hneg : r < 0 := by grind
      simp [hpos, hneg]

/-- Negating a `FastLC` negates its signum. -/
theorem signum_neg (x : FastLC) : (-x).signum = -x.signum := by
  rcases x with ⟨ts, hwf⟩
  cases ts with
  | nil =>
    change TermList.signumFast (TermList.negFast []) = -TermList.signumFast []
    rfl
  | cons p rest =>
    rcases p with ⟨e, c⟩
    change TermList.signumFast (TermList.negFast ((e, c) :: rest)) =
      -TermList.signumFast ((e, c) :: rest)
    simp only [TermList.negFast, List.map_cons, TermList.signumFast]
    have hne : c ≠ 0 := hwf.1
    by_cases hpos : c > 0
    · have hneg : ¬ (-c > 0) := by grind
      simp [hpos, hneg]
    · have hneg : -c > 0 := by grind
      simp [hpos, hneg]

/-- The sum of two strictly positive `FastLC` numbers is strictly positive. -/
theorem signum_add_pos {x y : FastLC} (hx : x.signum = 1) (hy : y.signum = 1) :
    (x + y).signum = 1 := by
  rcases (TermList.signumFast_eq_one_iff x.wf).mp hx with ⟨ex, hcx, hdomX⟩
  rcases (TermList.signumFast_eq_one_iff y.wf).mp hy with ⟨ey, hcy, hdomY⟩
  apply (TermList.signumFast_eq_one_iff (x + y).wf).mpr
  by_cases hgt : ex > ey
  · refine ⟨ex, ?_, ?_⟩
    · change (x + y).coeff ex > 0
      rw [coeff_add]
      have hy0 : y.coeff ex = 0 := hdomY ex hgt
      change TermList.coeffOf x.terms ex + y.coeff ex > 0
      rw [hy0]; grind
    · intro e he
      change (x + y).coeff e = 0
      rw [coeff_add]
      have hx0 : x.coeff e = 0 := hdomX e he
      have hy0 : y.coeff e = 0 := hdomY e (by grind)
      rw [hx0, hy0]; grind
  · by_cases hlt : ey > ex
    · refine ⟨ey, ?_, ?_⟩
      · change (x + y).coeff ey > 0
        rw [coeff_add]
        have hx0 : x.coeff ey = 0 := hdomX ey hlt
        change x.coeff ey + TermList.coeffOf y.terms ey > 0
        rw [hx0]; grind
      · intro e he
        change (x + y).coeff e = 0
        rw [coeff_add]
        have hx0 : x.coeff e = 0 := hdomX e (by grind)
        have hy0 : y.coeff e = 0 := hdomY e he
        rw [hx0, hy0]; grind
    · have heq : ex = ey := by grind
      subst heq
      refine ⟨ex, ?_, ?_⟩
      · change (x + y).coeff ex > 0
        rw [coeff_add]
        change TermList.coeffOf x.terms ex + TermList.coeffOf y.terms ex > 0
        grind
      · intro e he
        change (x + y).coeff e = 0
        rw [coeff_add]
        have hx0 : x.coeff e = 0 := hdomX e he
        have hy0 : y.coeff e = 0 := hdomY e he
        rw [hx0, hy0]; grind

private theorem coeffOf_mulNaiveTerms_eq_zero_of_allLt_left {bx by_ e : Rat}
    {xs ys : TermList} (hxs : TermList.AllLt bx xs)
    (hys : ∀ ey, ey > by_ → TermList.coeffOf ys ey = 0)
    (he : bx + by_ ≤ e) :
    TermList.coeffOf (TermList.mulNaiveTerms xs ys) e = 0 := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    rw [TermList.coeffOf_mulNaiveTerms_cons]
    have hgt : e - ex > by_ := by
      have : ex < bx := hxs.1
      grind
    rw [hys (e - ex) hgt, Rat.mul_zero, Rat.zero_add]
    exact ih hxs.2

/-- Signum is multiplicative on `FastLC`: `(x * y).signum = x.signum * y.signum`. -/
theorem signum_mul (x y : FastLC) : (x * y).signum = x.signum * y.signum := by
  rcases x with ⟨xs, hxs⟩
  rcases y with ⟨ys, hys⟩
  cases xs with
  | nil =>
    have hx0 : (⟨[], hxs⟩ : FastLC) = 0 := rfl
    rw [hx0, zero_mul]
    simp
  | cons px rx =>
    rcases px with ⟨ex, cx⟩
    cases ys with
    | nil =>
      have hy0 : (⟨[], hys⟩ : FastLC) = 0 := rfl
      rw [hy0, mul_zero]
      simp
    | cons py ry =>
      rcases py with ⟨ey, cy⟩
      let x : FastLC := ⟨(ex, cx) :: rx, hxs⟩
      let y : FastLC := ⟨(ey, cy) :: ry, hys⟩
      change (x * y).signum = x.signum * y.signum
      have hdomY : ∀ e, e > ey → TermList.coeffOf ((ey, cy) :: ry) e = 0 :=
        fun e he => TermList.coeffOf_eq_zero_of_gt_head hys he
      have hlead : (x * y).coeff (ex + ey) = cx * cy := by
        rw [coeff_mul]
        change TermList.coeffOf (TermList.mulNaiveTerms ((ex, cx) :: rx) ((ey, cy) :: ry)) (ex + ey) = cx * cy
        rw [TermList.coeffOf_mulNaiveTerms_cons]
        have hsub : ex + ey - ex = ey := by grind
        rw [hsub, TermList.coeffOf_cons_head_of_wf hys]
        have htail : TermList.coeffOf (TermList.mulNaiveTerms rx ((ey, cy) :: ry)) (ex + ey) = 0 :=
          coeffOf_mulNaiveTerms_eq_zero_of_allLt_left hxs.2.1 hdomY (by grind)
        rw [htail, Rat.add_zero]
      have hdomXY : ∀ e > ex + ey, (x * y).coeff e = 0 := by
        intro e he
        rw [coeff_mul]
        change TermList.coeffOf (TermList.mulNaiveTerms ((ex, cx) :: rx) ((ey, cy) :: ry)) e = 0
        rw [TermList.coeffOf_mulNaiveTerms_cons]
        have hy0 : TermList.coeffOf ((ey, cy) :: ry) (e - ex) = 0 :=
          hdomY (e - ex) (by grind)
        have htail : TermList.coeffOf (TermList.mulNaiveTerms rx ((ey, cy) :: ry)) e = 0 :=
          coeffOf_mulNaiveTerms_eq_zero_of_allLt_left hxs.2.1 hdomY (by grind)
        rw [hy0, Rat.mul_zero, Rat.zero_add, htail]
      have hcxNe : cx ≠ 0 := hxs.1
      have hcyNe : cy ≠ 0 := hys.1
      by_cases hcx : cx > 0 <;> by_cases hcy : cy > 0
      · have hprod : cx * cy > 0 := by
          have : (0 : Rat) < cx := hcx
          have : (0 : Rat) < cy := hcy
          exact Rat.mul_pos ‹_› ‹_›
        have h1 : (x * y).signum = 1 :=
          (TermList.signumFast_eq_one_iff (x * y).wf).mpr ⟨ex + ey, by rw [← hlead] at hprod; exact hprod, hdomXY⟩
        have hx1 : x.signum = 1 := by simp [x, signum, TermList.signumFast, hcx]
        have hy1 : y.signum = 1 := by simp [y, signum, TermList.signumFast, hcy]
        rw [h1, hx1, hy1]; rfl
      · have hcyNeg : cy < 0 := by grind
        have hprod : cx * cy < 0 := by
          have hpos : (0 : Rat) < cx * (-cy) := Rat.mul_pos hcx (by grind)
          grind
        have h1 : (x * y).signum = -1 :=
          (TermList.signumFast_eq_neg_one_iff (x * y).wf).mpr ⟨ex + ey, by rw [← hlead] at hprod; exact hprod, hdomXY⟩
        have hx1 : x.signum = 1 := by simp [x, signum, TermList.signumFast, hcx]
        have hy1 : y.signum = -1 := by simp [y, signum, TermList.signumFast, hcy]
        rw [h1, hx1, hy1]; rfl
      · have hcxNeg : cx < 0 := by grind
        have hprod : cx * cy < 0 := by
          have hpos : (0 : Rat) < (-cx) * cy := Rat.mul_pos (by grind) hcy
          grind
        have h1 : (x * y).signum = -1 :=
          (TermList.signumFast_eq_neg_one_iff (x * y).wf).mpr ⟨ex + ey, by rw [← hlead] at hprod; exact hprod, hdomXY⟩
        have hx1 : x.signum = -1 := by simp [x, signum, TermList.signumFast, hcx]
        have hy1 : y.signum = 1 := by simp [y, signum, TermList.signumFast, hcy]
        rw [h1, hx1, hy1]; rfl
      · have hcxNeg : cx < 0 := by grind
        have hcyNeg : cy < 0 := by grind
        have hprod : cx * cy > 0 := by
          have hpos : (0 : Rat) < (-cx) * (-cy) := Rat.mul_pos (by grind) (by grind)
          grind
        have h1 : (x * y).signum = 1 :=
          (TermList.signumFast_eq_one_iff (x * y).wf).mpr ⟨ex + ey, by rw [← hlead] at hprod; exact hprod, hdomXY⟩
        have hx1 : x.signum = -1 := by simp [x, signum, TermList.signumFast, hcx]
        have hy1 : y.signum = -1 := by simp [y, signum, TermList.signumFast, hcy]
        rw [h1, hx1, hy1]; rfl

/-- `FastLC` is an integral domain: `x * y = 0` iff `x = 0 ∨ y = 0`. -/
theorem mul_eq_zero_iff {x y : FastLC} : x * y = 0 ↔ x = 0 ∨ y = 0 := by
  rw [← signum_eq_zero_iff, signum_mul, Int.mul_eq_zero, signum_eq_zero_iff, signum_eq_zero_iff]

/-! ### Linear Order & `Std` Order Typeclasses -/

private theorem neg_sub (a b : FastLC) : -(a - b) = b - a := by
  ext e; simp; grind

private theorem sub_add_sub (a b c : FastLC) : (a - b) + (b - c) = a - c := by
  ext e; simp; grind

private theorem sub_eq_zero_iff (a b : FastLC) : a - b = 0 ↔ a = b := by
  constructor
  · intro h
    ext e
    have he := congrArg (fun x : FastLC => x.coeff e) h
    simp only [coeff_sub, coeff_zero] at he
    grind
  · rintro rfl
    rw [sub_eq_add_neg, add_neg_cancel]

/-- `FastLC` forms a linear order under its lexicographic non-Archimedean ordering `≤`. -/
instance : Std.IsLinearOrder FastLC where
  le_refl x := by
    show (x - x).signum ≤ 0
    rw [sub_eq_add_neg, add_neg_cancel]; decide
  le_trans a b c hab hbc := by
    show (a - c).signum ≤ 0
    have hab' : (a - b).signum ≤ 0 := hab
    have hbc' : (b - c).signum ≤ 0 := hbc
    rcases signum_trichotomy (a - b) with h1 | h1 | h1
    · rcases signum_trichotomy (b - c) with h2 | h2 | h2
      · have hp1 : (b - a).signum = 1 := by
          rw [← neg_sub a b, signum_neg, h1]; rfl
        have hp2 : (c - b).signum = 1 := by
          rw [← neg_sub b c, signum_neg, h2]; rfl
        have hsum : (c - a).signum = 1 := by
          have heq : (c - b) + (b - a) = c - a := sub_add_sub c b a
          rw [← heq]
          exact signum_add_pos hp2 hp1
        have hneg : (a - c).signum = -1 := by
          have := signum_neg (c - a)
          rw [neg_sub, hsum] at this
          exact this
        omega
      · have hbcEq : b = c := (sub_eq_zero_iff b c).mp ((signum_eq_zero_iff (b - c)).mp h2)
        subst hbcEq; exact hab'
      · omega
    · have habEq : a = b := (sub_eq_zero_iff a b).mp ((signum_eq_zero_iff (a - b)).mp h1)
      subst habEq; exact hbc'
    · omega
  le_antisymm a b hab hba := by
    have h1 : (a - b).signum ≤ 0 := hab
    have h2 : (b - a).signum ≤ 0 := hba
    have hneg : (b - a).signum = -(a - b).signum := by
      rw [← neg_sub a b, signum_neg]
    have hz : (a - b).signum = 0 := by omega
    exact (sub_eq_zero_iff a b).mp ((signum_eq_zero_iff (a - b)).mp hz)
  le_total a b := by
    show (a - b).signum ≤ 0 ∨ (b - a).signum ≤ 0
    have hneg : (b - a).signum = -(a - b).signum := by
      rw [← neg_sub a b, signum_neg]
    rcases signum_trichotomy (a - b) with h | h | h <;> omega

/-- Strict order `<` on `FastLC` is compatible with `≤`. -/
instance : Std.LawfulOrderLT FastLC where
  lt_iff a b := by
    show (a - b).signum = -1 ↔ (a - b).signum ≤ 0 ∧ ¬ (b - a).signum ≤ 0
    have hneg : (b - a).signum = -(a - b).signum := by
      rw [← neg_sub a b, signum_neg]
    rcases signum_trichotomy (a - b) with h | h | h <;> omega

/-- Boolean equality `==` on `FastLC` is compatible with `≤`. -/
instance : Std.LawfulOrderBEq FastLC where
  beq_iff_le_and_ge a b := by
    rw [beq_iff_eq]
    constructor
    · rintro rfl
      exact ⟨Std.IsPreorder.le_refl a, Std.IsPreorder.le_refl a⟩
    · rintro ⟨h1, h2⟩
      exact Std.IsPartialOrder.le_antisymm a b h1 h2

/-! ### Fast `O(min(|x|, |y|))` `Ord`, `Min` & `Max` Instances -/

/-- Direct `O(min(|x|, |y|))` lexicographic comparison on `FastLC` (zero allocation). -/
def compareFast (x y : FastLC) : Ordering :=
  TermList.compareFast x.terms y.terms

/-- Fast `O(min(|x|, |y|))` `Ord` instance enabling `Std.TreeMap`, `Std.TreeSet`, and sorting. -/
instance : Ord FastLC where
  compare := compareFast

/-- `Ord FastLC` (`compareFast`) agrees with the canonical linear order `≤`. -/
instance : Std.LawfulOrderOrd FastLC where
  isLE_compare a b := by
    show (compareFast a b).isLE ↔ (a - b).signum ≤ 0
    have hcmp := TermList.compareFast_eq_signum_sub a.wf b.wf
    change compareFast a b =
      let s := (a - b).signum
      if s < 0 then .lt else if s > 0 then .gt else .eq at hcmp
    rw [hcmp]
    rcases signum_trichotomy (a - b) with hs | hs | hs <;> simp [hs]
  isGE_compare a b := by
    show (compareFast a b).isGE ↔ (b - a).signum ≤ 0
    have hcmp := TermList.compareFast_eq_signum_sub a.wf b.wf
    change compareFast a b =
      let s := (a - b).signum
      if s < 0 then .lt else if s > 0 then .gt else .eq at hcmp
    have hneg : (b - a).signum = -(a - b).signum := by
      rw [← neg_sub a b, signum_neg]
    rw [hcmp, hneg]
    rcases signum_trichotomy (a - b) with hs | hs | hs <;> simp [hs]

/-- Fast `O(min(|a|, |b|))` minimum of two `FastLC` numbers (left-leaning). -/
instance : Min FastLC where
  min a b := if (compareFast a b).isLE then a else b

/-- Fast `O(min(|a|, |b|))` maximum of two `FastLC` numbers (left-leaning). -/
instance : Max FastLC where
  max a b := if (compareFast b a).isLE then a else b

/-- `Min FastLC` is left-leaning with respect to `≤` (also synthesizes `Std.LawfulOrderMin`). -/
instance : Std.LawfulOrderLeftLeaningMin FastLC where
  min_eq_left a b h := by
    change (if (compare a b).isLE then a else b) = a
    simp [(Std.LawfulOrderOrd.isLE_compare a b).mpr h]
  min_eq_right a b h := by
    change (if (compare a b).isLE then a else b) = b
    simp [mt (Std.LawfulOrderOrd.isLE_compare a b).mp h]

/-- `Max FastLC` is left-leaning with respect to `≤` (also synthesizes `Std.LawfulOrderMax`). -/
instance : Std.LawfulOrderLeftLeaningMax FastLC where
  max_eq_left a b h := by
    change (if (compare b a).isLE then a else b) = a
    simp [(Std.LawfulOrderOrd.isLE_compare b a).mpr h]
  max_eq_right a b h := by
    change (if (compare b a).isLE then a else b) = b
    simp [mt (Std.LawfulOrderOrd.isLE_compare b a).mp h]

/-! ### Normalization Lemmas for `min`, `max`, `abs`, `isZero` -/

/-- Characterization of `min` via `≤`. -/
theorem min_def (a b : FastLC) : min a b = if a ≤ b then a else b := by
  by_cases h : a ≤ b
  · simp [h, Std.LawfulOrderLeftLeaningMin.min_eq_left a b h]
  · simp [h, Std.LawfulOrderLeftLeaningMin.min_eq_right a b h]

/-- Characterization of `max` via `≤`. -/
theorem max_def (a b : FastLC) : max a b = if b ≤ a then a else b := by
  by_cases h : b ≤ a
  · simp [h, Std.LawfulOrderLeftLeaningMax.max_eq_left a b h]
  · simp [h, Std.LawfulOrderLeftLeaningMax.max_eq_right a b h]

/-- Characterization of `FastLC.abs` via `< 0`. -/
theorem abs_def (x : FastLC) : x.abs = if x < 0 then -x else x := by
  unfold abs
  have hlt : x < 0 ↔ x.signum < 0 := by
    show (x - 0).signum = -1 ↔ x.signum < 0
    have hsub : x - 0 = x := by rw [sub_eq_add_neg]; change x + 0 = x; exact add_zero x
    rw [hsub]
    rcases signum_trichotomy x with h | h | h <;> omega
  by_cases h : x < 0
  · simp [h, hlt.mp h]
  · simp [h, mt hlt.mpr h]

/-- `x.isZero = true` iff `x = 0`. -/
theorem isZero_iff (x : FastLC) : x.isZero = true ↔ x = 0 := by
  rcases x with ⟨ts, hwf⟩
  cases ts with
  | nil => simp [isZero]; rfl
  | cons p rest =>
    simp only [isZero, List.isEmpty_cons, Bool.false_eq_true, false_iff]
    intro h
    have := congrArg FastLC.terms h
    cases this

/-! ### Compile-Time Typeclass Synthesis Checks -/

section SynthesisChecks

example (n : Nat) : OfNat FastLC n := inferInstance
example : NatCast FastLC := inferInstance
example : IntCast FastLC := inferInstance
example : Coe Nat FastLC := inferInstance
example : Coe Int FastLC := inferInstance
example : Coe Rat FastLC := inferInstance
example : Inhabited FastLC := inferInstance
example : DecidableEq FastLC := inferInstance
example : BEq FastLC := inferInstance
example : LawfulBEq FastLC := inferInstance
example : Hashable FastLC := inferInstance
example : LawfulHashable FastLC := inferInstance
example : SMul Nat FastLC := inferInstance
example : SMul Int FastLC := inferInstance
example : SMul Rat FastLC := inferInstance
example : HSMul Rat FastLC FastLC := inferInstance
example : Ord FastLC := inferInstance
example : Std.OrientedOrd FastLC := inferInstance
example : Std.TransOrd FastLC := inferInstance
example : Std.LawfulEqOrd FastLC := inferInstance
example : Std.LawfulBEqOrd FastLC := inferInstance
example : Std.LawfulOrderOrd FastLC := inferInstance
example : LT FastLC := inferInstance
example : LE FastLC := inferInstance
example : DecidableLT FastLC := inferInstance
example : DecidableLE FastLC := inferInstance
example : Std.IsLinearOrder FastLC := inferInstance
example : Std.LawfulOrderLT FastLC := inferInstance
example : Std.LawfulOrderBEq FastLC := inferInstance
example : Min FastLC := inferInstance
example : Max FastLC := inferInstance
example : Std.LawfulOrderMin FastLC := inferInstance
example : Std.LawfulOrderMax FastLC := inferInstance
example : Std.LawfulOrderLeftLeaningMin FastLC := inferInstance
example : Std.LawfulOrderLeftLeaningMax FastLC := inferInstance
example : Repr FastLC := inferInstance
example : ToString FastLC := inferInstance

end SynthesisChecks

end FastLC
end LeanInf
