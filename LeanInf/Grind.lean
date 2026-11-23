import Init.Grind.Ring.Basic
import Init.Grind.Ordered.Ring
import Init.Grind.Module.Basic
import LeanInf.Instances

/-!
# Lean 4.36 `grind` Integration for `FastLC`

Zero-Mathlib, zero-`sorry` `Lean.Grind` algebra and order integration for `LeanInf.FastLC`:
- `Lean.Grind.CommRing FastLC` (Groebner basis commutative ring solver)
- `Lean.Grind.OrderedAdd FastLC` & `Lean.Grind.OrderedRing FastLC` (ordered-ring / linarith solver)
- `Lean.Grind.IsCharP FastLC 0` (synthesized automatically from `OrderedRing`)
- `Lean.Grind.NoNatZeroDivisors FastLC` (torsion-free integer-module scaling)
- Curated `@[grind]` rules & targeted `grind_pattern` triggers for `FastLC.ext`, `coeff`
  homomorphisms into `Rat`, `ofRat` injectivity, `min`/`max`/`abs`/`isZero` normalization,
  unit cancellation (`H * ε = 1`), and non-Archimedean ordering (`0 < ε < r < H`)
- Compiled `by grind` regression and showcase suite

**Mathematical soundness note:** `FastLC` stores finite canonical supports (`ℚ[H^ℚ]`) and its
computable `Inv` instance (`invNewton · 12`) truncates infinite geometric series, so `FastLC` is
an **ordered integral domain** (`CommRing` + `OrderedRing` + `NoNatZeroDivisors`) and intentionally
does **not** declare `Lean.Grind.Field FastLC`.
-/

namespace LeanInf
namespace FastLC

/-! ### `Lean.Grind` Ring, Ordered Ring & Torsion-Free Module Instances -/

/-- `FastLC` is a commutative ring for Lean 4.36's `grind` Groebner-basis solver.
    Reuses `FastLC`'s native fast `Add`, `Mul`, `Neg`, `Sub`, `HPow`, `OfNat`, `NatCast`,
    `IntCast`, `SMul Nat`, and `SMul Int` instances with zero typeclass diamonds. -/
instance : Lean.Grind.CommRing FastLC where
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := mul_add
  right_distrib := add_mul
  zero_mul := zero_mul
  mul_zero := mul_zero
  pow_zero _ := rfl
  pow_succ x n := by
    change x.powFast (n + 1) = x.powFast n * x
    rw [powFast_eq_powNaive, powFast_eq_powNaive, powNaive, mul_comm]
  ofNat_succ := ofNat_succ
  ofNat_eq_natCast := ofNat_eq_natCast
  nsmul_eq_natCast_mul := nsmul_eq_natCast_mul
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg := sub_eq_add_neg
  neg_zsmul i a := by
    rw [zsmul_eq_intCast_mul, zsmul_eq_intCast_mul, intCast_neg, neg_mul]
  zsmul_natCast_eq_nsmul _ _ := rfl
  intCast_ofNat := intCast_ofNat
  intCast_neg := intCast_neg

/-- Addition on `FastLC` is order-preserving (`a ≤ b ↔ a + c ≤ b + c`). -/
instance : Lean.Grind.OrderedAdd FastLC where
  add_le_left_iff {a b} c := by
    show (a - b).signum ≤ 0 ↔ ((a + c) - (b + c)).signum ≤ 0
    have h : (a + c) - (b + c) = a - b := by
      ext e; simp; grind
    rw [h]

/-- `FastLC` is a strict ordered ring (`0 < 1` and multiplication by positives preserves `<`). -/
instance : Lean.Grind.OrderedRing FastLC where
  zero_lt_one := by
    show ((0 : FastLC) - 1).signum = -1
    rw [sub_eq_add_neg, zero_add, signum_neg, signum_one]
  mul_lt_mul_of_pos_left {a b c} hab hc := by
    show (c * a - c * b).signum = -1
    have hab' : (a - b).signum = -1 := hab
    have hc' : (0 - c).signum = -1 := hc
    have h0c : (0 : FastLC) - c = -c := by rw [sub_eq_add_neg, zero_add]
    rw [h0c, signum_neg] at hc'
    have hcpos : c.signum = 1 := by omega
    rw [← mul_sub, signum_mul, hcpos, hab']
    rfl
  mul_lt_mul_of_pos_right {a b c} hab hc := by
    rw [mul_comm a c, mul_comm b c]
    have hab' : (a - b).signum = -1 := hab
    have hc' : (0 - c).signum = -1 := hc
    have h0c : (0 : FastLC) - c = -c := by rw [sub_eq_add_neg, zero_add]
    rw [h0c, signum_neg] at hc'
    have hcpos : c.signum = 1 := by omega
    show (c * a - c * b).signum = -1
    rw [← mul_sub, signum_mul, hcpos, hab']
    rfl

/-- `FastLC` has no natural-number zero divisors (torsion-free `IntModule` for `grind` linarith). -/
instance : Lean.Grind.NoNatZeroDivisors FastLC :=
  Lean.Grind.NoNatZeroDivisors.mk' fun k a hk hka => by
    rw [nsmul_eq_natCast_mul] at hka
    rcases mul_eq_zero_iff.mp hka with hk0 | ha0
    · exfalso
      have hrat : (k : Rat) = 0 := ofRat_injective hk0
      have hnum : ((k : Rat)).num = 0 := by rw [hrat]; rfl
      have : (k : Int) = 0 := hnum
      omega
    · exact ha0

/-! ### Exact Non-Archimedean Order & Monomial Unit Lemmas -/

/-- Exact product of two monomials: `(c₁ H^{e₁}) * (c₂ H^{e₂}) = (c₁ c₂) H^{e₁ + e₂}`. -/
theorem mono_mul_mono (e1 c1 e2 c2 : Rat) :
    mono e1 c1 * mono e2 c2 = mono (e1 + e2) (c1 * c2) := by
  ext e
  rw [coeff_mul, coeff_mono]
  by_cases hc1 : (c1 == 0) = true
  · have h1 : c1 = 0 := eq_of_beq hc1
    subst h1
    have ht : (mono e1 0).terms = [] := by unfold mono zero; simp
    rw [ht, TermList.coeffOf_mulNaiveTerms_nil]
    split <;> simp
  · have ht : (mono e1 c1).terms = [(e1, c1)] := by unfold mono; simp [hc1]
    rw [ht, TermList.coeffOf_mulNaiveTerms_cons, TermList.coeffOf_mulNaiveTerms_nil, Rat.add_zero]
    change c1 * (mono e2 c2).coeff (e - e1) = _
    rw [coeff_mono]
    have hiff : (e2 == e - e1) = (e1 + e2 == e) := by
      cases h1 : (e2 == e - e1) <;> cases h2 : (e1 + e2 == e) <;> try rfl
      · have heq : e1 + e2 = e := eq_of_beq h2
        have : e2 = e - e1 := by grind
        simp [this] at h1
      · have heq : e2 = e - e1 := eq_of_beq h1
        have : e1 + e2 = e := by grind
        simp [this] at h2
    rw [hiff]
    split <;> simp

/-- Every nonzero monomial has an exact two-sided multiplicative inverse `mono (-e) (Rat.inv c)`. -/
theorem mono_mul_inv {e c : Rat} (hc : c ≠ 0) :
    mono e c * mono (-e) (Rat.inv c) = 1 := by
  rw [mono_mul_mono]
  have he : e + (-e) = 0 := by grind
  have hc' : c * Rat.inv c = 1 := Rat.mul_inv_cancel c hc
  rw [he, hc']
  rfl

/-- Every nonzero embedded rational has an exact multiplicative inverse `ofRat (Rat.inv r)`. -/
theorem ofRat_mul_inv {r : Rat} (hr : r ≠ 0) :
    ofRat r * ofRat (Rat.inv r) = 1 := by
  simpa [ofRat] using mono_mul_inv (e := 0) hr

/-- `ε > 0`. -/
theorem eps_pos : (0 : FastLC) < infEps := by
  show ((0 : FastLC) - infEps).signum = -1
  rw [sub_eq_add_neg, zero_add, signum_neg, signum_infEps]

/-- `H > 0`. -/
theorem H_pos : (0 : FastLC) < infH := by
  show ((0 : FastLC) - infH).signum = -1
  rw [sub_eq_add_neg, zero_add, signum_neg, signum_infH]

/-- `ε` is strictly smaller than every strictly positive standard rational `ofRat r`. -/
theorem eps_lt_ofRat_of_pos {r : Rat} (hr : 0 < r) : infEps < ofRat r := by
  show (infEps - ofRat r).signum = -1
  apply (TermList.signumFast_eq_neg_one_iff (infEps - ofRat r).wf).mpr
  refine ⟨0, ?_, ?_⟩
  · change (infEps - ofRat r).coeff 0 < 0
    rw [coeff_sub, coeff_infEps, coeff_ofRat]
    have hne : ((-1 : Rat) == 0) = false := by decide
    simp only [hne, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    grind
  · intro e he
    change (infEps - ofRat r).coeff e = 0
    rw [coeff_sub, coeff_infEps, coeff_ofRat]
    have h1 : ((-1 : Rat) == e) = false := by
      cases hb : ((-1 : Rat) == e)
      · rfl
      · have : (-1 : Rat) = e := eq_of_beq hb; grind
    have h2 : ((0 : Rat) == e) = false := by
      cases hb : ((0 : Rat) == e)
      · rfl
      · have : (0 : Rat) = e := eq_of_beq hb; grind
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    grind

/-- Every standard rational `ofRat r` is strictly smaller than the infinite unit `H`. -/
theorem ofRat_lt_H (r : Rat) : ofRat r < infH := by
  show (ofRat r - infH).signum = -1
  apply (TermList.signumFast_eq_neg_one_iff (ofRat r - infH).wf).mpr
  refine ⟨1, ?_, ?_⟩
  · change (ofRat r - infH).coeff 1 < 0
    rw [coeff_sub, coeff_ofRat, coeff_infH]
    have hne : ((0 : Rat) == 1) = false := by decide
    simp only [hne, Bool.false_eq_true, ↓reduceIte, beq_self_eq_true]
    grind
  · intro e he
    change (ofRat r - infH).coeff e = 0
    rw [coeff_sub, coeff_ofRat, coeff_infH]
    have h1 : ((0 : Rat) == e) = false := by
      cases hb : ((0 : Rat) == e)
      · rfl
      · have : (0 : Rat) = e := eq_of_beq hb; grind
    have h2 : ((1 : Rat) == e) = false := by
      cases hb : ((1 : Rat) == e)
      · rfl
      · have : (1 : Rat) = e := eq_of_beq hb; grind
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    grind

/-- `ε < 1`. -/
theorem eps_lt_one : infEps < (1 : FastLC) :=
  eps_lt_ofRat_of_pos (by decide)

/-- `1 < H`. -/
theorem one_lt_H : (1 : FastLC) < infH :=
  ofRat_lt_H 1

/-- `ε < H`. -/
theorem eps_lt_H : infEps < infH :=
  Std.lt_trans eps_lt_one one_lt_H

/-- `ofRat` strictly reflects and preserves `<`. -/
theorem ofRat_lt_ofRat_iff (a b : Rat) : ofRat a < ofRat b ↔ a < b := by
  show (ofRat a - ofRat b).signum = -1 ↔ a < b
  rw [← ofRat_sub, signum_ofRat]
  by_cases h1 : a - b > 0
  · have hnot : ¬ (a < b) := by grind
    simp [h1, hnot]
  · by_cases h2 : a - b < 0
    · have hlt : a < b := by grind
      simp [h1, h2, hlt]
    · have hnot : ¬ (a < b) := by grind
      simp [h1, h2, hnot]

/-- `ofRat` reflects and preserves `≤`. -/
theorem ofRat_le_ofRat_iff (a b : Rat) : ofRat a ≤ ofRat b ↔ a ≤ b := by
  show (ofRat a - ofRat b).signum ≤ 0 ↔ a ≤ b
  rw [← ofRat_sub, signum_ofRat]
  by_cases h1 : a - b > 0
  · have hnot : ¬ (a ≤ b) := by grind
    simp [h1, hnot]
  · by_cases h2 : a - b < 0
    · have hle : a ≤ b := by grind
      simp [h1, h2, hle]
    · have hle : a ≤ b := by grind
      simp [h1, h2, hle]

/-- Every natural power `ε^n` is strictly positive. -/
theorem eps_pow_pos (n : Nat) : (0 : FastLC) < infEps ^ n := by
  induction n with
  | zero => exact Lean.Grind.OrderedRing.zero_lt_one
  | succ k ih =>
    rw [Lean.Grind.Semiring.pow_succ]
    have h := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_right ih eps_pos
    rwa [zero_mul] at h

/-- Every natural power `H^n` is strictly positive. -/
theorem H_pow_pos (n : Nat) : (0 : FastLC) < infH ^ n := by
  induction n with
  | zero => exact Lean.Grind.OrderedRing.zero_lt_one
  | succ k ih =>
    rw [Lean.Grind.Semiring.pow_succ]
    have h := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_right ih H_pos
    rwa [zero_mul] at h

/-- Higher powers of `ε` are strictly smaller: `m < n → ε^n < ε^m`. -/
theorem eps_pow_lt {m n : Nat} (h : m < n) : infEps ^ n < infEps ^ m := by
  induction h with
  | refl =>
    rw [Lean.Grind.Semiring.pow_succ]
    have h1 := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_left eps_lt_one (eps_pow_pos m)
    rwa [mul_one] at h1
  | @step k _ ih =>
    have hstep : infEps ^ (k + 1) < infEps ^ k := by
      rw [Lean.Grind.Semiring.pow_succ]
      have h1 := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_left eps_lt_one (eps_pow_pos k)
      rwa [mul_one] at h1
    exact Std.lt_trans hstep ih

/-- Higher powers of `H` are strictly larger: `m < n → H^m < H^n`. -/
theorem H_pow_lt {m n : Nat} (h : m < n) : infH ^ m < infH ^ n := by
  induction h with
  | refl =>
    rw [Lean.Grind.Semiring.pow_succ]
    have h1 := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_left one_lt_H (H_pow_pos m)
    rwa [mul_one] at h1
  | @step k _ ih =>
    have hstep : infH ^ k < infH ^ (k + 1) := by
      rw [Lean.Grind.Semiring.pow_succ]
      have h1 := Lean.Grind.OrderedRing.mul_lt_mul_of_pos_left one_lt_H (H_pow_pos k)
      rwa [mul_one] at h1
    exact Std.lt_trans ih hstep

/-- Positivity of `mkRat n d` when `n > 0` and `d > 0` (bridges `mkRat` literals for `grind`). -/
theorem mkRat_pos {n : Int} {d : Nat} (hn : 0 < n) (hd : 0 < d) :
    (0 : Rat) < mkRat n d := by
  rw [Rat.mkRat_eq_div]
  have hn' : (0 : Rat) < (n : Rat) := Rat.intCast_lt_intCast.mpr hn
  have hd' : (0 : Rat) < (d : Rat) := Rat.natCast_lt_natCast.mpr hd
  exact (Rat.lt_div_iff hd').mpr (by simpa using hn')

/-! ### Curated `@[grind]` Attributes & Targeted Trigger Patterns -/

attribute [grind ext] FastLC.ext

attribute [grind inj] FastLC.ofRat_injective

attribute [grind =]
  FastLC.coeff_zero
  FastLC.coeff_one
  FastLC.coeff_mono
  FastLC.coeff_ofRat
  FastLC.coeff_infH
  FastLC.coeff_infEps
  FastLC.coeff_dropBelow
  FastLC.coeff_scaleRat
  FastLC.ofRat_zero
  FastLC.ofRat_one
  FastLC.ofRat_neg
  FastLC.ofRat_add
  FastLC.ofRat_sub
  FastLC.ofRat_mul
  FastLC.ofRat_lt_ofRat_iff
  FastLC.ofRat_le_ofRat_iff
  FastLC.signum_zero
  FastLC.signum_one
  FastLC.signum_infH
  FastLC.signum_infEps
  FastLC.signum_neg
  FastLC.signum_mul
  FastLC.mono_mul_mono

attribute [grind hom]
  FastLC.coeff_add
  FastLC.coeff_sub
  FastLC.coeff_neg

attribute [grind norm]
  FastLC.min_def
  FastLC.max_def
  FastLC.abs_def
  FastLC.isZero_iff

-- Targeted ground triggers so `H * ε = 1` and `0 < ε < 1 < H` enter `grind`'s Groebner basis
-- and linarith solvers immediately whenever `infH` or `infEps` appears in a goal (zero looping).
grind_pattern H_mul_eps => infH
grind_pattern H_mul_eps => infEps
grind_pattern eps_mul_H => infEps
grind_pattern eps_pos => infEps
grind_pattern eps_lt_one => infEps
grind_pattern H_pos => infH
grind_pattern one_lt_H => infH
grind_pattern eps_lt_ofRat_of_pos => infEps, ofRat r
grind_pattern ofRat_lt_H => infH, ofRat r
grind_pattern mkRat_pos => mkRat n d

-- Nonlinear ordered-ring multiplication monotonicity helpers for `grind`.
/-- Nonnegative right-multiplication preserves `≤` on `FastLC`. -/
@[grind →] theorem mul_le_mul_of_nonneg_right {x y z : FastLC}
    (hxy : x ≤ y) (hz : 0 ≤ z) : x * z ≤ y * z :=
  Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_right hxy hz

/-- Nonnegative left-multiplication preserves `≤` on `FastLC`. -/
@[grind →] theorem mul_le_mul_of_nonneg_left {x y z : FastLC}
    (hxy : x ≤ y) (hz : 0 ≤ z) : z * x ≤ z * y :=
  Lean.Grind.OrderedRing.mul_le_mul_of_nonneg_left hxy hz

/-! ### Typeclass Synthesis & Diamond Verification -/

section GrindInstanceChecks

example : Lean.Grind.CommRing FastLC := inferInstance
example : Lean.Grind.OrderedAdd FastLC := inferInstance
example : Lean.Grind.OrderedRing FastLC := inferInstance
example : Std.IsLinearOrder FastLC := inferInstance
example : Std.LawfulOrderLT FastLC := inferInstance
example : Lean.Grind.IsCharP FastLC 0 := inferInstance
example : Lean.Grind.NoNatZeroDivisors FastLC := inferInstance

-- Zero-diamond checks: `CommRing` reuses `FastLC`'s native fast operations definitionally.
example : (inferInstance : Add FastLC) = Lean.Grind.Semiring.toAdd := rfl
example : (inferInstance : Mul FastLC) = Lean.Grind.Semiring.toMul := rfl
example : (inferInstance : Neg FastLC) = Lean.Grind.Ring.toNeg := rfl
example : (inferInstance : Sub FastLC) = Lean.Grind.Ring.toSub := rfl
example : (inferInstance : HPow FastLC Nat FastLC) = Lean.Grind.Semiring.npow := rfl

end GrindInstanceChecks

/-! ### `by grind` Showcase & Regression Suite (Zero `sorry`) -/

section GrindShowcase

/-- Commutative-ring binomial square identity solved purely by `by grind`. -/
theorem grind_add_sq (x y : FastLC) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  grind

/-- Difference of squares identity solved purely by `by grind`. -/
theorem grind_diff_squares (x y : FastLC) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  grind

/-- Binomial cube identity with arbitrary `Nat` numerals solved purely by `by grind`. -/
theorem grind_add_cube (x y : FastLC) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  grind

/-- **1-Line Newton Residual Squaring Proof via `by grind`**:
    Compare with the 32-line manual proof `newton_residual_squares` in `VerifiedRefactor.lean`! -/
theorem newton_residual_squares_grind (u y : FastLC) :
    (1 : FastLC) - u * newtonStep u y = (1 - u * y) ^ 2 := by
  unfold newtonStep
  grind

/-- Linear system over `FastLC` solved via characteristic-0 Groebner basis (`by grind`). -/
theorem grind_linear_system (x y : FastLC) (h1 : x + y = 5) (h2 : x - y = 1) :
    x = 3 ∧ y = 2 := by
  grind

/-- Natural and integer scalar multiplication handled directly by `by grind`. -/
theorem grind_smul_ring (x y : FastLC) :
    (3 : Nat) • x + (-2 : Int) • y = 3 * x - 2 * y := by
  grind

/-- Ordered-ring inequality (`x ≤ y → 0 ≤ z → x * z ≤ y * z`) solved purely by `by grind`. -/
theorem grind_mul_le_mul_of_nonneg_right (x y z : FastLC) (hxy : x ≤ y) (hz : 0 ≤ z) :
    x * z ≤ y * z := by
  grind

/-- Strict linear arithmetic over `FastLC` solved purely by `by grind`. -/
theorem grind_linarith_strict (a b c : FastLC) (hab : a < b) (hc : 0 < c) :
    2 * a + 3 * c < 2 * b + 4 * c := by
  grind

/-- `abs` nonnegativity solved purely by `by grind` (using `@[grind norm] abs_def`). -/
theorem grind_abs_nonneg (x : FastLC) : (0 : FastLC) ≤ x.abs := by
  grind

/-- `min` and `max` bounds solved purely by `by grind`. -/
theorem grind_min_max_bounds (a b : FastLC) :
    min a b ≤ a ∧ min a b ≤ b ∧ a ≤ max a b ∧ b ≤ max a b := by
  grind

/-- Nonstandard unit identity `H * ε + 1 = 2` solved purely by `by grind`. -/
theorem grind_H_mul_eps_add_one : infH * infEps + 1 = 2 := by
  grind

/-- Nonstandard strict positivity `0 < ε` solved purely by `by grind`. -/
theorem grind_eps_pos : (0 : FastLC) < infEps := by
  grind

/-- Nonstandard unit cancellation `ε * H * x = x` solved purely by `by grind`. -/
theorem grind_eps_mul_H_mul (x : FastLC) : infEps * infH * x = x := by
  grind

/-- Groebner basis combining polynomial expansion and `H * ε = 1` purely via `by grind`. -/
theorem grind_H_eps_expand :
    (infH + 1) * (infEps + 1) = infH + 2 + infEps := by
  grind

/-- Groebner basis cancellation `(H + ε)^2 - (H - ε)^2 = 4` purely via `by grind`. -/
theorem grind_H_eps_squares :
    (infH + infEps) ^ 2 - (infH - infEps) ^ 2 = 4 := by
  grind

/-- Non-Archimedean infinitesimal bound `0 < ε < 1/1000000` solved purely by `by grind`. -/
theorem grind_eps_infinitesimal :
    (0 : FastLC) < infEps ∧ infEps < ofRat (mkRat 1 1000000) := by
  grind

/-- Non-Archimedean infinite bound `x ≥ H → 1000000 < x` solved purely by `by grind`. -/
theorem grind_H_infinite (x : FastLC) (hx : x ≥ infH) :
    ofRat 1000000 < x := by
  grind

/-- Nonstandard strict order perturbation `x < x + ε` solved purely by `by grind`. -/
theorem grind_add_eps_gt (x : FastLC) : x < x + infEps := by
  grind

/-- Coefficient homomorphism projection into `Rat` solved purely by `by grind`. -/
theorem grind_coeff_sub_zero (x y : FastLC) (e : Rat) (h : (x - y).coeff e = 0) :
    x.coeff e = y.coeff e := by
  grind

/-- Extensionality + coefficient homomorphism (`@[grind ext]` + `@[grind hom]`):
    matching pointwise sum coefficients implies `x + y = z` purely by `by grind`. -/
theorem grind_ext_coeff_add (x y z : FastLC) (h : ∀ e, x.coeff e + y.coeff e = z.coeff e) :
    x + y = z := by
  grind

/-- `ofRat` injectivity solved purely by `by grind`. -/
theorem grind_ofRat_inj (a b : Rat) (h : ofRat a = ofRat b) : a = b := by
  grind

/-- Nonnegativity of squares on `FastLC` via `OrderedRing.sq_nonneg`. -/
theorem grind_sq_nonneg (x y : FastLC) : (0 : FastLC) ≤ (x - y) ^ 2 := by
  grind [Lean.Grind.OrderedRing.sq_nonneg]

/-- Non-Archimedean infinitesimal bound with rational division literal `(1 : Rat) / 1000000`. -/
theorem grind_eps_lt_div : infEps < ofRat ((1 : Rat) / 1000000) := by
  grind

end GrindShowcase

end FastLC
end LeanInf
