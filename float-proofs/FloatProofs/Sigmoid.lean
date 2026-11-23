import FloatLib
import FloatLib.Tactic.Roundoff
import FloatLib.Floats.Formats.BinaryInterchange.Configured.CorrectlyRounded
import FloatProofs.Convert

/-!
# T3: Overflow-Free `[0, 1]` & `< 4u` Verified Logistic Sigmoid + Native `Float` `roundoff`

Upgrades `LeanInf/StepFunction.lean` (`sigmoidFloat`, `sigmoidDerivFloat`, `sigmoidDeriv2Float`):
- **Part 3A**: Automatic kernel-checked `roundoff mixed` error bounds directly on Lean's native
  `Float` for `sigmoidDerivNative` and `sigmoidDeriv2Native`.
- **Part 3B**: Unconditional overflow-free finiteness, `[0, 1]` range preservation, and `< 4 u64`
  relative error for the two-branch IEEE-754 `Binary64` logistic sigmoid `sigmoidB64` across
  EVERY finite `Binary64` input (including `u = ±1000`, where naive `1 / (1 + exp(-u))` overflows).
-/

namespace FloatProofs

open FloatLib.Numerics
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-! ### Part 3A: Kernel-Checked `roundoff` Bounds on Lean's Native `Float` -/

/-- Exact mirror of `LeanInf.StepFunction.sigmoidDerivFloat` using `Float.ofNat` numerals
    for direct verification with `FloatLib.Tactic.Roundoff`. -/
def sigmoidDerivNative (s : Float) : Float :=
  s * ((1 : Float) - s)

/-- Exact mirror of `LeanInf.StepFunction.sigmoidDeriv2Float` using `Float.ofNat` numerals
    for direct verification with `FloatLib.Tactic.Roundoff`. -/
def sigmoidDeriv2Native (s : Float) : Float :=
  s * ((1 : Float) - s) * ((1 : Float) - (2 : Float) * s)

/-- **Theorem 3A-1 (`sigmoidDerivNative_mixedError`)**: Auto-generated kernel-checked `MixedError`
    bound directly on Lean's native `Float` for `s * (1 - s)`. -/
roundoff mixed theorem sigmoidDerivNative_mixedError :=
  fun (s : Float) => (ExecFloat.Binary.ofFloat (sigmoidDerivNative s) : Binary64).toReal

/-- **Theorem 3A-2 (`sigmoidDeriv2Native_mixedError`)**: Auto-generated kernel-checked `MixedError`
    bound directly on Lean's native `Float` for `s * (1 - s) * (1 - 2 * s)`. -/
roundoff mixed theorem sigmoidDeriv2Native_mixedError :=
  fun (s : Float) => (ExecFloat.Binary.ofFloat (sigmoidDeriv2Native s) : Binary64).toReal

/-! ### Part 3B: Unconditional Overflow-Free `[0, 1]` & `< 4u` `Binary64` Logistic Sigmoid -/

/-- Numerically stable two-branch IEEE-754 `Binary64` logistic sigmoid
    using `FloatLib`'s correctly rounded `exp`. -/
def sigmoidB64 (u : Binary64) : Binary64 :=
  if (0 : Binary64) ≤ u then
    let e := ExecFloat.Binary.CorrectlyRounded.exp (-u)
    1 / (1 + e)
  else
    let e := ExecFloat.Binary.CorrectlyRounded.exp u
    e / (1 + e)

/-- Exact mathematical logistic sigmoid `σ(x) = (1 + e^(-x))⁻¹`. -/
noncomputable def sigmoidReal (x : ℝ) : ℝ :=
  (1 + Real.exp (-x))⁻¹

private theorem u64_eq_zpow : u64 = (2 : ℝ) ^ (-53 : ℤ) := by
  unfold u64 Model.unitRoundoffAt FloatFormat.binary64
  simp only [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
    FloatLib.Numerics.Radix.toReal]
  congr 1

private theorem η64_eq_zpow : η64 = (2 : ℝ) ^ (-1075 : ℤ) := by
  unfold η64 Model.underflowErrorAt FloatFormat.binary64
  simp only [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
    FloatLib.Numerics.Radix.toReal, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent]
  congr 1

private theorem u64_pos : 0 < u64 := by
  rw [u64_eq_zpow]; positivity

private theorem η64_pos : 0 < η64 := by
  rw [η64_eq_zpow]; positivity

private theorem u64_le_tiny : u64 ≤ 1 / 1000 := by
  rw [u64_eq_zpow]
  have h1 : (2 : ℝ) ^ (-53 : ℤ) ≤ (2 : ℝ) ^ (-10 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (-10 : ℤ) ≤ 1 / 1000 := by norm_num
  linarith

private theorem η64_le_u64_div : η64 ≤ u64 / 1000 := by
  rw [η64_eq_zpow, u64_eq_zpow, div_eq_mul_one_div]
  have h1 : (2 : ℝ) ^ (-1075 : ℤ) ≤ (2 : ℝ) ^ (-63 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (-63 : ℤ) = (2 : ℝ) ^ (-53 : ℤ) * (2 : ℝ) ^ (-10 : ℤ) := by
    rw [← zpow_add₀ (by norm_num)]
    congr 1
  have h3 : (2 : ℝ) ^ (-10 : ℤ) ≤ 1 / 1000 := by norm_num
  have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ (-53 : ℤ) := by positivity
  have h5 : (2 : ℝ) ^ (-53 : ℤ) * (2 : ℝ) ^ (-10 : ℤ) ≤ (2 : ℝ) ^ (-53 : ℤ) * (1 / 1000) :=
    mul_le_mul_of_nonneg_left h3 h4
  rw [← h2] at h5
  exact h1.trans h5

private theorem two_le_Ω64 : (2 : ℝ) ≤ Ω64 := by
  have h1 : (2 : Binary64).isFinite = true := by float_decide
  have h2 : |(2 : Binary64).toReal| ≤ Ω64 :=
    ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite h1
  have hr : (2 : Binary64).toReal = 2 := by
    have hq : ExecFloat.Binary.toRat? (2 : Binary64) = some 2 := by float_decide
    have hc := Model.cast_toRat_eq_toReal (ExecFloat.Binary.toModel (2 : Binary64))
    change ((ExecFloat.Binary.toRat? (2 : Binary64)).getD 0 : ℝ) = (2 : Binary64).toReal at hc
    rw [hq] at hc
    simpa using hc.symm
  rw [hr] at h2
  linarith [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]

private theorem isZero_false_of_toReal_pos {v : Binary64} (hv : 0 < v.toReal) :
    ExecFloat.Binary.isZero v = false := by
  cases hz : ExecFloat.Binary.isZero v with
  | false => rfl
  | true =>
    exfalso
    have h0 : v.toReal = 0 := by
      unfold ExecFloat.Binary.toReal ExecFloat.Binary.isZero at *
      exact Model.toReal_eq_zero_of_isZero _ hz
    linarith

/-- Shared core analysis for `e = CorrectlyRounded.exp v` and `d = 1 + e` whenever `v ≤ 0`. -/
private theorem exp_add_one_core (v : Binary64) (hv : v.isFinite = true) (hv_le : v.toReal ≤ 0) :
    let e := ExecFloat.Binary.CorrectlyRounded.exp v
    let d := (1 : Binary64) + e
    e.isFinite = true ∧
    e.toReal = Model.roundAt FloatFormat.binary64 (Real.exp v.toReal) ∧
    0 ≤ e.toReal ∧ e.toReal ≤ 1 ∧
    d.isFinite = true ∧
    1 ≤ d.toReal ∧
    |d.toReal - (1 + e.toReal)| ≤ u64 * (1 + e.toReal) := by
  intro e d
  have hlt : Real.exp v.toReal <
      Model.Transcendentals.Certified.overflowThreshold FloatFormat.binary64 :=
    (Real.exp_le_one_iff.mpr hv_le).trans_lt
      (Model.Transcendentals.CorrectlyRounded.one_lt_overflowThreshold FloatFormat.isIEEE_binary64)
  have he_fin : e.isFinite = true :=
    ExecFloat.Binary.CorrectlyRounded.isFinite_exp_of_nonpos hv hv_le
  have he_round : e.toReal = Model.roundAt FloatFormat.binary64 (Real.exp v.toReal) :=
    ExecFloat.Binary.CorrectlyRounded.toReal_exp_eq_roundAt hv hlt
  have he_mem : e.toReal ∈ Set.Icc (0 : ℝ) 1 := by
    rw [he_round]
    exact Model.roundAt_mem_Icc_zero_one FloatFormat.binary64
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr hv_le⟩
  have he_ge0 : 0 ≤ e.toReal := he_mem.1
  have he_le1 : e.toReal ≤ 1 := he_mem.2
  have h1fin : ((1 : Binary64).isFinite) = true := ExecFloat.Binary.isFinite_one
  have h1real : ((1 : Binary64).toReal) = 1 := ExecFloat.Binary.toReal_one
  have hd_fin : d.isFinite = true := by
    change Model.isFinite (ExecFloat.Binary.toModel ((1 : Binary64) + e)) = true
    rw [ExecFloat.Binary.toModel_hAdd]
    refine Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite _ _
      FloatFormat.isIEEE_binary64 h1fin he_fin ?_
    change |(1 : Binary64).toReal + e.toReal| ≤ Ω64
    rw [h1real, abs_of_nonneg (by linarith)]
    linarith [two_le_Ω64]
  have hd_round : d.toReal = Model.roundAt FloatFormat.binary64 (1 + e.toReal) := by
    simpa [d, h1real] using ExecFloat.Binary.toReal_add_eq_roundAt hd_fin
  have hd_ge1 : 1 ≤ d.toReal := by
    rw [hd_round]
    have hmono := Model.roundAt_mono FloatFormat.binary64 (show (1 : ℝ) ≤ 1 + e.toReal by linarith)
    simpa [Model.roundAt_one] using hmono
  have hd_err : |d.toReal - (1 + e.toReal)| ≤ u64 * (1 + e.toReal) := by
    have emix := ExecFloat.Binary.mixedError_toReal_add_of_mul_nonneg hd_fin
      (MixedError.of_eq h1real) (MixedError.refl e.toReal) (by positivity)
    have hb := emix.bound
    rw [max_self, mul_zero, zero_add, add_zero, mul_zero, add_zero,
      abs_of_nonneg (show (0 : ℝ) ≤ 1 + e.toReal by linarith)] at hb
    exact hb
  exact ⟨he_fin, he_round, he_ge0, he_le1, hd_fin, hd_ge1, hd_err⟩

private theorem sigmoidB64_nonneg_branch (u : Binary64) (hu : u.isFinite = true)
    (hu_ge : 0 ≤ u.toReal) :
    let e := ExecFloat.Binary.CorrectlyRounded.exp (-u)
    let res : Binary64 := 1 / (1 + e)
    res.isFinite = true ∧
    0 ≤ res.toReal ∧ res.toReal ≤ 1 ∧
    |res.toReal - sigmoidReal u.toReal| ≤ 4 * u64 * sigmoidReal u.toReal + 2 * η64 := by
  intro e res
  have hu0 : 0 ≤ u64 := u64_pos.le
  have hu_tiny : u64 ≤ 1 / 1000 := u64_le_tiny
  have hη0 : 0 ≤ η64 := η64_pos.le
  have hη_tiny : η64 ≤ u64 / 1000 := η64_le_u64_div
  have h1Ω : (1 : ℝ) ≤ Ω64 := by linarith [two_le_Ω64]
  have h1fin : ((1 : Binary64).isFinite) = true := ExecFloat.Binary.isFinite_one
  have h1real : ((1 : Binary64).toReal) = 1 := ExecFloat.Binary.toReal_one
  have hneg_fin : (-u).isFinite = true := by
    rw [ExecFloat.Binary.isFinite_neg]
    exact hu
  have hneg_toReal : (-u).toReal = -u.toReal := by
    unfold ExecFloat.Binary.toReal
    rw [ExecFloat.Binary.toModel_neg]
    exact Model.toReal_neg _ hu
  have hneg_le : (-u).toReal ≤ 0 := by linarith
  obtain ⟨_, he_round, he_ge0, _, hd_fin, hd_ge1, hd_err⟩ := exp_add_one_core (-u) hneg_fin hneg_le
  set d := (1 : Binary64) + e
  set x := Real.exp (-u.toReal)
  rw [hneg_toReal] at he_round
  have hx_pos : 0 < x := Real.exp_pos _
  have hx_le1 : x ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hs_eq : sigmoidReal u.toReal = 1 / (1 + x) := by simp [sigmoidReal, x, one_div]
  have hs_pos : 0 < sigmoidReal u.toReal := by rw [hs_eq]; positivity
  have hdiv_fin : res.isFinite = true := by
    change Model.isFinite (ExecFloat.Binary.toModel ((1 : Binary64) / d)) = true
    rw [ExecFloat.Binary.toModel_hDiv]
    refine Model.isFinite_div_of_abs_div_le_posMaxFinite _ _
      FloatFormat.isIEEE_binary64 h1fin hd_fin (isZero_false_of_toReal_pos (by linarith)) ?_
    change |(1 : Binary64).toReal / d.toReal| ≤ Ω64
    rw [h1real, abs_of_nonneg (by positivity)]
    have hle1 : 1 / d.toReal ≤ 1 := div_le_one_of_le₀ hd_ge1 (by linarith)
    linarith
  have hdiv_round : res.toReal = Model.roundAt FloatFormat.binary64 (1 / d.toReal) := by
    simpa [res, d, h1real] using ExecFloat.Binary.toReal_div_eq_roundAt hd_fin hdiv_fin
  have hdiv_mem : res.toReal ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hdiv_round]
    exact Model.roundAt_mem_Icc_zero_one FloatFormat.binary64
      ⟨by positivity, div_le_one_of_le₀ hd_ge1 (by linarith)⟩
  refine ⟨hdiv_fin, hdiv_mem.1, hdiv_mem.2, ?_⟩
  set q : ℝ := 1 / d.toReal
  set s : ℝ := sigmoidReal u.toReal
  have he_err : |e.toReal - x| ≤ u64 * x + η64 := by
    have h := Model.abs_roundAt_sub_le_unitRoundoffAt FloatFormat.binary64 x
    rw [← he_round, abs_of_nonneg hx_pos.le] at h
    exact h
  have hd_lb : (1 - u64) * (1 + e.toReal) ≤ d.toReal := by
    have h := (abs_sub_le_iff.mp hd_err).2
    linarith
  have hratio : (1 + e.toReal) / d.toReal ≤ 1 / (1 - u64) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hu_frac : u64 / (1 - u64) ≤ (11 / 10 : ℝ) * u64 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hq_sub_s : |q - s| ≤ (21 / 10 : ℝ) * u64 * s + η64 := by
    have hident : q - s =
        (x - e.toReal) / (d.toReal * (1 + x)) +
        ((1 + e.toReal) - d.toReal) / (d.toReal * (1 + x)) := by
      rw [show s = 1 / (1 + x) from hs_eq]
      simp only [q]
      field_simp [show d.toReal ≠ 0 by linarith, show (1 : ℝ) + x ≠ 0 by linarith]
      ring
    rw [hident]
    have hpos_den : 0 < d.toReal * (1 + x) := by positivity
    have ht1 : |(x - e.toReal) / (d.toReal * (1 + x))| ≤ u64 * s + η64 := by
      rw [abs_div, abs_sub_comm, abs_of_pos hpos_den]
      have h1 : |e.toReal - x| / (d.toReal * (1 + x)) ≤ (u64 * x + η64) / (d.toReal * (1 + x)) :=
        div_le_div_of_nonneg_right he_err hpos_den.le
      have h2 : (u64 * x + η64) / (d.toReal * (1 + x)) ≤ (u64 * 1 + η64) / (1 + x) := by
        calc (u64 * x + η64) / (d.toReal * (1 + x))
            ≤ (u64 * 1 + η64) / (d.toReal * (1 + x)) :=
              div_le_div_of_nonneg_right (by nlinarith) hpos_den.le
          _ ≤ (u64 * 1 + η64) / (1 + x) :=
              div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      have h3 : (u64 * 1 + η64) / (1 + x) = u64 * s + η64 / (1 + x) := by
        rw [show s = 1 / (1 + x) from hs_eq]; ring
      have h4 : η64 / (1 + x) ≤ η64 := div_le_self hη0 (by linarith)
      linarith
    have ht2 : |((1 + e.toReal) - d.toReal) / (d.toReal * (1 + x))| ≤
        (11 / 10 : ℝ) * u64 * s := by
      rw [abs_div, abs_sub_comm, abs_of_pos hpos_den]
      have h1 : |d.toReal - (1 + e.toReal)| / (d.toReal * (1 + x)) ≤
          (u64 * (1 + e.toReal)) / (d.toReal * (1 + x)) :=
        div_le_div_of_nonneg_right hd_err hpos_den.le
      have h2 : (u64 * (1 + e.toReal)) / (d.toReal * (1 + x)) =
          u64 * ((1 + e.toReal) / d.toReal) * s := by
        rw [show s = 1 / (1 + x) from hs_eq]
        field_simp [show d.toReal ≠ 0 by linarith, show (1 : ℝ) + x ≠ 0 by linarith]
      have h3 : u64 * ((1 + e.toReal) / d.toReal) * s ≤ u64 * (1 / (1 - u64)) * s := by gcongr
      have h4 : u64 * (1 / (1 - u64)) * s = (u64 / (1 - u64)) * s := by ring
      have h5 : (u64 / (1 - u64)) * s ≤ (11 / 10 : ℝ) * u64 * s :=
        mul_le_mul_of_nonneg_right hu_frac hs_pos.le
      linarith
    calc |(x - e.toReal) / (d.toReal * (1 + x)) +
            ((1 + e.toReal) - d.toReal) / (d.toReal * (1 + x))|
        ≤ |(x - e.toReal) / (d.toReal * (1 + x))| +
          |((1 + e.toReal) - d.toReal) / (d.toReal * (1 + x))| := abs_add_le _ _
      _ ≤ (u64 * s + η64) + (11 / 10 : ℝ) * u64 * s := add_le_add ht1 ht2
      _ = (21 / 10 : ℝ) * u64 * s + η64 := by ring
  obtain ⟨δ, η, hstd, hδ, hη, hδη⟩ := Model.roundAt_standardModel FloatFormat.binary64 q
  rw [← hdiv_round] at hstd
  rcases mul_eq_zero.mp hδη with rfl | rfl
  · have hrew : res.toReal - s = (q - s) + η := by linarith
    rw [hrew]
    calc |(q - s) + η| ≤ |q - s| + |η| := abs_add_le _ _
      _ ≤ ((21 / 10 : ℝ) * u64 * s + η64) + η64 := add_le_add hq_sub_s hη
      _ ≤ 4 * u64 * s + 2 * η64 := by nlinarith
  · have hrew : res.toReal - s = (1 + δ) * (q - s) + δ * s := by linarith
    rw [hrew]
    have h1δ : |1 + δ| ≤ 1 + u64 := by
      calc |1 + δ| ≤ |1| + |δ| := abs_add_le _ _
        _ ≤ 1 + u64 := by norm_num; exact hδ
    have hmul1 : (1 + u64) * ((21 / 10 : ℝ) * u64 * s + η64) + u64 * s ≤
        4 * u64 * s + 2 * η64 := by
      have h1 : (1 + u64) * ((21 / 10 : ℝ) * u64) + u64 ≤ 4 * u64 := by nlinarith
      have h2 : (1 + u64) * η64 ≤ 2 * η64 := by nlinarith
      have h3 : ((1 + u64) * ((21 / 10 : ℝ) * u64) + u64) * s ≤ (4 * u64) * s :=
        mul_le_mul_of_nonneg_right h1 hs_pos.le
      linarith
    calc |(1 + δ) * (q - s) + δ * s|
        ≤ |(1 + δ) * (q - s)| + |δ * s| := abs_add_le _ _
      _ = |1 + δ| * |q - s| + |δ| * |s| := by rw [abs_mul, abs_mul]
      _ ≤ (1 + u64) * ((21 / 10 : ℝ) * u64 * s + η64) + u64 * s := by
          rw [abs_of_pos hs_pos]
          have h1 := mul_le_mul h1δ hq_sub_s (abs_nonneg _) (by linarith)
          have h2 := mul_le_mul_of_nonneg_right hδ hs_pos.le
          linarith
      _ ≤ 4 * u64 * s + 2 * η64 := hmul1

private theorem sigmoidB64_neg_branch (u : Binary64) (hu : u.isFinite = true)
    (hu_le : u.toReal ≤ 0) :
    let e := ExecFloat.Binary.CorrectlyRounded.exp u
    let res : Binary64 := e / (1 + e)
    res.isFinite = true ∧
    0 ≤ res.toReal ∧ res.toReal ≤ 1 ∧
    |res.toReal - sigmoidReal u.toReal| ≤ 4 * u64 * sigmoidReal u.toReal + 2 * η64 := by
  intro e res
  have hu0 : 0 ≤ u64 := u64_pos.le
  have hu_tiny : u64 ≤ 1 / 1000 := u64_le_tiny
  have hη0 : 0 ≤ η64 := η64_pos.le
  have h1Ω : (1 : ℝ) ≤ Ω64 := by linarith [two_le_Ω64]
  obtain ⟨he_fin, he_round, he_ge0, he_le1, hd_fin, hd_ge1, hd_err⟩ :=
    exp_add_one_core u hu hu_le
  set d := (1 : Binary64) + e
  set x := Real.exp u.toReal
  have hx_pos : 0 < x := Real.exp_pos _
  have hs_eq : sigmoidReal u.toReal = x / (1 + x) := by
    unfold sigmoidReal
    have hexp : Real.exp (-u.toReal) = x⁻¹ := Real.exp_neg u.toReal
    rw [hexp]
    field_simp [hx_pos.ne', show (1 : ℝ) + x ≠ 0 by linarith]
    ring
  have hs_pos : 0 < sigmoidReal u.toReal := by rw [hs_eq]; positivity
  have hdiv_fin : res.isFinite = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (e / d)) = true
    rw [ExecFloat.Binary.toModel_hDiv]
    refine Model.isFinite_div_of_abs_div_le_posMaxFinite _ _
      FloatFormat.isIEEE_binary64 he_fin hd_fin (isZero_false_of_toReal_pos (by linarith)) ?_
    change |e.toReal / d.toReal| ≤ Ω64
    rw [abs_of_nonneg (by positivity)]
    have hle1 : e.toReal / d.toReal ≤ 1 := div_le_one_of_le₀ (by linarith) (by linarith)
    linarith
  have hdiv_round : res.toReal = Model.roundAt FloatFormat.binary64 (e.toReal / d.toReal) :=
    ExecFloat.Binary.toReal_div_eq_roundAt hd_fin hdiv_fin
  have hdiv_mem : res.toReal ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hdiv_round]
    exact Model.roundAt_mem_Icc_zero_one FloatFormat.binary64
      ⟨by positivity, div_le_one_of_le₀ (by linarith) (by linarith)⟩
  refine ⟨hdiv_fin, hdiv_mem.1, hdiv_mem.2, ?_⟩
  set q : ℝ := e.toReal / d.toReal
  set s : ℝ := sigmoidReal u.toReal
  have he_err : |e.toReal - x| ≤ u64 * x + η64 := by
    have h := Model.abs_roundAt_sub_le_unitRoundoffAt FloatFormat.binary64 x
    rw [← he_round, abs_of_nonneg hx_pos.le] at h
    exact h
  have hd_lb : (1 - u64) * (1 + e.toReal) ≤ d.toReal := by
    have h := (abs_sub_le_iff.mp hd_err).2
    linarith
  have hratio : (1 + e.toReal) / d.toReal ≤ 1 / (1 - u64) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  have hu_frac : u64 / (1 - u64) ≤ (11 / 10 : ℝ) * u64 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hq_sub_s : |q - s| ≤ (21 / 10 : ℝ) * u64 * s + η64 := by
    have hident : q - s =
        (e.toReal - x) / (d.toReal * (1 + x)) +
        (x * ((1 + e.toReal) - d.toReal)) / (d.toReal * (1 + x)) := by
      rw [show s = x / (1 + x) from hs_eq]
      simp only [q]
      field_simp [show d.toReal ≠ 0 by linarith, show (1 : ℝ) + x ≠ 0 by linarith]
      ring
    rw [hident]
    have hpos_den : 0 < d.toReal * (1 + x) := by positivity
    have ht1 : |(e.toReal - x) / (d.toReal * (1 + x))| ≤ u64 * s + η64 := by
      rw [abs_div, abs_of_pos hpos_den]
      have h1 : |e.toReal - x| / (d.toReal * (1 + x)) ≤ (u64 * x + η64) / (d.toReal * (1 + x)) :=
        div_le_div_of_nonneg_right he_err hpos_den.le
      have h2 : (u64 * x + η64) / (d.toReal * (1 + x)) ≤ (u64 * x + η64) / (1 + x) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
      have h3 : (u64 * x + η64) / (1 + x) = u64 * s + η64 / (1 + x) := by
        rw [show s = x / (1 + x) from hs_eq]; ring
      have h4 : η64 / (1 + x) ≤ η64 := div_le_self hη0 (by linarith)
      linarith
    have ht2 : |(x * ((1 + e.toReal) - d.toReal)) / (d.toReal * (1 + x))| ≤
        (11 / 10 : ℝ) * u64 * s := by
      rw [abs_div, abs_mul, abs_of_pos hx_pos, abs_of_pos hpos_den, abs_sub_comm]
      have h1 : x * |d.toReal - (1 + e.toReal)| / (d.toReal * (1 + x)) ≤
          x * (u64 * (1 + e.toReal)) / (d.toReal * (1 + x)) := by
        apply div_le_div_of_nonneg_right _ hpos_den.le
        exact mul_le_mul_of_nonneg_left hd_err hx_pos.le
      have h2 : x * (u64 * (1 + e.toReal)) / (d.toReal * (1 + x)) =
          u64 * ((1 + e.toReal) / d.toReal) * s := by
        rw [show s = x / (1 + x) from hs_eq]
        field_simp [show d.toReal ≠ 0 by linarith, show (1 : ℝ) + x ≠ 0 by linarith]
      have h3 : u64 * ((1 + e.toReal) / d.toReal) * s ≤ u64 * (1 / (1 - u64)) * s := by gcongr
      have h4 : u64 * (1 / (1 - u64)) * s = (u64 / (1 - u64)) * s := by ring
      have h5 : (u64 / (1 - u64)) * s ≤ (11 / 10 : ℝ) * u64 * s :=
        mul_le_mul_of_nonneg_right hu_frac hs_pos.le
      linarith
    calc |(e.toReal - x) / (d.toReal * (1 + x)) +
            x * ((1 + e.toReal) - d.toReal) / (d.toReal * (1 + x))|
        ≤ |(e.toReal - x) / (d.toReal * (1 + x))| +
          |x * ((1 + e.toReal) - d.toReal) / (d.toReal * (1 + x))| := abs_add_le _ _
      _ ≤ (u64 * s + η64) + (11 / 10 : ℝ) * u64 * s := add_le_add ht1 ht2
      _ = (21 / 10 : ℝ) * u64 * s + η64 := by ring
  obtain ⟨δ, η, hstd, hδ, hη, hδη⟩ := Model.roundAt_standardModel FloatFormat.binary64 q
  rw [← hdiv_round] at hstd
  rcases mul_eq_zero.mp hδη with rfl | rfl
  · have hrew : res.toReal - s = (q - s) + η := by linarith
    rw [hrew]
    calc |(q - s) + η| ≤ |q - s| + |η| := abs_add_le _ _
      _ ≤ ((21 / 10 : ℝ) * u64 * s + η64) + η64 := add_le_add hq_sub_s hη
      _ ≤ 4 * u64 * s + 2 * η64 := by nlinarith
  · have hrew : res.toReal - s = (1 + δ) * (q - s) + δ * s := by linarith
    rw [hrew]
    have h1δ : |1 + δ| ≤ 1 + u64 := by
      calc |1 + δ| ≤ |1| + |δ| := abs_add_le _ _
        _ ≤ 1 + u64 := by norm_num; exact hδ
    have hmul1 : (1 + u64) * ((21 / 10 : ℝ) * u64 * s + η64) + u64 * s ≤
        4 * u64 * s + 2 * η64 := by
      have h1 : (1 + u64) * ((21 / 10 : ℝ) * u64) + u64 ≤ 4 * u64 := by nlinarith
      have h2 : (1 + u64) * η64 ≤ 2 * η64 := by nlinarith
      have h3 : ((1 + u64) * ((21 / 10 : ℝ) * u64) + u64) * s ≤ (4 * u64) * s :=
        mul_le_mul_of_nonneg_right h1 hs_pos.le
      linarith
    calc |(1 + δ) * (q - s) + δ * s|
        ≤ |(1 + δ) * (q - s)| + |δ * s| := abs_add_le _ _
      _ = |1 + δ| * |q - s| + |δ| * |s| := by rw [abs_mul, abs_mul]
      _ ≤ (1 + u64) * ((21 / 10 : ℝ) * u64 * s + η64) + u64 * s := by
          rw [abs_of_pos hs_pos]
          have h1 := mul_le_mul h1δ hq_sub_s (abs_nonneg _) (by linarith)
          have h2 := mul_le_mul_of_nonneg_right hδ hs_pos.le
          linarith
      _ ≤ 4 * u64 * s + 2 * η64 := hmul1

/-- **Theorem 3B (`sigmoidB64_spec`)**: Unconditional finiteness, `[0, 1]` range preservation,
    and `< 4 u64` relative accuracy for EVERY finite IEEE-754 `Binary64` input `u` (even `u = ±1000`,
    where naive `1 / (1 + exp(-u))` overflows to `NaN` or `0`). -/
theorem sigmoidB64_spec (u : Binary64) (hu : u.isFinite = true) :
    (sigmoidB64 u).isFinite = true ∧
    0 ≤ (sigmoidB64 u).toReal ∧ (sigmoidB64 u).toReal ≤ 1 ∧
    |(sigmoidB64 u).toReal - sigmoidReal u.toReal| ≤
      4 * u64 * sigmoidReal u.toReal + 2 * η64 := by
  have h0fin : ((0 : Binary64).isFinite) = true := ExecFloat.Binary.isFinite_zero
  have h0real : ((0 : Binary64).toReal) = 0 := by simp
  unfold sigmoidB64
  split_ifs with hge
  · have hu_ge : 0 ≤ u.toReal := by
      have := (ExecFloat.Binary.le_iff_toReal_le h0fin hu).mp hge
      rwa [h0real] at this
    exact sigmoidB64_nonneg_branch u hu hu_ge
  · have hu_le : u.toReal ≤ 0 := by
      by_contra hnot
      push Not at hnot
      exact hge ((ExecFloat.Binary.le_iff_toReal_le h0fin hu).mpr (by rw [h0real]; exact hnot.le))
    exact sigmoidB64_neg_branch u hu hu_le

end FloatProofs
