import FloatLib
import LeanInf.StepFunction
import FloatProofs.EvalFinite

/-!
# T4: Symbolic-to-Float Bridge for the Nonstandard Dirac Delta `D_sym L_H(0)`

Connects the pure Levi-Civita central-difference expansion at `x = 0`
(`(1/4)H - (1/48)ε + (1/480)ε³`) directly to the classical finite peak `N / 4` in IEEE-754
`Binary64` via Ogita–Rump–Oishi `Sum2`, together with a kernel-checked `float_decide`
certification at `N = 100`.
-/

namespace FloatProofs

open LeanInf
open FloatLib.Numerics
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- Exact 3-term Levi-Civita central-difference expansion at `x = 0`:
    `d0 = (1/4)H - (1/48)ε + (1/480)ε³`. -/
def diracCenterLC : FastLC :=
  ⟨[(1, mkRat 1 4), (-1, mkRat (-1) 48), (-3, mkRat 1 480)],
   ⟨by decide, ⟨by decide, by decide, trivial⟩,
    ⟨by decide, ⟨by decide, trivial⟩, ⟨by decide, trivial, trivial⟩⟩⟩⟩

/-- Canonical sorted term list of `diracCenterLC` (definitional). -/
theorem diracCenterLC_terms :
    diracCenterLC.terms = [(1, mkRat 1 4), (-1, mkRat (-1) 48), (-3, mkRat 1 480)] :=
  rfl

/-- `diracCenterLC` equals the algebraic sum of its three monomials `(1/4)H - (1/48)ε + (1/480)ε³`. -/
theorem diracCenterLC_eq_sum :
    diracCenterLC =
      FastLC.mono 1 (mkRat 1 4) + FastLC.mono (-1) (mkRat (-1) 48) + FastLC.mono (-3) (mkRat 1 480) := by
  ext e
  rw [FastLC.coeff_add, FastLC.coeff_add]
  simp only [FastLC.coeff, FastLC.mono, diracCenterLC, TermList.coeffOf]
  have h1 : (mkRat 1 4 == 0) = false := by decide
  have h2 : (mkRat (-1) 48 == 0) = false := by decide
  have h3 : (mkRat 1 480 == 0) = false := by decide
  simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceDIte, TermList.coeffOf, Rat.add_zero]
  ring

private theorem u64_eq_zpow' : u64 = (2 : ℝ) ^ (-53 : ℤ) := by
  unfold u64 Model.unitRoundoffAt FloatFormat.binary64
  simp only [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
    FloatLib.Numerics.Radix.toReal]
  congr 1

private theorem η64_eq_zpow' : η64 = (2 : ℝ) ^ (-1075 : ℤ) := by
  unfold η64 Model.underflowErrorAt FloatFormat.binary64
  simp only [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
    FloatLib.Numerics.Radix.toReal, FloatFormat.minSubnormalExponent, FloatFormat.minNormalExponent]
  congr 1

private theorem u64_pos' : 0 < u64 := by rw [u64_eq_zpow']; positivity

private theorem η64_pos' : 0 < η64 := by rw [η64_eq_zpow']; positivity

private theorem u64_le_tiny' : u64 ≤ 1 / 1000 := by
  rw [u64_eq_zpow']
  have h1 : (2 : ℝ) ^ (-53 : ℤ) ≤ (2 : ℝ) ^ (-10 : ℤ) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  have h2 : (2 : ℝ) ^ (-10 : ℤ) ≤ 1 / 1000 := by norm_num
  linarith

private theorem η64_le_u64_div' : η64 ≤ u64 / 1000 := by
  rw [η64_eq_zpow', u64_eq_zpow', div_eq_mul_one_div]
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

private theorem two_pow_100_le_Ω64 : (2 : ℝ) ^ (100 : ℕ) ≤ Ω64 := by
  unfold Ω64
  rw [Model.toReal_posMaxFinite_ieee FloatFormat.binary64 FloatFormat.isIEEE_binary64]
  have hmant : (1 : ℝ) ≤ ((Model.pow2 (FloatFormat.binary64.fracWidth + 1) - 1 : Nat) : ℝ) := by
    exact_mod_cast (by decide : 1 ≤ Model.pow2 (FloatFormat.binary64.fracWidth + 1) - 1)
  have hexp : (2 : ℝ) ^ (100 : ℕ) ≤
      Model.bpow (Int.ofNat (FloatFormat.ieeeMaxNormalExponent FloatFormat.binary64) -
          Int.ofNat FloatFormat.binary64.fracWidth) := by
    unfold Model.bpow
    simp only [FloatLib.Floats.Formats.Flocq.bpow, FloatLib.Numerics.binaryRadix,
      FloatLib.Numerics.Radix.toReal]
    rw [← zpow_natCast]
    refine zpow_le_zpow_right₀ (by norm_num) ?_
    decide
  nlinarith [show (0 : ℝ) ≤ (2 : ℝ) ^ (100 : ℕ) by positivity]

private theorem signedScaledRatToReal_eq_rat (q : Rat) :
    Model.signedScaledRatToReal (decide (q < 0)) q.num.natAbs q.den 0 = (q : ℝ) := by
  rw [Rat.cast_def]
  have hiff : q < 0 ↔ q.num < 0 := by
    constructor
    · intro h
      have hcast : (q : ℝ) < 0 := by exact_mod_cast h
      rw [Rat.cast_def] at hcast
      have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      have hnum : (q.num : ℝ) < 0 := by
        by_contra hge; push Not at hge
        exact not_le_of_gt hcast (div_nonneg hge hden.le)
      exact_mod_cast hnum
    · intro h
      have hnum : (q.num : ℝ) < 0 := by exact_mod_cast h
      have hden : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
      have hcast : (q : ℝ) < 0 := by rw [Rat.cast_def]; exact div_neg_of_neg_of_pos hnum hden
      exact_mod_cast hcast
  by_cases h : q.num < 0
  · have hq : q < 0 := hiff.mpr h
    simp [Model.signedScaledRatToReal, Model.scaledRatToReal, hq, abs_of_neg h, neg_div]
  · have hq : ¬ q < 0 := fun hlt => h (hiff.mp hlt)
    simp [Model.signedScaledRatToReal, Model.scaledRatToReal, hq, abs_of_nonneg (le_of_not_gt h)]

private theorem isFinite_pown_of_pos_le (x : Binary64) (e : ℤ) (hx : x.isFinite = true)
    (hx0 : 0 < x.toReal) (he : e ≠ 0) (hrange : |x.toReal ^ e| ≤ Ω64) :
    (ExecFloat.Binary.pown x e).isFinite = true := by
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite (x := ExecFloat.Binary.toModel x) hx
  have hrat : Model.toRat? (ExecFloat.Binary.toModel x) = some d.toRat := by
    unfold Model.toRat?; rw [hd]; rfl
  have hcast : (d.toRat : ℝ) = x.toReal := by
    have h := Model.cast_toRat_eq_toReal (ExecFloat.Binary.toModel x)
    rw [hrat] at h
    simpa [ExecFloat.Binary.toReal] using h
  have hnz : Model.isZero (ExecFloat.Binary.toModel x) = false := by
    cases hz : Model.isZero (ExecFloat.Binary.toModel x) with
    | false => rfl
    | true =>
      exfalso
      have h0 : x.toReal = 0 := Model.toReal_eq_zero_of_isZero _ hz
      linarith
  change Model.isFinite (ExecFloat.Binary.toModel (ExecFloat.Binary.pown x e)) = true
  rw [ExecFloat.Binary.toModel_pown, Model.pown_eq_roundAlgebraicRat _ e hrat hnz he,
    Model.roundAlgebraicRat, Model.roundRat]
  refine Model.isFinite_roundRatScaled_of_abs_le_posMaxFinite FloatFormat.binary64
    _ _ _ 0 FloatFormat.isIEEE_binary64 (d.toRat ^ e).den_nz ?_
  rw [signedScaledRatToReal_eq_rat, Rat.cast_zpow, hcast]
  exact hrange

private theorem add_finite_and_bound {a b : Binary64} {B : ℝ}
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hsum : |a.toReal + b.toReal| ≤ B) (hΩ : B ≤ Ω64) :
    (a + b).isFinite = true ∧ |(a + b).toReal| ≤ (1 + u64) * B + η64 := by
  have hfin : (a + b).isFinite = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (a + b)) = true
    rw [ExecFloat.Binary.toModel_hAdd]
    exact Model.isFinite_add_of_abs_toReal_add_le_posMaxFinite _ _
      FloatFormat.isIEEE_binary64 ha hb (hsum.trans hΩ)
  have hround : (a + b).toReal = Model.roundAt FloatFormat.binary64 (a.toReal + b.toReal) :=
    ExecFloat.Binary.toReal_add_eq_roundAt hfin
  have herr := Model.abs_roundAt_sub_le_unitRoundoffAt FloatFormat.binary64 (a.toReal + b.toReal)
  rw [← hround] at herr
  have habs : |(a + b).toReal| ≤ |a.toReal + b.toReal| + |(a + b).toReal - (a.toReal + b.toReal)| := by
    have hsplit : (a + b).toReal = (a.toReal + b.toReal) + ((a + b).toReal - (a.toReal + b.toReal)) := by ring
    conv_lhs => rw [hsplit]
    exact abs_add_le _ _
  have hu0 : 0 ≤ u64 := u64_pos'.le
  exact ⟨hfin, by nlinarith⟩

private theorem sub_finite_and_bound {a b : Binary64} {B : ℝ}
    (ha : a.isFinite = true) (hb : b.isFinite = true)
    (hsub : |a.toReal - b.toReal| ≤ B) (hΩ : B ≤ Ω64) :
    (a - b).isFinite = true ∧ |(a - b).toReal| ≤ (1 + u64) * B + η64 := by
  have hfin : (a - b).isFinite = true := by
    change Model.isFinite (ExecFloat.Binary.toModel (a - b)) = true
    rw [ExecFloat.Binary.toModel_hSub]
    exact Model.isFinite_sub_of_abs_toReal_sub_le_posMaxFinite _ _
      FloatFormat.isIEEE_binary64 ha hb (hsub.trans hΩ)
  have hround : (a - b).toReal = Model.roundAt FloatFormat.binary64 (a.toReal - b.toReal) :=
    ExecFloat.Binary.toReal_sub_eq_roundAt hfin
  have herr := Model.abs_roundAt_sub_le_unitRoundoffAt FloatFormat.binary64 (a.toReal - b.toReal)
  rw [← hround] at herr
  have habs : |(a - b).toReal| ≤ |a.toReal - b.toReal| + |(a - b).toReal - (a.toReal - b.toReal)| := by
    have hsplit : (a - b).toReal = (a.toReal - b.toReal) + ((a - b).toReal - (a.toReal - b.toReal)) := by ring
    conv_lhs => rw [hsplit]
    exact abs_add_le _ _
  have hu0 : 0 ≤ u64 := u64_pos'.le
  exact ⟨hfin, by nlinarith⟩

/-- One `sum2Step` preserves finiteness and keeps both state components bounded by `4 * B`
    whenever `1 ≤ B` and `64 * B ≤ Ω64`. -/
private theorem sum2Step_finite_and_bound (st : Binary64 × Binary64) (v : Binary64) (B : ℝ)
    (hs : st.1.isFinite = true) (hc : st.2.isFinite = true) (hv : v.isFinite = true)
    (hB1 : 1 ≤ B) (hΩ : 64 * B ≤ Ω64)
    (hbs : |st.1.toReal| ≤ B) (hbc : |st.2.toReal| ≤ B) (hbv : |v.toReal| ≤ B) :
    ExecFloat.Binary.isFinite (ExecFloat.Binary.sum2Step st v).1 = true ∧
    ExecFloat.Binary.isFinite (ExecFloat.Binary.sum2Step st v).2 = true ∧
    |ExecFloat.Binary.toReal (ExecFloat.Binary.sum2Step st v).1| ≤ 4 * B ∧
    |ExecFloat.Binary.toReal (ExecFloat.Binary.sum2Step st v).2| ≤ 4 * B := by
  have hu : u64 ≤ 1 / 1000 := u64_le_tiny'
  have hη : η64 ≤ 1 / 1000 := by linarith [η64_le_u64_div', u64_le_tiny']
  have hη0 : 0 ≤ η64 := η64_pos'.le
  have hu0 : 0 ≤ u64 := u64_pos'.le
  dsimp only [ExecFloat.Binary.sum2Step]
  set s : Binary64 := st.1
  set c : Binary64 := st.2
  have hs' := add_finite_and_bound hs hv
    (show |s.toReal + v.toReal| ≤ 2 * B from (abs_add_le _ _).trans (by linarith)) (by linarith)
  have hs'B : |(s + v).toReal| ≤ 3 * B := by nlinarith [hs'.2]
  have ha' := sub_finite_and_bound hs'.1 hv
    (show |(s + v).toReal - v.toReal| ≤ 4 * B from (abs_sub _ _).trans (by linarith)) (by linarith)
  have ha'B : |((s + v) - v).toReal| ≤ 5 * B := by nlinarith [ha'.2]
  have hb' := sub_finite_and_bound hs'.1 ha'.1
    (show |(s + v).toReal - ((s + v) - v).toReal| ≤ 8 * B from (abs_sub _ _).trans (by linarith)) (by linarith)
  have hb'B : |((s + v) - ((s + v) - v)).toReal| ≤ 10 * B := by nlinarith [hb'.2]
  have hδa := sub_finite_and_bound hs ha'.1
    (show |s.toReal - ((s + v) - v).toReal| ≤ 6 * B from (abs_sub _ _).trans (by linarith)) (by linarith)
  have hδaB : |(s - ((s + v) - v)).toReal| ≤ 8 * B := by nlinarith [hδa.2]
  have hδb := sub_finite_and_bound hv hb'.1
    (show |v.toReal - ((s + v) - ((s + v) - v)).toReal| ≤ 11 * B from (abs_sub _ _).trans (by linarith)) (by linarith)
  have hδbB : |(v - ((s + v) - ((s + v) - v))).toReal| ≤ 14 * B := by nlinarith [hδb.2]
  have hq := add_finite_and_bound hδa.1 hδb.1
    (show |(s - ((s + v) - v)).toReal + (v - ((s + v) - ((s + v) - v))).toReal| ≤ 22 * B from
      (abs_add_le _ _).trans (by linarith)) (by linarith)
  have htwo := ExecFloat.Binary.toReal_twoSum hq.1
  have hs'_err : |(s + v).toReal - (s.toReal + v.toReal)| ≤ u64 * (2 * B) + η64 := by
    have hr : (s + v).toReal = Model.roundAt FloatFormat.binary64 (s.toReal + v.toReal) :=
      ExecFloat.Binary.toReal_add_eq_roundAt hs'.1
    have he := Model.abs_roundAt_sub_le_unitRoundoffAt FloatFormat.binary64 (s.toReal + v.toReal)
    rw [← hr] at he
    have hab : |s.toReal + v.toReal| ≤ 2 * B := (abs_add_le _ _).trans (by linarith)
    nlinarith
  have hq_tight : |((s - ((s + v) - v)) + (v - ((s + v) - ((s + v) - v)))).toReal| ≤ B := by
    have hqeq : ((s - ((s + v) - v)) + (v - ((s + v) - ((s + v) - v)))).toReal =
        -((s + v).toReal - (s.toReal + v.toReal)) := by linarith
    rw [hqeq, abs_neg]
    nlinarith
  have hc'_tight := add_finite_and_bound hc hq.1
    (show |c.toReal + ((s - ((s + v) - v)) + (v - ((s + v) - ((s + v) - v)))).toReal| ≤ 2 * B from
      (abs_add_le _ _).trans (by linarith)) (by linarith)
  refine ⟨hs'.1, hc'_tight.1, by linarith, by nlinarith [hc'_tight.2]⟩

private theorem evalTermB64_finite (bigN : Binary64) (e c : Rat)
    (hN : bigN.isFinite = true) (hN_pos : 0 < bigN.toReal) (he : e.num ≠ 0)
    (hc_range : |(c : ℝ)| ≤ Ω64) (hp_range : |bigN.toReal ^ e.num| ≤ Ω64)
    (hprod_range : ((1 + u64) * |(c : ℝ)| + η64) * ((1 + u64) * |bigN.toReal ^ e.num| + η64) ≤ Ω64) :
    (ExecFloat.Binary.ofRat c : Binary64).isFinite = true ∧
    (ExecFloat.Binary.pown bigN e.num).isFinite = true ∧
    (evalTermB64 bigN (e, c)).isFinite = true := by
  have hc : (ExecFloat.Binary.ofRat c : Binary64).isFinite = true :=
    isFinite_ratToBinary64 c hc_range
  have hp : (ExecFloat.Binary.pown bigN e.num).isFinite = true :=
    isFinite_pown_of_pos_le bigN e.num hN hN_pos he hp_range
  have hmul : (evalTermB64 bigN (e, c)).isFinite = true := by
    change Model.isFinite (ExecFloat.Binary.toModel
      ((ExecFloat.Binary.ofRat c : Binary64) * ExecFloat.Binary.pown bigN e.num)) = true
    rw [ExecFloat.Binary.toModel_hMul]
    refine Model.isFinite_mul_of_abs_mul_le_posMaxFinite _ _
      FloatFormat.isIEEE_binary64 hc hp ?_
    change |(ExecFloat.Binary.ofRat c : Binary64).toReal| *
        |(ExecFloat.Binary.pown bigN e.num).toReal| ≤ Ω64
    have hcr : |(ExecFloat.Binary.ofRat c : Binary64).toReal| ≤ (1 + u64) * |(c : ℝ)| + η64 := by
      have he := (mixedError_ratToBinary64 c hc).bound
      unfold ratToBinary64 at he
      have htri : |(ExecFloat.Binary.ofRat c : Binary64).toReal| ≤
          |(c : ℝ)| + |(ExecFloat.Binary.ofRat c : Binary64).toReal - (c : ℝ)| := by
        have hs : (ExecFloat.Binary.ofRat c : Binary64).toReal =
            (c : ℝ) + ((ExecFloat.Binary.ofRat c : Binary64).toReal - (c : ℝ)) := by ring
        conv_lhs => rw [hs]
        exact abs_add_le _ _
      linarith
    have hpr : |(ExecFloat.Binary.pown bigN e.num).toReal| ≤
        (1 + u64) * |bigN.toReal ^ e.num| + η64 := by
      have hround := ExecFloat.Binary.toReal_pown_eq_roundAt bigN e.num hN hp
      have he : |(ExecFloat.Binary.pown bigN e.num).toReal - bigN.toReal ^ e.num| ≤
          u64 * |bigN.toReal ^ e.num| + η64 :=
        (ExecFloat.Binary.mixedError_toReal_of_eq_roundAt hround).bound
      have htri : |(ExecFloat.Binary.pown bigN e.num).toReal| ≤
          |bigN.toReal ^ e.num| + |(ExecFloat.Binary.pown bigN e.num).toReal - bigN.toReal ^ e.num| := by
        have hs : (ExecFloat.Binary.pown bigN e.num).toReal =
            bigN.toReal ^ e.num + ((ExecFloat.Binary.pown bigN e.num).toReal - bigN.toReal ^ e.num) := by ring
        conv_lhs => rw [hs]
        exact abs_add_le _ _
      linarith
    have hu0 : 0 ≤ u64 := u64_pos'.le
    have hη0 : 0 ≤ η64 := η64_pos'.le
    exact (mul_le_mul hcr hpr (abs_nonneg _) (by positivity)).trans hprod_range
  exact ⟨hc, hp, hmul⟩

private theorem termRelBound_le : termRelBound ≤ (31 / 10 : ℝ) * u64 := by
  have hu0 : 0 ≤ u64 := u64_pos'.le
  have hu : u64 ≤ 1 / 1000 := u64_le_tiny'
  have hu2 : u64 * u64 ≤ u64 / 1000 := by nlinarith
  have hu3 : u64 * (u64 * u64) ≤ u64 / 1000 := by nlinarith
  unfold termRelBound
  have hexp : (1 + u64) * (u64 + u64 + u64 * u64) + u64 =
      3 * u64 + 3 * (u64 * u64) + u64 * (u64 * u64) := by ring
  linarith

private theorem dirac_term1_err {N : ℝ} (hge : 2 ≤ N) :
    termErrorBound (1 / 4) (N ^ (1 : ℤ)) ≤ u64 * N := by
  have hu0 : 0 ≤ u64 := u64_pos'.le
  have hu : u64 ≤ 1 / 1000 := u64_le_tiny'
  have hη0 : 0 ≤ η64 := η64_pos'.le
  have hη : η64 ≤ u64 / 1000 := η64_le_u64_div'
  have hrel := termRelBound_le
  have hNpos : 0 < N := by linarith
  unfold termErrorBound termAbsBound
  rw [zpow_one, abs_of_pos (show 0 < 1 / 4 * N by positivity), abs_of_pos hNpos,
    abs_of_pos (show (0 : ℝ) < 1 / 4 by norm_num)]
  have hm1 : termRelBound * (1 / 4 * N) ≤ (31 / 40 : ℝ) * (u64 * N) := by
    have h := mul_le_mul_of_nonneg_right hrel (show (0 : ℝ) ≤ 1 / 4 * N by positivity)
    linarith [show ((31 / 10 : ℝ) * u64) * (1 / 4 * N) = (31 / 40 : ℝ) * (u64 * N) by ring]
  have hηN : η64 * N ≤ (u64 / 1000) * N := mul_le_mul_of_nonneg_right hη hNpos.le
  have hη1 : (1 + u64) * ((1 + u64) * η64 * N + (1 + u64) * η64 * (1 / 4) + η64 * η64) + η64 ≤
      (1 / 10 : ℝ) * (u64 * N) := by
    have hη2 : η64 * η64 ≤ η64 := by nlinarith
    have hηa : (1 + u64) * (η64 * N) ≤ 2 * ((u64 / 1000) * N) :=
      mul_le_mul (by linarith) hηN (by positivity) (by norm_num)
    have hηb : (1 + u64) * η64 * (1 / 4) ≤ (u64 / 1000) * N := by nlinarith
    have hηc : η64 * η64 ≤ (u64 / 1000) * N := by nlinarith
    have hsum : (1 + u64) * η64 * N + (1 + u64) * η64 * (1 / 4) + η64 * η64 ≤
        4 * ((u64 / 1000) * N) := by linarith [show (1 + u64) * η64 * N = (1 + u64) * (η64 * N) by ring]
    have hmul : (1 + u64) * ((1 + u64) * η64 * N + (1 + u64) * η64 * (1 / 4) + η64 * η64) ≤
        2 * (4 * ((u64 / 1000) * N)) :=
      mul_le_mul (by linarith) hsum (by positivity) (by norm_num)
    nlinarith
  have huN0 : 0 ≤ u64 * N := by positivity
  linarith

private theorem dirac_term2_err {N : ℝ} (hge : 2 ≤ N) :
    termErrorBound (-1 / 48) (N ^ (-1 : ℤ)) ≤ (1 / 10 : ℝ) * u64 * N := by
  have hu0 : 0 ≤ u64 := u64_pos'.le
  have hu : u64 ≤ 1 / 1000 := u64_le_tiny'
  have hη0 : 0 ≤ η64 := η64_pos'.le
  have hη : η64 ≤ u64 / 1000 := η64_le_u64_div'
  have hrel := termRelBound_le
  have hNpos : 0 < N := by linarith
  have hinv : N⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hNpos (by norm_num)]; linarith
  have hinv0 : 0 ≤ N⁻¹ := by positivity
  unfold termErrorBound termAbsBound
  rw [zpow_neg_one, abs_mul, abs_of_pos (inv_pos.mpr hNpos)]
  have h148 : |(-1 / 48 : ℝ)| = 1 / 48 := by norm_num
  rw [h148]
  have hm1 : termRelBound * (1 / 48 * N⁻¹) ≤ ((31 / 10 : ℝ) * u64) * (1 / 96) :=
    mul_le_mul hrel (by linarith) (by positivity) (by linarith)
  have hη2 : η64 * η64 ≤ η64 := by nlinarith
  have hinner : (1 + u64) * η64 * N⁻¹ + (1 + u64) * η64 * (1 / 48) + η64 * η64 ≤ 3 * η64 := by
    have ha : (1 + u64) * η64 * N⁻¹ ≤ (1 + u64) * η64 * (1 / 2) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    nlinarith
  have houter : (1 + u64) * ((1 + u64) * η64 * N⁻¹ + (1 + u64) * η64 * (1 / 48) + η64 * η64) ≤
      2 * (3 * η64) :=
    mul_le_mul (by linarith) hinner (by positivity) (by norm_num)
  nlinarith

private theorem dirac_term3_err {N : ℝ} (hge : 2 ≤ N) :
    termErrorBound (1 / 480) (N ^ (-3 : ℤ)) ≤ (1 / 10 : ℝ) * u64 * N := by
  have hu0 : 0 ≤ u64 := u64_pos'.le
  have hu : u64 ≤ 1 / 1000 := u64_le_tiny'
  have hη0 : 0 ≤ η64 := η64_pos'.le
  have hη : η64 ≤ u64 / 1000 := η64_le_u64_div'
  have hrel := termRelBound_le
  have hNpos : 0 < N := by linarith
  have hz : N ^ (-3 : ℤ) = (N ^ (3 : ℕ))⁻¹ := by
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
  have hN3 : 8 ≤ N ^ (3 : ℕ) := by nlinarith [show N ^ (3 : ℕ) = N * N * N by ring]
  have hinv : (N ^ (3 : ℕ))⁻¹ ≤ 1 / 8 := by rw [inv_le_comm₀ (by positivity) (by norm_num)]; linarith
  have hinv0 : 0 ≤ (N ^ (3 : ℕ))⁻¹ := by positivity
  unfold termErrorBound termAbsBound
  rw [hz, abs_mul, abs_of_pos (show 0 < (N ^ (3 : ℕ))⁻¹ by positivity)]
  have h1480 : |(1 / 480 : ℝ)| = 1 / 480 := by norm_num
  rw [h1480]
  have hm1 : termRelBound * (1 / 480 * (N ^ (3 : ℕ))⁻¹) ≤ ((31 / 10 : ℝ) * u64) * (1 / 3840) :=
    mul_le_mul hrel (by linarith) (by positivity) (by linarith)
  have hη2 : η64 * η64 ≤ η64 := by nlinarith
  have hinner : (1 + u64) * η64 * (N ^ (3 : ℕ))⁻¹ + (1 + u64) * η64 * (1 / 480) + η64 * η64 ≤
      3 * η64 := by
    have ha : (1 + u64) * η64 * (N ^ (3 : ℕ))⁻¹ ≤ (1 + u64) * η64 * (1 / 8) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    nlinarith
  have houter : (1 + u64) * ((1 + u64) * η64 * (N ^ (3 : ℕ))⁻¹ + (1 + u64) * η64 * (1 / 480) + η64 * η64) ≤
      2 * (3 * η64) :=
    mul_le_mul (by linarith) hinner (by positivity) (by norm_num)
  nlinarith

/-- **Theorem 4A (`diracCenter_bridge`)**: End-to-end symbolic-to-float Dirac delta peak bridge
    at `x = 0` for any normal IEEE-754 `Binary64` scale `2 ≤ N ≤ 2^50`:
    `|fl(evalFiniteSum2 diracCenterLC N) - N / 4| ≤ 1 / (48 * N) + 5 * u64 * N`. -/
theorem diracCenter_bridge (bigN : Binary64) (hN : bigN.isFinite = true)
    (hge : 2 ≤ bigN.toReal) (hle : bigN.toReal ≤ 2 ^ 50) :
    |(evalFiniteSum2 diracCenterLC bigN).toReal - bigN.toReal / 4| ≤
      1 / (48 * bigN.toReal) + 5 * u64 * bigN.toReal := by
  set N : ℝ := bigN.toReal
  have hNpos : 0 < N := by linarith
  have hu0 : 0 ≤ u64 := u64_pos'.le
  have hu : u64 ≤ 1 / 1000 := u64_le_tiny'
  have hη0 : 0 ≤ η64 := η64_pos'.le
  have hη : η64 ≤ u64 / 1000 := η64_le_u64_div'
  have hΩ100 : (2 : ℝ) ^ (100 : ℕ) ≤ Ω64 := two_pow_100_le_Ω64
  have hpow50 : (2 : ℝ) ^ (50 : ℕ) * (2 : ℝ) ^ (50 : ℕ) = (2 : ℝ) ^ (100 : ℕ) := by rw [← pow_add]
  have h2_50_pos : (1 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ) := one_le_pow₀ (by norm_num)
  have hN_le_Ω : N ≤ Ω64 := by nlinarith
  have h64_le_Ω : 64 * ((2 : ℝ) ^ (50 : ℕ) * 16) ≤ Ω64 := by
    have h1024 : (1024 : ℝ) ≤ (2 : ℝ) ^ (50 : ℕ) := by
      calc (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
        _ ≤ (2 : ℝ) ^ (50 : ℕ) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  have hc1 : ((mkRat 1 4 : Rat) : ℝ) = 1 / 4 := by norm_num [mkRat]
  have hc2 : ((mkRat (-1) 48 : Rat) : ℝ) = -1 / 48 := by norm_num [mkRat]
  have hc3 : ((mkRat 1 480 : Rat) : ℝ) = 1 / 480 := by norm_num [mkRat]
  have hN3_zpow : N ^ (-3 : ℤ) = (N ^ (3 : ℕ))⁻¹ := by
    rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) from rfl, zpow_neg, zpow_natCast]
  -- Step 1: Exact mathematical difference `|evalExactInt diracCenterLC N - N / 4| ≤ 1 / (48 * N)`
  have hexact_val : diracCenterLC.evalExactInt N =
      N / 4 - 1 / (48 * N) + 1 / (480 * N ^ (3 : ℕ)) := by
    unfold FastLC.evalExactInt
    rw [diracCenterLC_terms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hc1, hc2, hc3]
    have he1 : (1 : Rat).num = 1 := rfl
    have he2 : (-1 : Rat).num = -1 := rfl
    have he3 : (-3 : Rat).num = -3 := rfl
    rw [he1, he2, he3, zpow_one, zpow_neg_one, hN3_zpow]
    field_simp [hNpos.ne']
    ring
  have hexact_err : |diracCenterLC.evalExactInt N - N / 4| ≤ 1 / (48 * N) := by
    rw [hexact_val]
    have hdiff : (N / 4 - 1 / (48 * N) + 1 / (480 * N ^ (3 : ℕ))) - N / 4 =
        -(1 / (48 * N) - 1 / (480 * N ^ (3 : ℕ))) := by ring
    rw [hdiff, abs_neg]
    have hpos3 : 0 < 1 / (480 * N ^ (3 : ℕ)) := by positivity
    have hge_diff : 0 ≤ 1 / (48 * N) - 1 / (480 * N ^ (3 : ℕ)) := by
      have hle' : 1 / (480 * N ^ (3 : ℕ)) ≤ 1 / (48 * N) := by
        refine one_div_le_one_div_of_le (by positivity) ?_
        have hN2 : 4 ≤ N ^ 2 := by nlinarith
        nlinarith [show N ^ (3 : ℕ) = N * N ^ 2 by ring]
      linarith
    rw [abs_of_nonneg hge_diff]
    linarith
  -- Step 2: Finiteness of all 3 terms
  have hinv1 : |N ^ (-1 : ℤ)| ≤ 1 := by
    rw [zpow_neg_one, abs_of_pos (inv_pos.mpr hNpos)]
    exact inv_le_one_of_one_le₀ (by linarith)
  have hinv3 : |N ^ (-3 : ℤ)| ≤ 1 := by
    rw [hN3_zpow, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by nlinarith [show N ^ (3 : ℕ) = N * N * N by ring])
  have ht1_fin :
      (ExecFloat.Binary.ofRat (mkRat 1 4) : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN (1 : Rat).num).isFinite = true ∧
      (evalTermB64 bigN (1, mkRat 1 4)).isFinite = true := by
    refine evalTermB64_finite bigN 1 (mkRat 1 4) hN hNpos (by decide) ?_ ?_ ?_
    · rw [hc1]; norm_num; linarith
    · change |N ^ (1 : ℤ)| ≤ Ω64
      rw [zpow_one, abs_of_pos hNpos]; exact hN_le_Ω
    · change ((1 + u64) * |((mkRat 1 4 : Rat) : ℝ)| + η64) *
        ((1 + u64) * |N ^ (1 : ℤ)| + η64) ≤ Ω64
      rw [hc1, zpow_one, abs_of_pos hNpos]
      have h14 : |(1 / 4 : ℝ)| = 1 / 4 := by norm_num
      rw [h14]
      have hf1 : (1 + u64) * (1 / 4 : ℝ) + η64 ≤ 1 / 2 := by nlinarith
      have hf2 : (1 + u64) * N + η64 ≤ 2 * N := by nlinarith
      have hmul := mul_le_mul hf1 hf2 (by positivity) (by norm_num)
      linarith
  have ht2_fin :
      (ExecFloat.Binary.ofRat (mkRat (-1) 48) : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN (-1 : Rat).num).isFinite = true ∧
      (evalTermB64 bigN (-1, mkRat (-1) 48)).isFinite = true := by
    refine evalTermB64_finite bigN (-1) (mkRat (-1) 48) hN hNpos (by decide) ?_ ?_ ?_
    · rw [hc2]; norm_num; linarith
    · change |N ^ (-1 : ℤ)| ≤ Ω64; linarith
    · change ((1 + u64) * |((mkRat (-1) 48 : Rat) : ℝ)| + η64) *
        ((1 + u64) * |N ^ (-1 : ℤ)| + η64) ≤ Ω64
      rw [hc2]
      have h148 : |(-1 / 48 : ℝ)| = 1 / 48 := by norm_num
      rw [h148]
      have hf1 : (1 + u64) * (1 / 48 : ℝ) + η64 ≤ 1 := by nlinarith
      have hf2 : (1 + u64) * |N ^ (-1 : ℤ)| + η64 ≤ 2 := by nlinarith
      have hmul := mul_le_mul hf1 hf2 (by positivity) (by norm_num)
      linarith
  have ht3_fin :
      (ExecFloat.Binary.ofRat (mkRat 1 480) : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN (-3 : Rat).num).isFinite = true ∧
      (evalTermB64 bigN (-3, mkRat 1 480)).isFinite = true := by
    refine evalTermB64_finite bigN (-3) (mkRat 1 480) hN hNpos (by decide) ?_ ?_ ?_
    · rw [hc3]; norm_num; linarith
    · change |N ^ (-3 : ℤ)| ≤ Ω64; linarith
    · change ((1 + u64) * |((mkRat 1 480 : Rat) : ℝ)| + η64) *
        ((1 + u64) * |N ^ (-3 : ℤ)| + η64) ≤ Ω64
      rw [hc3]
      have h1480 : |(1 / 480 : ℝ)| = 1 / 480 := by norm_num
      rw [h1480]
      have hf1 : (1 + u64) * (1 / 480 : ℝ) + η64 ≤ 1 := by nlinarith
      have hf2 : (1 + u64) * |N ^ (-3 : ℤ)| + η64 ≤ 2 := by nlinarith
      have hmul := mul_le_mul hf1 hf2 (by positivity) (by norm_num)
      linarith
  have hterms : ∀ p ∈ diracCenterLC.terms,
      (ExecFloat.Binary.ofRat p.2 : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN p.1.num).isFinite = true ∧
      (evalTermB64 bigN p).isFinite = true := by
    rw [diracCenterLC_terms]
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · exact ht1_fin
    · exact ht2_fin
    · exact ht3_fin
  -- Step 3: Per-term error bounds and magnitudes
  set t1 := evalTermB64 bigN (1, mkRat 1 4)
  set t2 := evalTermB64 bigN (-1, mkRat (-1) 48)
  set t3 := evalTermB64 bigN (-3, mkRat 1 480)
  have hb1 : termErrorBound (1 / 4) (N ^ (1 : ℤ)) ≤ u64 * N := dirac_term1_err hge
  have hb2 : termErrorBound (-1 / 48) (N ^ (-1 : ℤ)) ≤ (1 / 10 : ℝ) * u64 * N := dirac_term2_err hge
  have hb3 : termErrorBound (1 / 480) (N ^ (-3 : ℤ)) ≤ (1 / 10 : ℝ) * u64 * N := dirac_term3_err hge
  have huN_le : u64 * N ≤ (1 / 1000 : ℝ) * N := mul_le_mul_of_nonneg_right hu hNpos.le
  have ht1_abs : |t1.toReal| ≤ (1 / 2 : ℝ) * N := by
    have herr := evalTermB64_abs_sub_le bigN 1 (mkRat 1 4) hN ht1_fin.1 ht1_fin.2.1 ht1_fin.2.2
    rw [hc1] at herr
    have herr' : |t1.toReal - 1 / 4 * N| ≤ u64 * N := by
      simpa [t1, zpow_one] using herr.trans hb1
    have h := abs_sub_le_iff.mp herr'
    rw [abs_le]; constructor <;> linarith
  have ht2_abs : |t2.toReal| ≤ (1 / 8 : ℝ) * N := by
    have herr := evalTermB64_abs_sub_le bigN (-1) (mkRat (-1) 48) hN ht2_fin.1 ht2_fin.2.1 ht2_fin.2.2
    rw [hc2] at herr
    have herr' : |t2.toReal - (-1 / 48) * N⁻¹| ≤ (1 / 10 : ℝ) * u64 * N := by
      simpa [t2, zpow_neg_one] using herr.trans hb2
    have h := abs_sub_le_iff.mp herr'
    have hinv : N⁻¹ ≤ 1 / 2 := by rw [inv_le_comm₀ hNpos (by norm_num)]; linarith
    have hinv0 : 0 ≤ N⁻¹ := by positivity
    rw [abs_le]; constructor <;> linarith
  have ht3_abs : |t3.toReal| ≤ (1 / 8 : ℝ) * N := by
    have herr := evalTermB64_abs_sub_le bigN (-3) (mkRat 1 480) hN ht3_fin.1 ht3_fin.2.1 ht3_fin.2.2
    rw [hc3] at herr
    have herr' : |t3.toReal - 1 / 480 * (N ^ (3 : ℕ))⁻¹| ≤ (1 / 10 : ℝ) * u64 * N := by
      have he3 : (-3 : Rat).num = -3 := rfl
      rw [he3] at herr
      have hcomb := herr.trans hb3
      rwa [hN3_zpow] at hcomb
    have h := abs_sub_le_iff.mp herr'
    have hinv : (N ^ (3 : ℕ))⁻¹ ≤ 1 / 8 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      nlinarith [show N ^ (3 : ℕ) = N * N * N by ring]
    have hinv0 : 0 ≤ (N ^ (3 : ℕ))⁻¹ := by positivity
    rw [abs_le]; constructor <;> linarith
  -- Step 4: Verify `sum2Step` finiteness `hsteps` and range `hrange`
  have h0fin : ((0 : Binary64).isFinite) = true := ExecFloat.Binary.isFinite_zero
  have h0real : ((0 : Binary64).toReal) = 0 := by simp
  have hstep1 := sum2Step_finite_and_bound ((0 : Binary64), (0 : Binary64)) t1
    ((2 : ℝ) ^ (50 : ℕ)) h0fin h0fin ht1_fin.2.2 h2_50_pos (by linarith)
    (by rw [h0real, abs_zero]; linarith) (by rw [h0real, abs_zero]; linarith) (by linarith)
  have hstep2 := sum2Step_finite_and_bound (ExecFloat.Binary.sum2Step (0, 0) t1) t2
    (4 * (2 : ℝ) ^ (50 : ℕ)) hstep1.1 hstep1.2.1 ht2_fin.2.2 (by linarith) (by linarith)
    hstep1.2.2.1 hstep1.2.2.2 (by linarith)
  have hstep3 := sum2Step_finite_and_bound
    (ExecFloat.Binary.sum2Step (ExecFloat.Binary.sum2Step (0, 0) t1) t2) t3
    (16 * (2 : ℝ) ^ (50 : ℕ)) hstep2.1 hstep2.2.1 ht3_fin.2.2 (by linarith) (by linarith)
    (by linarith [hstep2.2.2.1]) (by linarith [hstep2.2.2.2]) (by linarith)
  have hsteps : List.AllSteps ExecFloat.Binary.sum2Step
      (fun (st : Binary64 × Binary64) (v : Binary64) =>
        ExecFloat.Binary.isFinite (ExecFloat.Binary.sum2Step st v).2 = true)
      ((0 : Binary64), (0 : Binary64)) (diracCenterLC.terms.map (evalTermB64 bigN)) := by
    rw [diracCenterLC_terms]
    exact ⟨hstep1.2.1, hstep2.2.1, hstep3.2.1, trivial⟩
  have hn : (diracCenterLC.terms.length : ℝ) * u64 ≤ 1 / 8 := by
    rw [diracCenterLC_terms]; norm_num; linarith
  have hxs_eq : diracCenterLC.terms.map (evalTermB64 bigN) = [t1, t2, t3] := by
    simp [diracCenterLC_terms, t1, t2, t3]
  have hsum_abs_list : ([t1, t2, t3].map fun t => |t.toReal|).sum ≤ N := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    linarith
  have hsum_val_list : |([t1, t2, t3].map ExecFloat.Binary.toReal).sum| ≤ N := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    have htri : |t1.toReal + (t2.toReal + t3.toReal)| ≤ |t1.toReal| + |t2.toReal| + |t3.toReal| := by
      calc |t1.toReal + (t2.toReal + t3.toReal)|
          ≤ |t1.toReal| + |t2.toReal + t3.toReal| := abs_add_le _ _
        _ ≤ |t1.toReal| + (|t2.toReal| + |t3.toReal|) := add_le_add le_rfl (abs_add_le _ _)
        _ = |t1.toReal| + |t2.toReal| + |t3.toReal| := by ring
    linarith
  have hrange : |((diracCenterLC.terms.map (evalTermB64 bigN)).map ExecFloat.Binary.toReal).sum| +
      (ExecFloat.Binary.sum2Budgets (diracCenterLC.terms.map (evalTermB64 bigN))).1 ≤ Ω64 := by
    rw [hxs_eq]
    have hn3 : (([t1, t2, t3] : List Binary64).length : ℝ) * u64 ≤ 1 / 8 := by
      simp only [List.length_cons, List.length_nil]; norm_num; linarith
    have hbud : (ExecFloat.Binary.sum2Budgets [t1, t2, t3]).1 ≤
        2 * (([t1, t2, t3] : List Binary64).length : ℝ) ^ 2 * u64 ^ 2 *
          ([t1, t2, t3].map fun t => |t.toReal|).sum :=
      (ExecFloat.Binary.sum2Budgets_le [t1, t2, t3] hn3).1
    have hlen3 : (([t1, t2, t3] : List Binary64).length : ℝ) = 3 := by norm_num
    rw [hlen3] at hbud
    have hu2 : 2 * (3 : ℝ) ^ 2 * u64 ^ 2 ≤ 1 := by nlinarith only [hu0, hu]
    have hposA : 0 ≤ ([t1, t2, t3].map fun t => |t.toReal|).sum := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; positivity
    have hmul := mul_le_mul hu2 hsum_abs_list hposA (by norm_num)
    have h2N : 2 * N ≤ Ω64 := by nlinarith only [hle, hpow50, h2_50_pos, hΩ100, hNpos]
    linarith only [hsum_val_list, hbud, hmul, h2N]
  -- Step 5: Apply Theorem 2B and combine with `hexact_err`
  have h2b := abs_toReal_evalFiniteSum2_sub_evalExactInt_le diracCenterLC bigN
    hN hterms hsteps hrange hn
  rw [hxs_eq] at h2b
  have hterm_sum_le :
      (diracCenterLC.terms.map fun (e, c) => termErrorBound (c : ℝ) (N ^ e.num)).sum ≤
        3 * u64 * N := by
    rw [diracCenterLC_terms]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rw [hc1, hc2, hc3]
    have he1 : (1 : Rat).num = 1 := rfl
    have he2 : (-1 : Rat).num = -1 := rfl
    have he3 : (-3 : Rat).num = -3 := rfl
    rw [he1, he2, he3]
    have huN0 : 0 ≤ u64 * N := by positivity
    linarith only [hb1, hb2, hb3, huN0]
  have hlen3 : (diracCenterLC.terms.length : ℝ) = 3 := by rw [diracCenterLC_terms]; norm_num
  rw [hlen3] at h2b
  have hsum2_le : |(evalFiniteSum2 diracCenterLC bigN).toReal - diracCenterLC.evalExactInt N| ≤
      5 * u64 * N := by
    have hposA : 0 ≤ ([t1, t2, t3].map fun t => |t.toReal|).sum := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]; positivity
    have hquad : (9 / 4 : ℝ) * (3 : ℝ) ^ 2 * u64 ^ 2 *
        ([t1, t2, t3].map fun t => |t.toReal|).sum ≤ u64 * N := by
      have hq2 : (9 / 4 : ℝ) * (3 : ℝ) ^ 2 * u64 ^ 2 ≤ u64 := by nlinarith only [hu0, hu]
      have hq3 := mul_le_mul hq2 hsum_abs_list hposA hu0
      linarith only [hq3]
    have hlin : u64 * |([t1, t2, t3].map ExecFloat.Binary.toReal).sum| ≤ u64 * N :=
      mul_le_mul_of_nonneg_left hsum_val_list hu0
    linarith only [h2b, hlin, hquad, hterm_sum_le]
  have htri : |(evalFiniteSum2 diracCenterLC bigN).toReal - N / 4| ≤
      |(evalFiniteSum2 diracCenterLC bigN).toReal - diracCenterLC.evalExactInt N| +
      |diracCenterLC.evalExactInt N - N / 4| := by
    have hs : (evalFiniteSum2 diracCenterLC bigN).toReal - N / 4 =
        ((evalFiniteSum2 diracCenterLC bigN).toReal - diracCenterLC.evalExactInt N) +
        (diracCenterLC.evalExactInt N - N / 4) := by ring
    rw [hs]
    exact abs_add_le _ _
  linarith

/-- **Theorem 4B (`diracCenter_at_100_certified`)**: Kernel-checked (`float_decide`, zero
    `native_decide`!) certification upgrading `TestSuite.lean` (`evalFinite(dstep(0), 100) ≈ 25.0`)
    to a machine-checked theorem (`24.99979 < v < 24.99980`). -/
theorem diracCenter_at_100_certified :
    let v : Binary64 := evalFiniteSum2 diracCenterLC 100
    (24.99979 : Binary64) < v ∧ v < (24.99980 : Binary64) := by
  change (24.99979 : Binary64) <
      ExecFloat.Binary.sum2
        [ExecFloat.Binary.ofRat (mkRat 1 4) * ExecFloat.Binary.pown (100 : Binary64) 1,
         ExecFloat.Binary.ofRat (mkRat (-1) 48) * ExecFloat.Binary.pown (100 : Binary64) (-1),
         ExecFloat.Binary.ofRat (mkRat 1 480) * ExecFloat.Binary.pown (100 : Binary64) (-3)] ∧
    ExecFloat.Binary.sum2
        [ExecFloat.Binary.ofRat (mkRat 1 4) * ExecFloat.Binary.pown (100 : Binary64) 1,
         ExecFloat.Binary.ofRat (mkRat (-1) 48) * ExecFloat.Binary.pown (100 : Binary64) (-1),
         ExecFloat.Binary.ofRat (mkRat 1 480) * ExecFloat.Binary.pown (100 : Binary64) (-3)] <
      (24.99980 : Binary64)
  float_decide

end FloatProofs
