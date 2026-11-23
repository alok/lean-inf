import FloatLib
import LeanInf.VerifiedRefactor

/-!
# T1: Exact Single-Rounding `Rat ↔ Binary64` & Lossless `Binary64 ↪ FastLC` Embedding

Replaces the unprovable `opaque Float.scaleB` / `Float.round` path (`FastLC.ratToFloat` /
`FastLC.ratOfFloat`) with `FloatLib`'s single-rounded `ExecFloat.Binary.ofRat` and exact
dyadic decoding `ExecFloat.Binary.toRat?`.
-/

namespace FloatProofs

open LeanInf
open FloatLib.Numerics
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- IEEE-754 binary64 unit roundoff (`2^(-53)`). -/
noncomputable abbrev u64 : ℝ := Model.unitRoundoffAt FloatFormat.binary64

/-- IEEE-754 binary64 underflow absolute error (`2^(-1075)`). -/
noncomputable abbrev η64 : ℝ := Model.underflowErrorAt FloatFormat.binary64

/-- Largest finite IEEE-754 binary64 real magnitude (`(2 - 2^(-52)) * 2^1023`). -/
noncomputable abbrev Ω64 : ℝ := Model.toReal (Model.posMaxFinite FloatFormat.binary64)

/-- Single-rounded IEEE-754 binary64 conversion of an exact rational. -/
def ratToBinary64 (r : Rat) : Binary64 :=
  ExecFloat.Binary.ofRat r

/-- Convert the standard part of a finite `FastLC` directly to `Binary64` via single rounding. -/
def stdPartBinary64 (x : FastLC) : Option Binary64 :=
  x.stdPart.map ratToBinary64

/-- Losslessly embed a finite IEEE-754 `Binary64` into `FastLC` via exact dyadic decoding. -/
def fastLCOfBinary64? (f : Binary64) : Option FastLC :=
  (ExecFloat.Binary.toRat? f).map FastLC.ofRat

/-- `ratToBinary64 r` is finite whenever `|r| ≤ Ω64`. -/
theorem isFinite_ratToBinary64 (r : Rat) (hrange : |(r : ℝ)| ≤ Ω64) :
    (ratToBinary64 r).isFinite = true := by
  unfold ratToBinary64 ExecFloat.Binary.isFinite
  rw [ExecFloat.Binary.toModel_ofRat]
  exact Model.isFinite_ofRat r FloatFormat.isIEEE_binary64 hrange

/-- Any finite `ratToBinary64 r` equals nearest-even rounding of `(r : ℝ)`. -/
theorem toReal_ratToBinary64_eq_roundAt (r : Rat)
    (hfin : (ratToBinary64 r).isFinite = true) :
    (ratToBinary64 r).toReal = Model.roundAt FloatFormat.binary64 (r : ℝ) := by
  unfold ratToBinary64 ExecFloat.Binary.toReal ExecFloat.Binary.isFinite at *
  rw [ExecFloat.Binary.toModel_ofRat] at hfin ⊢
  exact Model.toReal_ofRat_eq_roundAt r FloatFormat.isIEEE_binary64 hfin

/-- Any finite `ratToBinary64 r` satisfies the standard binary64 `MixedError` bound. -/
theorem mixedError_ratToBinary64 (r : Rat)
    (hfin : (ratToBinary64 r).isFinite = true) :
    MixedError (ratToBinary64 r).toReal (r : ℝ) u64 η64 :=
  ExecFloat.Binary.mixedError_toReal_of_eq_roundAt (toReal_ratToBinary64_eq_roundAt r hfin)

/-- **Theorem 1A (`ratToBinary64_spec`)**: Single-rounding exactness, finiteness, half-ULP
    error bound, and `MixedError` specification for `ratToBinary64`. -/
theorem ratToBinary64_spec (r : Rat) (hrange : |(r : ℝ)| ≤ Ω64) :
    (ratToBinary64 r).isFinite = true ∧
    (ratToBinary64 r).toReal = Model.roundAt FloatFormat.binary64 (r : ℝ) ∧
    |(ratToBinary64 r).toReal - (r : ℝ)| ≤ Model.halfUlpAt FloatFormat.binary64 (r : ℝ) ∧
    MixedError (ratToBinary64 r).toReal (r : ℝ) u64 η64 := by
  have hfin : (ratToBinary64 r).isFinite = true := isFinite_ratToBinary64 r hrange
  have hround : (ratToBinary64 r).toReal = Model.roundAt FloatFormat.binary64 (r : ℝ) :=
    toReal_ratToBinary64_eq_roundAt r hfin
  refine ⟨hfin, hround, ?_, mixedError_ratToBinary64 r hfin⟩
  rw [hround]
  exact Model.abs_roundAt_sub_le FloatFormat.binary64 (r : ℝ)

/-- `FastLC.ofRat q` is always finite (its sole term, if any, has exponent `0`). -/
theorem FastLC.isFinite_ofRat (q : Rat) : (FastLC.ofRat q).isFinite = true := by
  unfold FastLC.ofRat FastLC.mono FastLC.isFinite
  split_ifs
  · rfl
  · simp

/-- The standard part of `FastLC.ofRat q` is `some q`. -/
theorem FastLC.stdPart_ofRat (q : Rat) : (FastLC.ofRat q).stdPart = some q := by
  unfold FastLC.stdPart
  rw [FastLC.isFinite_ofRat q]
  simp only [↓reduceIte, Option.some.injEq]
  unfold FastLC.ofRat FastLC.mono FastLC.coeff
  split_ifs with h
  · have hq : q = 0 := eq_of_beq h
    subst hq
    rfl
  · simp [TermList.coeffOf]

/-- **Theorem 1B (`stdPart_fastLCOfBinary64?_roundtrip`)**: Every finite IEEE-754 `Binary64`
    embeds losslessly into `FastLC` and round-trips through `stdPart` and `ratToBinary64`
    with exact real-value preservation (zero precision loss). -/
theorem stdPart_fastLCOfBinary64?_roundtrip (f : Binary64) (hfin : f.isFinite = true) :
    ∃ q : Rat,
      fastLCOfBinary64? f = some (FastLC.ofRat q) ∧
      (FastLC.ofRat q).stdPart = some q ∧
      (q : ℝ) = f.toReal ∧
      (ratToBinary64 q).toReal = f.toReal := by
  obtain ⟨d, hd⟩ := Model.exists_toDyadic?_of_isFinite (x := ExecFloat.Binary.toModel f) hfin
  refine ⟨d.toRat, ?_, FastLC.stdPart_ofRat d.toRat, ?_, ?_⟩
  · unfold fastLCOfBinary64? ExecFloat.Binary.toRat? Model.toRat?
    rw [hd]
    rfl
  · have hcast := Model.cast_toRat_eq_toReal (ExecFloat.Binary.toModel f)
    unfold Model.toRat? at hcast
    rw [hd] at hcast
    simpa [ExecFloat.Binary.toReal] using hcast
  · have hcast : (d.toRat : ℝ) = f.toReal := by
      have h := Model.cast_toRat_eq_toReal (ExecFloat.Binary.toModel f)
      unfold Model.toRat? at h
      rw [hd] at h
      simpa [ExecFloat.Binary.toReal] using h
    have hrange : |(d.toRat : ℝ)| ≤ Ω64 := by
      rw [hcast]
      exact ExecFloat.Binary.abs_toReal_le_posMaxFinite_of_isFinite hfin
    have hfinQ : (ratToBinary64 d.toRat).isFinite = true := isFinite_ratToBinary64 d.toRat hrange
    rw [toReal_ratToBinary64_eq_roundAt d.toRat hfinQ, hcast]
    exact Model.roundAt_toReal_eq (ExecFloat.Binary.toModel f) hfin

/-- **Theorem 1C (`stdPartBinary64_halfUlp`)**: `stdPartBinary64` of any finite `FastLC`
    whose standard part is in IEEE-754 range returns a finite `Binary64` within half an ULP
    of `x.coeff 0`. -/
theorem stdPartBinary64_halfUlp (x : FastLC) (hx : x.isFinite = true)
    (hrange : |(x.coeff 0 : ℝ)| ≤ Ω64) :
    ∃ b : Binary64,
      stdPartBinary64 x = some b ∧
      b.isFinite = true ∧
      |b.toReal - (x.coeff 0 : ℝ)| ≤ Model.halfUlpAt FloatFormat.binary64 (x.coeff 0 : ℝ) := by
  refine ⟨ratToBinary64 (x.coeff 0), ?_, ?_, ?_⟩
  · unfold stdPartBinary64 FastLC.stdPart
    rw [hx]
    rfl
  · exact (ratToBinary64_spec (x.coeff 0) hrange).1
  · exact (ratToBinary64_spec (x.coeff 0) hrange).2.2.1

end FloatProofs
