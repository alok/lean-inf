import FloatLib
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Sum.Proof
import FloatProofs.Convert

/-!
# T2: Verified IEEE-754 `Binary64` Finite Specialization (`H ↦ N`)

Replaces the unprovable `opaque Float.pow` + `opaque Float.scaleB` evaluation path
(`FastLC.evalFinite`) with three verified IEEE-754 `Binary64` evaluators:
- `evalFiniteB64` (left-to-right summation, Theorem 2A),
- `evalFiniteSum2` (Ogita–Rump–Oishi `TwoSum` compensated summation, Theorem 2B),
- `evalFiniteExactSum` (exact accumulation with a single final rounding, Theorem 2C).
-/

namespace LeanInf.FastLC

/-- Predicate stating that every exponent in `x : FastLC` is an integer (`den = 1`).
    Holds for all polynomials, Newton inverses, Taylor expansions (`expOrder`/`lnOrder`/
    `sinOrder`/`cosOrder`), `logisticStep`, `logisticDerivCentral`, `logisticDeriv2Central`,
    and `riemannArea`. -/
def hasIntExps (x : FastLC) : Prop :=
  ∀ p ∈ x.terms, p.1.den = 1

/-- Exact mathematical specialization `H ↦ N` in `ℝ` for integer-exponent `FastLC`. -/
noncomputable def evalExactInt (x : FastLC) (N : ℝ) : ℝ :=
  (x.terms.map fun (e, c) => (c : ℝ) * N ^ e.num).sum

end LeanInf.FastLC

namespace FloatProofs

open LeanInf
open FloatLib.Numerics
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- Single verified IEEE-754 `Binary64` term `fl(c) ⊗ fl(N^e)`. -/
def evalTermB64 (bigN : Binary64) (p : Rat × Rat) : Binary64 :=
  ExecFloat.Binary.ofRat p.2 * ExecFloat.Binary.pown bigN p.1.num

/-- (A) Direct verified left-to-right IEEE-754 `Binary64` analogue of `FastLC.evalFinite`. -/
def evalFiniteB64 (x : FastLC) (bigN : Binary64) : Binary64 :=
  (x.terms.map (evalTermB64 bigN)).foldl (· + ·) 0

/-- (B) Compensated `H ↦ N` evaluation using `FloatLib`'s `TwoSum`-backed Ogita–Rump–Oishi `Sum2`. -/
def evalFiniteSum2 (x : FastLC) (bigN : Binary64) : Binary64 :=
  ExecFloat.Binary.sum2 (x.terms.map (evalTermB64 bigN))

/-- (C) Exact-accumulation `H ↦ N` evaluation (zero intermediate summation rounding). -/
def evalFiniteExactSum (x : FastLC) (bigN : Binary64) : Binary64 :=
  ExecFloat.Binary.sumList (x.terms.map (evalTermB64 bigN))

/-- Relative error coefficient of a single `evalTermB64` product `fl(c) ⊗ fl(N^e)` (`≈ 3 u64`). -/
noncomputable def termRelBound : ℝ :=
  (1 + u64) * (u64 + u64 + u64 * u64) + u64

/-- Underflow/absolute error allowance of a single `evalTermB64` product `fl(c) ⊗ fl(N^e)`. -/
noncomputable def termAbsBound (cVal pVal : ℝ) : ℝ :=
  (1 + u64) * ((1 + u64) * η64 * |pVal| + (1 + u64) * η64 * |cVal| + η64 * η64) + η64

/-- Total per-term error bound `termRelBound * |c * N^e| + termAbsBound c (N^e)`. -/
noncomputable def termErrorBound (cVal pVal : ℝ) : ℝ :=
  termRelBound * |cVal * pVal| + termAbsBound cVal pVal

/-- Closed-form end-to-end error budget for left-to-right `evalFiniteB64 x bigN`. -/
noncomputable def evalErrB64 (x : FastLC) (bigN : Binary64) : ℝ :=
  ((1 + u64) ^ (x.terms.length - 1) - 1) *
    (x.terms.map fun (e, c) => |(c : ℝ) * bigN.toReal ^ e.num|).sum +
  (1 + u64) ^ (x.terms.length - 1) *
    (x.terms.map fun (e, c) => termErrorBound (c : ℝ) (bigN.toReal ^ e.num)).sum

/-- Per-term `MixedError` lemma combining `ofRat`, `pown`, and `*` in IEEE-754 `Binary64`. -/
theorem evalTermB64_mixedError (bigN : Binary64) (e c : Rat)
    (hN : bigN.isFinite = true)
    (hc : (ExecFloat.Binary.ofRat c : Binary64).isFinite = true)
    (hp : (ExecFloat.Binary.pown bigN e.num).isFinite = true)
    (hmul : (evalTermB64 bigN (e, c)).isFinite = true) :
    MixedError (evalTermB64 bigN (e, c)).toReal ((c : ℝ) * bigN.toReal ^ e.num)
      termRelBound (termAbsBound (c : ℝ) (bigN.toReal ^ e.num)) := by
  have ec : MixedError (ExecFloat.Binary.ofRat c : Binary64).toReal (c : ℝ) u64 η64 :=
    mixedError_ratToBinary64 c hc
  have ep : MixedError (ExecFloat.Binary.pown bigN e.num).toReal (bigN.toReal ^ e.num) u64 η64 :=
    ExecFloat.Binary.mixedError_toReal_of_eq_roundAt
      (ExecFloat.Binary.toReal_pown_eq_roundAt bigN e.num hN hp)
  exact ExecFloat.Binary.mixedError_toReal_mul hmul ec ep

/-- Absolute-error form of `evalTermB64_mixedError`. -/
theorem evalTermB64_abs_sub_le (bigN : Binary64) (e c : Rat)
    (hN : bigN.isFinite = true)
    (hc : (ExecFloat.Binary.ofRat c : Binary64).isFinite = true)
    (hp : (ExecFloat.Binary.pown bigN e.num).isFinite = true)
    (hmul : (evalTermB64 bigN (e, c)).isFinite = true) :
    |(evalTermB64 bigN (e, c)).toReal - (c : ℝ) * bigN.toReal ^ e.num| ≤
      termErrorBound (c : ℝ) (bigN.toReal ^ e.num) :=
  (evalTermB64_mixedError bigN e c hN hc hp hmul).bound

private theorem abs_sum_map_sub_sum_map_le {α : Type} (l : List α) (f g : α → ℝ) :
    |(l.map f).sum - (l.map g).sum| ≤ (l.map fun a => |f a - g a|).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have hsplit : (f a + (rest.map f).sum) - (g a + (rest.map g).sum) =
        (f a - g a) + ((rest.map f).sum - (rest.map g).sum) := by ring
    rw [hsplit]
    exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

private theorem sum_map_le_sum_map {α : Type} (l : List α) (f g : α → ℝ)
    (h : ∀ a ∈ l, f a ≤ g a) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun b hb => h b (by simp [hb]))

/-- **Theorem 2A (`abs_toReal_evalFiniteB64_sub_evalExactInt_le`)**: End-to-end IEEE-754
    `Binary64` error bound for left-to-right `evalFiniteB64` against exact `evalExactInt`. -/
theorem abs_toReal_evalFiniteB64_sub_evalExactInt_le (x : FastLC) (bigN : Binary64)
    (hN : bigN.isFinite = true)
    (hsum : (evalFiniteB64 x bigN).isFinite = true)
    (hterms : ∀ p ∈ x.terms,
      (ExecFloat.Binary.ofRat p.2 : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN p.1.num).isFinite = true ∧
      (evalTermB64 bigN p).isFinite = true) :
    |(evalFiniteB64 x bigN).toReal - x.evalExactInt bigN.toReal| ≤
      evalErrB64 x bigN := by
  have hfold : evalFiniteB64 x bigN =
      x.terms.foldl (fun acc p => acc + evalTermB64 bigN p) (0 : Binary64) := by
    unfold evalFiniteB64
    rw [List.foldl_map]
  have hsum' : (x.terms.foldl (fun acc p => acc + evalTermB64 bigN p) (0 : Binary64)).isFinite = true := by
    rwa [← hfold]
  have hscan : ∀ v ∈ x.terms.scanl (fun acc p => acc + evalTermB64 bigN p) (0 : Binary64),
      v.isFinite = true := fun v hv =>
    ExecFloat.Binary.isFinite_of_mem_scanl_add hsum' hv
  have hseed : ((0 : Binary64).toReal) = 0 := by simp
  have hmix := ExecFloat.Binary.mixedError_toReal_foldl_add_absolute_of_toReal_eq_zero
    (l := x.terms)
    (term := evalTermB64 bigN)
    (term₀ := fun p => (p.2 : ℝ) * bigN.toReal ^ p.1.num)
    (rel := fun _ => termRelBound)
    (err := fun p => termAbsBound (p.2 : ℝ) (bigN.toReal ^ p.1.num))
    (seed := (0 : Binary64))
    hseed hscan
    (fun p hp => (hterms p hp).2.2)
    (fun p hp => by
      obtain ⟨hc, hpow, hmul⟩ := hterms p hp
      exact evalTermB64_mixedError bigN p.1 p.2 hN hc hpow hmul)
  have hbound := hmix.bound
  rw [zero_mul, zero_add] at hbound
  rw [hfold]
  exact hbound

/-- **Theorem 2B (`abs_toReal_evalFiniteSum2_sub_evalExactInt_le`)**: End-to-end IEEE-754
    `Binary64` error bound for Ogita–Rump–Oishi compensated `evalFiniteSum2`, reducing the
    summation error from `O(n u ∑ |tᵢ|)` to `u |∑ tᵢ| + (9/4) n² u² ∑ |tᵢ|`. -/
theorem abs_toReal_evalFiniteSum2_sub_evalExactInt_le (x : FastLC) (bigN : Binary64)
    (hN : bigN.isFinite = true)
    (hterms : ∀ p ∈ x.terms,
      (ExecFloat.Binary.ofRat p.2 : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN p.1.num).isFinite = true ∧
      (evalTermB64 bigN p).isFinite = true)
    (hsteps : List.AllSteps ExecFloat.Binary.sum2Step
      (fun (st : Binary64 × Binary64) (v : Binary64) =>
        ExecFloat.Binary.isFinite (ExecFloat.Binary.sum2Step st v).2 = true)
      ((0 : Binary64), (0 : Binary64)) (x.terms.map (evalTermB64 bigN)))
    (hrange : |((x.terms.map (evalTermB64 bigN)).map ExecFloat.Binary.toReal).sum| +
      (ExecFloat.Binary.sum2Budgets (x.terms.map (evalTermB64 bigN))).1 ≤ Ω64)
    (hn : (x.terms.length : ℝ) * u64 ≤ 1 / 8) :
    |(evalFiniteSum2 x bigN).toReal - x.evalExactInt bigN.toReal| ≤
      u64 * |((x.terms.map (evalTermB64 bigN)).map ExecFloat.Binary.toReal).sum| +
      (9 / 4 : ℝ) * (x.terms.length : ℝ) ^ 2 * u64 ^ 2 *
        ((x.terms.map (evalTermB64 bigN)).map fun t => |t.toReal|).sum +
      (x.terms.map fun (e, c) => termErrorBound (c : ℝ) (bigN.toReal ^ e.num)).sum := by
  let xs : List Binary64 := x.terms.map (evalTermB64 bigN)
  have hsum2 :
      |(evalFiniteSum2 x bigN).toReal - (xs.map ExecFloat.Binary.toReal).sum| ≤
        u64 * |(xs.map ExecFloat.Binary.toReal).sum| +
        (9 / 4 : ℝ) * (xs.length : ℝ) ^ 2 * u64 ^ 2 *
          (xs.map fun t => |t.toReal|).sum :=
    ExecFloat.Binary.abs_toReal_sum2_sub_le xs hsteps hrange (by simpa [xs] using hn)
  have htermsErr :
      |(xs.map ExecFloat.Binary.toReal).sum - x.evalExactInt bigN.toReal| ≤
        (x.terms.map fun (e, c) => termErrorBound (c : ℝ) (bigN.toReal ^ e.num)).sum := by
    have hmap : (xs.map ExecFloat.Binary.toReal) =
        x.terms.map (fun p => (evalTermB64 bigN p).toReal) := by
      simp [xs, List.map_map, Function.comp]
    rw [hmap, FastLC.evalExactInt]
    refine (abs_sum_map_sub_sum_map_le x.terms
      (fun p => (evalTermB64 bigN p).toReal)
      (fun p => (p.2 : ℝ) * bigN.toReal ^ p.1.num)).trans ?_
    refine sum_map_le_sum_map x.terms _ _ fun p hp => ?_
    obtain ⟨hc, hpow, hmul⟩ := hterms p hp
    exact evalTermB64_abs_sub_le bigN p.1 p.2 hN hc hpow hmul
  have htri :
      |(evalFiniteSum2 x bigN).toReal - x.evalExactInt bigN.toReal| ≤
        |(evalFiniteSum2 x bigN).toReal - (xs.map ExecFloat.Binary.toReal).sum| +
        |(xs.map ExecFloat.Binary.toReal).sum - x.evalExactInt bigN.toReal| := by
    have hsplit : (evalFiniteSum2 x bigN).toReal - x.evalExactInt bigN.toReal =
        ((evalFiniteSum2 x bigN).toReal - (xs.map ExecFloat.Binary.toReal).sum) +
        ((xs.map ExecFloat.Binary.toReal).sum - x.evalExactInt bigN.toReal) := by ring
    rw [hsplit]
    exact abs_add_le _ _
  have hlen : (xs.length : ℝ) = (x.terms.length : ℝ) := by simp [xs]
  rw [hlen] at hsum2
  linarith

private theorem finiteSum_cast_eq_sum_toReal (xs : List Binary64) :
    (Model.Reduction.Semantics.finiteSum (xs.map ExecFloat.Binary.toModel) : ℝ) =
      (xs.map ExecFloat.Binary.toReal).sum := by
  induction xs with
  | nil =>
    simp [Model.Reduction.Semantics.finiteSum]
  | cons a rest ih =>
    simp only [List.map_cons, Model.Reduction.Semantics.finiteSum, List.sum_cons, Rat.cast_add] at ih ⊢
    congr 1
    have hcast := Model.cast_toRat_eq_toReal (ExecFloat.Binary.toModel a)
    unfold Model.Reduction.Semantics.finiteContribution Model.toRat? at *
    cases hd : Model.toDyadic? (ExecFloat.Binary.toModel a) <;>
      simpa [hd, ExecFloat.Binary.toReal] using hcast

/-- **Theorem 2C (`evalFiniteExactSum_eq_roundAt`)**: Exact-accumulation `evalFiniteExactSum`
    introduces strictly ONE final nearest-even rounding of the exact sum of the evaluated terms. -/
theorem evalFiniteExactSum_eq_roundAt (x : FastLC) (bigN : Binary64)
    (hterms : ∀ p ∈ x.terms, (evalTermB64 bigN p).isFinite = true)
    (hres : (evalFiniteExactSum x bigN).isFinite = true) :
    (evalFiniteExactSum x bigN).toReal =
      Model.roundAt FloatFormat.binary64
        ((x.terms.map (evalTermB64 bigN)).map ExecFloat.Binary.toReal).sum := by
  let xs : List Binary64 := x.terms.map (evalTermB64 bigN)
  have hxs : ∀ v ∈ xs, v.isFinite = true := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
    exact hterms p hp
  have harrFin : ∀ m ∈ (xs.toArray.map ExecFloat.Binary.toModel).toList, Model.isFinite m = true := by
    intro m hm
    rw [Array.toList_map, List.toList_toArray] at hm
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hm
    exact hxs v hv
  have hresModel : Model.isFinite
      (Model.sum FloatFormat.binary64 (xs.toArray.map ExecFloat.Binary.toModel)
        .nearest (status := true)).value = true := by
    have hval : (Model.sum FloatFormat.binary64 (xs.toArray.map ExecFloat.Binary.toModel)
        .nearest (status := true)).value =
        Model.sum FloatFormat.binary64 (xs.toArray.map ExecFloat.Binary.toModel) .nearest := rfl
    rw [hval]
    have hres' : Model.isFinite (ExecFloat.Binary.toModel (evalFiniteExactSum x bigN)) = true := hres
    unfold evalFiniteExactSum ExecFloat.Binary.sumList at hres'
    rw [ExecFloat.Binary.toModel_sum] at hres'
    exact hres'
  have hround := Model.Reduction.sum_status_value_toReal_eq_roundAt_of_finite
    FloatFormat.binary64 (xs.toArray.map ExecFloat.Binary.toModel)
    FloatFormat.isIEEE_binary64 harrFin hresModel
  have hval : (Model.sum FloatFormat.binary64 (xs.toArray.map ExecFloat.Binary.toModel)
      .nearest (status := true)).value =
      Model.sum FloatFormat.binary64 (xs.toArray.map ExecFloat.Binary.toModel) .nearest := rfl
  rw [hval, Array.toList_map, List.toList_toArray, finiteSum_cast_eq_sum_toReal] at hround
  change Model.toReal (ExecFloat.Binary.toModel (evalFiniteExactSum x bigN)) = _
  unfold evalFiniteExactSum ExecFloat.Binary.sumList
  rw [ExecFloat.Binary.toModel_sum]
  exact hround

end FloatProofs
