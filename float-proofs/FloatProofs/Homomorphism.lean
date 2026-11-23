import FloatLib
import FloatProofs.EvalFinite

/-!
# T5: Ring Homomorphism, Commutative Diagram & Catastrophic Cancellation Separation

Formalizes the comparison between:
1. Computing symbolically in `FastLC` and then specializing `H ↦ N` into `Binary64`, vs.
2. Specializing `H ↦ N` into `Binary64` first and then performing floating-point arithmetic.

Includes:
- Exact ring homomorphism theorems `evalExactInt_add` and `evalExactInt_mul`.
- End-to-end commutative-diagram discrepancy bound `evalFiniteB64_add_commutes_upto_roundoff`.
- Kernel-checked (`float_decide`, zero `native_decide`) separation theorem showing that for
  `x = H + 1`, `y = -H + 1`, and `N = 2^60`:
  - Symbolic `FastLC` cancels `H` before float evaluation → exact `2`.
  - Naive `Binary64` evaluation loses both `1`s to `2^60` → `0` (100% relative error).
  - `FloatLib`'s `TwoSum`-backed `ExecFloat.Binary.sum2` recovers exact `2`.
-/

namespace FloatProofs

open LeanInf
open FloatLib.Numerics
open FloatLib.Floats
open FloatLib.Floats.Formats.BinaryInterchange

/-- Exact mathematical specialization of an arbitrary `TermList` at `H ↦ N`. -/
noncomputable def evalTermList (ts : TermList) (N : ℝ) : ℝ :=
  (ts.map fun (e, c) => (c : ℝ) * N ^ e.num).sum

private theorem evalTermList_eq_finset_sum (ts : TermList) (S : Finset Rat) (N : ℝ)
    (hsub : ∀ p ∈ ts, p.1 ∈ S) :
    evalTermList ts N = ∑ e ∈ S, (TermList.coeffOf ts e : ℝ) * N ^ e.num := by
  induction ts with
  | nil =>
    simp [evalTermList, TermList.coeffOf]
  | cons p rest ih =>
    rcases p with ⟨e', c⟩
    have he' : e' ∈ S := hsub (e', c) (by simp)
    have hrest : ∀ q ∈ rest, q.1 ∈ S := fun q hq => hsub q (by simp [hq])
    simp only [evalTermList, List.map_cons, List.sum_cons]
    change (c : ℝ) * N ^ e'.num + evalTermList rest N = _
    rw [ih hrest]
    have hstep : ∀ e : Rat,
        (TermList.coeffOf ((e', c) :: rest) e : ℝ) * N ^ e.num =
          (if e' = e then (c : ℝ) * N ^ e.num else 0) +
          (TermList.coeffOf rest e : ℝ) * N ^ e.num := by
      intro e
      simp only [TermList.coeffOf, Rat.cast_add]
      by_cases heq : e' = e
      · subst heq; simp [add_mul]
      · have hbeq : (e' == e) = false := beq_false_of_ne heq
        simp [heq, hbeq]
    simp_rw [hstep, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq S e' (fun e => (c : ℝ) * N ^ e.num)]
    simp [he']

private theorem rat_eq_intCast_of_den_one {r : Rat} (hr : r.den = 1) :
    r = (r.num : Rat) := by
  apply Rat.ext
  · simp
  · simp [hr]

private theorem rat_add_num_of_den_one {a b : Rat} (ha : a.den = 1) (hb : b.den = 1) :
    (a + b).num = a.num + b.num := by
  have ha' : a = (a.num : Rat) := rat_eq_intCast_of_den_one ha
  have hb' : b = (b.num : Rat) := rat_eq_intCast_of_den_one hb
  rw [ha', hb', show (a.num : ℚ) + (b.num : ℚ) = ((a.num + b.num : ℤ) : ℚ) from
    (Int.cast_add a.num b.num).symm]
  exact Rat.num_intCast (a.num + b.num)

private theorem evalTermList_append (xs ys : TermList) (N : ℝ) :
    evalTermList (xs ++ ys) N = evalTermList xs N + evalTermList ys N := by
  simp [evalTermList, List.map_append, List.sum_append]

private theorem evalTermList_mul_row (ex cx : Rat) (hex : ex.den = 1)
    (ys : TermList) (hys : ∀ q ∈ ys, q.1.den = 1) {N : ℝ} (hN : N ≠ 0) :
    evalTermList (ys.map fun (ey, cy) => (ex + ey, cx * cy)) N =
      ((cx : ℝ) * N ^ ex.num) * evalTermList ys N := by
  induction ys with
  | nil =>
    simp [evalTermList]
  | cons q rest ih =>
    rcases q with ⟨ey, cy⟩
    have hey : ey.den = 1 := hys (ey, cy) (by simp)
    have hrest : ∀ r ∈ rest, r.1.den = 1 := fun r hr => hys r (by simp [hr])
    simp only [evalTermList, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih hrest, rat_add_num_of_den_one hex hey, zpow_add₀ hN, Rat.cast_mul]
    ring

private theorem evalTermList_mulNaiveTerms (xs ys : TermList)
    (hxs : ∀ p ∈ xs, p.1.den = 1) (hys : ∀ q ∈ ys, q.1.den = 1)
    {N : ℝ} (hN : N ≠ 0) :
    evalTermList (TermList.mulNaiveTerms xs ys) N =
      evalTermList xs N * evalTermList ys N := by
  induction xs with
  | nil =>
    simp [TermList.mulNaiveTerms, evalTermList]
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    have hex : ex.den = 1 := hxs (ex, cx) (by simp)
    have hrest : ∀ r ∈ rest, r.1.den = 1 := fun r hr => hxs r (by simp [hr])
    simp only [TermList.mulNaiveTerms, List.foldr_cons]
    rw [evalTermList_append, evalTermList_mul_row ex cx hex ys hys hN]
    change (cx : ℝ) * N ^ ex.num * evalTermList ys N +
        evalTermList (TermList.mulNaiveTerms rest ys) N =
      evalTermList ((ex, cx) :: rest) N * evalTermList ys N
    rw [ih hrest]
    simp only [evalTermList, List.map_cons, List.sum_cons]
    ring

/-- **Theorem 5A (`evalExactInt_add`)**: Exact additive homomorphism for `FastLC.evalExactInt`. -/
theorem evalExactInt_add (x y : FastLC) (N : ℝ) :
    (x + y).evalExactInt N = x.evalExactInt N + y.evalExactInt N := by
  classical
  let S : Finset Rat :=
    (x.terms.map Prod.fst).toFinset ∪
    (y.terms.map Prod.fst).toFinset ∪
    ((x + y).terms.map Prod.fst).toFinset
  have hxS : ∀ p ∈ x.terms, p.1 ∈ S := fun p hp => by
    simp only [S, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact Or.inl (Or.inl ⟨p, hp, rfl⟩)
  have hyS : ∀ p ∈ y.terms, p.1 ∈ S := fun p hp => by
    simp only [S, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact Or.inl (Or.inr ⟨p, hp, rfl⟩)
  have hxyS : ∀ p ∈ (x + y).terms, p.1 ∈ S := fun p hp => by
    simp only [S, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact Or.inr ⟨p, hp, rfl⟩
  change evalTermList (x + y).terms N = evalTermList x.terms N + evalTermList y.terms N
  rw [evalTermList_eq_finset_sum (x + y).terms S N hxyS,
      evalTermList_eq_finset_sum x.terms S N hxS,
      evalTermList_eq_finset_sum y.terms S N hyS,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hc : TermList.coeffOf (x + y).terms e =
      TermList.coeffOf x.terms e + TermList.coeffOf y.terms e :=
    FastLC.coeff_add x y e
  rw [hc, Rat.cast_add, add_mul]

/-- **Theorem 5B (`evalExactInt_mul`)**: Exact multiplicative homomorphism for `FastLC.evalExactInt`
    on integer-exponent Levi-Civita numbers at any nonzero real specialization `N ≠ 0`. -/
theorem evalExactInt_mul (x y : FastLC) (hx : x.hasIntExps) (hy : y.hasIntExps)
    {N : ℝ} (hN : N ≠ 0) :
    (x * y).evalExactInt N = x.evalExactInt N * y.evalExactInt N := by
  classical
  let m := TermList.mulNaiveTerms x.terms y.terms
  let S : Finset Rat :=
    ((x * y).terms.map Prod.fst).toFinset ∪ (m.map Prod.fst).toFinset
  have hxyS : ∀ p ∈ (x * y).terms, p.1 ∈ S := fun p hp => by
    simp only [S, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact Or.inl ⟨p, hp, rfl⟩
  have hmS : ∀ p ∈ m, p.1 ∈ S := fun p hp => by
    simp only [S, Finset.mem_union, List.mem_toFinset, List.mem_map]
    exact Or.inr ⟨p, hp, rfl⟩
  change evalTermList (x * y).terms N = evalTermList x.terms N * evalTermList y.terms N
  rw [evalTermList_eq_finset_sum (x * y).terms S N hxyS]
  have hsum_eq :
      ∑ e ∈ S, (TermList.coeffOf (x * y).terms e : ℝ) * N ^ e.num =
        ∑ e ∈ S, (TermList.coeffOf m e : ℝ) * N ^ e.num := by
    refine Finset.sum_congr rfl fun e _ => ?_
    have hc : TermList.coeffOf (x * y).terms e = TermList.coeffOf m e :=
      FastLC.coeff_mul x y e
    rw [hc]
  rw [hsum_eq, ← evalTermList_eq_finset_sum m S N hmS]
  exact evalTermList_mulNaiveTerms x.terms y.terms hx hy hN

/-- **Theorem 5C (`evalFiniteB64_add_commutes_upto_roundoff`)**: Commutative-diagram float
    discrepancy bound comparing symbolic-then-float (`evalFiniteB64 (x + y) bigN`) against
    float-then-add (`evalFiniteB64 x bigN + evalFiniteB64 y bigN`). -/
theorem evalFiniteB64_add_commutes_upto_roundoff (x y : FastLC) (bigN : Binary64)
    (hN : bigN.isFinite = true)
    (hsumX : (evalFiniteB64 x bigN).isFinite = true)
    (hsumY : (evalFiniteB64 y bigN).isFinite = true)
    (hsumXY : (evalFiniteB64 (x + y) bigN).isFinite = true)
    (hadd : (evalFiniteB64 x bigN + evalFiniteB64 y bigN).isFinite = true)
    (htX : ∀ p ∈ x.terms,
      (ExecFloat.Binary.ofRat p.2 : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN p.1.num).isFinite = true ∧
      (evalTermB64 bigN p).isFinite = true)
    (htY : ∀ p ∈ y.terms,
      (ExecFloat.Binary.ofRat p.2 : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN p.1.num).isFinite = true ∧
      (evalTermB64 bigN p).isFinite = true)
    (htXY : ∀ p ∈ (x + y).terms,
      (ExecFloat.Binary.ofRat p.2 : Binary64).isFinite = true ∧
      (ExecFloat.Binary.pown bigN p.1.num).isFinite = true ∧
      (evalTermB64 bigN p).isFinite = true) :
    |(evalFiniteB64 (x + y) bigN).toReal -
      (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal| ≤
      (1 + u64) * (evalErrB64 x bigN + evalErrB64 y bigN) + evalErrB64 (x + y) bigN +
        u64 * |x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal| := by
  have hx := abs_toReal_evalFiniteB64_sub_evalExactInt_le x bigN hN hsumX htX
  have hy := abs_toReal_evalFiniteB64_sub_evalExactInt_le y bigN hN hsumY htY
  have hxy := abs_toReal_evalFiniteB64_sub_evalExactInt_le (x + y) bigN hN hsumXY htXY
  rw [evalExactInt_add] at hxy
  have hadd_err :
      |(evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal -
        ((evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal)| ≤
        u64 * |(evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal| := by
    have hr := (ExecFloat.Binary.add_rounding hadd).bound
    simpa [add_zero] using hr
  have hsum_abs :
      |(evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal| ≤
        |x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal| +
          (evalErrB64 x bigN + evalErrB64 y bigN) := by
    have hsplit : (evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal =
        (x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal) +
        (((evalFiniteB64 x bigN).toReal - x.evalExactInt bigN.toReal) +
         ((evalFiniteB64 y bigN).toReal - y.evalExactInt bigN.toReal)) := by ring
    rw [hsplit]
    calc |(x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal) +
            (((evalFiniteB64 x bigN).toReal - x.evalExactInt bigN.toReal) +
             ((evalFiniteB64 y bigN).toReal - y.evalExactInt bigN.toReal))|
        ≤ |x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal| +
          |((evalFiniteB64 x bigN).toReal - x.evalExactInt bigN.toReal) +
           ((evalFiniteB64 y bigN).toReal - y.evalExactInt bigN.toReal)| := abs_add_le _ _
      _ ≤ |x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal| +
          (|(evalFiniteB64 x bigN).toReal - x.evalExactInt bigN.toReal| +
           |(evalFiniteB64 y bigN).toReal - y.evalExactInt bigN.toReal|) :=
            add_le_add le_rfl (abs_add_le _ _)
      _ ≤ |x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal| +
          (evalErrB64 x bigN + evalErrB64 y bigN) := by linarith
  have htri :
      |(evalFiniteB64 (x + y) bigN).toReal -
        (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal| ≤
        |(evalFiniteB64 (x + y) bigN).toReal -
          (x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal)| +
        |(x.evalExactInt bigN.toReal - (evalFiniteB64 x bigN).toReal) +
          (y.evalExactInt bigN.toReal - (evalFiniteB64 y bigN).toReal)| +
        |((evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal) -
          (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal| := by
    have hsplit : (evalFiniteB64 (x + y) bigN).toReal -
          (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal =
        ((evalFiniteB64 (x + y) bigN).toReal -
          (x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal)) +
        ((x.evalExactInt bigN.toReal - (evalFiniteB64 x bigN).toReal) +
          (y.evalExactInt bigN.toReal - (evalFiniteB64 y bigN).toReal)) +
        (((evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal) -
          (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal) := by ring
    rw [hsplit]
    calc _ ≤ |((evalFiniteB64 (x + y) bigN).toReal -
                (x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal)) +
              ((x.evalExactInt bigN.toReal - (evalFiniteB64 x bigN).toReal) +
                (y.evalExactInt bigN.toReal - (evalFiniteB64 y bigN).toReal))| +
             |((evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal) -
               (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal| := abs_add_le _ _
      _ ≤ _ := add_le_add (abs_add_le _ _) le_rfl
  have hmid :
      |(x.evalExactInt bigN.toReal - (evalFiniteB64 x bigN).toReal) +
        (y.evalExactInt bigN.toReal - (evalFiniteB64 y bigN).toReal)| ≤
        evalErrB64 x bigN + evalErrB64 y bigN := by
    calc _ ≤ |x.evalExactInt bigN.toReal - (evalFiniteB64 x bigN).toReal| +
             |y.evalExactInt bigN.toReal - (evalFiniteB64 y bigN).toReal| := abs_add_le _ _
      _ = |(evalFiniteB64 x bigN).toReal - x.evalExactInt bigN.toReal| +
          |(evalFiniteB64 y bigN).toReal - y.evalExactInt bigN.toReal| := by
            rw [abs_sub_comm, abs_sub_comm (y.evalExactInt bigN.toReal)]
      _ ≤ evalErrB64 x bigN + evalErrB64 y bigN := add_le_add hx hy
  have hu0 : 0 ≤ u64 := (Model.unitRoundoffAt_pos FloatFormat.binary64).le
  have hadd_err' :
      |((evalFiniteB64 x bigN).toReal + (evalFiniteB64 y bigN).toReal) -
        (evalFiniteB64 x bigN + evalFiniteB64 y bigN).toReal| ≤
        u64 * (|x.evalExactInt bigN.toReal + y.evalExactInt bigN.toReal| +
          (evalErrB64 x bigN + evalErrB64 y bigN)) := by
    rw [abs_sub_comm]
    exact hadd_err.trans (mul_le_mul_of_nonneg_left hsum_abs hu0)
  linarith

private def cancelX : FastLC :=
  ⟨[(1, 1), (0, 1)], ⟨by decide, ⟨by decide, trivial⟩, ⟨by decide, trivial, trivial⟩⟩⟩

private def cancelY : FastLC :=
  ⟨[(1, -1), (0, 1)], ⟨by decide, ⟨by decide, trivial⟩, ⟨by decide, trivial, trivial⟩⟩⟩

private def cancelSum : FastLC :=
  ⟨[(0, 2)], ⟨by decide, trivial, trivial⟩⟩

private theorem infH_add_one_eq : FastLC.infH + (1 : FastLC) = cancelX := by
  ext e
  rw [FastLC.coeff_add, FastLC.coeff_one]
  simp only [FastLC.coeff, FastLC.infH, cancelX, TermList.coeffOf, Rat.add_zero]

private theorem neg_infH_add_one_eq : -FastLC.infH + (1 : FastLC) = cancelY := by
  ext e
  rw [FastLC.coeff_add, FastLC.coeff_neg, FastLC.coeff_one]
  simp only [FastLC.coeff, FastLC.infH, cancelY, TermList.coeffOf, Rat.add_zero]
  split_ifs <;> norm_num

private theorem cancel_sum_eq : (FastLC.infH + (1 : FastLC)) + (-FastLC.infH + (1 : FastLC)) = cancelSum := by
  ext e
  rw [FastLC.coeff_add, FastLC.coeff_add, FastLC.coeff_add, FastLC.coeff_neg, FastLC.coeff_one]
  simp only [FastLC.coeff, FastLC.infH, cancelSum, TermList.coeffOf, Rat.add_zero]
  split_ifs <;> ring

/-- **Theorem 5D (`symbolic_fastLC_beats_naive_float_cancellation`)**: Machine-checked
    Catastrophic Cancellation Separation (strictly kernel-verified via `float_decide`!):
    For `x = H + 1`, `y = -H + 1`, and `N = 2^60` (exact in IEEE-754 binary64):
    1. Symbolic `FastLC` cancels `H` BEFORE float evaluation → `evalFiniteB64 (x + y) N = 2`.
    2. Naive float evaluation loses both `1`s to `2^60` → `evalFiniteB64 x N + evalFiniteB64 y N = 0`
       (100% relative error!).
    3. `ExecFloat.Binary.sum2` (`TwoSum` compensated sum) recovers exact `2`! -/
theorem symbolic_fastLC_beats_naive_float_cancellation :
    let x : FastLC := FastLC.infH + 1
    let y : FastLC := -FastLC.infH + 1
    let N : Binary64 := 1152921504606846976
    evalFiniteB64 (x + y) N = (2 : Binary64) ∧
    evalFiniteB64 x N + evalFiniteB64 y N = (0 : Binary64) ∧
    ExecFloat.Binary.sum2 [1, N, 1, -N] = (2 : Binary64) := by
  dsimp only
  rw [cancel_sum_eq, infH_add_one_eq, neg_infH_add_one_eq]
  refine ⟨?_, ?_, ?_⟩
  · change (((0 : Binary64) +
      (ExecFloat.Binary.ofRat (2 : Rat) * ExecFloat.Binary.pown (1152921504606846976 : Binary64) 0)) : Binary64) =
      (2 : Binary64)
    float_decide
  · change ((((0 : Binary64) +
        (ExecFloat.Binary.ofRat (1 : Rat) * ExecFloat.Binary.pown (1152921504606846976 : Binary64) 1)) +
        (ExecFloat.Binary.ofRat (1 : Rat) * ExecFloat.Binary.pown (1152921504606846976 : Binary64) 0)) +
      (((0 : Binary64) +
        (ExecFloat.Binary.ofRat (-1 : Rat) * ExecFloat.Binary.pown (1152921504606846976 : Binary64) 1)) +
        (ExecFloat.Binary.ofRat (1 : Rat) * ExecFloat.Binary.pown (1152921504606846976 : Binary64) 0))) =
      (0 : Binary64)
    float_decide
  · float_decide

end FloatProofs
