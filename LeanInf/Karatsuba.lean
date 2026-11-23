import Init.Data.Rat
import LeanInf.SortedLC

namespace LeanInf
namespace Karatsuba

open TermList

/-! ### Dense Polynomial Operations over `List Rat`

A dense polynomial `p : List Rat` represents `∑_{k} p[k] * u^k` where `u = H^(-step) = ε^step`.
Index `k` stores the coefficient of `u^k` (descending powers of `H`).
-/

/-- Coefficient of `u^k` in a dense polynomial (`0` out of bounds). -/
def dCoeff (p : List Rat) (k : Nat) : Rat :=
  p.getD k 0

@[simp] theorem dCoeff_nil (k : Nat) : dCoeff [] k = 0 := rfl

@[simp] theorem dCoeff_cons_zero (c : Rat) (rest : List Rat) :
    dCoeff (c :: rest) 0 = c := rfl

@[simp] theorem dCoeff_cons_succ (c : Rat) (rest : List Rat) (k : Nat) :
    dCoeff (c :: rest) (k + 1) = dCoeff rest k := rfl

/-- Dense polynomial addition (`O(max |a| |b|)`), using zero-GCD `ratAddFast`. -/
def dAdd : List Rat → List Rat → List Rat
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => ratAddFast x y :: dAdd xs ys

/-- Dense polynomial subtraction (`O(max |a| |b|)`), using zero-GCD `ratSubFast`. -/
def dSub : List Rat → List Rat → List Rat
  | [], b => b.map (fun y => -y)
  | a, [] => a
  | x :: xs, y :: ys => ratSubFast x y :: dSub xs ys

/-- Dense scalar multiplication (`O(|p|)`), using zero-GCD `ratMulFast`. -/
def dScale (c : Rat) (p : List Rat) : List Rat :=
  p.map (fun x => ratMulFast c x)

/-- Multiply a dense polynomial by `u^m` (prepend `m` zeros, `O(m)`). -/
def dShift (m : Nat) (p : List Rat) : List Rat :=
  List.replicate m 0 ++ p

/-- Schoolbook dense polynomial multiplication (`O(|a| * |b|)`). -/
def dMulSchoolbook : List Rat → List Rat → List Rat
  | [], _ => []
  | c :: rest, b => dAdd (dScale c b) (0 :: dMulSchoolbook rest b)

/-- Length of `dAdd a b` is `max a.length b.length`. -/
theorem dAdd_length (a b : List Rat) : (dAdd a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil => simp [dAdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [dAdd]
    | cons y ys =>
      simp only [dAdd, List.length_cons, ih ys]
      omega

/-- Coefficient specification of `dAdd`. -/
theorem dCoeff_dAdd (a b : List Rat) (k : Nat) :
    dCoeff (dAdd a b) k = dCoeff a k + dCoeff b k := by
  induction a generalizing b k with
  | nil => simp [dAdd, dCoeff, Rat.zero_add]
  | cons x xs ih =>
    cases b with
    | nil => simp [dAdd, dCoeff, Rat.add_zero]
    | cons y ys =>
      cases k with
      | zero => exact ratAddFast_eq x y
      | succ k' => exact ih ys k'

private theorem dCoeff_map_neg (b : List Rat) (k : Nat) :
    dCoeff (b.map (fun y => -y)) k = -(dCoeff b k) := by
  induction b generalizing k with
  | nil => simp [dCoeff]
  | cons y ys ih =>
    cases k with
    | zero => rfl
    | succ k' => exact ih k'

/-- Coefficient specification of `dSub`. -/
theorem dCoeff_dSub (a b : List Rat) (k : Nat) :
    dCoeff (dSub a b) k = dCoeff a k - dCoeff b k := by
  induction a generalizing b k with
  | nil =>
    simp only [dSub, dCoeff_nil, dCoeff_map_neg]
    grind
  | cons x xs ih =>
    cases b with
    | nil =>
      simp only [dSub, dCoeff_nil]
      grind
    | cons y ys =>
      cases k with
      | zero => exact ratSubFast_eq x y
      | succ k' => exact ih ys k'

/-- Coefficient specification of `dScale`. -/
theorem dCoeff_dScale (c : Rat) (p : List Rat) (k : Nat) :
    dCoeff (dScale c p) k = c * dCoeff p k := by
  induction p generalizing k with
  | nil => simp [dScale, dCoeff, Rat.mul_zero]
  | cons x xs ih =>
    cases k with
    | zero => exact ratMulFast_eq c x
    | succ k' => exact ih k'

/-- Coefficient specification of `dShift`. -/
theorem dCoeff_dShift (m : Nat) (p : List Rat) (k : Nat) :
    dCoeff (dShift m p) k = if k < m then 0 else dCoeff p (k - m) := by
  induction m generalizing k with
  | zero => simp [dShift]
  | succ m' ih =>
    cases k with
    | zero => simp [dShift, List.replicate_succ]
    | succ k' =>
      change dCoeff (0 :: dShift m' p) (k' + 1) = _
      rw [dCoeff_cons_succ, ih k']
      by_cases h : k' < m'
      · have h1 : k' + 1 < m' + 1 := by omega
        simp [h, h1]
      · have h1 : ¬ (k' + 1 < m' + 1) := by omega
        have hsub : k' + 1 - (m' + 1) = k' - m' := by omega
        simp [h, h1, hsub]

/-- Split identity: every polynomial equals its low part plus shifted high part. -/
theorem dCoeff_take_add_drop (a : List Rat) (m k : Nat) :
    dCoeff a k = dCoeff (a.take m) k + dCoeff (dShift m (a.drop m)) k := by
  induction a generalizing m k with
  | nil =>
    rw [List.take_nil, List.drop_nil, dCoeff_nil, dCoeff_dShift]
    split <;> simp [Rat.add_zero]
  | cons x xs ih =>
    cases m with
    | zero =>
      simp [dShift, Rat.zero_add]
    | succ m' =>
      cases k with
      | zero =>
        simp [dShift, List.replicate_succ, Rat.add_zero]
      | succ k' =>
        change dCoeff xs k' = dCoeff (xs.take m') k' + dCoeff (0 :: dShift m' (xs.drop m')) (k' + 1)
        rw [dCoeff_cons_succ]
        exact ih m' k'

/-- Schoolbook multiplication is congruent under coefficient-wise equality on the right. -/
theorem dCoeff_dMulSchoolbook_congr_right {a b₁ b₂ : List Rat}
    (hb : ∀ k, dCoeff b₁ k = dCoeff b₂ k) (k : Nat) :
    dCoeff (dMulSchoolbook a b₁) k = dCoeff (dMulSchoolbook a b₂) k := by
  induction a generalizing k with
  | nil => rfl
  | cons x xs ih =>
    simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, hb k]
    congr 1
    cases k with
    | zero => rfl
    | succ k' => exact ih k'

/-- Schoolbook multiplication distributes over `dAdd` on the right. -/
theorem dCoeff_dMulSchoolbook_add_right (a b₁ b₂ : List Rat) (k : Nat) :
    dCoeff (dMulSchoolbook a (dAdd b₁ b₂)) k =
      dCoeff (dMulSchoolbook a b₁) k + dCoeff (dMulSchoolbook a b₂) k := by
  induction a generalizing k with
  | nil => simp [dMulSchoolbook, Rat.add_zero]
  | cons x xs ih =>
    simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale]
    cases k with
    | zero =>
      simp only [dCoeff_cons_zero, Rat.add_zero, Rat.mul_add]
    | succ k' =>
      simp only [dCoeff_cons_succ, ih k', Rat.mul_add]
      grind

/-- Schoolbook multiplication distributes over `dAdd` on the left. -/
theorem dCoeff_dMulSchoolbook_add_left (a₁ a₂ b : List Rat) (k : Nat) :
    dCoeff (dMulSchoolbook (dAdd a₁ a₂) b) k =
      dCoeff (dMulSchoolbook a₁ b) k + dCoeff (dMulSchoolbook a₂ b) k := by
  induction a₁ generalizing a₂ k with
  | nil => simp [dAdd, dMulSchoolbook, Rat.zero_add]
  | cons x xs ih =>
    cases a₂ with
    | nil => simp [dAdd, dMulSchoolbook, Rat.add_zero]
    | cons y ys =>
      simp only [dAdd, dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, ratAddFast_eq, Rat.add_mul]
      cases k with
      | zero =>
        simp only [dCoeff_cons_zero, Rat.add_zero]
      | succ k' =>
        simp only [dCoeff_cons_succ, ih ys k']
        grind

/-- Shifting the left operand shifts the product. -/
theorem dCoeff_dMulSchoolbook_shift_left (m : Nat) (a b : List Rat) (k : Nat) :
    dCoeff (dMulSchoolbook (dShift m a) b) k = dCoeff (dShift m (dMulSchoolbook a b)) k := by
  induction m generalizing k with
  | zero => rfl
  | succ m' ih =>
    change dCoeff (dMulSchoolbook (0 :: dShift m' a) b) k =
      dCoeff (0 :: dShift m' (dMulSchoolbook a b)) k
    simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, Rat.zero_mul, Rat.zero_add]
    cases k with
    | zero => rfl
    | succ k' => exact ih k'

/-- Shifting the right operand shifts the product. -/
theorem dCoeff_dMulSchoolbook_shift_right (m : Nat) (a b : List Rat) (k : Nat) :
    dCoeff (dMulSchoolbook a (dShift m b)) k = dCoeff (dShift m (dMulSchoolbook a b)) k := by
  induction a generalizing k with
  | nil =>
    rw [dMulSchoolbook, dCoeff_nil, dCoeff_dShift]
    split <;> rfl
  | cons x xs ih =>
    simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, dCoeff_dShift]
    cases k with
    | zero =>
      cases m with
      | zero => simp [Rat.add_zero]
      | succ m' => simp [Rat.mul_zero, Rat.add_zero]
    | succ k' =>
      rw [dCoeff_cons_succ, ih k', dCoeff_dShift]
      by_cases h1 : k' + 1 < m
      · have h2 : k' < m := by omega
        simp [h1, h2, Rat.mul_zero, Rat.add_zero]
      · by_cases h2 : k' < m
        · have heq : k' + 1 - m = 0 := by omega
          simp [h1, h2, heq, Rat.add_zero]
        · have hsub : k' + 1 - m = (k' - m) + 1 := by omega
          simp [h1, h2, hsub]

/-- Double-shift composition law. -/
theorem dCoeff_dShift_dShift (m n : Nat) (p : List Rat) (k : Nat) :
    dCoeff (dShift m (dShift n p)) k = dCoeff (dShift (m + n) p) k := by
  simp only [dCoeff_dShift]
  by_cases h1 : k < m
  · have h2 : k < m + n := by omega
    simp [h1, h2]
  · by_cases h2 : k - m < n
    · have h3 : k < m + n := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (k < m + n) := by omega
      have hsub : k - m - n = k - (m + n) := by omega
      simp [h1, h2, h3, hsub]

/-- `dShift` respects coefficient-wise equality. -/
theorem dCoeff_dShift_congr {m : Nat} {p q : List Rat}
    (h : ∀ j, dCoeff p j = dCoeff q j) (k : Nat) :
    dCoeff (dShift m p) k = dCoeff (dShift m q) k := by
  rw [dCoeff_dShift, dCoeff_dShift]
  split
  · rfl
  · exact h (k - m)

/-- Schoolbook multiplication is congruent under coefficient-wise equality on the left. -/
theorem dCoeff_dMulSchoolbook_congr_left {a₁ a₂ b : List Rat}
    (ha : ∀ k, dCoeff a₁ k = dCoeff a₂ k) (k : Nat) :
    dCoeff (dMulSchoolbook a₁ b) k = dCoeff (dMulSchoolbook a₂ b) k := by
  induction a₁ generalizing a₂ k with
  | nil =>
    induction a₂ generalizing k with
    | nil => rfl
    | cons y ys ih2 =>
      have hy0 : y = 0 := by simpa using (ha 0).symm
      have hrest : ∀ j, dCoeff [] j = dCoeff ys j := fun j => ha (j + 1)
      simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, hy0, Rat.zero_mul, Rat.zero_add]
      cases k with
      | zero => rfl
      | succ k' => exact ih2 hrest k'
  | cons x xs ih1 =>
    cases a₂ with
    | nil =>
      have hx0 : x = 0 := by simpa using ha 0
      have hrest : ∀ j, dCoeff xs j = dCoeff [] j := fun j => ha (j + 1)
      simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, hx0, Rat.zero_mul, Rat.zero_add]
      cases k with
      | zero => rfl
      | succ k' => exact ih1 hrest k'
    | cons y ys =>
      have hxy : x = y := by simpa using ha 0
      have hrest : ∀ j, dCoeff xs j = dCoeff ys j := fun j => ha (j + 1)
      simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, hxy]
      congr 1
      cases k with
      | zero => rfl
      | succ k' => exact ih1 hrest k'

/-! ### Verified Refactor 3B: Karatsuba Multiplication (`O(n^{1.585})`) -/

/-- Verified Karatsuba divide-and-conquer polynomial multiplication.
    Splits operands at `m = max |a| |b| / 2` and computes only 3 recursive products
    instead of 4 whenever both lengths are at least `max cutoff 2`. -/
def dMulKaratsuba (cutoff : Nat := 16) (a b : List Rat) : List Rat :=
  let c := max cutoff 2
  if h : a.length < c ∨ b.length < c then
    dMulSchoolbook a b
  else
    let m := max a.length b.length / 2
    let a0 := a.take m
    let a1 := a.drop m
    let b0 := b.take m
    let b1 := b.drop m
    have h0 : max a0.length b0.length < max a.length b.length := by
      simp only [a0, b0, List.length_take]
      omega
    have h1 : max a1.length b1.length < max a.length b.length := by
      simp only [a1, b1, List.length_drop]
      omega
    have h2 : max (dAdd a0 a1).length (dAdd b0 b1).length < max a.length b.length := by
      rw [dAdd_length, dAdd_length]
      simp only [a0, a1, b0, b1, List.length_take, List.length_drop]
      omega
    let z0 := dMulKaratsuba cutoff a0 b0
    let z2 := dMulKaratsuba cutoff a1 b1
    let z1 := dSub (dSub (dMulKaratsuba cutoff (dAdd a0 a1) (dAdd b0 b1)) z0) z2
    dAdd z0 (dAdd (dShift m z1) (dShift (2 * m) z2))
termination_by max a.length b.length

/-- **Karatsuba Equivalence Theorem (zero `sorry`)**:
    For every cutoff, every pair of dense polynomials `a b : List Rat`, and every index `k`,
    Karatsuba produces the exact same coefficient as schoolbook multiplication. -/
theorem dCoeff_dMulKaratsuba (cutoff : Nat) (a b : List Rat) (k : Nat) :
    dCoeff (dMulKaratsuba cutoff a b) k = dCoeff (dMulSchoolbook a b) k := by
  unfold dMulKaratsuba
  dsimp only
  split
  · rfl
  · rename_i hge
    let c := max cutoff 2
    let m := max a.length b.length / 2
    let a0 := a.take m
    let a1 := a.drop m
    let b0 := b.take m
    let b1 := b.drop m
    have hc_ge : ¬ (a.length < c ∨ b.length < c) := hge
    have h0 : max a0.length b0.length < max a.length b.length := by
      simp only [a0, b0, List.length_take]; omega
    have h1 : max a1.length b1.length < max a.length b.length := by
      simp only [a1, b1, List.length_drop]; omega
    have h2 : max (dAdd a0 a1).length (dAdd b0 b1).length < max a.length b.length := by
      rw [dAdd_length, dAdd_length]
      simp only [a0, a1, b0, b1, List.length_take, List.length_drop]; omega
    -- Rewrite LHS using inductive hypotheses
    have ih0 : ∀ j, dCoeff (dMulKaratsuba cutoff a0 b0) j = dCoeff (dMulSchoolbook a0 b0) j :=
      fun j => dCoeff_dMulKaratsuba cutoff a0 b0 j
    have ih1 : ∀ j, dCoeff (dMulKaratsuba cutoff a1 b1) j = dCoeff (dMulSchoolbook a1 b1) j :=
      fun j => dCoeff_dMulKaratsuba cutoff a1 b1 j
    have ih2 : ∀ j, dCoeff (dMulKaratsuba cutoff (dAdd a0 a1) (dAdd b0 b1)) j =
        dCoeff (dMulSchoolbook (dAdd a0 a1) (dAdd b0 b1)) j :=
      fun j => dCoeff_dMulKaratsuba cutoff (dAdd a0 a1) (dAdd b0 b1) j
    -- Expand RHS by splitting a = a0 + u^m a1 and b = b0 + u^m b1
    have ha_split : ∀ j, dCoeff a j = dCoeff (dAdd a0 (dShift m a1)) j := by
      intro j; rw [dCoeff_dAdd]; exact dCoeff_take_add_drop a m j
    have hb_split : ∀ j, dCoeff b j = dCoeff (dAdd b0 (dShift m b1)) j := by
      intro j; rw [dCoeff_dAdd]; exact dCoeff_take_add_drop b m j
    have h11 : dCoeff (dMulSchoolbook (dShift m a1) (dShift m b1)) k =
        dCoeff (dShift (2 * m) (dMulSchoolbook a1 b1)) k := by
      rw [dCoeff_dMulSchoolbook_shift_left,
          dCoeff_dShift_congr (fun j => dCoeff_dMulSchoolbook_shift_right m a1 b1 j),
          dCoeff_dShift_dShift]
      have h2m : m + m = 2 * m := by omega
      rw [h2m]
    have hrhs : dCoeff (dMulSchoolbook a b) k =
        dCoeff (dMulSchoolbook a0 b0) k +
        (dCoeff (dShift m (dMulSchoolbook a0 b1)) k +
         dCoeff (dShift m (dMulSchoolbook a1 b0)) k) +
        dCoeff (dShift (2 * m) (dMulSchoolbook a1 b1)) k := by
      rw [dCoeff_dMulSchoolbook_congr_left ha_split,
          dCoeff_dMulSchoolbook_congr_right hb_split,
          dCoeff_dMulSchoolbook_add_left,
          dCoeff_dMulSchoolbook_add_right,
          dCoeff_dMulSchoolbook_add_right,
          dCoeff_dMulSchoolbook_shift_right,
          dCoeff_dMulSchoolbook_shift_left,
          h11]
      grind
    change dCoeff (dAdd (dMulKaratsuba cutoff a0 b0)
        (dAdd (dShift m (dSub (dSub (dMulKaratsuba cutoff (dAdd a0 a1) (dAdd b0 b1))
                                    (dMulKaratsuba cutoff a0 b0))
                              (dMulKaratsuba cutoff a1 b1)))
              (dShift (2 * m) (dMulKaratsuba cutoff a1 b1)))) k =
      dCoeff (dMulSchoolbook a b) k
    rw [hrhs]
    -- Expand LHS and apply Karatsuba's algebraic identity z1 = a0*b1 + a1*b0
    simp only [dCoeff_dAdd, dCoeff_dShift, dCoeff_dSub, ih0, ih1, ih2]
    have hz1 : ∀ j, dCoeff (dMulSchoolbook (dAdd a0 a1) (dAdd b0 b1)) j -
        dCoeff (dMulSchoolbook a0 b0) j - dCoeff (dMulSchoolbook a1 b1) j =
        dCoeff (dMulSchoolbook a0 b1) j + dCoeff (dMulSchoolbook a1 b0) j := by
      intro j
      rw [dCoeff_dMulSchoolbook_add_left, dCoeff_dMulSchoolbook_add_right,
          dCoeff_dMulSchoolbook_add_right]
      grind
    by_cases hkm : k < m
    · simp [hkm, Rat.zero_add, Rat.add_zero]
    · simp only [hkm, ↓reduceIte, hz1 (k - m)]
      grind
termination_by max a.length b.length

/-! ### Verified Bridge between `TermList` and Dense Grids -/

/-- Reconstruct a canonical `WF` `TermList` from dense coefficients on grid `e0 - (idx + k) * step`. -/
def fromGridAux (e0 step : Rat) (idx : Nat) : List Rat → TermList
  | [] => []
  | c :: rest =>
    let tail := fromGridAux e0 step (idx + 1) rest
    if c == 0 then tail
    else (e0 - (idx : Rat) * step, c) :: tail

/-- Reconstruct a canonical `WF` `TermList` from dense coefficients on `e0 - k * step`. -/
def fromGrid (e0 step : Rat) (ds : List Rat) : TermList :=
  fromGridAux e0 step 0 ds

private theorem nat_cast_succ_rat (n : Nat) : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
  grind

private theorem grid_exp_lt {e0 step : Rat} (hstep : step > 0) (idx : Nat) :
    e0 - ((idx + 1 : Nat) : Rat) * step < e0 - (idx : Rat) * step := by
  rw [nat_cast_succ_rat]
  grind

theorem fromGridAux_allLt {e0 step : Rat} (hstep : step > 0) (idx : Nat) (ds : List Rat)
    {bound : Rat} (hb : e0 - (idx : Rat) * step < bound) :
    AllLt bound (fromGridAux e0 step idx ds) := by
  induction ds generalizing idx bound with
  | nil => trivial
  | cons c rest ih =>
    simp only [fromGridAux]
    have hnext : e0 - ((idx + 1 : Nat) : Rat) * step < bound := by
      have hlt := grid_exp_lt (e0 := e0) hstep idx
      grind
    split
    · exact ih (idx + 1) hnext
    · exact ⟨hb, ih (idx + 1) hnext⟩

/-- `fromGridAux` always produces a canonical `WF` term list when `step > 0`. -/
theorem fromGridAux_wf {e0 step : Rat} (hstep : step > 0) (idx : Nat) (ds : List Rat) :
    WF (fromGridAux e0 step idx ds) := by
  induction ds generalizing idx with
  | nil => trivial
  | cons c rest ih =>
    simp only [fromGridAux]
    split
    · exact ih (idx + 1)
    · rename_i hnz
      have hc : c ≠ 0 := by intro h; simp [h] at hnz
      exact ⟨hc, fromGridAux_allLt hstep (idx + 1) rest (grid_exp_lt (e0 := e0) hstep idx), ih (idx + 1)⟩

/-- `fromGrid` always produces a canonical `WF` term list when `step > 0`. -/
theorem fromGrid_wf {e0 step : Rat} (hstep : step > 0) (ds : List Rat) :
    WF (fromGrid e0 step ds) :=
  fromGridAux_wf hstep 0 ds

/-- Coefficient evaluation of `fromGridAux`: agrees with `dCoeff` at grid points and is `0` elsewhere. -/
theorem coeffOf_fromGridAux_eq_zero_of_gt {e0 step e : Rat} (hstep : step > 0)
    (idx : Nat) (ds : List Rat) (hgt : e > e0 - (idx : Rat) * step) :
    coeffOf (fromGridAux e0 step idx ds) e = 0 := by
  have hall : AllLt e (fromGridAux e0 step idx ds) :=
    fromGridAux_allLt hstep idx ds (by grind)
  exact coeffOf_eq_zero_of_allLt hall (by grind)

/-- Coefficient-wise equivalence between two `fromGridAux` outputs whose dense lists have identical `dCoeff`. -/
theorem coeffOf_fromGridAux_congr {e0 step : Rat} (idx : Nat)
    {da db : List Rat} (h : ∀ k, dCoeff da k = dCoeff db k) (e : Rat) :
    coeffOf (fromGridAux e0 step idx da) e = coeffOf (fromGridAux e0 step idx db) e := by
  induction da generalizing db idx with
  | nil =>
    induction db generalizing idx with
    | nil => rfl
    | cons b bs ihb =>
      have hb0 : b = 0 := by simpa using (h 0).symm
      simp only [fromGridAux, hb0, beq_self_eq_true, ↓reduceIte]
      exact ihb (idx + 1) (fun k => by simpa using h (k + 1))
  | cons a as iha =>
    cases db with
    | nil =>
      have ha0 : a = 0 := by simpa using h 0
      simp only [fromGridAux, ha0, beq_self_eq_true, ↓reduceIte]
      exact iha (idx + 1) (db := []) (fun k => by simpa using h (k + 1))
    | cons b bs =>
      have hab : a = b := by simpa using h 0
      subst hab
      simp only [fromGridAux]
      split
      · exact iha (idx + 1) (fun k => by simpa using h (k + 1))
      · simp only [coeffOf, iha (idx + 1) (fun k => by simpa using h (k + 1))]

/-- Exact grid-aligned extraction: checks in one linear pass that every term in `ts` lies
    on `e0 - (idx + k) * step` within `fuel` slots. -/
def extractGridAux (e0 step : Rat) (idx : Nat) : Nat → TermList → Option (List Rat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, (e, c) :: rest =>
    let expected := e0 - (idx : Rat) * step
    if e == expected then
      (extractGridAux e0 step (idx + 1) fuel rest).map (c :: ·)
    else if e < expected then
      (extractGridAux e0 step (idx + 1) fuel ((e, c) :: rest)).map (0 :: ·)
    else
      none

/-- Soundness of `extractGridAux`: whenever extraction succeeds, `fromGridAux` recovers
    the exact same `coeffOf` at every rational exponent `e`. -/
theorem extractGridAux_sound {e0 step : Rat} {idx fuel : Nat} {ts : TermList} {ds : List Rat}
    (h : extractGridAux e0 step idx fuel ts = some ds) (e : Rat) :
    coeffOf (fromGridAux e0 step idx ds) e = coeffOf ts e := by
  induction fuel generalizing idx ts ds with
  | zero =>
    cases ts with
    | nil =>
      simp only [extractGridAux, Option.some.injEq] at h
      subst h; rfl
    | cons _ _ => simp [extractGridAux] at h
  | succ fuel' ih =>
    cases ts with
    | nil =>
      simp only [extractGridAux, Option.some.injEq] at h
      subst h; rfl
    | cons p rest =>
      rcases p with ⟨ep, cp⟩
      simp only [extractGridAux] at h
      split at h
      · rename_i heq_b
        have hep : ep = e0 - (idx : Rat) * step := eq_of_beq heq_b
        rcases Option.map_eq_some_iff.mp h with ⟨ds', hrec, rfl⟩
        simp only [fromGridAux]
        split
        · rename_i hcz
          have hcp : cp = 0 := eq_of_beq hcz
          rw [ih hrec]
          simp [coeffOf, hcp, Rat.zero_add]
        · simp only [coeffOf, ih hrec, hep]
      · split at h
        · rcases Option.map_eq_some_iff.mp h with ⟨ds', hrec, rfl⟩
          simp only [fromGridAux, beq_self_eq_true, ↓reduceIte]
          exact ih hrec
        · simp at h

/-! ### Bridging `fromGridAux` and `dMulSchoolbook` to `mulNaiveTerms` -/

private theorem coeffOf_fromGridAux_add (e0 step : Rat) (idx : Nat)
    (a b : List Rat) (e : Rat) :
    coeffOf (fromGridAux e0 step idx (dAdd a b)) e =
      coeffOf (fromGridAux e0 step idx a) e + coeffOf (fromGridAux e0 step idx b) e := by
  induction a generalizing b idx with
  | nil => simp [dAdd, fromGridAux, coeffOf, Rat.zero_add]
  | cons x xs ih =>
    cases b with
    | nil => simp [dAdd, fromGridAux, coeffOf, Rat.add_zero]
    | cons y ys =>
      simp only [dAdd, ratAddFast_eq, fromGridAux]
      have hrec := ih (idx + 1) ys
      by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> by_cases hxy : x + y = 0
      · simp [hx, hy, Rat.add_zero, hrec]
      · grind
      · grind
      · have hne_y : (y == 0) = false := by cases hb : (y == 0) <;> simp_all
        simp only [hx, hne_y, Rat.zero_add, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, coeffOf, hrec]
        grind
      · grind
      · have hne_x : (x == 0) = false := by cases hb : (x == 0) <;> simp_all
        simp only [hy, hne_x, Rat.add_zero, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, coeffOf, hrec]
        grind
      · have hne_x : (x == 0) = false := by cases hb : (x == 0) <;> simp_all
        have hne_y : (y == 0) = false := by cases hb : (y == 0) <;> simp_all
        simp only [hne_x, hne_y, hxy, beq_self_eq_true, ↓reduceIte, Bool.false_eq_true, coeffOf, hrec]
        split <;> grind
      · have hne_x : (x == 0) = false := by cases hb : (x == 0) <;> simp_all
        have hne_y : (y == 0) = false := by cases hb : (y == 0) <;> simp_all
        have hne_xy : (x + y == 0) = false := by cases hb : (x + y == 0) <;> simp_all
        simp only [hne_x, hne_y, hne_xy, Bool.false_eq_true, ↓reduceIte, coeffOf, hrec]
        split <;> grind

private theorem coeffOf_fromGridAux_scale (e0 step c : Rat) (idx : Nat) (b : List Rat) (e : Rat) :
    coeffOf (fromGridAux e0 step idx (dScale c b)) e =
      c * coeffOf (fromGridAux e0 step idx b) e := by
  induction b generalizing idx with
  | nil => simp [dScale, fromGridAux, coeffOf, Rat.mul_zero]
  | cons y ys ih =>
    have hsc : dScale c (y :: ys) = (c * y) :: dScale c ys := by
      simp [dScale, ratMulFast_eq]
    rw [hsc]
    simp only [fromGridAux]
    have hrec := ih (idx + 1)
    by_cases hy : y = 0
    · simp [hy, Rat.mul_zero, hrec]
    · by_cases hc : c = 0
      · subst hc
        simp [Rat.zero_mul, hrec]
      · have hne_y : (y == 0) = false := by cases hb : (y == 0) <;> simp_all
        have hcy : c * y ≠ 0 := by
          intro h; rcases Rat.mul_eq_zero.mp h with h1 | h2
          · exact hc h1
          · exact hy h2
        have hne_cy : (c * y == 0) = false := by cases hb : (c * y == 0) <;> simp_all
        simp only [hne_y, hne_cy, Bool.false_eq_true, ↓reduceIte, coeffOf, hrec, Rat.mul_add]
        split <;> simp [Rat.mul_zero]

private theorem coeffOf_fromGridAux_shift_base (e0 e1 step : Rat) (idx : Nat)
    (b : List Rat) (e : Rat) :
    coeffOf (fromGridAux (e0 + e1) step idx b) e =
      coeffOf (fromGridAux e1 step 0 b) (e - (e0 - (idx : Rat) * step)) := by
  suffices h : ∀ (j : Nat) (ds : List Rat),
      coeffOf (fromGridAux (e0 + e1) step (idx + j) ds) e =
        coeffOf (fromGridAux e1 step j ds) (e - (e0 - (idx : Rat) * step)) by
    simpa using h 0 b
  intro j ds
  induction ds generalizing j with
  | nil => rfl
  | cons y ys ih =>
    simp only [fromGridAux]
    have hrec : coeffOf (fromGridAux (e0 + e1) step (idx + j + 1) ys) e =
        coeffOf (fromGridAux e1 step (j + 1) ys) (e - (e0 - (idx : Rat) * step)) := by
      have := ih (j + 1)
      have heq : idx + (j + 1) = idx + j + 1 := by omega
      rwa [heq] at this
    split
    · exact hrec
    · simp only [coeffOf, hrec]
      congr 1
      have hiff : (e0 + e1 - ((idx + j : Nat) : Rat) * step == e) =
          (e1 - (j : Rat) * step == e - (e0 - (idx : Rat) * step)) := by
        have hcast : ((idx + j : Nat) : Rat) = (idx : Rat) + (j : Rat) := by grind
        cases h1 : (e0 + e1 - ((idx + j : Nat) : Rat) * step == e) <;>
          cases h2 : (e1 - (j : Rat) * step == e - (e0 - (idx : Rat) * step)) <;> try rfl
        · have heq := eq_of_beq h2
          have hgoal : e0 + e1 - ((idx + j : Nat) : Rat) * step = e := by rw [hcast]; grind
          rw [hgoal] at h1
          simp at h1
        · have heq := eq_of_beq h1
          have hgoal : e1 - (j : Rat) * step = e - (e0 - (idx : Rat) * step) := by rw [hcast] at heq; grind
          rw [hgoal] at h2
          simp at h2
      rw [hiff]

/-- Schoolbook dense multiplication matches `mulNaiveTerms` on grid-reconstructed term lists. -/
theorem coeffOf_fromGridAux_dMulSchoolbook (ex0 ey0 step : Rat) (idx : Nat)
    (da db : List Rat) (e : Rat) :
    coeffOf (fromGridAux (ex0 + ey0) step idx (dMulSchoolbook da db)) e =
      coeffOf (mulNaiveTerms (fromGridAux ex0 step idx da) (fromGridAux ey0 step 0 db)) e := by
  induction da generalizing idx with
  | nil => rfl
  | cons c rest ih =>
    simp only [dMulSchoolbook, coeffOf_fromGridAux_add, coeffOf_fromGridAux_scale]
    have htail : coeffOf (fromGridAux (ex0 + ey0) step idx (0 :: dMulSchoolbook rest db)) e =
        coeffOf (fromGridAux (ex0 + ey0) step (idx + 1) (dMulSchoolbook rest db)) e := by
      simp [fromGridAux]
    rw [htail, ih (idx + 1), coeffOf_fromGridAux_shift_base]
    simp only [fromGridAux]
    split
    · rename_i hz
      have hc : c = 0 := eq_of_beq hz
      simp [hc, Rat.zero_mul, Rat.zero_add]
    · rw [coeffOf_mulNaiveTerms_cons]

/-- Combined grid-Karatsuba multiplication matches `mulNaiveTerms` whenever extraction succeeds. -/
theorem coeffOf_fromGrid_dMulKaratsuba {ex0 ey0 step : Rat} (_hstep : step > 0)
    (cutoff : Nat) {xs ys : TermList} {da db : List Rat} {fx fy : Nat}
    (hx : extractGridAux ex0 step 0 fx xs = some da)
    (hy : extractGridAux ey0 step 0 fy ys = some db) (e : Rat) :
    coeffOf (fromGrid (ex0 + ey0) step (dMulKaratsuba cutoff da db)) e =
      coeffOf (mulNaiveTerms xs ys) e := by
  unfold fromGrid
  rw [coeffOf_fromGridAux_congr 0 (fun k => dCoeff_dMulKaratsuba cutoff da db k) e,
      coeffOf_fromGridAux_dMulSchoolbook]
  rw [coeffOf_mulNaiveTerms_congr_left (fun e' => extractGridAux_sound hx e'),
      coeffOf_mulNaiveTerms_congr_right (fun e' => extractGridAux_sound hy e')]

/-! ### Verified Unboxed `Array Int` Dense Polynomial Kernel (Rung 3)

For integer-coefficient dense grids (`c.den == 1`), operating directly on `Array Int`
eliminates `List Rat` cons-cell allocation, `Rat.gcd` normalization, and O(n) list splits,
while proving exact algebraic equivalence back to `dMulSchoolbook` and `mulNaiveTerms`.
-/

/-- Coefficient of `u^k` in an `Array Int` dense polynomial (`0` out of bounds). -/
@[inline] def aCoeff (arr : Array Int) (k : Nat) : Int :=
  if h : k < arr.size then arr[k] else 0

private theorem rat_ofInt_add (a b : Int) : Rat.ofInt (a + b) = Rat.ofInt a + Rat.ofInt b := by
  rw [Rat.add_def]
  apply Rat.ext <;> simp [Rat.normalize, Rat.ofInt]

private theorem rat_ofInt_sub (a b : Int) : Rat.ofInt (a - b) = Rat.ofInt a - Rat.ofInt b := by
  rw [Rat.sub_def]
  apply Rat.ext <;> simp [Rat.normalize, Rat.ofInt]

private theorem rat_ofInt_mul (a b : Int) : Rat.ofInt (a * b) = Rat.ofInt a * Rat.ofInt b := by
  rw [Rat.mul_def]
  apply Rat.ext <;> simp [Rat.normalize, Rat.ofInt]

private theorem rat_ofInt_zero : Rat.ofInt 0 = 0 := by
  apply Rat.ext <;> simp [Rat.ofInt]

/-- Out-of-bounds `aCoeff` is `0`. -/
theorem aCoeff_of_ge {arr : Array Int} {k : Nat} (h : arr.size ≤ k) : aCoeff arr k = 0 := by
  unfold aCoeff
  have hnot : ¬ (k < arr.size) := by omega
  simp [hnot]

private theorem dCoeff_map_ofInt (p : Array Int) (k : Nat) :
    dCoeff (p.toList.map Rat.ofInt) k = Rat.ofInt (aCoeff p k) := by
  unfold dCoeff aCoeff
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have h1 : k < (p.toList.map Rat.ofInt).length := by simpa using h
    rw [List.getElem?_eq_getElem h1]
    simp
  · rename_i h
    have h1 : (p.toList.map Rat.ofInt).length ≤ k := by simp at h ⊢; omega
    rw [List.getElem?_eq_none h1]
    simpa using rat_ofInt_zero.symm

/-- Coefficient lookup after `Array.push`. -/
theorem aCoeff_push (arr : Array Int) (v : Int) (k : Nat) :
    aCoeff (arr.push v) k = if k < arr.size then aCoeff arr k else if k = arr.size then v else 0 := by
  unfold aCoeff
  simp only [Array.size_push]
  by_cases hk : k < arr.size
  · have hk1 : k < arr.size + 1 := by omega
    simp [hk, hk1, Array.getElem_push_lt]
  · by_cases heq : k = arr.size
    · subst heq
      simp
    · have hnot : ¬ (k < arr.size + 1) := by omega
      simp [hk, heq, hnot]

/-- Coefficient lookup after `Array.set`. -/
theorem aCoeff_set (arr : Array Int) (idx : Nat) (v : Int) (h : idx < arr.size) (k : Nat) :
    aCoeff (arr.set idx v h) k = if k = idx then v else aCoeff arr k := by
  unfold aCoeff
  simp only [Array.size_set]
  by_cases hki : k = idx
  · subst hki; simp [h]
  · simp only [hki, ↓reduceIte]
    by_cases hk : k < arr.size
    · simp [hk, Array.getElem_set_ne h hk (Ne.symm hki)]
    · simp [hk]

private theorem aCoeff_extract (arr : Array Int) (start stop k : Nat) :
    aCoeff (arr.extract start stop) k =
      if k < min stop arr.size - start then aCoeff arr (start + k) else 0 := by
  unfold aCoeff
  simp only [Array.size_extract]
  split
  · rename_i hk
    have hlt : start + k < arr.size := by omega
    simp [hlt]
  · rfl

/-- Coefficient lookup on a zero-initialized `Array.replicate n 0`. -/
theorem aCoeff_replicate_zero (n k : Nat) :
    aCoeff (Array.replicate n (0 : Int)) k = 0 := by
  unfold aCoeff
  split
  · simp
  · rfl

/-- Dense `Array Int` addition loop (`O(max |a| |b|)`, single preallocated array). -/
def aAddLoop (a b : Array Int) (n i : Nat) (acc : Array Int) : Array Int :=
  if _h : i < n then
    aAddLoop a b n (i + 1) (acc.push (aCoeff a i + aCoeff b i))
  else
    acc
termination_by n - i

/-- Dense `Array Int` addition (`O(max |a| |b|)`). -/
@[inline] def aAdd (a b : Array Int) : Array Int :=
  let n := max a.size b.size
  aAddLoop a b n 0 (Array.mkEmpty n)

private theorem aAddLoop_size (a b : Array Int) (n i : Nat) (acc : Array Int)
    (hi : i ≤ n) (hacc : acc.size = i) :
    (aAddLoop a b n i acc).size = n := by
  unfold aAddLoop
  split
  · rename_i hlt
    exact aAddLoop_size a b n (i + 1) _ (by omega) (by simp [hacc])
  · omega
termination_by n - i

/-- Size of `aAdd a b` is `max a.size b.size`. -/
theorem aAdd_size (a b : Array Int) : (aAdd a b).size = max a.size b.size :=
  aAddLoop_size a b (max a.size b.size) 0 _ (Nat.zero_le _) (by simp)

private theorem aCoeff_aAddLoop (a b : Array Int) (n i : Nat) (acc : Array Int)
    (hi : i ≤ n) (hacc : acc.size = i) (k : Nat) :
    aCoeff (aAddLoop a b n i acc) k =
      if k < i then aCoeff acc k else if k < n then aCoeff a k + aCoeff b k else 0 := by
  unfold aAddLoop
  split
  · rename_i hlt
    rw [aCoeff_aAddLoop a b n (i + 1) _ (by omega) (by simp [hacc]) k]
    by_cases hk : k < i
    · have hk1 : k < i + 1 := by omega
      simp [hk, hk1, aCoeff_push, hacc]
    · by_cases heq : k = i
      · subst heq
        simp [hlt, aCoeff_push, hacc]
      · have hnot1 : ¬ (k < i + 1) := by omega
        simp [hk, hnot1]
  · rename_i hge
    have hni : n = i := by omega
    subst hni
    by_cases hk : k < n
    · simp [hk]
    · simp [hk, aCoeff_of_ge (by omega : acc.size ≤ k)]
termination_by n - i

/-- Coefficient specification of `aAdd`. -/
theorem aCoeff_aAdd (a b : Array Int) (k : Nat) :
    aCoeff (aAdd a b) k = aCoeff a k + aCoeff b k := by
  unfold aAdd
  rw [aCoeff_aAddLoop a b (max a.size b.size) 0 _ (Nat.zero_le _) (by simp) k]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  split
  · rfl
  · rename_i hge
    rw [aCoeff_of_ge (by omega : a.size ≤ k), aCoeff_of_ge (by omega : b.size ≤ k)]
    rfl

/-- Dense `Array Int` subtraction loop (`O(max |a| |b|)`, single preallocated array). -/
def aSubLoop (a b : Array Int) (n i : Nat) (acc : Array Int) : Array Int :=
  if _h : i < n then
    aSubLoop a b n (i + 1) (acc.push (aCoeff a i - aCoeff b i))
  else
    acc
termination_by n - i

/-- Dense `Array Int` subtraction (`O(max |a| |b|)`). -/
@[inline] def aSub (a b : Array Int) : Array Int :=
  let n := max a.size b.size
  aSubLoop a b n 0 (Array.mkEmpty n)

private theorem aCoeff_aSubLoop (a b : Array Int) (n i : Nat) (acc : Array Int)
    (hi : i ≤ n) (hacc : acc.size = i) (k : Nat) :
    aCoeff (aSubLoop a b n i acc) k =
      if k < i then aCoeff acc k else if k < n then aCoeff a k - aCoeff b k else 0 := by
  unfold aSubLoop
  split
  · rename_i hlt
    rw [aCoeff_aSubLoop a b n (i + 1) _ (by omega) (by simp [hacc]) k]
    by_cases hk : k < i
    · have hk1 : k < i + 1 := by omega
      simp [hk, hk1, aCoeff_push, hacc]
    · by_cases heq : k = i
      · subst heq
        simp [hlt, aCoeff_push, hacc]
      · have hnot1 : ¬ (k < i + 1) := by omega
        simp [hk, hnot1]
  · rename_i hge
    have hni : n = i := by omega
    subst hni
    by_cases hk : k < n
    · simp [hk]
    · simp [hk, aCoeff_of_ge (by omega : acc.size ≤ k)]
termination_by n - i

/-- Coefficient specification of `aSub`. -/
theorem aCoeff_aSub (a b : Array Int) (k : Nat) :
    aCoeff (aSub a b) k = aCoeff a k - aCoeff b k := by
  unfold aSub
  rw [aCoeff_aSubLoop a b (max a.size b.size) 0 _ (Nat.zero_le _) (by simp) k]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  split
  · rfl
  · rename_i hge
    rw [aCoeff_of_ge (by omega : a.size ≤ k), aCoeff_of_ge (by omega : b.size ≤ k)]
    rfl

/-- In-place `RC=1` fused scale-and-accumulate loop: `out[offset + j] += c * b[j]`. -/
def aScaleAddAtLoop (offset : Nat) (c : Int) (b : Array Int) (j : Nat) (out : Array Int) : Array Int :=
  if hj : j < b.size then
    let idx := offset + j
    if hidx : idx < out.size then
      let out' := out.set idx (out[idx] + c * b[j]) hidx
      aScaleAddAtLoop offset c b (j + 1) out'
    else
      out
  else
    out
termination_by b.size - j

/-- In-place `RC=1` fused scale-and-accumulate: `out[offset + j] += c * b[j]` for all `j`. -/
@[inline] def aScaleAddAt (out : Array Int) (offset : Nat) (c : Int) (b : Array Int) : Array Int :=
  if c == 0 then out else aScaleAddAtLoop offset c b 0 out

/-- `aScaleAddAtLoop` preserves array size. -/
theorem aScaleAddAtLoop_size (offset : Nat) (c : Int) (b : Array Int) (j : Nat)
    (out : Array Int) :
    (aScaleAddAtLoop offset c b j out).size = out.size := by
  unfold aScaleAddAtLoop
  split
  · dsimp only
    split
    · rw [aScaleAddAtLoop_size, Array.size_set]
    · rfl
  · rfl
termination_by b.size - j

private theorem aCoeff_aScaleAddAtLoop (offset : Nat) (c : Int) (b : Array Int) (j : Nat)
    (out : Array Int) (hsize : offset + b.size ≤ out.size) (k : Nat) :
    aCoeff (aScaleAddAtLoop offset c b j out) k =
      aCoeff out k + (if k < offset + j then 0 else c * aCoeff b (k - offset)) := by
  unfold aScaleAddAtLoop
  split
  · rename_i hj
    have hidx : offset + j < out.size := by omega
    simp only [hidx, ↓reduceDIte]
    have hsize' : offset + b.size ≤ (out.set (offset + j) (out[offset + j] + c * b[j]) hidx).size := by
      simpa using hsize
    rw [aCoeff_aScaleAddAtLoop offset c b (j + 1) _ hsize' k, aCoeff_set]
    by_cases hkeq : k = offset + j
    · subst hkeq
      have hsub : offset + j - offset = j := by omega
      have hnotlt : ¬ (offset + j < offset + j) := by omega
      have hlt1 : offset + j < offset + (j + 1) := by omega
      simp [hnotlt, hlt1, hsub, aCoeff, hidx, hj]
    · simp only [hkeq, ↓reduceIte]
      by_cases hk : k < offset + j
      · have hk1 : k < offset + (j + 1) := by omega
        simp [hk, hk1]
      · have hk1 : ¬ (k < offset + (j + 1)) := by omega
        simp [hk, hk1]
  · rename_i hj
    have hge : b.size ≤ j := by omega
    by_cases hk : k < offset + j
    · simp [hk]
    · have hkb : b.size ≤ k - offset := by omega
      simp [hk, aCoeff_of_ge hkb]
termination_by b.size - j

/-- Coefficient specification of `aScaleAddAt`. -/
theorem aCoeff_aScaleAddAt (out : Array Int) (offset : Nat) (c : Int) (b : Array Int)
    (hsize : offset + b.size ≤ out.size) (k : Nat) :
    aCoeff (aScaleAddAt out offset c b) k =
      aCoeff out k + (if k < offset then 0 else c * aCoeff b (k - offset)) := by
  unfold aScaleAddAt
  split
  · rename_i hc
    have hc0 : c = 0 := eq_of_beq hc
    subst hc0
    split <;> simp
  · simpa using aCoeff_aScaleAddAtLoop offset c b 0 out hsize k

/-- In-place `RC=1` schoolbook loop over `a[i]`, accumulating `a[i] * u^i * b` into `out`. -/
def aMulSchoolbookLoop (a b : Array Int) (i : Nat) (out : Array Int) : Array Int :=
  if hi : i < a.size then
    let out' := aScaleAddAt out i a[i] b
    aMulSchoolbookLoop a b (i + 1) out'
  else
    out
termination_by a.size - i

/-- Verified in-place `RC=1` unboxed `Array Int` schoolbook multiplication (`~9 ns/op`). -/
def aMulSchoolbookInt (a b : Array Int) : Array Int :=
  if a.isEmpty || b.isEmpty then #[]
  else
    let out := Array.replicate (a.size + b.size - 1) (0 : Int)
    aMulSchoolbookLoop a b 0 out

private theorem aMulSchoolbookLoop_spec (a b : Array Int) (i : Nat) (out : Array Int)
    (hsize : a.size + b.size - 1 ≤ out.size) (hb : b.size > 0) (k : Nat) :
    Rat.ofInt (aCoeff (aMulSchoolbookLoop a b i out) k) =
      Rat.ofInt (aCoeff out k) +
        dCoeff (dShift i (dMulSchoolbook ((a.toList.drop i).map Rat.ofInt) (b.toList.map Rat.ofInt))) k := by
  unfold aMulSchoolbookLoop
  split
  · rename_i hi
    have hsc_size : i + b.size ≤ out.size := by omega
    have hout'_size : (aScaleAddAt out i a[i] b).size = out.size := by
      unfold aScaleAddAt
      split
      · rfl
      · exact aScaleAddAtLoop_size i a[i] b 0 out
    rw [aMulSchoolbookLoop_spec a b (i + 1) _ (by omega) hb k,
        aCoeff_aScaleAddAt out i a[i] b hsc_size k, rat_ofInt_add]
    have hdrop : a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
      have hi' : i < a.toList.length := by simpa using hi
      simpa using List.drop_eq_getElem_cons hi'
    rw [hdrop, List.map_cons, dMulSchoolbook]
    simp only [dCoeff_dShift, dCoeff_dAdd, dCoeff_dScale, dCoeff_map_ofInt]
    by_cases hki : k < i
    · have hki1 : k < i + 1 := by omega
      simp [hki, hki1, rat_ofInt_zero, Rat.add_zero]
    · by_cases hkeq : k = i
      · subst hkeq
        have hki1 : k < k + 1 := by omega
        have hsub : k - k = 0 := by omega
        simp [hki, hki1, hsub, rat_ofInt_mul, Rat.add_zero]
      · have hki1 : ¬ (k < i + 1) := by omega
        have hsub : k - i = (k - (i + 1)) + 1 := by omega
        simp only [hki, hki1, ↓reduceIte, hsub, dCoeff_cons_succ, rat_ofInt_mul, Rat.add_assoc]
  · rename_i hge
    have hdrop : a.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hdrop, List.map_nil, dMulSchoolbook, dCoeff_dShift]
    split <;> simp [Rat.add_zero]
termination_by a.size - i

/-- **In-place `Array Int` Schoolbook Equivalence Theorem (zero `sorry`)**:
    `aMulSchoolbookInt` produces the exact same coefficients as `dMulSchoolbook` over `Rat`. -/
theorem aCoeff_aMulSchoolbookInt (a b : Array Int) (k : Nat) :
    Rat.ofInt (aCoeff (aMulSchoolbookInt a b) k) =
      dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) (b.toList.map Rat.ofInt)) k := by
  unfold aMulSchoolbookInt
  split
  · rename_i hemp
    simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero] at hemp
    rcases hemp with ha | hb
    · have hal : a.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using ha)
      simp [hal, dMulSchoolbook, aCoeff, rat_ofInt_zero]
    · have hbl : b.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hb)
      rw [hbl, List.map_nil]
      have hz : dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) []) k = 0 := by
        have hnil : ∀ xs : List Rat, ∀ j, dCoeff (dMulSchoolbook xs []) j = 0 := by
          intro xs
          induction xs with
          | nil => intro j; rfl
          | cons x xs ih =>
            intro j
            simp only [dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, dCoeff_nil, Rat.mul_zero, Rat.zero_add]
            cases j with
            | zero => rfl
            | succ j' => exact ih j'
        exact hnil _ k
      simp [hz, aCoeff, rat_ofInt_zero]
  · rename_i hne
    simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero, not_or] at hne
    have hbpos : b.size > 0 := Nat.pos_of_ne_zero hne.2
    have hspec := aMulSchoolbookLoop_spec a b 0 (Array.replicate (a.size + b.size - 1) 0)
      (by simp) hbpos k
    simpa [aCoeff_replicate_zero, rat_ofInt_zero, Rat.zero_add, dCoeff_dShift] using hspec

/-- Single-pass Karatsuba recombination loop: `z0 + u^m z1 + u^{2m} z2` in one allocation. -/
def aCombineKaratsubaLoop (m : Nat) (z0 z1 z2 : Array Int) (n i : Nat) (acc : Array Int) : Array Int :=
  if _h : i < n then
    let v0 := aCoeff z0 i
    let v1 := if i < m then 0 else aCoeff z1 (i - m)
    let v2 := if i < 2 * m then 0 else aCoeff z2 (i - 2 * m)
    aCombineKaratsubaLoop m z0 z1 z2 n (i + 1) (acc.push (v0 + v1 + v2))
  else
    acc
termination_by n - i

/-- Combine Karatsuba subproducts `z0 + u^m z1 + u^{2m} z2` directly into one `Array Int`. -/
@[inline] def aCombineKaratsuba (m : Nat) (z0 z1 z2 : Array Int) : Array Int :=
  let n := max z0.size (max (m + z1.size) (2 * m + z2.size))
  aCombineKaratsubaLoop m z0 z1 z2 n 0 (Array.mkEmpty n)

private theorem aCoeff_aCombineKaratsubaLoop (m : Nat) (z0 z1 z2 : Array Int) (n i : Nat)
    (acc : Array Int) (hi : i ≤ n) (hacc : acc.size = i) (k : Nat) :
    aCoeff (aCombineKaratsubaLoop m z0 z1 z2 n i acc) k =
      if k < i then aCoeff acc k
      else if k < n then
        aCoeff z0 k + (if k < m then 0 else aCoeff z1 (k - m)) +
          (if k < 2 * m then 0 else aCoeff z2 (k - 2 * m))
      else 0 := by
  unfold aCombineKaratsubaLoop
  split
  · rename_i hlt
    rw [aCoeff_aCombineKaratsubaLoop m z0 z1 z2 n (i + 1) _ (by omega) (by simp [hacc]) k]
    by_cases hk : k < i
    · have hk1 : k < i + 1 := by omega
      simp [hk, hk1, aCoeff_push, hacc]
    · by_cases heq : k = i
      · subst heq
        simp [hlt, aCoeff_push, hacc]
      · have hnot1 : ¬ (k < i + 1) := by omega
        simp [hk, hnot1]
  · rename_i hge
    have hni : n = i := by omega
    subst hni
    by_cases hk : k < n
    · simp [hk]
    · simp [hk, aCoeff_of_ge (by omega : acc.size ≤ k)]
termination_by n - i

/-- Coefficient specification of `aCombineKaratsuba`. -/
theorem aCoeff_aCombineKaratsuba (m : Nat) (z0 z1 z2 : Array Int) (k : Nat) :
    aCoeff (aCombineKaratsuba m z0 z1 z2) k =
      aCoeff z0 k + (if k < m then 0 else aCoeff z1 (k - m)) +
        (if k < 2 * m then 0 else aCoeff z2 (k - 2 * m)) := by
  unfold aCombineKaratsuba
  let n := max z0.size (max (m + z1.size) (2 * m + z2.size))
  rw [aCoeff_aCombineKaratsubaLoop m z0 z1 z2 n 0 _ (Nat.zero_le _) (by simp) k]
  simp only [Nat.not_lt_zero, ↓reduceIte]
  split
  · rfl
  · rename_i hge
    have h0 : z0.size ≤ k := by omega
    rw [aCoeff_of_ge h0]
    split
    · split
      · rfl
      · rename_i h2
        rw [aCoeff_of_ge (by omega : z2.size ≤ k - 2 * m)]; rfl
    · rename_i h1
      rw [aCoeff_of_ge (by omega : z1.size ≤ k - m)]
      split
      · rfl
      · rename_i h2
        rw [aCoeff_of_ge (by omega : z2.size ≤ k - 2 * m)]; rfl

/-- Verified unboxed `Array Int` Karatsuba multiplication (`O(n^{1.585})`, falling back to
    in-place `RC=1` `aMulSchoolbookInt` below `max cutoff 2`). -/
def aMulKaratsubaInt (cutoff : Nat := 32) (a b : Array Int) : Array Int :=
  let c := max cutoff 2
  if h : a.size < c ∨ b.size < c then
    aMulSchoolbookInt a b
  else
    let m := max a.size b.size / 2
    let a0 := a.extract 0 m
    let a1 := a.extract m a.size
    let b0 := b.extract 0 m
    let b1 := b.extract m b.size
    have h0 : max a0.size b0.size < max a.size b.size := by
      simp only [a0, b0, Array.size_extract]; omega
    have h1 : max a1.size b1.size < max a.size b.size := by
      simp only [a1, b1, Array.size_extract]; omega
    have h2 : max (aAdd a0 a1).size (aAdd b0 b1).size < max a.size b.size := by
      rw [aAdd_size, aAdd_size]
      simp only [a0, a1, b0, b1, Array.size_extract]; omega
    let z0 := aMulKaratsubaInt cutoff a0 b0
    let z2 := aMulKaratsubaInt cutoff a1 b1
    let z1 := aSub (aSub (aMulKaratsubaInt cutoff (aAdd a0 a1) (aAdd b0 b1)) z0) z2
    aCombineKaratsuba m z0 z1 z2
termination_by max a.size b.size

private theorem aAdd_map_ofInt_dCoeff (x y : Array Int) (k : Nat) :
    dCoeff ((aAdd x y).toList.map Rat.ofInt) k =
      dCoeff (dAdd (x.toList.map Rat.ofInt) (y.toList.map Rat.ofInt)) k := by
  rw [dCoeff_map_ofInt, aCoeff_aAdd, rat_ofInt_add, dCoeff_dAdd, dCoeff_map_ofInt, dCoeff_map_ofInt]

private theorem extract_split_dCoeff (a : Array Int) (m k : Nat) :
    dCoeff (a.toList.map Rat.ofInt) k =
      dCoeff (dAdd ((a.extract 0 m).toList.map Rat.ofInt)
                   (dShift m ((a.extract m a.size).toList.map Rat.ofInt))) k := by
  rw [dCoeff_dAdd, dCoeff_dShift, dCoeff_map_ofInt, dCoeff_map_ofInt, dCoeff_map_ofInt,
      aCoeff_extract, aCoeff_extract]
  by_cases hkm : k < m
  · by_cases hka : k < a.size
    · have h1 : k < min m a.size := by omega
      simp [hkm, h1, Rat.add_zero]
    · have h1 : ¬ (k < min m a.size) := by omega
      simp [hkm, h1, aCoeff_of_ge (by omega : a.size ≤ k), rat_ofInt_zero, Rat.add_zero]
  · have h1 : ¬ (k < min m a.size) := by omega
    by_cases hka : k < a.size
    · have h2 : k - m < a.size - m := by omega
      have hsum : m + (k - m) = k := by omega
      simp [hkm, h1, h2, hsum, rat_ofInt_zero, Rat.zero_add]
    · have h2 : ¬ (k - m < a.size - m) := by omega
      simp [hkm, h1, h2, aCoeff_of_ge (by omega : a.size ≤ k), rat_ofInt_zero, Rat.zero_add]

/-- **`Array Int` Karatsuba Equivalence Theorem (zero `sorry`)**:
    `aMulKaratsubaInt` matches `dMulSchoolbook` over `Rat` at every index `k`. -/
theorem aCoeff_aMulKaratsubaInt (cutoff : Nat) (a b : Array Int) (k : Nat) :
    Rat.ofInt (aCoeff (aMulKaratsubaInt cutoff a b) k) =
      dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) (b.toList.map Rat.ofInt)) k := by
  unfold aMulKaratsubaInt
  dsimp only
  split
  · exact aCoeff_aMulSchoolbookInt a b k
  · rename_i hge
    let c := max cutoff 2
    let m := max a.size b.size / 2
    let a0 := a.extract 0 m
    let a1 := a.extract m a.size
    let b0 := b.extract 0 m
    let b1 := b.extract m b.size
    have h0 : max a0.size b0.size < max a.size b.size := by
      simp only [a0, b0, Array.size_extract]; omega
    have h1 : max a1.size b1.size < max a.size b.size := by
      simp only [a1, b1, Array.size_extract]; omega
    have h2 : max (aAdd a0 a1).size (aAdd b0 b1).size < max a.size b.size := by
      rw [aAdd_size, aAdd_size]
      simp only [a0, a1, b0, b1, Array.size_extract]; omega
    let ra0 := a0.toList.map Rat.ofInt
    let ra1 := a1.toList.map Rat.ofInt
    let rb0 := b0.toList.map Rat.ofInt
    let rb1 := b1.toList.map Rat.ofInt
    have ih0 : ∀ j, Rat.ofInt (aCoeff (aMulKaratsubaInt cutoff a0 b0) j) =
        dCoeff (dMulSchoolbook ra0 rb0) j :=
      fun j => aCoeff_aMulKaratsubaInt cutoff a0 b0 j
    have ih1 : ∀ j, Rat.ofInt (aCoeff (aMulKaratsubaInt cutoff a1 b1) j) =
        dCoeff (dMulSchoolbook ra1 rb1) j :=
      fun j => aCoeff_aMulKaratsubaInt cutoff a1 b1 j
    have ih2 : ∀ j, Rat.ofInt (aCoeff (aMulKaratsubaInt cutoff (aAdd a0 a1) (aAdd b0 b1)) j) =
        dCoeff (dMulSchoolbook (dAdd ra0 ra1) (dAdd rb0 rb1)) j := by
      intro j
      rw [aCoeff_aMulKaratsubaInt cutoff (aAdd a0 a1) (aAdd b0 b1) j,
          dCoeff_dMulSchoolbook_congr_left (aAdd_map_ofInt_dCoeff a0 a1),
          dCoeff_dMulSchoolbook_congr_right (aAdd_map_ofInt_dCoeff b0 b1)]
    have h11 : dCoeff (dMulSchoolbook (dShift m ra1) (dShift m rb1)) k =
        dCoeff (dShift (2 * m) (dMulSchoolbook ra1 rb1)) k := by
      rw [dCoeff_dMulSchoolbook_shift_left,
          dCoeff_dShift_congr (fun j => dCoeff_dMulSchoolbook_shift_right m ra1 rb1 j),
          dCoeff_dShift_dShift]
      have h2m : m + m = 2 * m := by omega
      rw [h2m]
    have hrhs : dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) (b.toList.map Rat.ofInt)) k =
        dCoeff (dMulSchoolbook ra0 rb0) k +
        (dCoeff (dShift m (dMulSchoolbook ra0 rb1)) k +
         dCoeff (dShift m (dMulSchoolbook ra1 rb0)) k) +
        dCoeff (dShift (2 * m) (dMulSchoolbook ra1 rb1)) k := by
      rw [dCoeff_dMulSchoolbook_congr_left (extract_split_dCoeff a m),
          dCoeff_dMulSchoolbook_congr_right (extract_split_dCoeff b m),
          dCoeff_dMulSchoolbook_add_left,
          dCoeff_dMulSchoolbook_add_right,
          dCoeff_dMulSchoolbook_add_right,
          dCoeff_dMulSchoolbook_shift_right,
          dCoeff_dMulSchoolbook_shift_left,
          h11]
      grind
    change Rat.ofInt (aCoeff (aCombineKaratsuba m (aMulKaratsubaInt cutoff a0 b0)
        (aSub (aSub (aMulKaratsubaInt cutoff (aAdd a0 a1) (aAdd b0 b1))
                    (aMulKaratsubaInt cutoff a0 b0))
              (aMulKaratsubaInt cutoff a1 b1))
        (aMulKaratsubaInt cutoff a1 b1)) k) = _
    rw [hrhs, aCoeff_aCombineKaratsuba, rat_ofInt_add, rat_ofInt_add, ih0]
    have hz1 : ∀ j, Rat.ofInt (aCoeff (aSub (aSub (aMulKaratsubaInt cutoff (aAdd a0 a1) (aAdd b0 b1))
                                                  (aMulKaratsubaInt cutoff a0 b0))
                                            (aMulKaratsubaInt cutoff a1 b1)) j) =
        dCoeff (dMulSchoolbook ra0 rb1) j + dCoeff (dMulSchoolbook ra1 rb0) j := by
      intro j
      rw [aCoeff_aSub, aCoeff_aSub, rat_ofInt_sub, rat_ofInt_sub, ih2, ih0, ih1,
          dCoeff_dMulSchoolbook_add_left, dCoeff_dMulSchoolbook_add_right,
          dCoeff_dMulSchoolbook_add_right]
      grind
    simp only [dCoeff_dShift]
    by_cases hkm : k < m
    · have h2m : k < 2 * m := by omega
      simp [hkm, h2m, rat_ofInt_zero, Rat.add_zero]
    · by_cases h2m : k < 2 * m
      · simp [hkm, h2m, hz1 (k - m), rat_ofInt_zero, Rat.add_zero]
      · simp [hkm, h2m, hz1 (k - m), ih1 (k - 2 * m)]
termination_by max a.size b.size

/-! ### Fast Single-Pass `Array Int` Grid Bridge (`extractIntGrid` & `fromIntGrid`) -/

/-- Single-pass running-exponent integer-coefficient grid extractor (zero `Rat.mul`,
    zero `Option.map` cons allocation). Succeeds iff every term has `c.den == 1` and aligns
    on `e0 - k * step` within `fuel` slots. -/
def extractIntGridLoop (step : Rat) : Nat → Rat → TermList → Array Int → Option (Array Int)
  | _, _, [], acc => some acc
  | 0, _, _ :: _, _ => none
  | fuel + 1, curExp, (e, c) :: rest, acc =>
    if c.den != 1 then none
    else
      match ratCmpFast e curExp with
      | .eq => extractIntGridLoop step fuel (ratSubFast curExp step) rest (acc.push c.num)
      | .lt => extractIntGridLoop step fuel (ratSubFast curExp step) ((e, c) :: rest) (acc.push 0)
      | .gt => none

/-- Entry point for single-pass `Array Int` grid extraction. -/
@[inline] def extractIntGrid (e0 step : Rat) (fuel : Nat) (ts : TermList) : Option (Array Int) :=
  extractIntGridLoop step fuel e0 ts (Array.mkEmpty ts.length)

/-- Classified result of single-pass integer-coefficient grid extraction, distinguishing
    non-integer coefficients (`den ≠ 1`) from genuinely off-grid (sparse) exponents. -/
inductive IntGridResult where
  /-- All terms align on `e0 - k * step` with integer coefficients (`den == 1`). -/
  | ok (arr : Array Int)
  /-- Encountered a non-integer coefficient (`den ≠ 1`); rational grid path may still apply. -/
  | nonInt
  /-- Encountered an off-grid exponent or fuel exhaustion; skip rational grid walk immediately. -/
  | offGrid

/-- Single-pass classified integer grid extraction loop. -/
def extractIntGridClassifiedLoop (step : Rat) :
    Nat → Rat → TermList → Array Int → IntGridResult
  | _, _, [], acc => .ok acc
  | 0, _, _ :: _, _ => .offGrid
  | fuel + 1, curExp, (e, c) :: rest, acc =>
    if c.den != 1 then .nonInt
    else
      match ratCmpFast e curExp with
      | .eq => extractIntGridClassifiedLoop step fuel (ratSubFast curExp step) rest (acc.push c.num)
      | .lt => extractIntGridClassifiedLoop step fuel (ratSubFast curExp step) ((e, c) :: rest) (acc.push 0)
      | .gt => .offGrid

/-- Classified entry point for single-pass `Array Int` grid extraction. -/
@[inline] def extractIntGridClassified (e0 step : Rat) (fuel : Nat) (ts : TermList) : IntGridResult :=
  extractIntGridClassifiedLoop step fuel e0 ts (Array.mkEmpty ts.length)

private theorem extractIntGridClassifiedLoop_ok (step : Rat) (fuel : Nat) (curExp : Rat)
    (ts : TermList) (acc res : Array Int)
    (h : extractIntGridClassifiedLoop step fuel curExp ts acc = .ok res) :
    extractIntGridLoop step fuel curExp ts acc = some res := by
  induction fuel generalizing curExp ts acc with
  | zero =>
    cases ts with
    | nil =>
      simp only [extractIntGridClassifiedLoop, IntGridResult.ok.injEq] at h
      subst h; rfl
    | cons _ _ => simp [extractIntGridClassifiedLoop] at h
  | succ fuel' ih =>
    cases ts with
    | nil =>
      simp only [extractIntGridClassifiedLoop, IntGridResult.ok.injEq] at h
      subst h; rfl
    | cons p rest =>
      rcases p with ⟨ep, cp⟩
      simp only [extractIntGridClassifiedLoop] at h
      simp only [extractIntGridLoop]
      split at h
      · simp at h
      · rename_i hden
        simp only [hden, Bool.false_eq_true, ↓reduceIte]
        cases hcmp : ratCmpFast ep curExp <;> simp only [hcmp] at h
        · exact ih _ _ _ h
        · exact ih _ _ _ h
        · simp at h

/-- Soundness bridge: `.ok arr` from `extractIntGridClassified` implies `extractIntGrid = some arr`. -/
theorem extractIntGridClassified_ok {e0 step : Rat} {fuel : Nat} {ts : TermList} {arr : Array Int}
    (h : extractIntGridClassified e0 step fuel ts = .ok arr) :
    extractIntGrid e0 step fuel ts = some arr :=
  extractIntGridClassifiedLoop_ok step fuel e0 ts (Array.mkEmpty ts.length) arr h

private theorem fromGridAux_append_singleton (e0 step : Rat) (idx : Nat) (ds : List Rat) (x : Rat) :
    fromGridAux e0 step idx (ds ++ [x]) =
      fromGridAux e0 step idx ds ++
        (if x == 0 then [] else [(e0 - ((idx + ds.length : Nat) : Rat) * step, x)]) := by
  induction ds generalizing idx with
  | nil =>
    simp [fromGridAux]
  | cons c rest ih =>
    simp only [List.cons_append, fromGridAux, List.length_cons]
    have hidx : idx + 1 + rest.length = idx + (rest.length + 1) := by omega
    rw [ih (idx + 1), hidx]
    split
    · rfl
    · rfl

private theorem extractIntGridLoop_sound {e0 step : Rat} {fuel : Nat} {ts : TermList}
    {acc res : Array Int}
    (h : extractIntGridLoop step fuel (e0 - (acc.size : Rat) * step) ts acc = some res) (e : Rat) :
    coeffOf (fromGrid e0 step (res.toList.map Rat.ofInt)) e =
      coeffOf (fromGrid e0 step (acc.toList.map Rat.ofInt)) e + coeffOf ts e := by
  induction fuel generalizing ts acc res with
  | zero =>
    cases ts with
    | nil =>
      simp only [extractIntGridLoop, Option.some.injEq] at h
      subst h
      simp [coeffOf, Rat.add_zero]
    | cons _ _ => simp [extractIntGridLoop] at h
  | succ fuel' ih =>
    cases ts with
    | nil =>
      simp only [extractIntGridLoop, Option.some.injEq] at h
      subst h
      simp [coeffOf, Rat.add_zero]
    | cons p rest =>
      rcases p with ⟨ep, cp⟩
      simp only [extractIntGridLoop] at h
      split at h
      · simp at h
      · rename_i hden_ne
        have hden : cp.den = 1 := by simpa using hden_ne
        have hcp : Rat.ofInt cp.num = cp := by
          apply Rat.ext <;> simp [Rat.ofInt, hden]
        have hsub : ratSubFast (e0 - (acc.size : Rat) * step) step =
            e0 - ((acc.size + 1 : Nat) : Rat) * step := by
          rw [ratSubFast_eq, nat_cast_succ_rat]; grind
        cases hcmp : ratCmpFast ep (e0 - (acc.size : Rat) * step) <;> rw [hcmp] at h
        · -- .lt: emit 0 gap, keep (ep, cp) :: rest
          have hsz : (acc.push 0).size = acc.size + 1 := Array.size_push 0
          rw [hsub, ← hsz] at h
          rw [ih h]
          simp only [fromGrid, Array.toList_push, List.map_append, List.map_singleton,
            fromGridAux_append_singleton, rat_ofInt_zero, beq_self_eq_true, ↓reduceIte,
            List.append_nil]
        · -- .eq: emit cp.num, advance rest
          have hep : ep = e0 - (acc.size : Rat) * step := by
            have h1 : ¬ (ep > e0 - (acc.size : Rat) * step) := by
              intro hg; have := (ratCmpFast_gt _ _).mpr hg; rw [hcmp] at this; cases this
            have h2 : ¬ (e0 - (acc.size : Rat) * step > ep) := by
              intro hl; have := (ratCmpFast_lt _ _).mpr hl; rw [hcmp] at this; cases this
            grind
          have hsz : (acc.push cp.num).size = acc.size + 1 := Array.size_push cp.num
          rw [hsub, ← hsz] at h
          rw [ih h]
          simp only [fromGrid, Array.toList_push, List.map_append, List.map_singleton,
            fromGridAux_append_singleton, hcp, List.length_map, Array.length_toList,
            Nat.zero_add, coeffOf_append]
          split
          · rename_i hz
            have hcz : cp = 0 := eq_of_beq hz
            simp [coeffOf, hcz, Rat.zero_add, Rat.add_zero]
          · simp only [coeffOf, hep, Rat.add_zero, Rat.add_assoc]
        · -- .gt: rejected
          simp at h

/-- Soundness of `extractIntGrid`: whenever extraction succeeds, `fromGrid` on the mapped array
    has the exact same `coeffOf` as `ts` at every rational exponent `e`. -/
theorem extractIntGrid_sound {e0 step : Rat} {fuel : Nat} {ts : TermList} {arr : Array Int}
    (h : extractIntGrid e0 step fuel ts = some arr) (e : Rat) :
    coeffOf (fromGrid e0 step (arr.toList.map Rat.ofInt)) e = coeffOf ts e := by
  unfold extractIntGrid at h
  have hcur : e0 = e0 - ((Array.mkEmpty ts.length : Array Int).size : Rat) * step := by
    simp; grind
  rw [hcur] at h
  have hs := extractIntGridLoop_sound (e0 := e0) (step := step) h e
  simpa [fromGrid, fromGridAux, coeffOf, Rat.zero_add] using hs

/-- Backwards tail-recursive reconstruction from `Array Int` into a canonical `WF` `TermList`
    (zero `List.reverse`, zero `Rat.mul` inside the loop). -/
def fromIntGridLoop (step : Rat) (arr : Array Int) :
    (i : Nat) → i ≤ arr.size → Rat → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, hi, curExp, acc =>
    let nextExp := ratAddFast curExp step
    let c := arr[i]
    let acc' := if c == 0 then acc else (nextExp, Rat.ofInt c) :: acc
    fromIntGridLoop step arr i (Nat.le_of_succ_le hi) nextExp acc'

/-- Reconstruct a canonical `WF` `TermList` from an `Array Int` on grid `e0 - k * step`. -/
def fromIntGrid (e0 step : Rat) (arr : Array Int) : TermList :=
  fromIntGridLoop step arr arr.size (Nat.le_refl _) (e0 - (arr.size : Rat) * step) []

private theorem fromIntGridLoop_eq (e0 step : Rat) (arr : Array Int) (i : Nat)
    (hi : i ≤ arr.size) (acc : TermList) :
    fromIntGridLoop step arr i hi (e0 - (i : Rat) * step) acc =
      fromGridAux e0 step 0 ((arr.toList.take i).map Rat.ofInt) ++ acc := by
  induction i generalizing acc with
  | zero =>
    simp [fromIntGridLoop, fromGridAux]
  | succ i ih =>
    simp only [fromIntGridLoop]
    have hnext : ratAddFast (e0 - ((i + 1 : Nat) : Rat) * step) step = e0 - (i : Rat) * step := by
      rw [ratAddFast_eq, nat_cast_succ_rat]; grind
    rw [hnext, ih (Nat.le_of_succ_le hi)]
    have htake : arr.toList.take (i + 1) = arr.toList.take i ++ [arr[i]] := by
      have hi' : i < arr.toList.length := by simp; omega
      simpa using List.take_succ_eq_append_getElem hi'
    rw [htake, List.map_append, List.map_singleton, fromGridAux_append_singleton]
    have hlen : ((arr.toList.take i).map Rat.ofInt).length = i := by
      simp [List.length_take]; omega
    have hzero : (arr[i] == 0) = (Rat.ofInt arr[i] == 0) := by
      cases h1 : (arr[i] == 0) <;> cases h2 : (Rat.ofInt arr[i] == 0) <;> try rfl
      · have hr : Rat.ofInt arr[i] = 0 := eq_of_beq h2
        have hnum : (Rat.ofInt arr[i]).num = (0 : Rat).num := congrArg Rat.num hr
        simp [Rat.ofInt] at hnum
        simp [hnum] at h1
      · have hz : arr[i] = 0 := eq_of_beq h1
        rw [hz, rat_ofInt_zero] at h2; simp at h2
    rw [hlen, Nat.zero_add, hzero]
    split <;> simp [List.append_assoc]

/-- Structural identity bridging `fromIntGrid` directly to `fromGrid`. -/
theorem fromIntGrid_eq_fromGrid (e0 step : Rat) (arr : Array Int) :
    fromIntGrid e0 step arr = fromGrid e0 step (arr.toList.map Rat.ofInt) := by
  unfold fromIntGrid fromGrid
  rw [fromIntGridLoop_eq]
  simp [List.take_of_length_le]

/-- `fromIntGrid` always produces a canonical `WF` term list when `step > 0`. -/
theorem fromIntGrid_wf {e0 step : Rat} (hstep : step > 0) (arr : Array Int) :
    WF (fromIntGrid e0 step arr) := by
  rw [fromIntGrid_eq_fromGrid]
  exact fromGrid_wf hstep _

/-- Combined `Array Int` grid-Karatsuba multiplication matches `mulNaiveTerms` whenever
    `extractIntGrid` succeeds on both operands. -/
theorem coeffOf_fromIntGrid_aMulKaratsubaInt {ex0 ey0 step : Rat} (_hstep : step > 0)
    (cutoff : Nat) {xs ys : TermList} {ia ib : Array Int} {fx fy : Nat}
    (hx : extractIntGrid ex0 step fx xs = some ia)
    (hy : extractIntGrid ey0 step fy ys = some ib) (e : Rat) :
    coeffOf (fromIntGrid (ratAddFast ex0 ey0) step (aMulKaratsubaInt cutoff ia ib)) e =
      coeffOf (mulNaiveTerms xs ys) e := by
  rw [ratAddFast_eq, fromIntGrid_eq_fromGrid]
  unfold fromGrid
  have hcongr : ∀ k, dCoeff ((aMulKaratsubaInt cutoff ia ib).toList.map Rat.ofInt) k =
      dCoeff (dMulSchoolbook (ia.toList.map Rat.ofInt) (ib.toList.map Rat.ofInt)) k := fun k => by
    rw [dCoeff_map_ofInt]; exact aCoeff_aMulKaratsubaInt cutoff ia ib k
  rw [coeffOf_fromGridAux_congr 0 hcongr e, coeffOf_fromGridAux_dMulSchoolbook]
  rw [coeffOf_mulNaiveTerms_congr_left (fun e' => by simpa [fromGrid] using extractIntGrid_sound hx e'),
      coeffOf_mulNaiveTerms_congr_right (fun e' => by simpa [fromGrid] using extractIntGrid_sound hy e')]

/-! ### Unified Verified Fast Multiplication (`mulFast`) -/

/-- Heuristic step-size guess from the leading exponent gaps of `xs` and `ys`. -/
def guessGridStep (xs ys : TermList) : Option Rat :=
  match xs, ys with
  | (ex0, _) :: (ex1, _) :: _, (ey0, _) :: (ey1, _) :: _ =>
    let dx := ratSubFast ex0 ex1
    let dy := ratSubFast ey0 ey1
    let step := match ratCmpFast dx dy with | .gt => dy | _ => dx
    if step.num > 0 then some step else none
  | _, _ => none

/-- Verified fast multiplication for canonical `TermList`:
    1. When both operands have `≥ 4` terms and align onto an integer-coefficient (`den == 1`)
       arithmetic grid, dispatches to **verified unboxed `Array Int` Karatsuba / schoolbook**.
    2. Otherwise, when both operands have `≥ cutoff` terms on a rational arithmetic grid,
       dispatches to **verified `List Rat` Karatsuba** (`O(n^{1.585})`).
    3. Otherwise falls back to **verified balanced-tree sparse merge** (`mulTree`). -/
def mulFast (xs ys : TermList) (cutoff : Nat := 16) : TermList :=
  if xs.length ≥ 4 && ys.length ≥ 4 then
    match xs, ys, guessGridStep xs ys with
    | (ex0, _) :: _, (ey0, _) :: _, some step =>
      if step > 0 then
        let fuel := 2 * (xs.length + ys.length) + 16
        match extractIntGrid ex0 step fuel xs, extractIntGrid ey0 step fuel ys with
        | some ia, some ib =>
          fromIntGrid (ratAddFast ex0 ey0) step (aMulKaratsubaInt 32 ia ib)
        | _, _ =>
          if xs.length ≥ cutoff && ys.length ≥ cutoff then
            match extractGridAux ex0 step 0 fuel xs, extractGridAux ey0 step 0 fuel ys with
            | some da, some db =>
              fromGrid (ratAddFast ex0 ey0) step (dMulKaratsuba cutoff da db)
            | _, _ => mulTree xs ys
          else
            mulTree xs ys
      else mulTree xs ys
    | _, _, _ => mulTree xs ys
  else
    mulTree xs ys

/-- `mulFast` preserves canonical well-formedness. -/
theorem mulFast_wf {xs ys : TermList} (hxs : WF xs) (hys : WF ys) (cutoff : Nat := 16) :
    WF (mulFast xs ys cutoff) := by
  unfold mulFast
  split
  · split
    · split
      · rename_i hstep
        dsimp only
        split
        · exact fromIntGrid_wf hstep _
        · split
          · split
            · exact fromGrid_wf hstep _
            · exact mulTree_wf hxs hys
          · exact mulTree_wf hxs hys
      · exact mulTree_wf hxs hys
    · exact mulTree_wf hxs hys
  · exact mulTree_wf hxs hys

/-- **Unified Multiplication Equivalence Theorem (zero `sorry`)**:
    `mulFast` (combining unboxed `Array Int` Karatsuba, rational Karatsuba, and balanced-tree
    sparse merge) produces the exact same mathematical Levi-Civita product as naive `O(nm)`
    multiplication at every rational exponent `e`. -/
theorem coeffOf_mulFast (xs ys : TermList) (e : Rat) (cutoff : Nat := 16) :
    coeffOf (mulFast xs ys cutoff) e = coeffOf (mulNaiveTerms xs ys) e := by
  unfold mulFast
  split
  · split
    · split
      · rename_i hstep
        dsimp only
        split
        · rename_i ia ib hx hy
          exact coeffOf_fromIntGrid_aMulKaratsubaInt hstep 32 hx hy e
        · split
          · split
            · rename_i da db hx hy
              rw [ratAddFast_eq]
              exact coeffOf_fromGrid_dMulKaratsuba hstep cutoff hx hy e
            · exact coeffOf_mulTree _ _ e
          · exact coeffOf_mulTree _ _ e
      · exact coeffOf_mulTree _ _ e
    · exact coeffOf_mulTree _ _ e
  · exact coeffOf_mulTree _ _ e

end Karatsuba
end LeanInf
