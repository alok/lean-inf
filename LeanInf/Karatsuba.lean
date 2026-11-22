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

/-- Dense polynomial addition (`O(max |a| |b|)`). -/
def dAdd : List Rat → List Rat → List Rat
  | [], b => b
  | a, [] => a
  | x :: xs, y :: ys => (x + y) :: dAdd xs ys

/-- Dense polynomial subtraction (`O(max |a| |b|)`). -/
def dSub : List Rat → List Rat → List Rat
  | [], b => b.map (fun y => -y)
  | a, [] => a
  | x :: xs, y :: ys => (x - y) :: dSub xs ys

/-- Dense scalar multiplication (`O(|p|)`). -/
def dScale (c : Rat) (p : List Rat) : List Rat :=
  p.map (fun x => c * x)

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
      | zero => rfl
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
      | zero => rfl
      | succ k' => exact ih ys k'

/-- Coefficient specification of `dScale`. -/
theorem dCoeff_dScale (c : Rat) (p : List Rat) (k : Nat) :
    dCoeff (dScale c p) k = c * dCoeff p k := by
  induction p generalizing k with
  | nil => simp [dScale, dCoeff, Rat.mul_zero]
  | cons x xs ih =>
    cases k with
    | zero => rfl
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
      simp only [dAdd, dMulSchoolbook, dCoeff_dAdd, dCoeff_dScale, Rat.add_mul]
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
      simp only [dAdd, fromGridAux]
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
    change coeffOf (fromGridAux e0 step idx ((c * y) :: dScale c ys)) e =
      c * coeffOf (fromGridAux e0 step idx (y :: ys)) e
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

/-! ### Unified Verified Fast Multiplication (`mulFast`) -/

/-- Heuristic step-size guess from the leading exponent gaps of `xs` and `ys`. -/
def guessGridStep (xs ys : TermList) : Option Rat :=
  match xs, ys with
  | (ex0, _) :: (ex1, _) :: _, (ey0, _) :: (ey1, _) :: _ =>
    let dx := ex0 - ex1
    let dy := ey0 - ey1
    let step := if dx ≤ dy then dx else dy
    if step > 0 then some step else none
  | _, _ => none

/-- Verified fast multiplication for canonical `TermList`:
    - When both operands have at least `cutoff` terms and align onto a dense arithmetic
      exponent grid, dispatches to **verified Karatsuba** (`O(n^{1.585})`).
    - Otherwise falls back to **verified balanced-tree sparse merge** (`mulTree`, `O(nm log n)`). -/
def mulFast (xs ys : TermList) (cutoff : Nat := 16) : TermList :=
  if xs.length ≥ cutoff && ys.length ≥ cutoff then
    match xs, ys, guessGridStep xs ys with
    | (ex0, _) :: _, (ey0, _) :: _, some step =>
      if step > 0 then
        let fuel := 2 * (xs.length + ys.length) + 16
        match extractGridAux ex0 step 0 fuel xs, extractGridAux ey0 step 0 fuel ys with
        | some da, some db =>
          fromGrid (ex0 + ey0) step (dMulKaratsuba cutoff da db)
        | _, _ => mulTree xs ys
      else mulTree xs ys
    | _, _, _ => mulTree xs ys
  else
    mulTree xs ys

/-- `mulFast` preserves canonical well-formedness. -/
theorem mulFast_wf {xs ys : TermList} (hys : WF ys) (cutoff : Nat := 16) :
    WF (mulFast xs ys cutoff) := by
  unfold mulFast
  split
  · split
    · split
      · rename_i hstep
        dsimp only
        split
        · exact fromGrid_wf hstep _
        · exact mulTree_wf hys
      · exact mulTree_wf hys
    · exact mulTree_wf hys
  · exact mulTree_wf hys

/-- **Unified Multiplication Equivalence Theorem (zero `sorry`)**:
    `mulFast` (combining dense Karatsuba + balanced-tree sparse merge) produces the exact same
    mathematical Levi-Civita product as naive `O(nm)` multiplication at every rational exponent `e`. -/
theorem coeffOf_mulFast (xs ys : TermList) (e : Rat) (cutoff : Nat := 16) :
    coeffOf (mulFast xs ys cutoff) e = coeffOf (mulNaiveTerms xs ys) e := by
  unfold mulFast
  split
  · split
    · split
      · rename_i hstep
        dsimp only
        split
        · rename_i da db hx hy
          exact coeffOf_fromGrid_dMulKaratsuba hstep cutoff hx hy e
        · exact coeffOf_mulTree _ _ e
      · exact coeffOf_mulTree _ _ e
    · exact coeffOf_mulTree _ _ e
  · exact coeffOf_mulTree _ _ e

end Karatsuba
end LeanInf
