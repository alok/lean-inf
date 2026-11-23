import Init.Data.Array.Lemmas
import LeanInf.Karatsuba

namespace LeanInf
namespace Kronecker

open Karatsuba

/-! ### Verified Kronecker Substitution over `Array Int` (Rung 5, Zero `sorry`)

Packs two `Array Int` polynomials into two big integers at base `2^bits` using balanced
divide-and-conquer shift-packing, multiplies them with a **single** GMP `Int.mul`
(delegating to GMP's Toom-Cook / FFT inside `libleanrt`, zero `@[extern]`), adds a
doubling-computed bias repunit so every product coefficient lies in `[0, 2^bits)`,
and unpacks in `O(L log L)` shift-only operations.
-/

/-! #### 1. Runtime Coefficient Bound (`maxAbs`) -/

/-- Scan `arr[i..]` to compute the maximum absolute value of any coefficient. -/
def maxAbsLoop (arr : Array Int) (i : Nat) (m : Nat) : Nat :=
  if hi : i < arr.size then
    let v := arr[i].natAbs
    maxAbsLoop arr (i + 1) (if v > m then v else m)
  else
    m
termination_by arr.size - i

/-- Maximum absolute value of any coefficient in `arr` (`0` if empty). -/
@[inline] def maxAbs (arr : Array Int) : Nat :=
  maxAbsLoop arr 0 0

private theorem maxAbsLoop_ge_acc (arr : Array Int) (i m : Nat) :
    m ≤ maxAbsLoop arr i m := by
  unfold maxAbsLoop
  split
  · rename_i hi
    have hstep : m ≤ (if arr[i].natAbs > m then arr[i].natAbs else m) := by split <;> omega
    exact Nat.le_trans hstep (maxAbsLoop_ge_acc arr (i + 1) _)
  · exact Nat.le_refl m
termination_by arr.size - i

private theorem maxAbsLoop_ge_elem (arr : Array Int) (i m k : Nat) (hik : i ≤ k) (hk : k < arr.size) :
    arr[k].natAbs ≤ maxAbsLoop arr i m := by
  unfold maxAbsLoop
  split
  · rename_i hi
    by_cases heq : k = i
    · subst heq
      have h1 : arr[k].natAbs ≤ (if arr[k].natAbs > m then arr[k].natAbs else m) := by split <;> omega
      exact Nat.le_trans h1 (maxAbsLoop_ge_acc arr (k + 1) _)
    · exact maxAbsLoop_ge_elem arr (i + 1) _ k (by omega) hk
  · omega
termination_by arr.size - i

/-- Every coefficient in `arr` has `natAbs ≤ maxAbs arr`. -/
theorem natAbs_aCoeff_le_maxAbs (arr : Array Int) (k : Nat) :
    (aCoeff arr k).natAbs ≤ maxAbs arr := by
  unfold aCoeff
  split
  · rename_i hk
    exact maxAbsLoop_ge_elem arr 0 0 k (Nat.zero_le k) hk
  · exact Nat.zero_le _

/-! #### 2. Tight Coefficient Bound & Size of `aMulSchoolbookInt` -/

private def activeInRange (bSize k i n : Nat) : Nat :=
  if i < n then
    (if i ≤ k ∧ k - i < bSize then 1 else 0) + activeInRange bSize k (i + 1) n
  else 0
termination_by n - i

private theorem activeInRange_le_len (bSize k i n : Nat) :
    activeInRange bSize k i n ≤ n - i := by
  unfold activeInRange
  split
  · have ih := activeInRange_le_len bSize k (i + 1) n
    split <;> omega
  · omega
termination_by n - i

private theorem activeInRange_le_bSize (bSize k i n : Nat) :
    activeInRange bSize k i n ≤ (if i ≤ k then min (k + 1 - i) bSize else 0) := by
  unfold activeInRange
  split
  · have ih := activeInRange_le_bSize bSize k (i + 1) n
    by_cases hik : i ≤ k
    · by_cases hlt : k - i < bSize
      · have : activeInRange bSize k (i + 1) n ≤ k - i := by
          split at ih <;> omega
        simp [hik, hlt]; omega
      · have : activeInRange bSize k (i + 1) n ≤ bSize := by
          split at ih <;> omega
        simp [hik, hlt]; omega
    · have : activeInRange bSize k (i + 1) n = 0 := by
        have hnot : ¬ (i + 1 ≤ k) := by omega
        simp [hnot] at ih; exact ih
      simp [hik, this]
  · split <;> omega
termination_by n - i

private theorem aScaleAddAt_size (out : Array Int) (offset : Nat) (c : Int) (b : Array Int) :
    (aScaleAddAt out offset c b).size = out.size := by
  unfold aScaleAddAt
  split
  · rfl
  · exact aScaleAddAtLoop_size offset c b 0 out

private theorem aMulSchoolbookLoop_size (a b : Array Int) (i : Nat) (out : Array Int) :
    (aMulSchoolbookLoop a b i out).size = out.size := by
  unfold aMulSchoolbookLoop
  split
  · rw [aMulSchoolbookLoop_size, aScaleAddAt_size]
  · rfl
termination_by a.size - i

private theorem aMulSchoolbookLoop_natAbs_le (a b : Array Int) (i : Nat) (out : Array Int)
    (hsize : a.size + b.size - 1 ≤ out.size) (hb : b.size > 0) (k : Nat) :
    (aCoeff (aMulSchoolbookLoop a b i out) k).natAbs ≤
      (aCoeff out k).natAbs + activeInRange b.size k i a.size * (maxAbs a * maxAbs b) := by
  unfold aMulSchoolbookLoop activeInRange
  split
  · rename_i hi
    have hsc_size : i + b.size ≤ out.size := by omega
    have hout'_size : a.size + b.size - 1 ≤ (aScaleAddAt out i a[i] b).size := by
      rw [aScaleAddAt_size]; exact hsize
    have ih := aMulSchoolbookLoop_natAbs_le a b (i + 1) (aScaleAddAt out i a[i] b) hout'_size hb k
    rw [aCoeff_aScaleAddAt out i a[i] b hsc_size k] at ih
    have hstep : (aCoeff out k + (if k < i then 0 else a[i] * aCoeff b (k - i))).natAbs ≤
        (aCoeff out k).natAbs + (if i ≤ k ∧ k - i < b.size then 1 else 0) * (maxAbs a * maxAbs b) := by
      by_cases hki : k < i
      · have hnot : ¬ (i ≤ k ∧ k - i < b.size) := by omega
        simp [hki, hnot]
      · by_cases hkb : k - i < b.size
        · have hand : i ≤ k ∧ k - i < b.size := ⟨by omega, hkb⟩
          have ha : a[i].natAbs ≤ maxAbs a := by
            have h0 := natAbs_aCoeff_le_maxAbs a i
            unfold aCoeff at h0
            simp only [hi, ↓reduceDIte] at h0
            exact h0
          have hbb : (aCoeff b (k - i)).natAbs ≤ maxAbs b := natAbs_aCoeff_le_maxAbs b (k - i)
          have hmul : (a[i] * aCoeff b (k - i)).natAbs ≤ maxAbs a * maxAbs b := by
            rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha hbb
          have htri : (aCoeff out k + a[i] * aCoeff b (k - i)).natAbs ≤
              (aCoeff out k).natAbs + (a[i] * aCoeff b (k - i)).natAbs :=
            Int.natAbs_add_le _ _
          simp only [hki, ↓reduceIte, hand.1, hand.2, and_self, Nat.one_mul]
          exact Nat.le_trans htri (Nat.add_le_add_left hmul _)
        · have hnot : ¬ (i ≤ k ∧ k - i < b.size) := by omega
          have hz : aCoeff b (k - i) = 0 := aCoeff_of_ge (by omega)
          simp [hki, hnot, hz]
    rw [Nat.add_mul]
    exact Nat.le_trans ih (by omega)
  · simp
termination_by a.size - i

/-- Every product coefficient of `aMulSchoolbookInt a b` is bounded in `natAbs` by
    `min a.size b.size * maxAbs a * maxAbs b`. -/
theorem natAbs_aMulSchoolbookInt_le (a b : Array Int) (k : Nat) :
    (aCoeff (aMulSchoolbookInt a b) k).natAbs ≤ min a.size b.size * maxAbs a * maxAbs b := by
  unfold aMulSchoolbookInt
  split
  · simp [aCoeff]
  · rename_i hne
    simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero, not_or] at hne
    have hbpos : b.size > 0 := Nat.pos_of_ne_zero hne.2
    have hmain := aMulSchoolbookLoop_natAbs_le a b 0 (Array.replicate (a.size + b.size - 1) 0)
      (by simp) hbpos k
    rw [aCoeff_replicate_zero] at hmain
    simp only [Int.natAbs_zero, Nat.zero_add] at hmain
    have h1 : activeInRange b.size k 0 a.size ≤ a.size := by
      simpa using activeInRange_le_len b.size k 0 a.size
    have h2 : activeInRange b.size k 0 a.size ≤ b.size := by
      have := activeInRange_le_bSize b.size k 0 a.size
      simp only [Nat.zero_le, ↓reduceIte] at this
      omega
    have hmin : activeInRange b.size k 0 a.size ≤ min a.size b.size := Nat.le_min.mpr ⟨h1, h2⟩
    have hmul : activeInRange b.size k 0 a.size * (maxAbs a * maxAbs b) ≤
        min a.size b.size * (maxAbs a * maxAbs b) :=
      Nat.mul_le_mul_right _ hmin
    rw [Nat.mul_assoc]
    exact Nat.le_trans hmain hmul

/-- When `a` and `b` are nonempty, `(aMulSchoolbookInt a b).size = a.size + b.size - 1`. -/
theorem aMulSchoolbookInt_size {a b : Array Int} (ha : a.size > 0) (hb : b.size > 0) :
    (aMulSchoolbookInt a b).size = a.size + b.size - 1 := by
  unfold aMulSchoolbookInt
  have hne : (a.isEmpty || b.isEmpty) = false := by
    cases h : (a.isEmpty || b.isEmpty)
    · rfl
    · simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero] at h; omega
  simp [hne, aMulSchoolbookLoop_size]

/-! #### 3. Fast Bit-Shift Arithmetic on `Int` and `Nat` -/

/-- Multiply an `Int` by `2^s` using pure `Nat.shiftLeft` (`mpz_mul_2exp`, zero `mpz_mul`). -/
@[inline] def shiftInt (x : Int) (s : Nat) : Int :=
  if x ≥ 0 then Int.ofNat (x.toNat <<< s)
  else -Int.ofNat (x.natAbs <<< s)

/-- `shiftInt x s` equals exact multiplication `x * 2^s`. -/
theorem shiftInt_eq (x : Int) (s : Nat) : shiftInt x s = x * ((2 ^ s : Nat) : Int) := by
  unfold shiftInt
  split
  · rename_i hge
    rw [Nat.shiftLeft_eq]
    have hx : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hge
    change ((x.toNat * 2 ^ s : Nat) : Int) = x * ((2 ^ s : Nat) : Int)
    rw [Int.natCast_mul, hx]
  · rename_i hlt
    rw [Nat.shiftLeft_eq]
    have hx : -((x.natAbs : Nat) : Int) = x := by
      cases x with
      | ofNat n => omega
      | negSucc n => rfl
    change -((x.natAbs * 2 ^ s : Nat) : Int) = x * ((2 ^ s : Nat) : Int)
    rw [Int.natCast_mul, ← Int.neg_mul, hx]

/-! #### 4. Balanced Divide-and-Conquer Shift-Packing & Horner Evaluation -/

/-- Exact polynomial evaluation of `f` on `[lo, lo + len)` at `X : Int`:
    `∑_{j=0}^{len-1} f (lo + j) * X^j`. -/
def evalRange (f : Nat → Int) (X : Int) (lo : Nat) : Nat → Int
  | 0 => 0
  | len + 1 => evalRange f X lo len + f (lo + len) * X ^ len

private theorem evalRange_split (f : Nat → Int) (X : Int) (lo m r : Nat) :
    evalRange f X lo (m + r) = evalRange f X lo m + evalRange f X (lo + m) r * X ^ m := by
  induction r with
  | zero => simp [evalRange]
  | succ r' ih =>
    have hmr : m + (r' + 1) = (m + r') + 1 := by omega
    rw [hmr, evalRange, evalRange, ih, Int.add_mul, Int.add_assoc]
    congr 1
    have h1 : lo + (m + r') = (lo + m) + r' := by omega
    have h2 : X ^ (m + r') = X ^ r' * X ^ m := by
      rw [← Int.pow_add, Nat.add_comm]
    rw [h1, h2, Int.mul_assoc]

/-- Balanced divide-and-conquer shift-packing of `arr[lo .. lo + len)` at base `2^bits`. -/
def packIntRange (arr : Array Int) (bits lo len : Nat) : Int :=
  if len = 0 then 0
  else if len = 1 then aCoeff arr lo
  else
    let m := len / 2
    let left := packIntRange arr bits lo m
    let right := packIntRange arr bits (lo + m) (len - m)
    left + shiftInt right (m * bits)
termination_by len

/-- `packIntRange` evaluates `arr[lo .. lo + len)` at `X = 2^bits`. -/
theorem packIntRange_eq (arr : Array Int) (bits lo len : Nat) :
    packIntRange arr bits lo len = evalRange (aCoeff arr) ((2 ^ bits : Nat) : Int) lo len := by
  unfold packIntRange
  split
  · rename_i h0; subst h0; rfl
  · split
    · rename_i _ h1; subst h1; simp [evalRange]
    · rename_i hne0 hne1
      dsimp only
      let m := len / 2
      have hm_lt : m < len := by omega
      have hr_lt : len - m < len := by omega
      rw [packIntRange_eq arr bits lo m,
          packIntRange_eq arr bits (lo + m) (len - m),
          shiftInt_eq]
      have hpow : (((2 ^ (m * bits) : Nat) : Int)) = (((2 ^ bits : Nat) : Int)) ^ m := by
        rw [Nat.mul_comm, Nat.pow_mul]
        simp
      rw [hpow, ← evalRange_split]
      have hsum : m + (len - m) = len := by omega
      rw [hsum]
termination_by len

/-! #### 5. Doubling Repunit (`O(log L)` shifts) -/

/-- Exact geometric sum `∑_{j=0}^{n-1} B^j` over `Nat`. -/
def geomSum (B : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => geomSum B n + B ^ n

private theorem geomSum_split (B m r : Nat) :
    geomSum B (m + r) = geomSum B m + geomSum B r * B ^ m := by
  induction r with
  | zero => simp [geomSum]
  | succ r' ih =>
    have hmr : m + (r' + 1) = (m + r') + 1 := by omega
    rw [hmr, geomSum, geomSum, ih, Nat.add_mul, Nat.add_assoc]
    congr 1
    rw [← Nat.pow_add, Nat.add_comm r' m]

/-- `O(log n)` binary-doubling computation of `∑_{j=0}^{n-1} (2^bits)^j`. -/
def repunit (bits : Nat) (n : Nat) : Nat :=
  if n = 0 then 0
  else if n = 1 then 1
  else
    let m := n / 2
    let r := repunit bits m
    let dbl := r + (r <<< (m * bits))
    if n % 2 = 0 then dbl
    else dbl + (1 <<< ((2 * m) * bits))
termination_by n

/-- `repunit bits n` equals exact `geomSum (2 ^ bits) n`. -/
theorem repunit_eq (bits n : Nat) : repunit bits n = geomSum (2 ^ bits) n := by
  unfold repunit
  split
  · rename_i h0; subst h0; rfl
  · split
    · rename_i _ h1; subst h1; simp [geomSum]
    · rename_i hne0 hne1
      dsimp only
      have hm_lt : n / 2 < n := by omega
      rw [repunit_eq bits (n / 2), Nat.shiftLeft_eq, Nat.shiftLeft_eq]
      have hpow1 : 2 ^ (n / 2 * bits) = (2 ^ bits) ^ (n / 2) := by
        rw [Nat.mul_comm, Nat.pow_mul]
      have hpow2 : 2 ^ (2 * (n / 2) * bits) = (2 ^ bits) ^ (2 * (n / 2)) := by
        rw [Nat.mul_comm, Nat.pow_mul]
      rw [hpow1, hpow2, ← geomSum_split]
      have h2m : n / 2 + n / 2 = 2 * (n / 2) := by omega
      rw [h2m]
      split
      · rename_i hmod
        have hEq : 2 * (n / 2) = n := by omega
        rw [hEq]
      · rename_i hmod
        have hEq : 2 * (n / 2) + 1 = n := by omega
        rw [Nat.one_mul, ← geomSum]
        exact congrArg (geomSum (2 ^ bits)) hEq
termination_by n

/-! #### 6. Balanced Shift-Only Unpacking (`O(L log L)` bit shifts, zero division) -/

/-- Exact base-`B` evaluation of `d : Nat → Nat` on `[lo, lo + len)`. -/
def natEvalRange (d : Nat → Nat) (B lo : Nat) : Nat → Nat
  | 0 => 0
  | len + 1 => natEvalRange d B lo len + d (lo + len) * B ^ len

private theorem natEvalRange_split (d : Nat → Nat) (B lo m r : Nat) :
    natEvalRange d B lo (m + r) = natEvalRange d B lo m + natEvalRange d B (lo + m) r * B ^ m := by
  induction r with
  | zero => simp [natEvalRange]
  | succ r' ih =>
    have hmr : m + (r' + 1) = (m + r') + 1 := by omega
    rw [hmr, natEvalRange, natEvalRange, ih, Nat.add_mul, Nat.add_assoc]
    congr 1
    have h1 : lo + (m + r') = (lo + m) + r' := by omega
    have h2 : B ^ (m + r') = B ^ r' * B ^ m := by rw [← Nat.pow_add, Nat.add_comm]
    rw [h1, h2, Nat.mul_assoc]

private theorem natEvalRange_lt (d : Nat → Nat) (B lo len : Nat)
    (hB : B > 0) (hd : ∀ j, j < len → d (lo + j) < B) :
    natEvalRange d B lo len < B ^ len := by
  induction len with
  | zero => simp [natEvalRange]
  | succ len' ih =>
    rw [natEvalRange]
    have hih := ih (fun j hj => hd j (by omega))
    have hdlast : d (lo + len') ≤ B - 1 := by have := hd len' (by omega); omega
    have hmul : d (lo + len') * B ^ len' ≤ (B - 1) * B ^ len' :=
      Nat.mul_le_mul_right _ hdlast
    have hpow : B ^ (len' + 1) = B ^ len' + (B - 1) * B ^ len' := by
      rw [Nat.pow_succ, Nat.mul_comm (B ^ len') B]
      cases B with
      | zero => omega
      | succ B' =>
        simp only [Nat.add_sub_cancel, Nat.succ_mul]
        omega
    omega

/-- Shift-only balanced divide-and-conquer unpack of base-`2^bits` digits biased by `half`. -/
def unpackNatLoop (bits : Nat) (half : Int) (x : Nat) (len : Nat) (acc : Array Int) : Array Int :=
  if len = 0 then acc
  else if len = 1 then
    acc.push ((x : Int) - half)
  else
    let m := len / 2
    let s := m * bits
    let hi := x >>> s
    let lo := x - (hi <<< s)
    let acc1 := unpackNatLoop bits half lo m acc
    unpackNatLoop bits half hi (len - m) acc1
termination_by len

private theorem unpackNatLoop_size (bits : Nat) (half : Int) (x len : Nat) (acc : Array Int) :
    (unpackNatLoop bits half x len acc).size = acc.size + len := by
  unfold unpackNatLoop
  split
  · rename_i h0; subst h0; simp
  · split
    · rename_i _ h1; subst h1; simp
    · rename_i hne0 hne1
      dsimp only
      have hm_lt : len / 2 < len := by omega
      have hr_lt : len - len / 2 < len := by omega
      rw [unpackNatLoop_size bits half _ (len - len / 2),
          unpackNatLoop_size bits half _ (len / 2)]
      omega
termination_by len

private theorem unpackNatLoop_spec (bits : Nat) (half : Int) (d : Nat → Nat)
    (lo len : Nat) (acc : Array Int)
    (hd : ∀ j, j < len → d (lo + j) < 2 ^ bits) (k : Nat) :
    aCoeff (unpackNatLoop bits half (natEvalRange d (2 ^ bits) lo len) len acc) k =
      if k < acc.size then aCoeff acc k
      else if k < acc.size + len then (d (lo + (k - acc.size)) : Int) - half
      else 0 := by
  unfold unpackNatLoop
  split
  · rename_i h0
    subst h0
    by_cases hk : k < acc.size
    · simp [hk]
    · simp [hk, aCoeff_of_ge (by omega : acc.size ≤ k)]
  · split
    · rename_i _ h1
      subst h1
      simp only [natEvalRange, Nat.zero_add, Nat.pow_zero, Nat.mul_one]
      rw [aCoeff_push]
      by_cases hk : k < acc.size
      · simp [hk]
      · by_cases heq : k = acc.size
        · subst heq; simp
        · have hnot : ¬ (k < acc.size + 1) := by omega
          simp [hk, heq, hnot]
    · rename_i hne0 hne1
      dsimp only
      let m := len / 2
      have hm_lt : m < len := by omega
      have hr_lt : len - m < len := by omega
      have hsum : m + (len - m) = len := by omega
      let B := 2 ^ bits
      have hBpos : B > 0 := Nat.pow_pos (by decide)
      have hlo_lt : natEvalRange d B lo m < B ^ m :=
        natEvalRange_lt d B lo m hBpos (fun j hj => hd j (by omega))
      have hsplit : natEvalRange d B lo len =
          natEvalRange d B lo m + natEvalRange d B (lo + m) (len - m) * B ^ m := by
        simpa [hsum] using natEvalRange_split d B lo m (len - m)
      have hpow : 2 ^ (m * bits) = B ^ m := by
        dsimp only [B]; rw [Nat.mul_comm, Nat.pow_mul]
      have hBm_pos : B ^ m > 0 := Nat.pow_pos hBpos
      have hhi : (natEvalRange d B lo len) >>> (m * bits) = natEvalRange d B (lo + m) (len - m) := by
        rw [Nat.shiftRight_eq_div_pow, hpow, hsplit, Nat.add_mul_div_right _ _ hBm_pos,
            Nat.div_eq_of_lt hlo_lt, Nat.zero_add]
      have hlo : natEvalRange d B lo len -
          ((natEvalRange d B lo len) >>> (m * bits) <<< (m * bits)) = natEvalRange d B lo m := by
        rw [hhi, Nat.shiftLeft_eq, hpow, hsplit, Nat.add_sub_cancel]
      change aCoeff (unpackNatLoop bits half (natEvalRange d B lo len >>> (m * bits)) (len - m)
          (unpackNatLoop bits half
            (natEvalRange d B lo len - (natEvalRange d B lo len >>> (m * bits) <<< (m * bits)))
            m acc)) k = _
      rw [hlo, hhi]
      have ih2 := unpackNatLoop_spec bits half d (lo + m) (len - m)
        (unpackNatLoop bits half (natEvalRange d B lo m) m acc)
        (fun j hj => by
          have : lo + m + j = lo + (m + j) := by omega
          rw [this]; exact hd (m + j) (by omega)) k
      rw [ih2, unpackNatLoop_size]
      have ih1 := unpackNatLoop_spec bits half d lo m acc
        (fun j hj => hd j (by omega)) k
      rw [ih1]
      by_cases hk0 : k < acc.size
      · have hk1 : k < acc.size + m := by omega
        simp [hk0, hk1]
      · by_cases hk1 : k < acc.size + m
        · have hk2 : k < acc.size + len := by omega
          simp [hk0, hk1, hk2]
        · by_cases hk2 : k < acc.size + len
          · have hk2' : k < acc.size + m + (len - m) := by omega
            have hidx : lo + m + (k - (acc.size + m)) = lo + (k - acc.size) := by omega
            simp [hk0, hk1, hk2, hk2', hidx]
          · have hk2' : ¬ (k < acc.size + m + (len - m)) := by omega
            simp [hk0, hk1, hk2, hk2']
termination_by len

/-! #### 7. Polynomial Evaluation Homomorphism & Verified Kronecker Multiplication -/

private theorem evalRange_congr {f g : Nat → Int} (X : Int) (lo len : Nat)
    (h : ∀ j, j < len → f (lo + j) = g (lo + j)) :
    evalRange f X lo len = evalRange g X lo len := by
  induction len with
  | zero => rfl
  | succ len' ih =>
    rw [evalRange, evalRange, ih (fun j hj => h j (by omega)), h len' (by omega)]

private theorem evalRange_add (f g : Nat → Int) (X : Int) (lo len : Nat) :
    evalRange (fun k => f k + g k) X lo len = evalRange f X lo len + evalRange g X lo len := by
  induction len with
  | zero => simp [evalRange]
  | succ len' ih =>
    simp only [evalRange, ih, Int.add_mul]
    omega

private theorem evalRange_zero (X : Int) (lo len : Nat) :
    evalRange (fun _ => 0) X lo len = 0 := by
  induction len with
  | zero => rfl
  | succ len' ih => simp [evalRange, ih]

private theorem evalRange_const (c X : Int) (lo len : Nat) :
    evalRange (fun _ => c) X lo len = c * evalRange (fun _ => 1) X 0 len := by
  induction len with
  | zero => simp [evalRange]
  | succ len' ih =>
    simp only [evalRange, ih, Int.one_mul, Int.mul_add]

private theorem evalRange_ones_natCast (B len : Nat) :
    evalRange (fun _ => (1 : Int)) (B : Int) 0 len = ((geomSum B len : Nat) : Int) := by
  induction len with
  | zero => rfl
  | succ len' ih =>
    simp only [evalRange, geomSum, ih, Int.one_mul, Int.natCast_add, Int.natCast_pow]

private theorem evalRange_natEvalRange (d : Nat → Nat) (B lo len : Nat) :
    evalRange (fun k => (d k : Int)) (B : Int) lo len = ((natEvalRange d B lo len : Nat) : Int) := by
  induction len with
  | zero => rfl
  | succ len' ih =>
    simp only [evalRange, natEvalRange, ih, Int.natCast_add, Int.natCast_mul, Int.natCast_pow]

private theorem evalRange_scale (c : Int) (f : Nat → Int) (X : Int) (lo len : Nat) :
    evalRange (fun k => c * f k) X lo len = c * evalRange f X lo len := by
  induction len with
  | zero => simp [evalRange]
  | succ len' ih =>
    simp only [evalRange, ih, Int.mul_add, Int.mul_assoc]

private theorem evalRange_aScaleAddAt (out b : Array Int) (offset : Nat) (c X : Int) (L : Nat)
    (hsize : offset + b.size ≤ out.size) (hL : offset + b.size ≤ L) :
    evalRange (aCoeff (aScaleAddAt out offset c b)) X 0 L =
      evalRange (aCoeff out) X 0 L + c * evalRange (aCoeff b) X 0 b.size * X ^ offset := by
  rw [evalRange_congr (g := fun j => aCoeff out j + (if j < offset then 0 else c * aCoeff b (j - offset)))
        X 0 L (fun j _ => by simpa using aCoeff_aScaleAddAt out offset c b hsize j),
      evalRange_add]
  congr 1
  have hLsplit : L = offset + (b.size + (L - (offset + b.size))) := by omega
  rw [hLsplit, evalRange_split, evalRange_split]
  have h1 : evalRange (fun k => if k < offset then 0 else c * aCoeff b (k - offset)) X 0 offset = 0 := by
    rw [evalRange_congr (g := fun _ => 0) X 0 offset (fun j hj => by simp [hj]), evalRange_zero]
  have h2 : evalRange (fun k => if k < offset then 0 else c * aCoeff b (k - offset)) X (0 + offset) b.size =
      c * evalRange (aCoeff b) X 0 b.size := by
    rw [← evalRange_scale]
    have hreidx : ∀ n, evalRange (fun k => if k < offset then 0 else c * aCoeff b (k - offset)) X (0 + offset) n =
        evalRange (fun k => c * aCoeff b k) X 0 n := by
      intro n
      induction n with
      | zero => rfl
      | succ n' ih =>
        have hnot : ¬ (offset + n' < offset) := by omega
        have hsub : offset + n' - offset = n' := by omega
        rw [Nat.zero_add] at ih ⊢
        simp only [evalRange, ih, hnot, ↓reduceIte, hsub, Nat.zero_add]
    exact hreidx b.size
  have h3 : evalRange (fun k => if k < offset then 0 else c * aCoeff b (k - offset)) X
      (0 + offset + b.size) (L - (offset + b.size)) = 0 := by
    rw [evalRange_congr (g := fun _ => 0) X (0 + offset + b.size) (L - (offset + b.size)) (fun j _ => by
          have hnot : ¬ (0 + offset + b.size + j < offset) := by omega
          have hge : b.size ≤ 0 + offset + b.size + j - offset := by omega
          simp only [hnot, ↓reduceIte, aCoeff_of_ge hge, Int.mul_zero]),
        evalRange_zero]
  rw [h1, h2, h3]
  simp

private theorem evalRange_aMulSchoolbookLoop (a b : Array Int) (i : Nat) (out : Array Int) (X : Int)
    (L : Nat) (hsize : a.size + b.size - 1 ≤ out.size) (hL : a.size + b.size - 1 ≤ L)
    (hb : b.size > 0) :
    evalRange (aCoeff (aMulSchoolbookLoop a b i out)) X 0 L =
      evalRange (aCoeff out) X 0 L +
        evalRange (aCoeff a) X i (a.size - i) * X ^ i * evalRange (aCoeff b) X 0 b.size := by
  unfold aMulSchoolbookLoop
  split
  · rename_i hi
    have hsc_size : i + b.size ≤ out.size := by omega
    have hsc_L : i + b.size ≤ L := by omega
    have hout'_size : a.size + b.size - 1 ≤ (aScaleAddAt out i a[i] b).size := by
      rw [aScaleAddAt_size]; exact hsize
    rw [evalRange_aMulSchoolbookLoop a b (i + 1) (aScaleAddAt out i a[i] b) X L hout'_size hL hb,
        evalRange_aScaleAddAt out b i a[i] X L hsc_size hsc_L]
    have hsplit_a : evalRange (aCoeff a) X i (a.size - i) =
        a[i] + evalRange (aCoeff a) X (i + 1) (a.size - (i + 1)) * X := by
      have hlen : a.size - i = 1 + (a.size - (i + 1)) := by omega
      rw [hlen, evalRange_split]
      simp [evalRange, aCoeff, hi, Int.pow_one]
    rw [hsplit_a, Int.add_mul, Int.add_mul]
    have hpow : X ^ (i + 1) = X * X ^ i := by
      rw [Int.pow_succ, Int.mul_comm]
    rw [hpow]
    have hterm1 : a[i] * evalRange (aCoeff b) X 0 b.size * X ^ i =
        a[i] * X ^ i * evalRange (aCoeff b) X 0 b.size := by
      rw [Int.mul_assoc, Int.mul_comm (evalRange (aCoeff b) X 0 b.size) (X ^ i), ← Int.mul_assoc]
    have hterm2 : evalRange (aCoeff a) X (i + 1) (a.size - (i + 1)) * (X * X ^ i) *
          evalRange (aCoeff b) X 0 b.size =
        evalRange (aCoeff a) X (i + 1) (a.size - (i + 1)) * X * X ^ i *
          evalRange (aCoeff b) X 0 b.size := by
      rw [← Int.mul_assoc (evalRange (aCoeff a) X (i + 1) (a.size - (i + 1))) X (X ^ i)]
    rw [hterm1, hterm2, Int.add_assoc]
  · rename_i hge
    have h0 : a.size - i = 0 := by omega
    simp [h0, evalRange]
termination_by a.size - i

/-- **Kronecker Polynomial Evaluation Homomorphism**:
    Evaluating `aMulSchoolbookInt a b` at any integer `X` equals `(eval a X) * (eval b X)`. -/
theorem evalRange_aMulSchoolbookInt {a b : Array Int} (ha : a.size > 0) (hb : b.size > 0) (X : Int) :
    evalRange (aCoeff (aMulSchoolbookInt a b)) X 0 (a.size + b.size - 1) =
      evalRange (aCoeff a) X 0 a.size * evalRange (aCoeff b) X 0 b.size := by
  unfold aMulSchoolbookInt
  have hne : (a.isEmpty || b.isEmpty) = false := by
    cases h : (a.isEmpty || b.isEmpty)
    · rfl
    · simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero] at h; omega
  simp only [hne, Bool.false_eq_true, ↓reduceIte]
  rw [evalRange_aMulSchoolbookLoop a b 0 (Array.replicate (a.size + b.size - 1) 0) X
        (a.size + b.size - 1) (by simp) (Nat.le_refl _) hb]
  have hz : evalRange (aCoeff (Array.replicate (a.size + b.size - 1) 0)) X 0 (a.size + b.size - 1) = 0 := by
    rw [evalRange_congr (g := fun _ => 0) X 0 (a.size + b.size - 1) (fun j _ => aCoeff_replicate_zero _ _), evalRange_zero]
  simp [hz]

private theorem lt_two_pow_succ_log2 (n : Nat) : n < 2 ^ (n.log2 + 1) := by
  by_cases h0 : n = 0
  · subst h0; decide
  · exact (Nat.log2_lt h0).mp (Nat.lt_succ_self n.log2)

/-- **Verified Kronecker Substitution Multiplication (`Array Int × Array Int → Array Int`)**:
    Packs both polynomials at base `2^bits`, performs ONE GMP `Int.mul` (hitting GMP Toom/FFT),
    adds a doubling-computed bias repunit, and unpacks via shift-only divide-and-conquer. -/
def aMulKronecker (a b : Array Int) : Array Int :=
  if a.isEmpty || b.isEmpty then #[]
  else
    let ma := maxAbs a
    let mb := maxAbs b
    if ma == 0 || mb == 0 then #[]
    else
      let outLen := a.size + b.size - 1
      let bound := min a.size b.size * ma * mb
      let halfBits := bound.log2 + 1
      let bits := halfBits + 1
      let half : Int := Int.ofNat (1 <<< halfBits)
      let pa := packIntRange a bits 0 a.size
      let pb := packIntRange b bits 0 b.size
      let prod := pa * pb
      let bias : Int := Int.ofNat ((repunit bits outLen) <<< halfBits)
      let shifted := (prod + bias).toNat
      unpackNatLoop bits half shifted outLen (Array.mkEmpty outLen)

/-- **Kronecker Equivalence Theorem (zero `sorry`)**:
    `aMulKronecker a b` produces the exact same integer coefficient as `aMulSchoolbookInt a b`
    at every index `k : Nat`. -/
theorem aCoeff_aMulKronecker (a b : Array Int) (k : Nat) :
    aCoeff (aMulKronecker a b) k = aCoeff (aMulSchoolbookInt a b) k := by
  unfold aMulKronecker
  split
  · rename_i hemp
    unfold aMulSchoolbookInt
    simp [hemp]
  · rename_i hne
    simp only [Bool.or_eq_true, Array.isEmpty_iff_size_eq_zero, not_or] at hne
    have hapos : a.size > 0 := Nat.pos_of_ne_zero hne.1
    have hbpos : b.size > 0 := Nat.pos_of_ne_zero hne.2
    dsimp only
    split
    · rename_i hzero
      simp only [Bool.or_eq_true, beq_iff_eq] at hzero
      have hbd := natAbs_aMulSchoolbookInt_le a b k
      rcases hzero with hma | hmb
      · rw [hma] at hbd
        have hz : aCoeff (aMulSchoolbookInt a b) k = 0 := by simpa using hbd
        rw [hz]; rfl
      · rw [hmb] at hbd
        have hz : aCoeff (aMulSchoolbookInt a b) k = 0 := by simpa using hbd
        rw [hz]; rfl
    · rename_i hnz
      let outLen := a.size + b.size - 1
      let bound := min a.size b.size * maxAbs a * maxAbs b
      let halfBits := bound.log2 + 1
      let bits := halfBits + 1
      have hhalf_gt : bound < 2 ^ halfBits := lt_two_pow_succ_log2 bound
      have hhalf_eq : Int.ofNat (1 <<< halfBits) = ((2 ^ halfBits : Nat) : Int) := by
        rw [Nat.shiftLeft_eq, Nat.one_mul]; rfl
      have hbits_pow : 2 ^ bits = 2 ^ halfBits + 2 ^ halfBits := by
        dsimp only [bits]; rw [Nat.pow_succ]; omega
      let c : Nat → Int := aCoeff (aMulSchoolbookInt a b)
      let d : Nat → Nat := fun j => (c j + ((2 ^ halfBits : Nat) : Int)).toNat
      have hd_lt : ∀ j, j < outLen → d j < 2 ^ bits := by
        intro j _
        have hcj : (c j).natAbs ≤ bound := natAbs_aMulSchoolbookInt_le a b j
        dsimp only [d]
        omega
      have hd_cast : ∀ j, ((d j : Nat) : Int) = c j + ((2 ^ halfBits : Nat) : Int) := by
        intro j
        have hcj : (c j).natAbs ≤ bound := natAbs_aMulSchoolbookInt_le a b j
        dsimp only [d]
        omega
      have hbias : Int.ofNat ((repunit bits outLen) <<< halfBits) =
          ((2 ^ halfBits : Nat) : Int) * ((geomSum (2 ^ bits) outLen : Nat) : Int) := by
        rw [repunit_eq, Nat.shiftLeft_eq, Nat.mul_comm]
        exact Int.natCast_mul _ _
      have hpack : packIntRange a bits 0 a.size * packIntRange b bits 0 b.size +
            Int.ofNat ((repunit bits outLen) <<< halfBits) =
          ((natEvalRange d (2 ^ bits) 0 outLen : Nat) : Int) := by
        rw [packIntRange_eq, packIntRange_eq, ← evalRange_aMulSchoolbookInt hapos hbpos,
            hbias, ← evalRange_ones_natCast, ← evalRange_const, ← evalRange_add]
        rw [evalRange_congr (g := fun j => ((d j : Nat) : Int)) ((2 ^ bits : Nat) : Int) 0 outLen
              (fun j _ => (hd_cast (0 + j)).symm)]
        exact evalRange_natEvalRange d (2 ^ bits) 0 outLen
      have htoNat : (packIntRange a bits 0 a.size * packIntRange b bits 0 b.size +
            Int.ofNat ((repunit bits outLen) <<< halfBits)).toNat =
          natEvalRange d (2 ^ bits) 0 outLen := by
        rw [hpack]; exact Int.toNat_natCast _
      change aCoeff (unpackNatLoop bits (Int.ofNat (1 <<< halfBits))
          (packIntRange a bits 0 a.size * packIntRange b bits 0 b.size +
            Int.ofNat ((repunit bits outLen) <<< halfBits)).toNat
          outLen (Array.mkEmpty outLen)) k = c k
      rw [hhalf_eq, htoNat, unpackNatLoop_spec bits ((2 ^ halfBits : Nat) : Int) d 0 outLen
            (Array.mkEmpty outLen) (fun j hj => by simpa using hd_lt j hj) k]
      have hsz0 : (Array.mkEmpty outLen : Array Int).size = 0 := rfl
      simp only [hsz0, Nat.not_lt_zero, ↓reduceIte, Nat.zero_add, Nat.sub_zero]
      by_cases hk : k < outLen
      · simp only [hk, ↓reduceIte, hd_cast k]
        omega
      · simp only [hk, ↓reduceIte]
        have hsz : (aMulSchoolbookInt a b).size = outLen := aMulSchoolbookInt_size hapos hbpos
        exact (aCoeff_of_ge (by omega : (aMulSchoolbookInt a b).size ≤ k)).symm

/-- Unified verified `Array Int` multiplier: dispatches to GMP Kronecker substitution strictly
    in the multi-limb GMP regime (`min ≥ 16` and `maxAbs ≥ 2^18`, where scalar `Int.mul`
    allocates GMP limbs), and keeps unboxed tagged-`Int` Karatsuba/schoolbook for small-int
    dense products (`mul_dense`). -/
def aMulIntFast (cutoff : Nat := 32) (a b : Array Int) : Array Int :=
  if min a.size b.size ≥ 16 && (maxAbs a ≥ (1 <<< 18) || maxAbs b ≥ (1 <<< 18)) then
    aMulKronecker a b
  else
    aMulKaratsubaInt cutoff a b

/-- `aMulIntFast` matches `dMulSchoolbook` over `Rat` at every index `k`. -/
theorem aCoeff_aMulIntFast (cutoff : Nat) (a b : Array Int) (k : Nat) :
    Rat.ofInt (aCoeff (aMulIntFast cutoff a b) k) =
      dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) (b.toList.map Rat.ofInt)) k := by
  unfold aMulIntFast
  split
  · rw [aCoeff_aMulKronecker]; exact aCoeff_aMulSchoolbookInt a b k
  · exact aCoeff_aMulKaratsubaInt cutoff a b k

/-- Verified top-level `TermList` multiplication combining Kronecker GMP, unboxed `Array Int`
    Karatsuba/schoolbook, rational Karatsuba, and contiguous-`Array` sparse `mulTree`. -/
def mulFastKronecker (xs ys : TermList) (cutoff : Nat := 16) : TermList :=
  if xs.length ≥ 4 && ys.length ≥ 4 then
    match xs, ys, guessGridStep xs ys with
    | (ex0, _) :: _, (ey0, _) :: _, some step =>
      if step > 0 then
        let fuel := 2 * (xs.length + ys.length) + 16
        match extractIntGridClassified ex0 step fuel xs with
        | .ok ia =>
          match extractIntGridClassified ey0 step fuel ys with
          | .ok ib =>
            fromIntGrid (TermList.ratAddFast ex0 ey0) step (aMulIntFast 32 ia ib)
          | .nonInt =>
            if xs.length ≥ cutoff && ys.length ≥ cutoff then
              match extractGridAux ex0 step 0 fuel xs, extractGridAux ey0 step 0 fuel ys with
              | some da, some db =>
                fromGrid (TermList.ratAddFast ex0 ey0) step (dMulKaratsuba cutoff da db)
              | _, _ => TermList.mulTree xs ys
            else TermList.mulTree xs ys
          | .offGrid => TermList.mulTree xs ys
        | .nonInt =>
          if xs.length ≥ cutoff && ys.length ≥ cutoff then
            match extractGridAux ex0 step 0 fuel xs, extractGridAux ey0 step 0 fuel ys with
            | some da, some db =>
              fromGrid (TermList.ratAddFast ex0 ey0) step (dMulKaratsuba cutoff da db)
            | _, _ => TermList.mulTree xs ys
          else TermList.mulTree xs ys
        | .offGrid => TermList.mulTree xs ys
      else TermList.mulTree xs ys
    | _, _, _ => TermList.mulTree xs ys
  else
    TermList.mulTree xs ys

/-- `mulFastKronecker` preserves canonical well-formedness. -/
theorem mulFastKronecker_wf {xs ys : TermList} (hxs : TermList.WF xs) (hys : TermList.WF ys)
    (cutoff : Nat := 16) : TermList.WF (mulFastKronecker xs ys cutoff) := by
  unfold mulFastKronecker
  split
  · split
    · split
      · rename_i hstep
        dsimp only
        split
        · split
          · exact fromIntGrid_wf hstep _
          · split
            · split
              · exact fromGrid_wf hstep _
              · exact TermList.mulTree_wf hxs hys
            · exact TermList.mulTree_wf hxs hys
          · exact TermList.mulTree_wf hxs hys
        · split
          · split
            · exact fromGrid_wf hstep _
            · exact TermList.mulTree_wf hxs hys
          · exact TermList.mulTree_wf hxs hys
        · exact TermList.mulTree_wf hxs hys
      · exact TermList.mulTree_wf hxs hys
    · exact TermList.mulTree_wf hxs hys
  · exact TermList.mulTree_wf hxs hys

/-- **Unified Kronecker+Karatsuba+Sparse Multiplication Equivalence Theorem (zero `sorry`)**. -/
theorem coeffOf_mulFastKronecker (xs ys : TermList) (e : Rat) (cutoff : Nat := 16) :
    TermList.coeffOf (mulFastKronecker xs ys cutoff) e =
      TermList.coeffOf (TermList.mulNaiveTerms xs ys) e := by
  unfold mulFastKronecker
  split
  · split
    · split
      · rename_i hstep
        dsimp only
        split
        · rename_i ia hx_ok
          have hx := extractIntGridClassified_ok hx_ok
          split
          · rename_i ib hy_ok
            have hy := extractIntGridClassified_ok hy_ok
            rw [TermList.ratAddFast_eq, fromIntGrid_eq_fromGrid]
            unfold fromGrid
            have hcongr : ∀ k, dCoeff ((aMulIntFast 32 ia ib).toList.map Rat.ofInt) k =
                dCoeff (dMulSchoolbook (ia.toList.map Rat.ofInt) (ib.toList.map Rat.ofInt)) k := fun k => by
              have hmap : dCoeff ((aMulIntFast 32 ia ib).toList.map Rat.ofInt) k =
                  Rat.ofInt (aCoeff (aMulIntFast 32 ia ib) k) := by
                unfold dCoeff aCoeff
                rw [List.getD_eq_getElem?_getD]
                split
                · rename_i h
                  have h1 : k < ((aMulIntFast 32 ia ib).toList.map Rat.ofInt).length := by simpa using h
                  rw [List.getElem?_eq_getElem h1]; simp
                · rename_i h
                  have h1 : ((aMulIntFast 32 ia ib).toList.map Rat.ofInt).length ≤ k := by simp at h ⊢; omega
                  rw [List.getElem?_eq_none h1]
                  apply Rat.ext <;> simp [Rat.ofInt]
              rw [hmap]
              exact aCoeff_aMulIntFast 32 ia ib k
            rw [coeffOf_fromGridAux_congr 0 hcongr e, coeffOf_fromGridAux_dMulSchoolbook]
            rw [TermList.coeffOf_mulNaiveTerms_congr_left (fun e' => by simpa [fromGrid] using extractIntGrid_sound hx e'),
                TermList.coeffOf_mulNaiveTerms_congr_right (fun e' => by simpa [fromGrid] using extractIntGrid_sound hy e')]
          · split
            · split
              · rename_i da db hx' hy'
                rw [TermList.ratAddFast_eq]
                exact coeffOf_fromGrid_dMulKaratsuba hstep cutoff hx' hy' e
              · exact TermList.coeffOf_mulTree _ _ e
            · exact TermList.coeffOf_mulTree _ _ e
          · exact TermList.coeffOf_mulTree _ _ e
        · split
          · split
            · rename_i da db hx' hy'
              rw [TermList.ratAddFast_eq]
              exact coeffOf_fromGrid_dMulKaratsuba hstep cutoff hx' hy' e
            · exact TermList.coeffOf_mulTree _ _ e
          · exact TermList.coeffOf_mulTree _ _ e
        · exact TermList.coeffOf_mulTree _ _ e
      · exact TermList.coeffOf_mulTree _ _ e
    · exact TermList.coeffOf_mulTree _ _ e
  · exact TermList.coeffOf_mulTree _ _ e

end Kronecker
end LeanInf
