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

private theorem aScaleAddAt_size (out : Array Int) (offset : Nat) (c : Int) (b : Array Int)
    (hsize : offset + b.size ≤ out.size) :
    (aScaleAddAt out offset c b hsize).size = out.size := by
  unfold aScaleAddAt
  split
  · rfl
  · exact aScaleAddAtLoop_size offset c b 0 out hsize

private theorem aMulSchoolbookLoop_size (a b : Array Int) (i : Nat) (out : Array Int)
    (hsize : a.size + b.size - 1 ≤ out.size) :
    (aMulSchoolbookLoop a b i out hsize).size = out.size := by
  unfold aMulSchoolbookLoop
  split
  · dsimp only
    rw [aMulSchoolbookLoop_size, aScaleAddAt_size]
  · rfl
termination_by a.size - i

private theorem aMulSchoolbookLoop_natAbs_le (a b : Array Int) (i : Nat) (out : Array Int)
    (hsize : a.size + b.size - 1 ≤ out.size) (hb : b.size > 0) (k : Nat) :
    (aCoeff (aMulSchoolbookLoop a b i out hsize) k).natAbs ≤
      (aCoeff out k).natAbs + activeInRange b.size k i a.size * (maxAbs a * maxAbs b) := by
  unfold aMulSchoolbookLoop activeInRange
  split
  · rename_i hi
    dsimp only
    have hsc_size : i + b.size ≤ out.size := by omega
    have hout'_size : a.size + b.size - 1 ≤ (aScaleAddAt out i a[i] b hsc_size).size := by
      rw [aScaleAddAt_size]; exact hsize
    have ih := aMulSchoolbookLoop_natAbs_le a b (i + 1) (aScaleAddAt out i a[i] b hsc_size) hout'_size hb k
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
    evalRange (aCoeff (aScaleAddAt out offset c b hsize)) X 0 L =
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
    evalRange (aCoeff (aMulSchoolbookLoop a b i out hsize)) X 0 L =
      evalRange (aCoeff out) X 0 L +
        evalRange (aCoeff a) X i (a.size - i) * X ^ i * evalRange (aCoeff b) X 0 b.size := by
  unfold aMulSchoolbookLoop
  split
  · rename_i hi
    dsimp only
    have hsc_size : i + b.size ≤ out.size := by omega
    have hsc_L : i + b.size ≤ L := by omega
    have hout'_size : a.size + b.size - 1 ≤ (aScaleAddAt out i a[i] b hsc_size).size := by
      rw [aScaleAddAt_size]; exact hsize
    rw [evalRange_aMulSchoolbookLoop a b (i + 1) (aScaleAddAt out i a[i] b hsc_size) X L hout'_size hL hb,
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

/-- Core Kronecker multiplication given precomputed `bound = min a.size b.size * maxAbs a * maxAbs b`
    (eliminating duplicate `maxAbs` scans when called from `aMulIntFast`). -/
@[inline] def aMulKroneckerCore (a b : Array Int) (bound : Nat) : Array Int :=
  let outLen := a.size + b.size - 1
  let halfBits := bound.log2 + 1
  let bits := halfBits + 1
  let half : Int := Int.ofNat (1 <<< halfBits)
  let pa := packIntRange a bits 0 a.size
  let pb := packIntRange b bits 0 b.size
  let prod := pa * pb
  let bias : Int := Int.ofNat ((repunit bits outLen) <<< halfBits)
  let shifted := (prod + bias).toNat
  unpackNatLoop bits half shifted outLen (Array.mkEmpty outLen)

/-- **Verified Kronecker Substitution Multiplication (`Array Int × Array Int → Array Int`)**:
    Packs both polynomials at base `2^bits`, performs ONE GMP `Int.mul` (hitting GMP Toom/FFT),
    adds a doubling-computed bias repunit, and unpacks via shift-only divide-and-conquer. -/
def aMulKronecker (a b : Array Int) : Array Int :=
  if a.isEmpty || b.isEmpty then #[]
  else
    let ma := maxAbs a
    let mb := maxAbs b
    if ma == 0 || mb == 0 then #[]
    else aMulKroneckerCore a b (min a.size b.size * ma * mb)

private theorem aCoeff_aMulKroneckerCore (a b : Array Int) (hapos : a.size > 0) (hbpos : b.size > 0)
    (k : Nat) :
    aCoeff (aMulKroneckerCore a b (min a.size b.size * maxAbs a * maxAbs b)) k =
      aCoeff (aMulSchoolbookInt a b) k := by
  unfold aMulKroneckerCore
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
    · exact aCoeff_aMulKroneckerCore a b hapos hbpos k

/-- Unified verified `Array Int` multiplier: computes `bound = min(|a|, |b|) * max|a| * max|b|`
    once and dispatches to GMP Kronecker substitution either at the `LEAN_MAX_SMALL_INT`
    (`2^31 - 1`, `lean.h:1570`) product-overflow cliff (`min ≥ 24 && bound ≥ 2^30`) or at the
    asymptotic small-int crossover (`min ≥ 1024`), keeping unboxed Karatsuba/schoolbook below. -/
def aMulIntFast (cutoff : Nat := 32) (a b : Array Int) : Array Int :=
  if min a.size b.size ≥ 24 then
    let ma := maxAbs a
    let mb := maxAbs b
    if ma == 0 || mb == 0 then #[]
    else
      let bound := min a.size b.size * ma * mb
      if bound ≥ (1 <<< 30) || min a.size b.size ≥ 1024 then
        aMulKroneckerCore a b bound
      else
        aMulKaratsubaInt cutoff a b
  else
    aMulKaratsubaInt cutoff a b

/-- `aMulIntFast` matches `dMulSchoolbook` over `Rat` at every index `k`. -/
theorem aCoeff_aMulIntFast (cutoff : Nat) (a b : Array Int) (k : Nat) :
    Rat.ofInt (aCoeff (aMulIntFast cutoff a b) k) =
      dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) (b.toList.map Rat.ofInt)) k := by
  unfold aMulIntFast
  split
  · rename_i hmin
    have hapos : a.size > 0 := by omega
    have hbpos : b.size > 0 := by omega
    dsimp only
    split
    · rename_i hzero
      simp only [Bool.or_eq_true, beq_iff_eq] at hzero
      have hbd := natAbs_aMulSchoolbookInt_le a b k
      have hz : aCoeff (aMulSchoolbookInt a b) k = 0 := by
        rcases hzero with hma | hmb
        · rw [hma] at hbd; simpa using hbd
        · rw [hmb] at hbd; simpa using hbd
      rw [← aCoeff_aMulSchoolbookInt a b k, hz]
      rfl
    · split
      · rw [aCoeff_aMulKroneckerCore a b hapos hbpos k]
        exact aCoeff_aMulSchoolbookInt a b k
      · exact aCoeff_aMulKaratsubaInt cutoff a b k
  · exact aCoeff_aMulKaratsubaInt cutoff a b k

/-- Single-pack Kronecker squaring kernel: packs `a` ONCE into `pa` and computes `pa * pa`
    (cutting packing in half and enabling GMP's pointer-equality `mpn_sqr` fast path).
    Definitionally equal (`rfl`) to `aMulKroneckerCore a a bound`. -/
@[inline] def aSqrKroneckerCore (a : Array Int) (bound : Nat) : Array Int :=
  let outLen := a.size + a.size - 1
  let halfBits := bound.log2 + 1
  let bits := halfBits + 1
  let half : Int := Int.ofNat (1 <<< halfBits)
  let pa := packIntRange a bits 0 a.size
  let prod := pa * pa
  let bias : Int := Int.ofNat ((repunit bits outLen) <<< halfBits)
  let shifted := (prod + bias).toNat
  unpackNatLoop bits half shifted outLen (Array.mkEmpty outLen)

private theorem aSqrKroneckerCore_eq (a : Array Int) (bound : Nat) :
    aSqrKroneckerCore a bound = aMulKroneckerCore a a bound := rfl

/-- Unified verified `Array Int` squarer: uses single-pack GMP `aSqrKroneckerCore` above the
    `LEAN_MAX_SMALL_INT` product-overflow cliff (`a.size ≥ 24 && a.size * ma * ma ≥ 2^30`) or
    at the small-int asymptotic crossover (`a.size ≥ 1024`), and single-extract / half-work
    `aSqrKaratsubaInt` below. -/
def aSqrIntFast (cutoff : Nat := 32) (a : Array Int) : Array Int :=
  if a.size ≥ 24 then
    let ma := maxAbs a
    if ma == 0 then #[]
    else
      let bound := a.size * ma * ma
      if bound ≥ (1 <<< 30) || a.size ≥ 1024 then
        aSqrKroneckerCore a bound
      else
        aSqrKaratsubaInt cutoff a
  else
    aSqrKaratsubaInt cutoff a

/-- `aSqrIntFast` matches `dMulSchoolbook a a` over `Rat` at every index `k`. -/
theorem aCoeff_aSqrIntFast (cutoff : Nat) (a : Array Int) (k : Nat) :
    Rat.ofInt (aCoeff (aSqrIntFast cutoff a) k) =
      dCoeff (dMulSchoolbook (a.toList.map Rat.ofInt) (a.toList.map Rat.ofInt)) k := by
  unfold aSqrIntFast
  split
  · rename_i hmin
    have hapos : a.size > 0 := by omega
    dsimp only
    split
    · rename_i hzero
      have hma : maxAbs a = 0 := eq_of_beq hzero
      have hbd := natAbs_aMulSchoolbookInt_le a a k
      rw [hma] at hbd
      have hz : aCoeff (aMulSchoolbookInt a a) k = 0 := by simpa using hbd
      rw [← aCoeff_aMulSchoolbookInt a a k, hz]
      rfl
    · split
      · have hmin_self : a.size = min a.size a.size := (Nat.min_self a.size).symm
        rw [aSqrKroneckerCore_eq, hmin_self, aCoeff_aMulKroneckerCore a a hapos hapos k]
        exact aCoeff_aMulSchoolbookInt a a k
      · exact aCoeff_aSqrKaratsubaInt cutoff a k
  · exact aCoeff_aSqrKaratsubaInt cutoff a k

/-- Verified top-level `TermList` multiplication combining Kronecker GMP, unboxed `Array Int`
    Karatsuba/schoolbook, rational Karatsuba, and contiguous-`Array` sparse `mulTree`. -/
private theorem dCoeff_map_mkRat (arr : Array Int) (dc : Nat) (k : Nat) :
    dCoeff (arr.toList.map (fun c => mkRat c dc)) k = mkRat (aCoeff arr k) dc := by
  unfold dCoeff aCoeff
  rw [List.getD_eq_getElem?_getD]
  split
  · rename_i h
    have h1 : k < (arr.toList.map (fun c => mkRat c dc)).length := by simpa using h
    rw [List.getElem?_eq_getElem h1]; simp
  · rename_i h
    have h1 : (arr.toList.map (fun c => mkRat c dc)).length ≤ k := by simp at h ⊢; omega
    rw [List.getElem?_eq_none h1]
    simp

private theorem map_mkRat_eq_dScale (arr : Array Int) (dc : Nat) :
    arr.toList.map (fun c => mkRat c dc) = dScale (mkRat 1 dc) (arr.toList.map Rat.ofInt) := by
  unfold dScale
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply, TermList.ratMulFast_eq, ← TermList.mkRat_one c, Rat.mkRat_mul_mkRat,
    Int.one_mul, Nat.mul_one]

/-- Coefficient specification bridging scaled `aMulIntFast` to `mulNaiveTerms`. -/
theorem coeffOf_fromScaledIntGrid_aMulIntFast {ex0 ey0 step : Rat} {dcx dcy : Nat}
    (hdcx : dcx ≠ 0) (hdcy : dcy ≠ 0) {xs ys : TermList} {ia ib : Array Int}
    (hx : ∀ e, TermList.coeffOf (fromGrid ex0 step (ia.toList.map (fun c => mkRat c dcx))) e =
      TermList.coeffOf xs e)
    (hy : ∀ e, TermList.coeffOf (fromGrid ey0 step (ib.toList.map (fun c => mkRat c dcy))) e =
      TermList.coeffOf ys e) (e : Rat) :
    TermList.coeffOf
        (fromScaledIntGrid (TermList.ratAddFast ex0 ey0) step (dcx * dcy) (aMulIntFast 32 ia ib)) e =
      TermList.coeffOf (TermList.mulNaiveTerms xs ys) e := by
  have hdcp : dcx * dcy ≠ 0 := Nat.mul_ne_zero hdcx hdcy
  rw [TermList.ratAddFast_eq, fromScaledIntGrid_eq_fromGrid _ _ hdcp]
  unfold fromGrid
  have hcongr : ∀ k,
      dCoeff ((aMulIntFast 32 ia ib).toList.map (fun c => mkRat c (dcx * dcy))) k =
      dCoeff (dMulSchoolbook (ia.toList.map (fun c => mkRat c dcx))
                             (ib.toList.map (fun c => mkRat c dcy))) k := by
    intro k
    rw [dCoeff_map_mkRat, map_mkRat_eq_dScale ia dcx, map_mkRat_eq_dScale ib dcy,
        dCoeff_dMulSchoolbook_scale_left, dCoeff_dMulSchoolbook_scale_right,
        ← aCoeff_aMulIntFast 32 ia ib k, ← TermList.mkRat_one (aCoeff (aMulIntFast 32 ia ib) k),
        ← Rat.mul_assoc, Rat.mkRat_mul_mkRat, Rat.mkRat_mul_mkRat]
    simp
  rw [coeffOf_fromGridAux_congr 0 hcongr e, coeffOf_fromGridAux_dMulSchoolbook]
  rw [TermList.coeffOf_mulNaiveTerms_congr_left (fun e' => by simpa [fromGrid] using hx e'),
      TermList.coeffOf_mulNaiveTerms_congr_right (fun e' => by simpa [fromGrid] using hy e')]

/-- Verified rational dense multiplication via bounded-LCM coefficient denominator clearing
    (`dcx, dcy ≤ 2^128`), dispatching directly into `aMulIntFast 32` (unboxed `Array Int`
    Karatsuba + multi-limb Kronecker GMP) and normalizing once during backwards reconstruction. -/
def mulRationalDense (ex0 ey0 step : Rat) (fuel cutoff : Nat) (xs ys : TermList)
    (oa : Option (Array Int) := none) : TermList :=
  let maxRatDen : Nat := 1 <<< 128
  match oa with
  | some ia =>
    let dcy := TermList.scanCoeffLcm maxRatDen ys 1
    if dcy != 0 then
      match extractScaledIntGrid ey0 step dcy fuel ys with
      | some ib =>
        fromScaledIntGrid (TermList.ratAddFast ex0 ey0) step dcy (aMulIntFast 32 ia ib)
      | none => TermList.mulTree xs ys
    else if xs.length ≥ cutoff && ys.length ≥ cutoff then
      match extractGridAux ex0 step 0 fuel xs, extractGridAux ey0 step 0 fuel ys with
      | some da, some db =>
        fromGrid (TermList.ratAddFast ex0 ey0) step (dMulKaratsuba cutoff da db)
      | _, _ => TermList.mulTree xs ys
    else TermList.mulTree xs ys
  | none =>
    let dcx := TermList.scanCoeffLcm maxRatDen xs 1
    let dcy := TermList.scanCoeffLcm maxRatDen ys 1
    if dcx != 0 && dcy != 0 then
      match extractScaledIntGrid ex0 step dcx fuel xs with
      | some ia =>
        match extractScaledIntGrid ey0 step dcy fuel ys with
        | some ib =>
          fromScaledIntGrid (TermList.ratAddFast ex0 ey0) step (dcx * dcy) (aMulIntFast 32 ia ib)
        | none => TermList.mulTree xs ys
      | none => TermList.mulTree xs ys
    else if xs.length ≥ cutoff && ys.length ≥ cutoff then
      match extractGridAux ex0 step 0 fuel xs, extractGridAux ey0 step 0 fuel ys with
      | some da, some db =>
        fromGrid (TermList.ratAddFast ex0 ey0) step (dMulKaratsuba cutoff da db)
      | _, _ => TermList.mulTree xs ys
    else TermList.mulTree xs ys

private theorem mulRationalDense_wf {ex0 ey0 step : Rat} (hstep : step > 0) (fuel cutoff : Nat)
    {xs ys : TermList} (hxs : TermList.WF xs) (hys : TermList.WF ys) (oa : Option (Array Int)) :
    TermList.WF (mulRationalDense ex0 ey0 step fuel cutoff xs ys oa) := by
  unfold mulRationalDense
  dsimp only
  cases oa with
  | some ia =>
    dsimp only
    split
    · rename_i hdcy
      have hdcy' : TermList.scanCoeffLcm (1 <<< 128) ys 1 ≠ 0 := by simpa using hdcy
      split
      · exact fromScaledIntGrid_wf hstep hdcy' _
      · exact TermList.mulTree_wf hxs hys
    · split
      · split
        · exact fromGrid_wf hstep _
        · exact TermList.mulTree_wf hxs hys
      · exact TermList.mulTree_wf hxs hys
  | none =>
    dsimp only
    split
    · rename_i hdc
      simp only [Bool.and_eq_true, bne_iff_ne] at hdc
      have hdcp : TermList.scanCoeffLcm (1 <<< 128) xs 1 *
          TermList.scanCoeffLcm (1 <<< 128) ys 1 ≠ 0 := Nat.mul_ne_zero hdc.1 hdc.2
      split
      · split
        · exact fromScaledIntGrid_wf hstep hdcp _
        · exact TermList.mulTree_wf hxs hys
      · exact TermList.mulTree_wf hxs hys
    · split
      · split
        · exact fromGrid_wf hstep _
        · exact TermList.mulTree_wf hxs hys
      · exact TermList.mulTree_wf hxs hys

private theorem coeffOf_mulRationalDense {ex0 ey0 step : Rat} (hstep : step > 0)
    (fuel cutoff : Nat) (xs ys : TermList) (oa : Option (Array Int))
    (hoa : ∀ ia, oa = some ia → extractIntGrid ex0 step fuel xs = some ia) (e : Rat) :
    TermList.coeffOf (mulRationalDense ex0 ey0 step fuel cutoff xs ys oa) e =
      TermList.coeffOf (TermList.mulNaiveTerms xs ys) e := by
  unfold mulRationalDense
  dsimp only
  cases oa with
  | some ia =>
    dsimp only
    split
    · rename_i hdcy
      have hdcy' : TermList.scanCoeffLcm (1 <<< 128) ys 1 ≠ 0 := by simpa using hdcy
      have ⟨_, hys_cdvd⟩ := TermList.scanCoeffLcm_dvd (1 <<< 128) ys 1 _ (by decide) rfl hdcy'
      split
      · rename_i ib hib
        have hx_int := hoa ia rfl
        have hx_sound : ∀ e', TermList.coeffOf (fromGrid ex0 step (ia.toList.map (fun c => mkRat c 1))) e' =
            TermList.coeffOf xs e' := by
          intro e'
          have hmap : ia.toList.map (fun c => mkRat c 1) = ia.toList.map Rat.ofInt := by
            apply List.map_congr_left; intro c _; exact TermList.mkRat_one c
          rw [hmap]; exact extractIntGrid_sound hx_int e'
        have hy_sound := extractScaledIntGrid_sound hdcy' hys_cdvd hib
        have hres := coeffOf_fromScaledIntGrid_aMulIntFast (by decide : (1 : Nat) ≠ 0) hdcy' hx_sound hy_sound e
        simpa [Nat.one_mul] using hres
      · exact TermList.coeffOf_mulTree _ _ e
    · split
      · split
        · rename_i da db hx' hy'
          rw [TermList.ratAddFast_eq]
          exact coeffOf_fromGrid_dMulKaratsuba hstep cutoff hx' hy' e
        · exact TermList.coeffOf_mulTree _ _ e
      · exact TermList.coeffOf_mulTree _ _ e
  | none =>
    dsimp only
    split
    · rename_i hdc
      simp only [Bool.and_eq_true, bne_iff_ne] at hdc
      rcases hdc with ⟨hdcx, hdcy⟩
      have ⟨_, hxs_cdvd⟩ := TermList.scanCoeffLcm_dvd (1 <<< 128) xs 1 _ (by decide) rfl hdcx
      have ⟨_, hys_cdvd⟩ := TermList.scanCoeffLcm_dvd (1 <<< 128) ys 1 _ (by decide) rfl hdcy
      split
      · rename_i ia hia
        split
        · rename_i ib hib
          exact coeffOf_fromScaledIntGrid_aMulIntFast hdcx hdcy
            (extractScaledIntGrid_sound hdcx hxs_cdvd hia)
            (extractScaledIntGrid_sound hdcy hys_cdvd hib) e
        · exact TermList.coeffOf_mulTree _ _ e
      · exact TermList.coeffOf_mulTree _ _ e
    · split
      · split
        · rename_i da db hx' hy'
          rw [TermList.ratAddFast_eq]
          exact coeffOf_fromGrid_dMulKaratsuba hstep cutoff hx' hy' e
        · exact TermList.coeffOf_mulTree _ _ e
      · exact TermList.coeffOf_mulTree _ _ e

/-- Verified top-level `TermList` multiplication combining Kronecker GMP, unboxed `Array Int`
    Karatsuba/schoolbook, denominator-cleared rational dense grids, and scaled-SOA sparse `mulTree`. -/
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
            mulRationalDense ex0 ey0 step fuel cutoff xs ys (some ia)
          | .offGrid => TermList.mulTree xs ys
        | .nonInt =>
          mulRationalDense ex0 ey0 step fuel cutoff xs ys none
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
          · exact mulRationalDense_wf hstep _ cutoff hxs hys _
          · exact TermList.mulTree_wf hxs hys
        · exact mulRationalDense_wf hstep _ cutoff hxs hys _
        · exact TermList.mulTree_wf hxs hys
      · exact TermList.mulTree_wf hxs hys
    · exact TermList.mulTree_wf hxs hys
  · exact TermList.mulTree_wf hxs hys

/-- **Unified Kronecker+Karatsuba+RationalClearing+Sparse Multiplication Equivalence Theorem (zero `sorry`)**. -/
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
          · exact coeffOf_mulRationalDense hstep _ cutoff _ _ (some ia)
              (fun _ heq => by cases heq; exact hx) e
          · exact TermList.coeffOf_mulTree _ _ e
        · exact coeffOf_mulRationalDense hstep _ cutoff _ _ none (fun _ heq => by cases heq) e
        · exact TermList.coeffOf_mulTree _ _ e
      · exact TermList.coeffOf_mulTree _ _ e
    · exact TermList.coeffOf_mulTree _ _ e
  · exact TermList.coeffOf_mulTree _ _ e

/-! #### 8. Verified In-Array Binary Exponentiation (`aPowIntFast` & `powFastGrid`) -/

/-- Denotational naive power on `TermList` used to state `powFastGrid` soundness. -/
def powNaiveTerms (xs : TermList) : Nat → TermList
  | 0 => [(0, 1)]
  | n + 1 => TermList.mulNaiveTerms xs (powNaiveTerms xs n)

private theorem coeffOf_mulNaiveTerms_one_right (xs : TermList) (e : Rat) :
    TermList.coeffOf (TermList.mulNaiveTerms xs [(0, 1)]) e = TermList.coeffOf xs e := by
  rw [TermList.coeffOf_mulNaiveTerms_comm, TermList.coeffOf_mulNaiveTerms_cons,
      TermList.coeffOf_mulNaiveTerms_nil, Rat.one_mul, Rat.add_zero]
  have hsub : e - (0 : Rat) = e := by grind
  rw [hsub]

private theorem coeffOf_powNaiveTerms_add (xs : TermList) (a b : Nat) (e : Rat) :
    TermList.coeffOf (powNaiveTerms xs (a + b)) e =
      TermList.coeffOf (TermList.mulNaiveTerms (powNaiveTerms xs a) (powNaiveTerms xs b)) e := by
  induction a generalizing e with
  | zero =>
    rw [Nat.zero_add, powNaiveTerms, TermList.coeffOf_mulNaiveTerms_cons,
        TermList.coeffOf_mulNaiveTerms_nil, Rat.one_mul, Rat.add_zero]
    have hsub : e - (0 : Rat) = e := by grind
    rw [hsub]
  | succ a' ih =>
    have hsucc : a' + 1 + b = (a' + b) + 1 := by omega
    rw [hsucc, powNaiveTerms, powNaiveTerms]
    rw [TermList.coeffOf_mulNaiveTerms_congr_right (fun e' => ih e'),
        ← TermList.coeffOf_mulNaiveTerms_assoc]

/-- Coefficient specification bridging scaled `aSqrIntFast` to `mulNaiveTerms`. -/
theorem coeffOf_fromScaledIntGrid_aSqrIntFast {ex0 step : Rat} {dc : Nat}
    (hdc : dc ≠ 0) {xs : TermList} {ia : Array Int}
    (hx : ∀ e, TermList.coeffOf (fromGrid ex0 step (ia.toList.map (fun c => mkRat c dc))) e =
      TermList.coeffOf xs e) (e : Rat) :
    TermList.coeffOf
        (fromScaledIntGrid (ex0 + ex0) step (dc * dc) (aSqrIntFast 32 ia)) e =
      TermList.coeffOf (TermList.mulNaiveTerms xs xs) e := by
  have hdcp : dc * dc ≠ 0 := Nat.mul_ne_zero hdc hdc
  rw [fromScaledIntGrid_eq_fromGrid _ _ hdcp]
  unfold fromGrid
  have hcongr : ∀ k,
      dCoeff ((aSqrIntFast 32 ia).toList.map (fun c => mkRat c (dc * dc))) k =
      dCoeff (dMulSchoolbook (ia.toList.map (fun c => mkRat c dc))
                             (ia.toList.map (fun c => mkRat c dc))) k := by
    intro k
    rw [dCoeff_map_mkRat, map_mkRat_eq_dScale ia dc,
        dCoeff_dMulSchoolbook_scale_left, dCoeff_dMulSchoolbook_scale_right,
        ← aCoeff_aSqrIntFast 32 ia k, ← TermList.mkRat_one (aCoeff (aSqrIntFast 32 ia) k),
        ← Rat.mul_assoc, Rat.mkRat_mul_mkRat, Rat.mkRat_mul_mkRat]
    simp
  rw [coeffOf_fromGridAux_congr 0 hcongr e, coeffOf_fromGridAux_dMulSchoolbook]
  rw [TermList.coeffOf_mulNaiveTerms_congr_left (fun e' => by simpa [fromGrid] using hx e'),
      TermList.coeffOf_mulNaiveTerms_congr_right (fun e' => by simpa [fromGrid] using hx e')]

/-- Binary exponentiation purely in `Array Int` using `aSqrIntFast` (single-pack GMP Kronecker
    or half-work Karatsuba squaring) and `aMulIntFast` — zero intermediate `TermList` round-trips. -/
def aPowIntFast (a : Array Int) (n : Nat) : Array Int :=
  if h0 : n = 0 then #[1]
  else if h1 : n = 1 then a
  else
    have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    let half := aPowIntFast a (n / 2)
    let sq := aSqrIntFast 32 half
    if n % 2 == 0 then sq else aMulIntFast 32 a sq
termination_by n

private theorem natPow_ne_zero {d : Nat} (hd : d ≠ 0) (n : Nat) : d ^ n ≠ 0 := by
  induction n with
  | zero => simp
  | succ _ ih => exact Nat.mul_ne_zero ih hd

/-- **In-Array Exponentiation Equivalence Theorem (zero `sorry`)**:
    `fromScaledIntGrid (n * ex0) step (dc^n) (aPowIntFast ia n)` has identical coefficients
    to `powNaiveTerms xs n`. -/
theorem coeffOf_fromScaledIntGrid_aPowIntFast {ex0 step : Rat} {dc : Nat}
    (hdc : dc ≠ 0) {xs : TermList} {ia : Array Int}
    (hx : ∀ e, TermList.coeffOf (fromGrid ex0 step (ia.toList.map (fun c => mkRat c dc))) e =
      TermList.coeffOf xs e)
    (n : Nat) (e : Rat) :
    TermList.coeffOf (fromScaledIntGrid ((n : Rat) * ex0) step (dc ^ n) (aPowIntFast ia n)) e =
      TermList.coeffOf (powNaiveTerms xs n) e := by
  unfold aPowIntFast
  split
  · rename_i h0
    subst h0
    have hpow : dc ^ 0 = 1 := rfl
    have hmul : ((0 : Nat) : Rat) * ex0 = 0 := by grind
    rw [hpow, hmul, fromScaledIntGrid_eq_fromGrid _ _ (by decide : (1 : Nat) ≠ 0)]
    change TermList.coeffOf (fromGrid 0 step [mkRat 1 1]) e = TermList.coeffOf [(0, 1)] e
    have h1 : mkRat 1 1 = (1 : Rat) := rfl
    rw [h1]
    unfold fromGrid fromGridAux
    have hne : ((1 : Rat) == 0) = false := by decide
    have hsub0 : (0 : Rat) - (0 : Rat) = 0 := by grind
    simp [hne, fromGridAux, hsub0]
  · rename_i hne0
    split
    · rename_i h1
      subst h1
      have hpow : dc ^ 1 = dc := Nat.pow_one dc
      have hmul : ((1 : Nat) : Rat) * ex0 = ex0 := by grind
      rw [hpow, hmul, fromScaledIntGrid_eq_fromGrid _ _ hdc, hx e]
      rw [powNaiveTerms, powNaiveTerms, coeffOf_mulNaiveTerms_one_right]
    · rename_i hne1
      have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      let k := n / 2
      have hdck : dc ^ k ≠ 0 := natPow_ne_zero hdc k
      have ih : ∀ e', TermList.coeffOf
          (fromGrid ((k : Rat) * ex0) step
            ((aPowIntFast ia k).toList.map (fun c => mkRat c (dc ^ k)))) e' =
          TermList.coeffOf (powNaiveTerms xs k) e' := fun e' => by
        rw [← fromScaledIntGrid_eq_fromGrid _ _ hdck]
        exact coeffOf_fromScaledIntGrid_aPowIntFast hdc hx k e'
      have hsq : ∀ e', TermList.coeffOf
          (fromScaledIntGrid ((k : Rat) * ex0 + (k : Rat) * ex0) step (dc ^ k * dc ^ k)
            (aSqrIntFast 32 (aPowIntFast ia k))) e' =
          TermList.coeffOf (powNaiveTerms xs (k + k)) e' := fun e' => by
        rw [coeffOf_fromScaledIntGrid_aSqrIntFast hdck ih e', coeffOf_powNaiveTerms_add]
      dsimp only
      split
      · rename_i heven
        have hmod : n % 2 = 0 := eq_of_beq heven
        have hsum : k + k = n := by omega
        have hpow : dc ^ k * dc ^ k = dc ^ n := by rw [← Nat.pow_add, hsum]
        have hexp : (k : Rat) * ex0 + (k : Rat) * ex0 = (n : Rat) * ex0 := by
          have hk : ((k : Rat) + (k : Rat)) = (n : Rat) := by
            rw [← Rat.natCast_add, hsum]
          rw [← Rat.add_mul, hk]
        rw [← hexp, ← hpow, hsq e, hsum]
      · rename_i hodd
        have hmod : n % 2 ≠ 0 := fun h => hodd (by simp [h])
        have hsum : (k + k) + 1 = n := by omega
        have hsq_grid : ∀ e', TermList.coeffOf
            (fromGrid ((k : Rat) * ex0 + (k : Rat) * ex0) step
              ((aSqrIntFast 32 (aPowIntFast ia k)).toList.map (fun c => mkRat c (dc ^ k * dc ^ k)))) e' =
            TermList.coeffOf (powNaiveTerms xs (k + k)) e' := fun e' => by
          rw [← fromScaledIntGrid_eq_fromGrid _ _ (Nat.mul_ne_zero hdck hdck)]
          exact hsq e'
        have hmul_res := coeffOf_fromScaledIntGrid_aMulIntFast hdc (Nat.mul_ne_zero hdck hdck)
          hx hsq_grid e
        have hpow : dc * (dc ^ k * dc ^ k) = dc ^ n := by
          rw [← Nat.pow_add, Nat.mul_comm, ← Nat.pow_succ]
          exact congrArg (dc ^ ·) hsum
        have hexp : TermList.ratAddFast ex0 ((k : Rat) * ex0 + (k : Rat) * ex0) = (n : Rat) * ex0 := by
          rw [TermList.ratAddFast_eq]
          have hcast : ((k + k + 1 : Nat) : Rat) = (n : Rat) := congrArg Nat.cast hsum
          simp only [Rat.natCast_add] at hcast
          grind
        rw [hexp, hpow] at hmul_res
        rw [hmul_res]
        have hpn : powNaiveTerms xs n = TermList.mulNaiveTerms xs (powNaiveTerms xs (k + k)) := by
          rw [← hsum]; rfl
        rw [hpn]
termination_by n

/-- Fast binary exponentiation on `Rat` using `TermList.ratMulFast`. -/
def powRatFast (c : Rat) (n : Nat) : Rat :=
  if h0 : n = 0 then 1
  else if h1 : n = 1 then c
  else
    have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    let half := powRatFast c (n / 2)
    let sq := TermList.ratMulFast half half
    if n % 2 == 0 then sq else TermList.ratMulFast c sq
termination_by n

private theorem coeffOf_powNaiveTerms_mono (ex c : Rat) (n : Nat) (e : Rat) :
    TermList.coeffOf (powNaiveTerms [(ex, c)] n) e =
      TermList.coeffOf [((n : Rat) * ex, powRatFast c n)] e := by
  unfold powRatFast
  split
  · rename_i h0
    subst h0
    have h0e : ((0 : Nat) : Rat) * ex = 0 := by grind
    rw [h0e, powNaiveTerms]
  · rename_i hne0
    split
    · rename_i h1
      subst h1
      have h1e : ((1 : Nat) : Rat) * ex = ex := by grind
      rw [h1e, powNaiveTerms, powNaiveTerms, coeffOf_mulNaiveTerms_one_right]
    · rename_i hne1
      have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      let k := n / 2
      have ih : ∀ e', TermList.coeffOf (powNaiveTerms [(ex, c)] k) e' =
          TermList.coeffOf [((k : Rat) * ex, powRatFast c k)] e' :=
        fun e' => coeffOf_powNaiveTerms_mono ex c k e'
      have hmul_mono : ∀ (e1 c1 e2 c2 target : Rat),
          TermList.coeffOf (TermList.mulNaiveTerms [(e1, c1)] [(e2, c2)]) target =
          TermList.coeffOf [(e1 + e2, c1 * c2)] target := by
        intro e1 c1 e2 c2 target
        simp only [TermList.mulNaiveTerms, List.foldr_cons, List.foldr_nil, List.map_cons,
          List.map_nil, List.append_nil, TermList.coeffOf, Rat.add_zero]
      have hsq : ∀ e', TermList.coeffOf (powNaiveTerms [(ex, c)] (k + k)) e' =
          TermList.coeffOf [((k : Rat) * ex + (k : Rat) * ex,
            TermList.ratMulFast (powRatFast c k) (powRatFast c k))] e' := fun e' => by
        rw [coeffOf_powNaiveTerms_add,
            TermList.coeffOf_mulNaiveTerms_congr_left ih,
            TermList.coeffOf_mulNaiveTerms_congr_right ih,
            hmul_mono, TermList.ratMulFast_eq]
      dsimp only
      split
      · rename_i heven
        have hmod : n % 2 = 0 := eq_of_beq heven
        have hsum : k + k = n := by omega
        have hexp : (k : Rat) * ex + (k : Rat) * ex = (n : Rat) * ex := by
          have hk : (k : Rat) + (k : Rat) = (n : Rat) := by rw [← Rat.natCast_add, hsum]
          rw [← Rat.add_mul, hk]
        calc TermList.coeffOf (powNaiveTerms [(ex, c)] n) e
            = TermList.coeffOf (powNaiveTerms [(ex, c)] (k + k)) e := by rw [hsum]
          _ = TermList.coeffOf [((k : Rat) * ex + (k : Rat) * ex,
                TermList.ratMulFast (powRatFast c k) (powRatFast c k))] e := hsq e
          _ = TermList.coeffOf [((n : Rat) * ex,
                TermList.ratMulFast (powRatFast c (n / 2)) (powRatFast c (n / 2)))] e := by
              rw [hexp]
      · rename_i hodd
        have hmod : n % 2 ≠ 0 := fun h => hodd (by simp [h])
        have hsum : (k + k) + 1 = n := by omega
        have hexp : ex + ((k : Rat) * ex + (k : Rat) * ex) = (n : Rat) * ex := by
          have hcast : ((k + k + 1 : Nat) : Rat) = (n : Rat) := congrArg Nat.cast hsum
          simp only [Rat.natCast_add] at hcast
          grind
        calc TermList.coeffOf (powNaiveTerms [(ex, c)] n) e
            = TermList.coeffOf (powNaiveTerms [(ex, c)] ((k + k) + 1)) e := by rw [hsum]
          _ = TermList.coeffOf (TermList.mulNaiveTerms [(ex, c)] (powNaiveTerms [(ex, c)] (k + k))) e := rfl
          _ = TermList.coeffOf (TermList.mulNaiveTerms [(ex, c)]
                [((k : Rat) * ex + (k : Rat) * ex,
                  TermList.ratMulFast (powRatFast c k) (powRatFast c k))]) e :=
              TermList.coeffOf_mulNaiveTerms_congr_right hsq e
          _ = TermList.coeffOf [(ex + ((k : Rat) * ex + (k : Rat) * ex),
                c * TermList.ratMulFast (powRatFast c k) (powRatFast c k))] e := hmul_mono _ _ _ _ e
          _ = TermList.coeffOf [((n : Rat) * ex,
                TermList.ratMulFast c (TermList.ratMulFast (powRatFast c (n / 2)) (powRatFast c (n / 2))))] e := by
              rw [hexp, TermList.ratMulFast_eq, TermList.ratMulFast_eq]
termination_by n

/-- Heuristic step-size guess for a single `TermList` from its leading 1–2 exponent gaps. -/
def guessGridStepSingle (xs : TermList) : Option Rat :=
  match xs with
  | (e0, _) :: (e1, _) :: (e2, _) :: _ =>
    let d1 := TermList.ratSubFast e0 e1
    let d2 := TermList.ratSubFast e1 e2
    let step := match TermList.ratCmpFast d1 d2 with | .gt => d2 | _ => d1
    if step.num > 0 then some step else none
  | (e0, _) :: (e1, _) :: _ =>
    let step := TermList.ratSubFast e0 e1
    if step.num > 0 then some step else none
  | _ => none

/-- Verified in-array grid exponentiation for `TermList`:
    - `0^n` → `0` (`O(1)`), single monomial `(c H^e)^n` → `c^n H^{n e}` (`O(log n)` scalar)
    - Grid-aligned integer series → single extract + `aPowIntFast` (GMP `aSqrKroneckerCore` /
      half-work `aSqrKaratsubaInt`) + single `fromIntGrid`
    - Grid-aligned bounded-LCM rational series (`n * bits(dc) ≤ 256`) → single denominator-cleared
      extract + `aPowIntFast` + single `fromScaledIntGrid`
    - Off-grid or huge-denominator inputs return `none` for `FastLC.powFastLoop` fallback. -/
def powFastGrid (xs : TermList) (n : Nat) : Option TermList :=
  if n == 0 then some [(0, 1)]
  else if n == 1 then none
  else
    match xs with
    | [] => some []
    | [(e, c)] =>
      let cn := powRatFast c n
      some (if cn == 0 then [] else [((n : Rat) * e, cn)])
    | (ex0, _) :: _ :: _ =>
      match guessGridStepSingle xs with
      | some step =>
        if step > 0 then
          let fuel := 4 * xs.length + 16
          match extractIntGridClassified ex0 step fuel xs with
          | .ok ia =>
            some (fromIntGrid ((n : Rat) * ex0) step (aPowIntFast ia n))
          | .nonInt =>
            let maxRatDen : Nat := 1 <<< 64
            let dc := TermList.scanCoeffLcm maxRatDen xs 1
            if dc != 0 && n * (dc.log2 + 1) ≤ 256 then
              match extractScaledIntGrid ex0 step dc fuel xs with
              | some ia =>
                some (fromScaledIntGrid ((n : Rat) * ex0) step (dc ^ n) (aPowIntFast ia n))
              | none => none
            else none
          | .offGrid => none
        else none
      | none => none

/-- Every `TermList` returned by `powFastGrid` is canonically well-formed. -/
theorem powFastGrid_wf {xs ts : TermList} {n : Nat} (h : powFastGrid xs n = some ts) :
    TermList.WF ts := by
  unfold powFastGrid at h
  split at h
  · cases h; exact ⟨by decide, trivial, trivial⟩
  · split at h
    · cases h
    · cases xs with
      | nil => cases h; trivial
      | cons p1 rest1 =>
        cases rest1 with
        | nil =>
          rcases p1 with ⟨e, c⟩
          dsimp only at h
          cases h
          split
          · trivial
          · rename_i hne
            exact ⟨fun hc => hne (by simp [hc]), trivial, trivial⟩
        | cons p2 rest2 =>
          rcases p1 with ⟨ex0, c0⟩
          dsimp only at h
          split at h
          · rename_i step _
            split at h
            · rename_i hstep
              split at h
              · cases h; exact fromIntGrid_wf hstep _
              · split at h
                · rename_i hdc
                  simp only [Bool.and_eq_true, bne_iff_ne] at hdc
                  split at h
                  · cases h
                    exact fromScaledIntGrid_wf hstep (natPow_ne_zero hdc.1 n) _
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h

/-- **Verified `powFastGrid` Soundness Theorem (zero `sorry`)**:
    Whenever `powFastGrid xs n = some ts`, every coefficient of `ts` equals `powNaiveTerms xs n`. -/
theorem coeffOf_powFastGrid {xs ts : TermList} {n : Nat} (h : powFastGrid xs n = some ts)
    (e : Rat) :
    TermList.coeffOf ts e = TermList.coeffOf (powNaiveTerms xs n) e := by
  unfold powFastGrid at h
  split at h
  · rename_i h0
    have hn : n = 0 := eq_of_beq h0
    subst hn; cases h; rfl
  · rename_i hne0
    split at h
    · cases h
    · have hn0 : n ≠ 0 := fun h0 => hne0 (by simp [h0])
      cases xs with
      | nil =>
        cases h
        cases n with
        | zero => exact absurd rfl hn0
        | succ n' => rfl
      | cons p1 rest1 =>
        cases rest1 with
        | nil =>
          rcases p1 with ⟨ex, c⟩
          dsimp only at h
          cases h
          rw [coeffOf_powNaiveTerms_mono ex c n e]
          split
          · rename_i hcn0
            have hcn : powRatFast c n = 0 := eq_of_beq hcn0
            rw [hcn]
            simp [TermList.coeffOf, Rat.add_zero]
          · rfl
        | cons p2 rest2 =>
          rcases p1 with ⟨ex0, c0⟩
          dsimp only at h
          split at h
          · rename_i step _
            split at h
            · rename_i hstep
              split at h
              · rename_i ia hx_ok
                cases h
                have hx := extractIntGridClassified_ok hx_ok
                have hx_sound : ∀ e', TermList.coeffOf
                    (fromGrid ex0 step (ia.toList.map (fun c => mkRat c 1))) e' =
                    TermList.coeffOf ((ex0, c0) :: p2 :: rest2) e' := by
                  intro e'
                  have hmap : ia.toList.map (fun c => mkRat c 1) = ia.toList.map Rat.ofInt := by
                    apply List.map_congr_left; intro c _; exact TermList.mkRat_one c
                  rw [hmap]; exact extractIntGrid_sound hx e'
                have hres := coeffOf_fromScaledIntGrid_aPowIntFast (by decide : (1 : Nat) ≠ 0)
                  hx_sound n e
                have h1pow : (1 : Nat) ^ n = 1 := Nat.one_pow n
                rw [h1pow, fromScaledIntGrid_eq_fromGrid _ _ (by decide : (1 : Nat) ≠ 0)] at hres
                have hmap2 : (aPowIntFast ia n).toList.map (fun c => mkRat c 1) =
                    (aPowIntFast ia n).toList.map Rat.ofInt := by
                  apply List.map_congr_left; intro c _; exact TermList.mkRat_one c
                rw [fromIntGrid_eq_fromGrid, ← hmap2]
                exact hres
              · split at h
                · rename_i hdc
                  simp only [Bool.and_eq_true, bne_iff_ne] at hdc
                  have ⟨_, hcdvd⟩ := TermList.scanCoeffLcm_dvd (1 <<< 64)
                    ((ex0, c0) :: p2 :: rest2) 1 _ (by decide) rfl hdc.1
                  split at h
                  · rename_i ia hia
                    cases h
                    exact coeffOf_fromScaledIntGrid_aPowIntFast hdc.1
                      (extractScaledIntGrid_sound hdc.1 hcdvd hia) n e
                  · cases h
                · cases h
              · cases h
            · cases h
          · cases h

end Kronecker
end LeanInf
