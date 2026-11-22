import Init.Data.Rat
import LeanInf.LeviCivitaNum

namespace LeanInf

/-- A list of `(exponent, coefficient)` pairs representing `∑ c * H^e`. -/
abbrev TermList := List (Rat × Rat)

namespace TermList

/-! ### Small `Rat` helpers (zero `sorry`) -/

private theorem rat_lt_trans {a b c : Rat} (h1 : a < b) (h2 : b < c) : a < c := by
  grind

private theorem rat_eq_of_not_gt_not_lt {a b : Rat} (h1 : ¬ a > b) (h2 : ¬ b > a) : a = b := by
  grind

private theorem rat_add_lt_add_left_of_lt {k a b : Rat} (h : a < b) : k + a < k + b := by
  grind

private theorem rat_mul_ne_zero {a b : Rat} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  rcases Rat.mul_eq_zero.mp h with h1 | h2
  · exact ha h1
  · exact hb h2

/-! ### Zero-GCD `Rat` Fast Paths (`den == 1`) & Single-Cross-Multiply Comparison -/

private theorem rat_eq_ofInt_of_den_eq_one {a : Rat} (h : a.den = 1) : a = Rat.ofInt a.num := by
  apply Rat.ext <;> simp [Rat.ofInt, h]

/-- Zero-GCD rational addition fast path when both denominators are `1`. -/
@[inline] def ratAddFast (a b : Rat) : Rat :=
  if a.den == 1 && b.den == 1 then Rat.ofInt (a.num + b.num) else a + b

/-- Zero-GCD rational subtraction fast path when both denominators are `1`. -/
@[inline] def ratSubFast (a b : Rat) : Rat :=
  if a.den == 1 && b.den == 1 then Rat.ofInt (a.num - b.num) else a - b

/-- Zero-GCD rational multiplication fast path when both denominators are `1`. -/
@[inline] def ratMulFast (a b : Rat) : Rat :=
  if a.den == 1 && b.den == 1 then Rat.ofInt (a.num * b.num) else a * b

/-- Single-comparison 3-way ordering on `Rat` (zero multiplies when denominators match,
    one cross-multiply pair otherwise). -/
@[inline] def ratCmpFast (a b : Rat) : Ordering :=
  if a.den == b.den then
    if a.num > b.num then .gt
    else if a.num < b.num then .lt
    else .eq
  else
    let lhs := a.num * (b.den : Int)
    let rhs := b.num * (a.den : Int)
    if lhs > rhs then .gt
    else if lhs < rhs then .lt
    else .eq

/-- `ratAddFast` is extensionally identical to `Rat.add`. -/
theorem ratAddFast_eq (a b : Rat) : ratAddFast a b = a + b := by
  unfold ratAddFast
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases a with ⟨an, ad, had, hac⟩
    rcases b with ⟨bn, bd, hbd, hbc⟩
    simp only at h
    rcases h with ⟨rfl, rfl⟩
    rw [Rat.add_def]
    apply Rat.ext <;> simp [Rat.normalize, Rat.ofInt]
  · rfl

/-- `ratSubFast` is extensionally identical to `Rat.sub`. -/
theorem ratSubFast_eq (a b : Rat) : ratSubFast a b = a - b := by
  unfold ratSubFast
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases a with ⟨an, ad, had, hac⟩
    rcases b with ⟨bn, bd, hbd, hbc⟩
    simp only at h
    rcases h with ⟨rfl, rfl⟩
    rw [Rat.sub_def]
    apply Rat.ext <;> simp [Rat.normalize, Rat.ofInt]
  · rfl

/-- `ratMulFast` is extensionally identical to `Rat.mul`. -/
theorem ratMulFast_eq (a b : Rat) : ratMulFast a b = a * b := by
  unfold ratMulFast
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rcases a with ⟨an, ad, had, hac⟩
    rcases b with ⟨bn, bd, hbd, hbc⟩
    simp only at h
    rcases h with ⟨rfl, rfl⟩
    rw [Rat.mul_def]
    apply Rat.ext <;> simp [Rat.normalize, Rat.ofInt]
  · rfl

/-- `ratCmpFast` returns `.gt` iff `a > b`. -/
theorem ratCmpFast_gt (a b : Rat) : ratCmpFast a b = .gt ↔ a > b := by
  unfold ratCmpFast
  split
  · rename_i hd
    have hdeq : a.den = b.den := eq_of_beq hd
    have hpos : (0 : Int) < (b.den : Int) := by
      have := Nat.pos_of_ne_zero b.den_nz; omega
    simp only [GT.gt, Rat.lt_iff, hdeq]
    split
    · rename_i h
      simp only [true_iff]
      exact Int.mul_lt_mul_of_pos_right h hpos
    · split <;> (
        simp only [reduceCtorEq, false_iff]
        intro hlt
        have : b.num < a.num := Int.lt_of_mul_lt_mul_right hlt (by omega)
        omega)
  · simp only [GT.gt, Rat.lt_iff]
    split
    · rename_i h; simp; omega
    · split <;> (simp; omega)

/-- `ratCmpFast` returns `.lt` iff `b > a`. -/
theorem ratCmpFast_lt (a b : Rat) : ratCmpFast a b = .lt ↔ b > a := by
  unfold ratCmpFast
  split
  · rename_i hd
    have hdeq : a.den = b.den := eq_of_beq hd
    have hpos : (0 : Int) < (b.den : Int) := by
      have := Nat.pos_of_ne_zero b.den_nz; omega
    simp only [GT.gt, Rat.lt_iff, hdeq]
    split
    · rename_i h
      simp only [reduceCtorEq, false_iff]
      intro hlt
      have : a.num < b.num := Int.lt_of_mul_lt_mul_right hlt (by omega)
      omega
    · split
      · rename_i h1 h2
        simp only [true_iff]
        exact Int.mul_lt_mul_of_pos_right h2 hpos
      · rename_i h1 h2
        simp only [reduceCtorEq, false_iff]
        intro hlt
        have : a.num < b.num := Int.lt_of_mul_lt_mul_right hlt (by omega)
        omega
  · simp only [GT.gt, Rat.lt_iff]
    split
    · rename_i h; simp; omega
    · split
      · rename_i h1 h2; simp; omega
      · rename_i h1 h2; simp; omega

private theorem rat_num_beq_zero_eq (r : Rat) : (r.num == 0) = (r == 0) := by
  cases h1 : (r.num == 0) <;> cases h2 : (r == 0) <;> try rfl
  · have hr : r = 0 := eq_of_beq h2
    subst hr; simp at h1
  · have hn : r.num = 0 := eq_of_beq h1
    have hd : r.den = 1 := by
      have hcop := r.reduced
      rw [hn] at hcop
      simpa using hcop
    have hr : r = 0 := by apply Rat.ext <;> simp [hn, hd]
    rw [hr] at h2; simp at h2

/-! ### Denotational Semantics & Canonical Invariant -/

/-- Exact mathematical coefficient of `H^e` denoted by any term list
    (summing duplicate exponents, returning `0` if absent). -/
def coeffOf : TermList → Rat → Rat
  | [], _ => 0
  | (e', c) :: rest, e => (if e' == e then c else 0) + coeffOf rest e

/-- Every term in `ts` has exponent strictly smaller than `bound`. -/
def AllLt (bound : Rat) : TermList → Prop
  | [] => True
  | (e, _) :: rest => e < bound ∧ AllLt bound rest

/-- Canonical invariant: strictly descending exponents and all coefficients nonzero. -/
def WF : TermList → Prop
  | [] => True
  | (e, c) :: rest => c ≠ 0 ∧ AllLt e rest ∧ WF rest

/-- Monotonicity of `AllLt` with respect to the upper bound. -/
theorem allLt_mono {a b : Rat} {ts : TermList} (hab : a < b) (h : AllLt a ts) : AllLt b ts := by
  induction ts with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    exact ⟨rat_lt_trans h.1 hab, ih h.2⟩

/-- `coeffOf` distributes over list concatenation. -/
theorem coeffOf_append (xs ys : TermList) (e : Rat) :
    coeffOf (xs ++ ys) e = coeffOf xs e + coeffOf ys e := by
  induction xs with
  | nil => simp [coeffOf, Rat.zero_add]
  | cons p rest ih =>
    rcases p with ⟨e', c⟩
    simp [coeffOf, ih, Rat.add_assoc]

/-- Any exponent at or above the `AllLt` upper bound has coefficient `0`. -/
theorem coeffOf_eq_zero_of_allLt {bound e : Rat} {ts : TermList}
    (h : AllLt bound ts) (hle : bound ≤ e) : coeffOf ts e = 0 := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨e', c⟩
    have hlt' : e' < bound := h.1
    have hlt : e' < e := by grind
    have hne : (e' == e) = false := by
      cases hb : (e' == e)
      · rfl
      · have : e' = e := eq_of_beq hb
        grind
    simp [coeffOf, hne, ih h.2, Rat.add_zero]

/-- On a well-formed term list, the head exponent's coefficient is exactly the head coefficient. -/
theorem coeffOf_cons_head_of_wf {e0 c0 : Rat} {rest : TermList}
    (hwf : WF ((e0, c0) :: rest)) : coeffOf ((e0, c0) :: rest) e0 = c0 := by
  have hz : coeffOf rest e0 = 0 := coeffOf_eq_zero_of_allLt hwf.2.1 (by grind)
  simp [coeffOf, hz, Rat.add_zero]

/-- On a well-formed term list, any exponent strictly above the head exponent has coefficient `0`. -/
theorem coeffOf_eq_zero_of_gt_head {e0 c0 e : Rat} {rest : TermList}
    (hwf : WF ((e0, c0) :: rest)) (hgt : e > e0) : coeffOf ((e0, c0) :: rest) e = 0 := by
  have hne : (e0 == e) = false := by
    cases hb : (e0 == e)
    · rfl
    · have : e0 = e := eq_of_beq hb
      grind
  have hz : coeffOf rest e = 0 := coeffOf_eq_zero_of_allLt hwf.2.1 (by grind)
  simp [coeffOf, hne, hz, Rat.add_zero]

/-- Canonicality: two well-formed term lists with identical coefficients at every exponent
    are structurally identical. -/
theorem eq_of_wf_of_coeffOf_eq {xs ys : TermList}
    (hxs : WF xs) (hys : WF ys) (heq : ∀ e, coeffOf xs e = coeffOf ys e) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons p rest =>
      rcases p with ⟨ey, cy⟩
      have h0 := heq ey
      rw [coeffOf_cons_head_of_wf hys] at h0
      simp [coeffOf] at h0
      exact absurd h0.symm hys.1
  | cons px restx ih =>
    rcases px with ⟨ex, cx⟩
    cases ys with
    | nil =>
      have h0 := heq ex
      rw [coeffOf_cons_head_of_wf hxs] at h0
      simp [coeffOf] at h0
      exact absurd h0 hxs.1
    | cons py resty =>
      rcases py with ⟨ey, cy⟩
      by_cases hgt : ex > ey
      · have h0 := heq ex
        rw [coeffOf_cons_head_of_wf hxs, coeffOf_eq_zero_of_gt_head hys hgt] at h0
        exact absurd h0 hxs.1
      · by_cases hlt : ey > ex
        · have h0 := heq ey
          rw [coeffOf_eq_zero_of_gt_head hxs hlt, coeffOf_cons_head_of_wf hys] at h0
          exact absurd h0.symm hys.1
        · have hexy : ex = ey := rat_eq_of_not_gt_not_lt hgt hlt
          subst hexy
          have hc : cx = cy := by
            have h0 := heq ex
            rw [coeffOf_cons_head_of_wf hxs, coeffOf_cons_head_of_wf hys] at h0
            exact h0
          subst hc
          congr 1
          apply ih hxs.2.2 hys.2.2
          intro e
          have h0 := heq e
          simp only [coeffOf] at h0
          grind

/-! ### Verified Refactor 1: `O(1)` Signum & Leading Term -/

/-- `O(1)` signum on canonical strictly-descending term lists (replaces `O(n log n)` sort). -/
def signumFast : TermList → Int
  | [] => 0
  | (_, c) :: _ => if c > 0 then 1 else -1

/-- `O(1)` dominant (largest-exponent) term lookup. -/
def leadingTermFast : TermList → Option (Rat × Rat)
  | [] => none
  | p :: _ => some p

/-- `signumFast` returns `0` iff every coefficient is zero. -/
theorem signumFast_eq_zero_iff {ts : TermList} (hwf : WF ts) :
    signumFast ts = 0 ↔ ∀ e, coeffOf ts e = 0 := by
  cases ts with
  | nil => simp [signumFast, coeffOf]
  | cons p rest =>
    rcases p with ⟨e0, c0⟩
    constructor
    · intro h
      simp [signumFast] at h
      split at h <;> omega
    · intro hall
      have h0 := hall e0
      rw [coeffOf_cons_head_of_wf hwf] at h0
      exact absurd h0 hwf.1

/-- `signumFast` returns `1` iff the dominant (largest-exponent) nonzero term is positive. -/
theorem signumFast_eq_one_iff {ts : TermList} (hwf : WF ts) :
    signumFast ts = 1 ↔ ∃ e0, coeffOf ts e0 > 0 ∧ ∀ e > e0, coeffOf ts e = 0 := by
  cases ts with
  | nil =>
    simp only [signumFast, coeffOf]
    constructor
    · intro h; omega
    · rintro ⟨e0, hgt, _⟩; grind
  | cons p rest =>
    rcases p with ⟨e0, c0⟩
    constructor
    · intro h
      simp only [signumFast] at h
      have hcpos : c0 > 0 := by
        split at h
        · assumption
        · omega
      refine ⟨e0, ?_, ?_⟩
      · rw [coeffOf_cons_head_of_wf hwf]; exact hcpos
      · intro e he; exact coeffOf_eq_zero_of_gt_head hwf he
    · rintro ⟨e1, hpos, hdom⟩
      have heq : e1 = e0 := by
        by_cases hgt : e1 > e0
        · rw [coeffOf_eq_zero_of_gt_head hwf hgt] at hpos; grind
        · by_cases hlt : e0 > e1
          · have h0 := hdom e0 hlt
            rw [coeffOf_cons_head_of_wf hwf] at h0
            exact absurd h0 hwf.1
          · exact rat_eq_of_not_gt_not_lt hgt hlt
      subst heq
      rw [coeffOf_cons_head_of_wf hwf] at hpos
      simp [signumFast, hpos]

/-- `signumFast` returns `-1` iff the dominant (largest-exponent) nonzero term is negative. -/
theorem signumFast_eq_neg_one_iff {ts : TermList} (hwf : WF ts) :
    signumFast ts = -1 ↔ ∃ e0, coeffOf ts e0 < 0 ∧ ∀ e > e0, coeffOf ts e = 0 := by
  cases ts with
  | nil =>
    simp only [signumFast, coeffOf]
    constructor
    · intro h; omega
    · rintro ⟨e0, hlt, _⟩; grind
  | cons p rest =>
    rcases p with ⟨e0, c0⟩
    constructor
    · intro h
      simp only [signumFast] at h
      have hcneg : c0 < 0 := by
        split at h
        · omega
        · have hne : c0 ≠ 0 := hwf.1
          grind
      refine ⟨e0, ?_, ?_⟩
      · rw [coeffOf_cons_head_of_wf hwf]; exact hcneg
      · intro e he; exact coeffOf_eq_zero_of_gt_head hwf he
    · rintro ⟨e1, hneg, hdom⟩
      have heq : e1 = e0 := by
        by_cases hgt : e1 > e0
        · rw [coeffOf_eq_zero_of_gt_head hwf hgt] at hneg; grind
        · by_cases hlt : e0 > e1
          · have h0 := hdom e0 hlt
            rw [coeffOf_cons_head_of_wf hwf] at h0
            exact absurd h0 hwf.1
          · exact rat_eq_of_not_gt_not_lt hgt hlt
      subst heq
      rw [coeffOf_cons_head_of_wf hwf] at hneg
      have hnotpos : ¬ c0 > 0 := by grind
      simp [signumFast, hnotpos]

/-! ### Verified Refactor 2: `O(n + m)` Sorted Two-Pointer Addition & Negation -/

/-- `O(n + m)` two-pointer sorted merge addition with on-the-fly zero cancellation. -/
def addMerge : TermList → TermList → TermList
  | [], ys => ys
  | xs, [] => xs
  | (ex, cx) :: xs, (ey, cy) :: ys =>
    if ex > ey then (ex, cx) :: addMerge xs ((ey, cy) :: ys)
    else if ey > ex then (ey, cy) :: addMerge ((ex, cx) :: xs) ys
    else
      let s := cx + cy
      if s == 0 then addMerge xs ys
      else (ex, s) :: addMerge xs ys

/-- `addMerge` preserves exponent upper bounds. -/
theorem addMerge_allLt {b : Rat} {xs ys : TermList}
    (hx : AllLt b xs) (hy : AllLt b ys) : AllLt b (addMerge xs ys) := by
  induction xs generalizing ys with
  | nil => simpa [addMerge] using hy
  | cons px restx ihx =>
    rcases px with ⟨ex, cx⟩
    induction ys with
    | nil => simpa [addMerge] using hx
    | cons py resty ihy =>
      rcases py with ⟨ey, cy⟩
      simp only [addMerge]
      split
      · exact ⟨hx.1, ihx hx.2 hy⟩
      · split
        · exact ⟨hy.1, ihy hy.2⟩
        · split
          · exact ihx hx.2 hy.2
          · exact ⟨hx.1, ihx hx.2 hy.2⟩

/-- `addMerge` preserves canonical well-formedness. -/
theorem addMerge_wf {xs ys : TermList} (hxs : WF xs) (hys : WF ys) :
    WF (addMerge xs ys) := by
  induction xs generalizing ys with
  | nil => simpa [addMerge] using hys
  | cons px restx ihx =>
    rcases px with ⟨ex, cx⟩
    induction ys with
    | nil => simpa [addMerge] using hxs
    | cons py resty ihy =>
      rcases py with ⟨ey, cy⟩
      simp only [addMerge]
      split
      · rename_i hgt
        refine ⟨hxs.1, addMerge_allLt hxs.2.1 ⟨hgt, allLt_mono hgt hys.2.1⟩, ihx hxs.2.2 hys⟩
      · split
        · rename_i _ hlt
          refine ⟨hys.1, addMerge_allLt ⟨hlt, allLt_mono hlt hxs.2.1⟩ hys.2.1, ihy hys.2.2⟩
        · rename_i h1 h2
          have heq : ex = ey := rat_eq_of_not_gt_not_lt h1 h2
          subst heq
          split
          · exact ihx hxs.2.2 hys.2.2
          · rename_i hnz
            have hne : cx + cy ≠ 0 := by
              intro h0; simp [h0] at hnz
            exact ⟨hne, addMerge_allLt hxs.2.1 hys.2.1, ihx hxs.2.2 hys.2.2⟩

/-- `addMerge` agrees coefficient-wise with exact Levi-Civita addition at every exponent `e`. -/
theorem coeffOf_addMerge (xs ys : TermList) (e : Rat) :
    coeffOf (addMerge xs ys) e = coeffOf xs e + coeffOf ys e := by
  induction xs generalizing ys with
  | nil => simp [addMerge, coeffOf, Rat.zero_add]
  | cons px restx ihx =>
    rcases px with ⟨ex, cx⟩
    induction ys with
    | nil => simp [addMerge, coeffOf, Rat.add_zero]
    | cons py resty ihy =>
      rcases py with ⟨ey, cy⟩
      simp only [addMerge]
      split
      · simp [coeffOf, ihx, Rat.add_assoc]
      · split
        · rw [coeffOf, ihy]
          simp only [coeffOf]
          grind
        · rename_i h1 h2
          have heq : ex = ey := rat_eq_of_not_gt_not_lt h1 h2
          subst heq
          split
          · rename_i hz
            have hsum : cx + cy = 0 := eq_of_beq hz
            rw [ihx resty]
            simp only [coeffOf]
            by_cases hbe : (ex == e) = true
            · simp [hbe]; grind
            · have hf : (ex == e) = false := by cases hb : (ex == e) <;> simp_all
              simp [hf, Rat.zero_add]
          · rw [coeffOf, ihx resty]
            simp only [coeffOf]
            by_cases hbe : (ex == e) = true
            · simp [hbe]; grind
            · have hf : (ex == e) = false := by cases hb : (ex == e) <;> simp_all
              simp [hf, Rat.zero_add]

/-- `O(n)` negation preserving canonical sorted order. -/
def negFast (xs : TermList) : TermList :=
  xs.map (fun (e, c) => (e, -c))

/-- `negFast` preserves exponent upper bounds. -/
theorem negFast_allLt {b : Rat} {xs : TermList} (h : AllLt b xs) : AllLt b (negFast xs) := by
  induction xs with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    exact ⟨h.1, ih h.2⟩

/-- `negFast` preserves canonical well-formedness. -/
theorem negFast_wf {xs : TermList} (h : WF xs) : WF (negFast xs) := by
  induction xs with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    refine ⟨?_, negFast_allLt h.2.1, ih h.2.2⟩
    intro hc
    have : c = 0 := by grind
    exact h.1 this

/-- `negFast` negates every coefficient. -/
theorem coeffOf_negFast (xs : TermList) (e : Rat) :
    coeffOf (negFast xs) e = -(coeffOf xs e) := by
  induction xs with
  | nil => simp [negFast, coeffOf]
  | cons p rest ih =>
    rcases p with ⟨e', c⟩
    change coeffOf ((e', -c) :: negFast rest) e = -(coeffOf ((e', c) :: rest) e)
    simp only [coeffOf, ih]
    split <;> grind

/-- `O(n + m)` subtraction via `addMerge` and `negFast`. -/
def subFast (xs ys : TermList) : TermList :=
  addMerge xs (negFast ys)

/-- `subFast` preserves canonical well-formedness. -/
theorem subFast_wf {xs ys : TermList} (hx : WF xs) (hy : WF ys) : WF (subFast xs ys) :=
  addMerge_wf hx (negFast_wf hy)

/-- `subFast` subtracts coefficients at every exponent `e`. -/
theorem coeffOf_subFast (xs ys : TermList) (e : Rat) :
    coeffOf (subFast xs ys) e = coeffOf xs e - coeffOf ys e := by
  simp [subFast, coeffOf_addMerge, coeffOf_negFast, Rat.sub_eq_add_neg]

/-- Tail-recursive, single-comparison sorted merge loop compiled via `@[csimp]`. -/
def addMergeTRLoop : TermList → TermList → TermList → TermList
  | [], ys, acc => acc.reverseAux ys
  | xs, [], acc => acc.reverseAux xs
  | (ex, cx) :: xs, (ey, cy) :: ys, acc =>
    match ratCmpFast ex ey with
    | .gt => addMergeTRLoop xs ((ey, cy) :: ys) ((ex, cx) :: acc)
    | .lt => addMergeTRLoop ((ex, cx) :: xs) ys ((ey, cy) :: acc)
    | .eq =>
      let s := ratAddFast cx cy
      if s.num == 0 then addMergeTRLoop xs ys acc
      else addMergeTRLoop xs ys ((ex, s) :: acc)

/-- Compiled tail-recursive entry point for `addMerge`. -/
@[inline] def addMergeTR (xs ys : TermList) : TermList :=
  addMergeTRLoop xs ys []

private theorem addMergeTRLoop_eq (xs ys acc : TermList) :
    addMergeTRLoop xs ys acc = acc.reverse ++ addMerge xs ys := by
  induction xs generalizing ys acc with
  | nil =>
    simp [addMergeTRLoop, addMerge, List.reverseAux_eq]
  | cons px restx ihx =>
    rcases px with ⟨ex, cx⟩
    induction ys generalizing acc with
    | nil =>
      simp [addMergeTRLoop, addMerge, List.reverseAux_eq]
    | cons py resty ihy =>
      rcases py with ⟨ey, cy⟩
      simp only [addMergeTRLoop, addMerge]
      cases hcmp : ratCmpFast ex ey with
      | gt =>
        have hgt : ex > ey := (ratCmpFast_gt ex ey).mp hcmp
        simp only [hgt, ↓reduceIte]
        rw [ihx ((ey, cy) :: resty) ((ex, cx) :: acc), List.reverse_cons, List.append_assoc]
        rfl
      | lt =>
        have hlt : ey > ex := (ratCmpFast_lt ex ey).mp hcmp
        have hngt : ¬ (ex > ey) := by grind
        simp only [hngt, hlt, ↓reduceIte]
        rw [ihy ((ey, cy) :: acc), List.reverse_cons, List.append_assoc]
        rfl
      | eq =>
        have hngt : ¬ (ex > ey) := by
          intro h; have := (ratCmpFast_gt ex ey).mpr h; rw [hcmp] at this; cases this
        have hnlt : ¬ (ey > ex) := by
          intro h; have := (ratCmpFast_lt ex ey).mpr h; rw [hcmp] at this; cases this
        simp only [hngt, hnlt, ↓reduceIte, ratAddFast_eq, rat_num_beq_zero_eq]
        split
        · exact ihx resty acc
        · rw [ihx resty ((ex, cx + cy) :: acc), List.reverse_cons, List.append_assoc]
          rfl

/-- **`@[csimp]` Verified Kernel Replacement (`addMerge → addMergeTR`)**:
    Replaces recursive `addMerge` at compile time with single-comparison, zero-GCD,
    tail-recursive `addMergeTR` while keeping all existing proofs unchanged. -/
@[csimp] theorem addMerge_eq_addMergeTR : @addMerge = @addMergeTR := by
  funext xs ys
  simpa [addMergeTR] using (addMergeTRLoop_eq xs ys []).symm

/-! ### Verified Refactor 3A: Balanced-Tree Sparse Multiplication -/

/-- Multiply a canonical term list by a single term `(e0, c0)` in `O(m)` time,
    preserving strict descending order. -/
def scaleTerm (e0 c0 : Rat) (ys : TermList) : TermList :=
  if c0 == 0 then []
  else ys.map (fun (ey, cy) => (e0 + ey, c0 * cy))

/-- Tail-recursive zero-GCD scaling loop compiled via `@[csimp]` for `scaleTerm`. -/
def scaleTermTRLoop (e0 c0 : Rat) : TermList → TermList → TermList
  | [], acc => acc.reverse
  | (ey, cy) :: rest, acc =>
    scaleTermTRLoop e0 c0 rest ((ratAddFast e0 ey, ratMulFast c0 cy) :: acc)

/-- Compiled tail-recursive entry point for `scaleTerm`. -/
@[inline] def scaleTermTR (e0 c0 : Rat) (ys : TermList) : TermList :=
  if c0.num == 0 then []
  else scaleTermTRLoop e0 c0 ys []

private theorem scaleTermTRLoop_eq (e0 c0 : Rat) (ys acc : TermList) :
    scaleTermTRLoop e0 c0 ys acc = acc.reverse ++ ys.map (fun (ey, cy) => (e0 + ey, c0 * cy)) := by
  induction ys generalizing acc with
  | nil => simp [scaleTermTRLoop]
  | cons p rest ih =>
    rcases p with ⟨ey, cy⟩
    simp only [scaleTermTRLoop, List.map_cons, ratAddFast_eq, ratMulFast_eq]
    rw [ih ((e0 + ey, c0 * cy) :: acc), List.reverse_cons, List.append_assoc]
    rfl

/-- **`@[csimp]` Verified Kernel Replacement (`scaleTerm → scaleTermTR`)**:
    Replaces `scaleTerm` with tail-recursive, zero-GCD `scaleTermTR` at compile time. -/
@[csimp] theorem scaleTerm_eq_scaleTermTR : @scaleTerm = @scaleTermTR := by
  funext e0 c0 ys
  unfold scaleTerm scaleTermTR
  rw [rat_num_beq_zero_eq]
  split
  · rfl
  · simpa using (scaleTermTRLoop_eq e0 c0 ys []).symm

/-- `scaleTerm` shifts the `AllLt` bound by `+ e0`. -/
theorem scaleTerm_allLt {b e0 c0 : Rat} {ys : TermList} (h : AllLt b ys) :
    AllLt (e0 + b) (scaleTerm e0 c0 ys) := by
  unfold scaleTerm
  split
  · trivial
  · induction ys with
    | nil => trivial
    | cons p rest ih =>
      rcases p with ⟨ey, cy⟩
      exact ⟨rat_add_lt_add_left_of_lt h.1, ih h.2⟩

/-- `scaleTerm` preserves canonical well-formedness. -/
theorem scaleTerm_wf {e0 c0 : Rat} {ys : TermList} (hys : WF ys) :
    WF (scaleTerm e0 c0 ys) := by
  unfold scaleTerm
  split
  · trivial
  · rename_i hnz
    have hc0 : c0 ≠ 0 := by intro h; simp [h] at hnz
    induction ys with
    | nil => trivial
    | cons p rest ih =>
      rcases p with ⟨ey, cy⟩
      refine ⟨rat_mul_ne_zero hc0 hys.1, ?_, ih hys.2.2⟩
      have hlt := scaleTerm_allLt (e0 := e0) (c0 := c0) hys.2.1
      simpa [scaleTerm, hnz] using hlt

/-- `scaleTerm` scales and shifts `coeffOf` by `(e0, c0)`. -/
theorem coeffOf_scaleTerm (e0 c0 : Rat) (ys : TermList) (e : Rat) :
    coeffOf (scaleTerm e0 c0 ys) e = c0 * coeffOf ys (e - e0) := by
  unfold scaleTerm
  split
  · rename_i hz
    have hc0 : c0 = 0 := eq_of_beq hz
    simp [coeffOf, hc0]
  · induction ys with
    | nil => simp [coeffOf]
    | cons p rest ih =>
      rcases p with ⟨ey, cy⟩
      simp only [List.map_cons, coeffOf, ih, Rat.mul_add]
      have hiff : (e0 + ey == e) = (ey == e - e0) := by
        cases h1 : (e0 + ey == e) <;> cases h2 : (ey == e - e0) <;> try rfl
        · have heq : ey = e - e0 := eq_of_beq h2
          have : e0 + ey = e := by grind
          simp [this] at h1
        · have heq : e0 + ey = e := eq_of_beq h1
          have : ey = e - e0 := by grind
          simp [this] at h2
      rw [hiff]
      split <;> simp [Rat.mul_zero]

/-- Direct `O(n * m)` naive reference multiplication (unmerged Cartesian product). -/
def mulNaiveTerms (xs ys : TermList) : TermList :=
  xs.foldr (fun (ex, cx) acc =>
    (ys.map (fun (ey, cy) => (ex + ey, cx * cy))) ++ acc) []

/-- Naive multiplication by empty list has zero coefficients. -/
theorem coeffOf_mulNaiveTerms_nil (ys : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms [] ys) e = 0 := rfl

/-- Convolution step for `mulNaiveTerms`. -/
theorem coeffOf_mulNaiveTerms_cons (ex cx : Rat) (xs ys : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms ((ex, cx) :: xs) ys) e =
      cx * coeffOf ys (e - ex) + coeffOf (mulNaiveTerms xs ys) e := by
  simp only [mulNaiveTerms, List.foldr_cons, coeffOf_append]
  congr 1
  induction ys with
  | nil => simp [coeffOf]
  | cons p rest ih =>
    rcases p with ⟨ey, cy⟩
    simp only [List.map_cons, coeffOf, ih, Rat.mul_add]
    have hiff : (ex + ey == e) = (ey == e - ex) := by
      cases h1 : (ex + ey == e) <;> cases h2 : (ey == e - ex) <;> try rfl
      · have heq : ey = e - ex := eq_of_beq h2
        have : ex + ey = e := by grind
        simp [this] at h1
      · have heq : ex + ey = e := eq_of_beq h1
        have : ey = e - ex := by grind
        simp [this] at h2
    rw [hiff]
    split <;> simp [Rat.mul_zero]

/-- `mulNaiveTerms` respects semantic equivalence in its right operand. -/
theorem coeffOf_mulNaiveTerms_congr_right {xs ys₁ ys₂ : TermList}
    (hy : ∀ e, coeffOf ys₁ e = coeffOf ys₂ e) (e : Rat) :
    coeffOf (mulNaiveTerms xs ys₁) e = coeffOf (mulNaiveTerms xs ys₂) e := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    rw [coeffOf_mulNaiveTerms_cons, coeffOf_mulNaiveTerms_cons, hy (e - ex), ih]

private theorem coeffOf_mulNaiveTerms_nil_right (xs : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms xs []) e = 0 := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    rw [coeffOf_mulNaiveTerms_cons, coeffOf, Rat.mul_zero, Rat.zero_add, ih]

private theorem coeffOf_mulNaiveTerms_cons_right (xs : TermList) (ey cy : Rat)
    (ys : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms xs ((ey, cy) :: ys)) e =
      cy * coeffOf xs (e - ey) + coeffOf (mulNaiveTerms xs ys) e := by
  induction xs with
  | nil => simp [coeffOf_mulNaiveTerms_nil, coeffOf, Rat.mul_zero, Rat.add_zero]
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    rw [coeffOf_mulNaiveTerms_cons, coeffOf_mulNaiveTerms_cons, ih]
    simp only [coeffOf]
    have hiff : (ey == e - ex) = (ex == e - ey) := by
      cases h1 : (ey == e - ex) <;> cases h2 : (ex == e - ey) <;> try rfl
      · have : ex = e - ey := eq_of_beq h2
        have : ey = e - ex := by grind
        simp [this] at h1
      · have : ey = e - ex := eq_of_beq h1
        have : ex = e - ey := by grind
        simp [this] at h2
    rw [hiff]
    split <;> grind

/-- Commutativity of Levi-Civita multiplication on `coeffOf`. -/
theorem coeffOf_mulNaiveTerms_comm (xs ys : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms xs ys) e = coeffOf (mulNaiveTerms ys xs) e := by
  induction ys with
  | nil =>
    rw [coeffOf_mulNaiveTerms_nil_right, coeffOf_mulNaiveTerms_nil]
  | cons p rest ih =>
    rcases p with ⟨ey, cy⟩
    rw [coeffOf_mulNaiveTerms_cons_right, coeffOf_mulNaiveTerms_cons, ih]

/-- `mulNaiveTerms` respects semantic equivalence in its left operand. -/
theorem coeffOf_mulNaiveTerms_congr_left {xs₁ xs₂ ys : TermList}
    (hx : ∀ e, coeffOf xs₁ e = coeffOf xs₂ e) (e : Rat) :
    coeffOf (mulNaiveTerms xs₁ ys) e = coeffOf (mulNaiveTerms xs₂ ys) e := by
  rw [coeffOf_mulNaiveTerms_comm, coeffOf_mulNaiveTerms_congr_right hx, coeffOf_mulNaiveTerms_comm]

/-- Left distributivity of `mulNaiveTerms` over concatenation. -/
theorem coeffOf_mulNaiveTerms_add_left (xs₁ xs₂ ys : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms (xs₁ ++ xs₂) ys) e =
      coeffOf (mulNaiveTerms xs₁ ys) e + coeffOf (mulNaiveTerms xs₂ ys) e := by
  induction xs₁ with
  | nil => simp [coeffOf_mulNaiveTerms_nil, Rat.zero_add]
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    simp only [List.cons_append, coeffOf_mulNaiveTerms_cons, ih, Rat.add_assoc]

/-- `mulNaiveTerms` commutes with `scaleTerm` on the left. -/
theorem coeffOf_mulNaiveTerms_scaleTerm_left (e0 c0 : Rat) (xs ys : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms (scaleTerm e0 c0 xs) ys) e =
      c0 * coeffOf (mulNaiveTerms xs ys) (e - e0) := by
  unfold scaleTerm
  split
  · rename_i hz
    have hc0 : c0 = 0 := eq_of_beq hz
    simp [coeffOf_mulNaiveTerms_nil, hc0]
  · induction xs with
    | nil => simp [coeffOf_mulNaiveTerms_nil]
    | cons p rest ih =>
      rcases p with ⟨ex, cx⟩
      simp only [List.map_cons, coeffOf_mulNaiveTerms_cons, ih, Rat.mul_add]
      congr 1
      have hsub : e - (e0 + ex) = (e - e0) - ex := by grind
      rw [hsub, Rat.mul_assoc]

private theorem coeffOf_mulNaiveTerms_zeroMap_left (ex : Rat) (ys zs : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms (ys.map (fun (ey, cy) => (ex + ey, (0 : Rat) * cy))) zs) e = 0 := by
  induction ys with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨ey, cy⟩
    change coeffOf (mulNaiveTerms ((ex + ey, 0 * cy) :: rest.map (fun (ey, cy) => (ex + ey, (0 : Rat) * cy))) zs) e = 0
    rw [coeffOf_mulNaiveTerms_cons, Rat.zero_mul, Rat.zero_mul, Rat.zero_add]
    exact ih

/-- Associativity of Levi-Civita multiplication on `coeffOf`. -/
theorem coeffOf_mulNaiveTerms_assoc (xs ys zs : TermList) (e : Rat) :
    coeffOf (mulNaiveTerms (mulNaiveTerms xs ys) zs) e =
      coeffOf (mulNaiveTerms xs (mulNaiveTerms ys zs)) e := by
  induction xs generalizing e with
  | nil => rfl
  | cons px restx ih =>
    rcases px with ⟨ex, cx⟩
    have hcons : mulNaiveTerms ((ex, cx) :: restx) ys =
        (ys.map (fun (ey, cy) => (ex + ey, cx * cy))) ++ mulNaiveTerms restx ys := rfl
    rw [hcons, coeffOf_mulNaiveTerms_add_left, coeffOf_mulNaiveTerms_cons, ih e]
    congr 1
    by_cases hcx : cx = 0
    · subst hcx
      rw [Rat.zero_mul]
      exact coeffOf_mulNaiveTerms_zeroMap_left ex ys zs e
    · have hsc : ys.map (fun (ey, cy) => (ex + ey, cx * cy)) = scaleTerm ex cx ys := by
        have hnz : (cx == 0) = false := by
          cases hb : (cx == 0)
          · rfl
          · exact absurd (eq_of_beq hb) hcx
        simp [scaleTerm, hnz]
      rw [hsc, coeffOf_mulNaiveTerms_scaleTerm_left]

/-- Pairwise pass of a balanced binary-tree merge over sorted term lists. -/
def mergePairs : List TermList → List TermList
  | [] => []
  | [x] => [x]
  | x :: y :: rest => addMerge x y :: mergePairs rest

/-- Every pairwise merge pass strictly shrinks lists of length at least `2`. -/
theorem mergePairs_length_lt {l : List TermList} (h : 1 < l.length) :
    (mergePairs l).length < l.length := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: rest =>
    simp only [mergePairs, List.length_cons]
    cases rest with
    | nil => simp [mergePairs]
    | cons a rest2 =>
      cases rest2 with
      | nil => simp [mergePairs]
      | cons b rest3 =>
        have hrec := mergePairs_length_lt (l := a :: b :: rest3) (by simp)
        omega

/-- Sum of `coeffOf` across a list of term lists. -/
def sumCoeffOf : List TermList → Rat → Rat
  | [], _ => 0
  | x :: rest, e => coeffOf x e + sumCoeffOf rest e

/-- `mergePairs` preserves the total coefficient sum at every exponent `e`. -/
theorem sumCoeffOf_mergePairs (l : List TermList) (e : Rat) :
    sumCoeffOf (mergePairs l) e = sumCoeffOf l e := by
  match l with
  | [] => rfl
  | [x] => rfl
  | x :: y :: rest =>
    simp only [mergePairs, sumCoeffOf, coeffOf_addMerge, sumCoeffOf_mergePairs rest e, Rat.add_assoc]

/-- `mergePairs` preserves well-formedness across all lists. -/
theorem mergePairs_wf {l : List TermList} (h : ∀ t ∈ l, WF t) :
    ∀ t ∈ mergePairs l, WF t := by
  match l with
  | [] => intro t ht; simp [mergePairs] at ht
  | [x] => intro t ht; exact h t ht
  | x :: y :: rest =>
    intro t ht
    simp only [mergePairs, List.mem_cons] at ht
    rcases ht with rfl | ht'
    · exact addMerge_wf (h x (by simp)) (h y (by simp))
    · exact mergePairs_wf (fun u hu => h u (by simp [hu])) t ht'

/-- Balanced binary-tree merge of `n` sorted term lists in `O(total_terms * log n)`. -/
def mergeAll : List TermList → TermList
  | [] => []
  | [x] => x
  | x :: y :: rest =>
    have : (mergePairs (x :: y :: rest)).length < (x :: y :: rest).length :=
      mergePairs_length_lt (by simp)
    mergeAll (mergePairs (x :: y :: rest))
termination_by l => l.length

/-- `mergeAll` produces a canonical well-formed term list. -/
theorem mergeAll_wf {l : List TermList} (h : ∀ t ∈ l, WF t) : WF (mergeAll l) := by
  match l with
  | [] => simp [mergeAll, WF]
  | [x] => simp [mergeAll]; exact h x (by simp)
  | x :: y :: rest =>
    have : (mergePairs (x :: y :: rest)).length < (x :: y :: rest).length :=
      mergePairs_length_lt (by simp)
    rw [mergeAll]
    exact mergeAll_wf (mergePairs_wf h)
termination_by l.length

/-- `mergeAll` equals the coefficient sum of its input lists at every exponent `e`. -/
theorem coeffOf_mergeAll (l : List TermList) (e : Rat) :
    coeffOf (mergeAll l) e = sumCoeffOf l e := by
  match l with
  | [] => simp [mergeAll, coeffOf, sumCoeffOf]
  | [x] => simp [mergeAll, sumCoeffOf, Rat.add_zero]
  | x :: y :: rest =>
    have : (mergePairs (x :: y :: rest)).length < (x :: y :: rest).length :=
      mergePairs_length_lt (by simp)
    rw [mergeAll, coeffOf_mergeAll (mergePairs (x :: y :: rest)) e, sumCoeffOf_mergePairs]
termination_by l.length

/-- Verified sparse multiplication: short-circuits empty/singleton operands in `O(n)`
    and maps the shorter operand so balanced-tree merging runs in `O(nm log min(n, m))`. -/
def mulTree (xs ys : TermList) : TermList :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | [(ex, cx)], ys => scaleTerm ex cx ys
  | xs, [(ey, cy)] => scaleTerm ey cy xs
  | xs, ys =>
    if xs.length ≤ ys.length then
      mergeAll (xs.map (fun (ex, cx) => scaleTerm ex cx ys))
    else
      mergeAll (ys.map (fun (ey, cy) => scaleTerm ey cy xs))

/-- `mulTree` preserves canonical well-formedness. -/
theorem mulTree_wf {xs ys : TermList} (hxs : WF xs) (hys : WF ys) : WF (mulTree xs ys) := by
  unfold mulTree
  split
  · trivial
  · trivial
  · exact scaleTerm_wf hys
  · exact scaleTerm_wf hxs
  · split
    · apply mergeAll_wf
      intro t ht
      rcases List.mem_map.mp ht with ⟨⟨ex, cx⟩, _, rfl⟩
      exact scaleTerm_wf hys
    · apply mergeAll_wf
      intro t ht
      rcases List.mem_map.mp ht with ⟨⟨ey, cy⟩, _, rfl⟩
      exact scaleTerm_wf hxs

/-- Sum of shifted runs equals naive multiplication at every exponent `e`. -/
theorem sumCoeffOf_scaleRuns (xs ys : TermList) (e : Rat) :
    sumCoeffOf (xs.map (fun (ex, cx) => scaleTerm ex cx ys)) e =
      coeffOf (mulNaiveTerms xs ys) e := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    simp only [List.map_cons, sumCoeffOf, coeffOf_scaleTerm, ih, coeffOf_mulNaiveTerms_cons]

/-- Formal equivalence theorem: `mulTree` computes the exact same mathematical Levi-Civita
    product as naive `O(nm)` multiplication at every rational exponent `e`. -/
theorem coeffOf_mulTree (xs ys : TermList) (e : Rat) :
    coeffOf (mulTree xs ys) e = coeffOf (mulNaiveTerms xs ys) e := by
  unfold mulTree
  split
  · rfl
  · rw [coeffOf_mulNaiveTerms_comm]; rfl
  · rename_i ex cx ys'
    rw [coeffOf_scaleTerm, coeffOf_mulNaiveTerms_cons, coeffOf_mulNaiveTerms_nil, Rat.add_zero]
  · rename_i xs' ey cy _
    rw [coeffOf_scaleTerm, coeffOf_mulNaiveTerms_comm, coeffOf_mulNaiveTerms_cons,
        coeffOf_mulNaiveTerms_nil, Rat.add_zero]
  · split
    · rw [coeffOf_mergeAll, sumCoeffOf_scaleRuns]
    · rw [coeffOf_mergeAll, sumCoeffOf_scaleRuns, coeffOf_mulNaiveTerms_comm]

/-! ### Contiguous `Array`-Backed Sparse Merge (`@[csimp]` Kernel for `mulTree`, Rung 4) -/

/-- Append `src[i..]` onto `acc` in a tight contiguous array push loop. -/
def appendSliceArr (src : Array (Rat × Rat)) (i : Nat) (acc : Array (Rat × Rat)) :
    Array (Rat × Rat) :=
  if hi : i < src.size then
    appendSliceArr src (i + 1) (acc.push src[i])
  else
    acc
termination_by src.size - i

private theorem appendSliceArr_toList (src : Array (Rat × Rat)) (i : Nat)
    (acc : Array (Rat × Rat)) :
    (appendSliceArr src i acc).toList = acc.toList ++ src.toList.drop i := by
  unfold appendSliceArr
  split
  · rename_i hi
    rw [appendSliceArr_toList src (i + 1) (acc.push src[i]), Array.toList_push, List.append_assoc]
    have hdrop : src.toList.drop i = src[i] :: src.toList.drop (i + 1) := by
      have hi' : i < src.toList.length := by simpa using hi
      simpa using List.drop_eq_getElem_cons hi'
    rw [hdrop]
    rfl
  · rename_i hge
    have hdrop : src.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [hdrop]
termination_by src.size - i

/-- Contiguous array scaling loop (zero cons cells, zero `List.reverse`). -/
def scaleTermArrLoop (e0 c0 : Rat) (ys : Array (Rat × Rat)) (i : Nat)
    (acc : Array (Rat × Rat)) : Array (Rat × Rat) :=
  if hi : i < ys.size then
    let p := ys[i]
    scaleTermArrLoop e0 c0 ys (i + 1) (acc.push (ratAddFast e0 p.1, ratMulFast c0 p.2))
  else
    acc
termination_by ys.size - i

/-- Contiguous `Array` version of `scaleTerm`. -/
@[inline] def scaleTermArr (e0 c0 : Rat) (ys : Array (Rat × Rat)) : Array (Rat × Rat) :=
  if c0.num == 0 then #[]
  else scaleTermArrLoop e0 c0 ys 0 (Array.mkEmpty ys.size)

private theorem scaleTermArrLoop_toList (e0 c0 : Rat) (ys : Array (Rat × Rat)) (i : Nat)
    (acc : Array (Rat × Rat)) :
    (scaleTermArrLoop e0 c0 ys i acc).toList =
      acc.toList ++ (ys.toList.drop i).map (fun (ey, cy) => (e0 + ey, c0 * cy)) := by
  unfold scaleTermArrLoop
  split
  · rename_i hi
    dsimp only
    rw [scaleTermArrLoop_toList e0 c0 ys (i + 1), Array.toList_push, List.append_assoc]
    have hdrop : ys.toList.drop i = ys[i] :: ys.toList.drop (i + 1) := by
      have hi' : i < ys.toList.length := by simpa using hi
      simpa using List.drop_eq_getElem_cons hi'
    rw [hdrop, List.map_cons, ratAddFast_eq, ratMulFast_eq]
    rfl
  · rename_i hge
    have hdrop : ys.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [hdrop]
termination_by ys.size - i

private theorem scaleTermArr_toList (e0 c0 : Rat) (ys : Array (Rat × Rat)) :
    (scaleTermArr e0 c0 ys).toList = scaleTerm e0 c0 ys.toList := by
  unfold scaleTermArr scaleTerm
  rw [rat_num_beq_zero_eq]
  split
  · rfl
  · simpa using scaleTermArrLoop_toList e0 c0 ys 0 (Array.mkEmpty ys.size)

/-- Contiguous two-pointer sorted merge over `Array (Rat × Rat)` (zero cons cells, zero reverse). -/
def mergeArrLoop (xs ys : Array (Rat × Rat)) (i j : Nat) (acc : Array (Rat × Rat)) :
    Array (Rat × Rat) :=
  if hi : i < xs.size then
    if hj : j < ys.size then
      let px := xs[i]
      let py := ys[j]
      match ratCmpFast px.1 py.1 with
      | .gt => mergeArrLoop xs ys (i + 1) j (acc.push px)
      | .lt => mergeArrLoop xs ys i (j + 1) (acc.push py)
      | .eq =>
        let s := ratAddFast px.2 py.2
        if s.num == 0 then mergeArrLoop xs ys (i + 1) (j + 1) acc
        else mergeArrLoop xs ys (i + 1) (j + 1) (acc.push (px.1, s))
    else
      appendSliceArr xs i acc
  else
    appendSliceArr ys j acc
termination_by (xs.size - i) + (ys.size - j)

/-- Contiguous `Array` version of `addMerge`. -/
@[inline] def mergeArr (xs ys : Array (Rat × Rat)) : Array (Rat × Rat) :=
  mergeArrLoop xs ys 0 0 (Array.mkEmpty (xs.size + ys.size))

private theorem mergeArrLoop_toList (xs ys : Array (Rat × Rat)) (i j : Nat)
    (acc : Array (Rat × Rat)) :
    (mergeArrLoop xs ys i j acc).toList =
      acc.toList ++ addMerge (xs.toList.drop i) (ys.toList.drop j) := by
  unfold mergeArrLoop
  split
  · rename_i hi
    have hxdrop : xs.toList.drop i = xs[i] :: xs.toList.drop (i + 1) := by
      have hi' : i < xs.toList.length := by simpa using hi
      simpa using List.drop_eq_getElem_cons hi'
    split
    · rename_i hj
      have hydrop : ys.toList.drop j = ys[j] :: ys.toList.drop (j + 1) := by
        have hj' : j < ys.toList.length := by simpa using hj
        simpa using List.drop_eq_getElem_cons hj'
      dsimp only
      rcases hpx : xs[i] with ⟨ex, cx⟩
      rcases hpy : ys[j] with ⟨ey, cy⟩
      rw [hpx] at hxdrop
      rw [hpy] at hydrop
      cases hcmp : ratCmpFast ex ey with
      | gt =>
        have hgt : ex > ey := (ratCmpFast_gt _ _).mp hcmp
        rw [mergeArrLoop_toList xs ys (i + 1) j (acc.push (ex, cx)), Array.toList_push,
            List.append_assoc, hxdrop, hydrop]
        simp only [addMerge, hgt, ↓reduceIte]
        rfl
      | lt =>
        have hlt : ey > ex := (ratCmpFast_lt _ _).mp hcmp
        have hngt : ¬ (ex > ey) := by grind
        rw [mergeArrLoop_toList xs ys i (j + 1) (acc.push (ey, cy)), Array.toList_push,
            List.append_assoc, hxdrop, hydrop]
        simp only [addMerge, hngt, hlt, ↓reduceIte]
        rfl
      | eq =>
        have hngt : ¬ (ex > ey) := by
          intro h; have := (ratCmpFast_gt _ _).mpr h; rw [hcmp] at this; cases this
        have hnlt : ¬ (ey > ex) := by
          intro h; have := (ratCmpFast_lt _ _).mpr h; rw [hcmp] at this; cases this
        rw [hxdrop, hydrop]
        simp only [addMerge, hngt, hnlt, ↓reduceIte, ratAddFast_eq, rat_num_beq_zero_eq]
        split
        · exact mergeArrLoop_toList xs ys (i + 1) (j + 1) acc
        · rw [mergeArrLoop_toList xs ys (i + 1) (j + 1), Array.toList_push, List.append_assoc]
          rfl
    · rename_i hnj
      have hydrop : ys.toList.drop j = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [appendSliceArr_toList, hydrop, hxdrop]
      simp [addMerge]
  · rename_i hni
    have hxdrop : xs.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [appendSliceArr_toList, hxdrop]
    simp [addMerge]
termination_by (xs.size - i) + (ys.size - j)

private theorem mergeArr_toList (xs ys : Array (Rat × Rat)) :
    (mergeArr xs ys).toList = addMerge xs.toList ys.toList := by
  simpa [mergeArr] using mergeArrLoop_toList xs ys 0 0 (Array.mkEmpty (xs.size + ys.size))

/-- Pairwise balanced-tree merge pass over contiguous `Array` runs. -/
def mergePairsArr : List (Array (Rat × Rat)) → List (Array (Rat × Rat))
  | [] => []
  | [x] => [x]
  | x :: y :: rest => mergeArr x y :: mergePairsArr rest

private theorem mergePairsArr_length_lt {l : List (Array (Rat × Rat))} (h : 1 < l.length) :
    (mergePairsArr l).length < l.length := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | _ :: _ :: rest =>
    simp only [mergePairsArr, List.length_cons]
    cases rest with
    | nil => simp [mergePairsArr]
    | cons a rest2 =>
      cases rest2 with
      | nil => simp [mergePairsArr]
      | cons b rest3 =>
        have hrec := mergePairsArr_length_lt (l := a :: b :: rest3) (by simp)
        omega

private theorem mergePairsArr_map_toList (l : List (Array (Rat × Rat))) :
    (mergePairsArr l).map Array.toList = mergePairs (l.map Array.toList) := by
  match l with
  | [] => rfl
  | [x] => rfl
  | x :: y :: rest =>
    simp only [mergePairsArr, List.map_cons, mergePairs, mergeArr_toList,
      mergePairsArr_map_toList rest]

/-- Balanced binary-tree merge over contiguous `Array` runs. -/
def mergeAllArr : List (Array (Rat × Rat)) → Array (Rat × Rat)
  | [] => #[]
  | [x] => x
  | x :: y :: rest =>
    have : (mergePairsArr (x :: y :: rest)).length < (x :: y :: rest).length :=
      mergePairsArr_length_lt (by simp)
    mergeAllArr (mergePairsArr (x :: y :: rest))
termination_by l => l.length

private theorem mergeAllArr_toList (l : List (Array (Rat × Rat))) :
    (mergeAllArr l).toList = mergeAll (l.map Array.toList) := by
  match l with
  | [] => simp [mergeAllArr, mergeAll]
  | [x] => simp [mergeAllArr, mergeAll]
  | x :: y :: rest =>
    have : (mergePairsArr (x :: y :: rest)).length < (x :: y :: rest).length :=
      mergePairsArr_length_lt (by simp)
    rw [mergeAllArr, mergeAllArr_toList (mergePairsArr (x :: y :: rest)),
        mergePairsArr_map_toList]
    simp [mergeAll]
termination_by l.length

/-- Compiled contiguous-`Array` kernel for `mulTree` (zero intermediate cons cells or reverses). -/
def mulTreeArr (xs ys : TermList) : TermList :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | [(ex, cx)], ys => scaleTerm ex cx ys
  | xs, [(ey, cy)] => scaleTerm ey cy xs
  | xs, ys =>
    if xs.length ≤ ys.length then
      let ysArr := ys.toArray
      (mergeAllArr (xs.map (fun (ex, cx) => scaleTermArr ex cx ysArr))).toList
    else
      let xsArr := xs.toArray
      (mergeAllArr (ys.map (fun (ey, cy) => scaleTermArr ey cy xsArr))).toList

/-- **`@[csimp]` Verified Kernel Replacement (`mulTree → mulTreeArr`)**:
    Replaces linked-list balanced merging inside `mulTree` with contiguous `Array` merging
    at compile time while keeping all proofs completely unchanged. -/
@[csimp] theorem mulTree_eq_mulTreeArr : @mulTree = @mulTreeArr := by
  funext xs ys
  unfold mulTree mulTreeArr
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · split
    · rw [mergeAllArr_toList, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      rcases p with ⟨ex, cx⟩
      simpa using (scaleTermArr_toList ex cx ys.toArray).symm
    · rw [mergeAllArr_toList, List.map_map]
      congr 1
      apply List.map_congr_left
      intro p _
      rcases p with ⟨ey, cy⟩
      simpa using (scaleTermArr_toList ey cy xs.toArray).symm

/-! ### Sorting & Truncation Helpers -/

/-- Insert a single `(e, c)` pair into a canonical term list while preserving `WF`. -/
def insertTerm (e c : Rat) (ts : TermList) : TermList :=
  if c == 0 then ts else addMerge [(e, c)] ts

/-- `insertTerm` preserves canonical well-formedness. -/
theorem insertTerm_wf {e c : Rat} {ts : TermList} (hts : WF ts) : WF (insertTerm e c ts) := by
  unfold insertTerm
  split
  · exact hts
  · rename_i hnz
    have hc : c ≠ 0 := by intro h; simp [h] at hnz
    exact addMerge_wf ⟨hc, trivial, trivial⟩ hts

/-- `insertTerm` adds `c` at exponent `e0` and leaves all other exponents unchanged. -/
theorem coeffOf_insertTerm (e0 c0 : Rat) (ts : TermList) (e : Rat) :
    coeffOf (insertTerm e0 c0 ts) e = (if e0 == e then c0 else 0) + coeffOf ts e := by
  unfold insertTerm
  split
  · rename_i hz
    have hc0 : c0 = 0 := eq_of_beq hz
    split <;> simp [hc0, Rat.zero_add]
  · rw [coeffOf_addMerge]
    simp [coeffOf, Rat.add_zero]

/-- Canonicalize an arbitrary term list into a `WF` strictly-descending list with no zeros. -/
def normalize (ts : TermList) : TermList :=
  mergeAll (ts.map (fun (e, c) => if c == 0 then [] else [(e, c)]))

/-- `normalize` always produces a well-formed term list. -/
theorem normalize_wf (ts : TermList) : WF (normalize ts) := by
  apply mergeAll_wf
  intro t ht
  rcases List.mem_map.mp ht with ⟨p, _, rfl⟩
  rcases p with ⟨e, c⟩
  dsimp only
  split
  · trivial
  · rename_i hnz
    have hc : c ≠ 0 := by intro h; simp [h] at hnz
    exact ⟨hc, trivial, trivial⟩

/-- `normalize` preserves `coeffOf` at every exponent `e`. -/
theorem coeffOf_normalize (ts : TermList) (e : Rat) :
    coeffOf (normalize ts) e = coeffOf ts e := by
  rw [normalize, coeffOf_mergeAll]
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨e', c⟩
    simp only [List.map_cons, sumCoeffOf, coeffOf, ih]
    congr 1
    split
    · rename_i hz
      have hc : c = 0 := eq_of_beq hz
      split <;> simp [coeffOf, hc]
    · simp [coeffOf, Rat.add_zero]

/-- Truncate a canonical term list to its `n` largest-exponent terms (preserves `WF`). -/
def truncate (n : Nat) (ts : TermList) : TermList :=
  ts.take n

/-- Taking a prefix preserves `AllLt`. -/
theorem allLt_take {b : Rat} {ts : TermList} (n : Nat) (h : AllLt b ts) :
    AllLt b (ts.take n) := by
  induction ts generalizing n with
  | nil => simp [AllLt]
  | cons p rest ih =>
    cases n with
    | zero => trivial
    | succ k =>
      rcases p with ⟨e, c⟩
      exact ⟨h.1, ih k h.2⟩

/-- `truncate` preserves canonical well-formedness. -/
theorem truncate_wf {ts : TermList} (n : Nat) (h : WF ts) : WF (truncate n ts) := by
  unfold truncate
  induction ts generalizing n with
  | nil => simp [WF]
  | cons p rest ih =>
    cases n with
    | zero => trivial
    | succ k =>
      rcases p with ⟨e, c⟩
      exact ⟨h.1, allLt_take k h.2.1, ih k h.2.2⟩

/-- `O(k)` prefix drop of terms below `minExp` on a canonical strictly-descending `TermList`.
    Replaces `O(k log k)` `normalize ∘ filter` in `FastLC.dropBelow`. -/
def takeWhileGe (minExp : Rat) : TermList → TermList
  | [] => []
  | (e, c) :: rest =>
    if e ≥ minExp then (e, c) :: takeWhileGe minExp rest else []

/-- Tail-recursive single-comparison loop compiled via `@[csimp]` for `takeWhileGe`. -/
def takeWhileGeTRLoop (minExp : Rat) : TermList → TermList → TermList
  | [], acc => acc.reverse
  | (e, c) :: rest, acc =>
    match ratCmpFast e minExp with
    | .lt => acc.reverse
    | _ => takeWhileGeTRLoop minExp rest ((e, c) :: acc)

/-- Compiled tail-recursive entry point for `takeWhileGe`. -/
@[inline] def takeWhileGeTR (minExp : Rat) (ts : TermList) : TermList :=
  takeWhileGeTRLoop minExp ts []

private theorem takeWhileGeTRLoop_eq (minExp : Rat) (ts acc : TermList) :
    takeWhileGeTRLoop minExp ts acc = acc.reverse ++ takeWhileGe minExp ts := by
  induction ts generalizing acc with
  | nil => simp [takeWhileGeTRLoop, takeWhileGe]
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [takeWhileGeTRLoop, takeWhileGe]
    cases hcmp : ratCmpFast e minExp with
    | lt =>
      have hlt : minExp > e := (ratCmpFast_lt e minExp).mp hcmp
      have hnge : ¬ (e ≥ minExp) := by grind
      simp [hnge]
    | gt =>
      have hgt : e > minExp := (ratCmpFast_gt e minExp).mp hcmp
      have hge : e ≥ minExp := by grind
      simp only [hge, ↓reduceIte]
      rw [ih ((e, c) :: acc), List.reverse_cons, List.append_assoc]
      rfl
    | eq =>
      have hnlt : ¬ (minExp > e) := by
        intro h; have := (ratCmpFast_lt e minExp).mpr h; rw [hcmp] at this; cases this
      have hge : e ≥ minExp := by grind
      simp only [hge, ↓reduceIte]
      rw [ih ((e, c) :: acc), List.reverse_cons, List.append_assoc]
      rfl

/-- **`@[csimp]` Verified Kernel Replacement (`takeWhileGe → takeWhileGeTR`)**. -/
@[csimp] theorem takeWhileGe_eq_takeWhileGeTR : @takeWhileGe = @takeWhileGeTR := by
  funext minExp ts
  simpa [takeWhileGeTR] using (takeWhileGeTRLoop_eq minExp ts []).symm

/-- `takeWhileGe` preserves `AllLt`. -/
theorem takeWhileGe_allLt {b : Rat} (minExp : Rat) {ts : TermList} (h : AllLt b ts) :
    AllLt b (takeWhileGe minExp ts) := by
  induction ts with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [takeWhileGe]
    split
    · exact ⟨h.1, ih h.2⟩
    · trivial

/-- `takeWhileGe` preserves canonical well-formedness. -/
theorem takeWhileGe_wf (minExp : Rat) {ts : TermList} (h : WF ts) :
    WF (takeWhileGe minExp ts) := by
  induction ts with
  | nil => trivial
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [takeWhileGe]
    split
    · exact ⟨h.1, takeWhileGe_allLt minExp h.2.1, ih h.2.2⟩
    · trivial

/-- Exact coefficient specification of `takeWhileGe` on canonical `WF` term lists. -/
theorem coeffOf_takeWhileGe (minExp : Rat) {ts : TermList} (h : WF ts) (e : Rat) :
    coeffOf (takeWhileGe minExp ts) e = if e ≥ minExp then coeffOf ts e else 0 := by
  induction ts with
  | nil => simp [takeWhileGe, coeffOf]
  | cons p rest ih =>
    rcases p with ⟨e0, c0⟩
    simp only [takeWhileGe]
    split
    · rename_i he0
      simp only [coeffOf, ih h.2.2]
      by_cases hge : e ≥ minExp
      · simp [hge]
      · have hne : (e0 == e) = false := by
          cases hb : (e0 == e)
          · rfl
          · have : e0 = e := eq_of_beq hb; grind
        simp [hge, hne, Rat.zero_add]
    · rename_i hnge
      simp only [coeffOf]
      by_cases hge : e ≥ minExp
      · have hgt : e > e0 := by grind
        simp only [hge, ↓reduceIte]
        exact (coeffOf_eq_zero_of_gt_head h hgt).symm
      · simp [hge]

/-- `O(k)` prefix take of at most `maxTerms` terms strictly above `cutoff` (for `truncateRel`). -/
def takeWhileGt (cutoff : Rat) : Nat → TermList → TermList
  | 0, _ => []
  | _, [] => []
  | n + 1, (e, c) :: rest =>
    if e > cutoff then (e, c) :: takeWhileGt cutoff n rest else []

/-- `takeWhileGt` preserves `AllLt`. -/
theorem takeWhileGt_allLt {b : Rat} (cutoff : Rat) (n : Nat) {ts : TermList} (h : AllLt b ts) :
    AllLt b (takeWhileGt cutoff n ts) := by
  induction ts generalizing n with
  | nil => cases n <;> trivial
  | cons p rest ih =>
    cases n with
    | zero => trivial
    | succ k =>
      rcases p with ⟨e, c⟩
      simp only [takeWhileGt]
      split
      · exact ⟨h.1, ih k h.2⟩
      · trivial

/-- `takeWhileGt` preserves canonical well-formedness. -/
theorem takeWhileGt_wf (cutoff : Rat) (n : Nat) {ts : TermList} (h : WF ts) :
    WF (takeWhileGt cutoff n ts) := by
  induction ts generalizing n with
  | nil => cases n <;> trivial
  | cons p rest ih =>
    cases n with
    | zero => trivial
    | succ k =>
      rcases p with ⟨e, c⟩
      simp only [takeWhileGt]
      split
      · exact ⟨h.1, takeWhileGt_allLt cutoff k h.2.1, ih k h.2.2⟩
      · trivial

end TermList

end LeanInf
