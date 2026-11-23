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

/-- Tail-recursive early-exit coefficient lookup exploiting canonical strictly-descending `WF`
    order (stops immediately once `e' ≤ e`, zero `Rat.add` calls, zero recursion stack). -/
def coeffOfWF : TermList → Rat → Rat
  | [], _ => 0
  | (e', c) :: rest, e =>
    match ratCmpFast e' e with
    | .gt => coeffOfWF rest e
    | .eq => c
    | .lt => 0

/-- `coeffOfWF` agrees identically with denotational `coeffOf` on every canonical `WF` list. -/
theorem coeffOfWF_eq_coeffOf {ts : TermList} (hwf : WF ts) (e : Rat) :
    coeffOfWF ts e = coeffOf ts e := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨e', c⟩
    simp only [coeffOfWF]
    cases hcmp : ratCmpFast e' e with
    | gt =>
      have hgt : e' > e := (ratCmpFast_gt e' e).mp hcmp
      have hne : (e' == e) = false := by
        cases hb : (e' == e)
        · rfl
        · have : e' = e := eq_of_beq hb; grind
      simp only [coeffOf, hne, Bool.false_eq_true, ↓reduceIte, Rat.zero_add]
      exact ih hwf.2.2
    | eq =>
      have hngt : ¬ (e' > e) := by
        intro h; have := (ratCmpFast_gt e' e).mpr h; rw [hcmp] at this; cases this
      have hnlt : ¬ (e > e') := by
        intro h; have := (ratCmpFast_lt e' e).mpr h; rw [hcmp] at this; cases this
      have heq : e' = e := rat_eq_of_not_gt_not_lt hngt hnlt
      subst heq
      exact (coeffOf_cons_head_of_wf hwf).symm
    | lt =>
      have hlt : e > e' := (ratCmpFast_lt e' e).mp hcmp
      exact (coeffOf_eq_zero_of_gt_head hwf hlt).symm

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

/-! ### Scaled Common-Denominator SOA Sparse Merge (Rung 6, zero `sorry`) -/

private theorem mkRat_one (n : Int) : mkRat n 1 = Rat.ofInt n := by
  apply Rat.ext <;> simp [Rat.num_mkRat, Rat.den_mkRat, Rat.ofInt]

private theorem mkRat_add_same_den (a b : Int) {d : Nat} (hd : d ≠ 0) :
    mkRat a d + mkRat b d = mkRat (a + b) d := by
  rw [Rat.mkRat_add_mkRat a b hd hd, ← Int.add_mul, Rat.mkRat_mul_right hd]

private theorem mkRat_lt_iff {a b : Int} {d : Nat} (hd : d ≠ 0) :
    mkRat a d < mkRat b d ↔ a < b := by
  have hdpos : (0 : Int) < (d : Int) := by omega
  have h1 : (mkRat a d).num * (d : Int) = a * ((mkRat a d).den : Int) :=
    ((Rat.mkRat_eq_iff hd (mkRat a d).den_nz).mp (Rat.mkRat_self _).symm).symm
  have h2 : (mkRat b d).num * (d : Int) = b * ((mkRat b d).den : Int) :=
    ((Rat.mkRat_eq_iff hd (mkRat b d).den_nz).mp (Rat.mkRat_self _).symm).symm
  have hda : (0 : Int) < ((mkRat a d).den : Int) := by
    have := Nat.pos_of_ne_zero (mkRat a d).den_nz; omega
  have hdb : (0 : Int) < ((mkRat b d).den : Int) := by
    have := Nat.pos_of_ne_zero (mkRat b d).den_nz; omega
  rw [Rat.lt_iff]
  constructor
  · intro hlt
    have hm : (mkRat a d).num * ((mkRat b d).den : Int) * (d : Int) <
        (mkRat b d).num * ((mkRat a d).den : Int) * (d : Int) :=
      Int.mul_lt_mul_of_pos_right hlt hdpos
    have hL : (mkRat a d).num * ((mkRat b d).den : Int) * (d : Int) =
        a * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by
      calc (mkRat a d).num * ((mkRat b d).den : Int) * (d : Int)
          = ((mkRat a d).num * (d : Int)) * ((mkRat b d).den : Int) := by grind
        _ = (a * ((mkRat a d).den : Int)) * ((mkRat b d).den : Int) := by rw [h1]
        _ = a * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by grind
    have hR : (mkRat b d).num * ((mkRat a d).den : Int) * (d : Int) =
        b * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by
      calc (mkRat b d).num * ((mkRat a d).den : Int) * (d : Int)
          = ((mkRat b d).num * (d : Int)) * ((mkRat a d).den : Int) := by grind
        _ = (b * ((mkRat b d).den : Int)) * ((mkRat a d).den : Int) := by rw [h2]
        _ = b * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by grind
    rw [hL, hR] at hm
    have hprod : (0 : Int) < ((mkRat a d).den : Int) * ((mkRat b d).den : Int) :=
      Int.mul_pos hda hdb
    exact Int.lt_of_mul_lt_mul_right hm (by omega)
  · intro hab
    have hprod : (0 : Int) < ((mkRat a d).den : Int) * ((mkRat b d).den : Int) :=
      Int.mul_pos hda hdb
    have hm : a * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) <
        b * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) :=
      Int.mul_lt_mul_of_pos_right hab hprod
    have hL : (mkRat a d).num * ((mkRat b d).den : Int) * (d : Int) =
        a * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by
      calc (mkRat a d).num * ((mkRat b d).den : Int) * (d : Int)
          = ((mkRat a d).num * (d : Int)) * ((mkRat b d).den : Int) := by grind
        _ = (a * ((mkRat a d).den : Int)) * ((mkRat b d).den : Int) := by rw [h1]
        _ = a * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by grind
    have hR : (mkRat b d).num * ((mkRat a d).den : Int) * (d : Int) =
        b * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by
      calc (mkRat b d).num * ((mkRat a d).den : Int) * (d : Int)
          = ((mkRat b d).num * (d : Int)) * ((mkRat a d).den : Int) := by grind
        _ = (b * ((mkRat b d).den : Int)) * ((mkRat a d).den : Int) := by rw [h2]
        _ = b * (((mkRat a d).den : Int) * ((mkRat b d).den : Int)) := by grind
    rw [← hL, ← hR] at hm
    exact Int.lt_of_mul_lt_mul_right hm (by omega)

private theorem mkRat_scaled_eq (r : Rat) {d : Nat} (hd : d ≠ 0) (hdvd : r.den ∣ d) :
    mkRat (r.num * Int.ofNat (d / r.den)) d = r := by
  have hk_mul : r.den * (d / r.den) = d := Nat.mul_div_cancel' hdvd
  have hk_nz : d / r.den ≠ 0 := by
    intro h0; rw [h0, Nat.mul_zero] at hk_mul; exact hd hk_mul.symm
  calc mkRat (r.num * Int.ofNat (d / r.den)) d
      = mkRat (r.num * ((d / r.den : Nat) : Int)) (r.den * (d / r.den)) := by rw [hk_mul]; rfl
    _ = mkRat r.num r.den := Rat.mkRat_mul_right hk_nz
    _ = r := Rat.mkRat_self r

/-- Compute bounded LCM of exponent denominators (`0` signals bound exceeded). -/
def scanExpLcm (maxDen : Nat) : TermList → Nat → Nat
  | [], acc => acc
  | (e, _) :: rest, acc =>
    let d := e.den
    if d == 1 || acc % d == 0 then
      scanExpLcm maxDen rest acc
    else
      let acc' := Nat.lcm acc d
      if acc' > maxDen then 0 else scanExpLcm maxDen rest acc'

/-- Compute bounded LCM of coefficient denominators (`0` signals bound exceeded). -/
def scanCoeffLcm (maxDen : Nat) : TermList → Nat → Nat
  | [], acc => acc
  | (_, c) :: rest, acc =>
    let d := c.den
    if d == 1 || acc % d == 0 then
      scanCoeffLcm maxDen rest acc
    else
      let acc' := Nat.lcm acc d
      if acc' > maxDen then 0 else scanCoeffLcm maxDen rest acc'

private theorem scanExpLcm_dvd (maxDen : Nat) (ts : TermList) (acc D : Nat)
    (hacc : acc ≠ 0) (h : scanExpLcm maxDen ts acc = D) (hD : D ≠ 0) :
    acc ∣ D ∧ ∀ p ∈ ts, p.1.den ∣ D := by
  induction ts generalizing acc with
  | nil =>
    simp only [scanExpLcm] at h
    subst h
    exact ⟨Nat.dvd_refl _, fun _ hm => by simp at hm⟩
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [scanExpLcm] at h
    split at h
    · rename_i hskip
      have hdvd_e : e.den ∣ acc := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hskip
        rcases hskip with h1 | hmod
        · rw [h1]; exact Nat.one_dvd acc
        · exact Nat.dvd_of_mod_eq_zero hmod
      have ⟨haccD, hrest⟩ := ih acc hacc h
      refine ⟨haccD, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · exact Nat.dvd_trans hdvd_e haccD
      · exact hrest q hmem
    · split at h
      · exact absurd h.symm hD
      · have hlcm_nz : Nat.lcm acc e.den ≠ 0 := by
          have ha : 0 < acc := Nat.pos_of_ne_zero hacc
          have he : 0 < e.den := Nat.pos_of_ne_zero e.den_nz
          have hg : 0 < Nat.gcd acc e.den := Nat.gcd_pos_of_pos_left e.den ha
          have hmul : Nat.lcm acc e.den * Nat.gcd acc e.den = acc * e.den := Nat.lcm_mul_gcd acc e.den
          intro h0; rw [h0, Nat.zero_mul] at hmul
          have : 0 < acc * e.den := Nat.mul_pos ha he
          omega
        have ⟨hlcmD, hrest⟩ := ih (Nat.lcm acc e.den) hlcm_nz h
        refine ⟨Nat.dvd_trans (Nat.dvd_lcm_left acc e.den) hlcmD, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hmem
        · exact Nat.dvd_trans (Nat.dvd_lcm_right acc e.den) hlcmD
        · exact hrest q hmem

private theorem scanCoeffLcm_dvd (maxDen : Nat) (ts : TermList) (acc D : Nat)
    (hacc : acc ≠ 0) (h : scanCoeffLcm maxDen ts acc = D) (hD : D ≠ 0) :
    acc ∣ D ∧ ∀ p ∈ ts, p.2.den ∣ D := by
  induction ts generalizing acc with
  | nil =>
    simp only [scanCoeffLcm] at h
    subst h
    exact ⟨Nat.dvd_refl _, fun _ hm => by simp at hm⟩
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [scanCoeffLcm] at h
    split at h
    · rename_i hskip
      have hdvd_c : c.den ∣ acc := by
        simp only [Bool.or_eq_true, beq_iff_eq] at hskip
        rcases hskip with h1 | hmod
        · rw [h1]; exact Nat.one_dvd acc
        · exact Nat.dvd_of_mod_eq_zero hmod
      have ⟨haccD, hrest⟩ := ih acc hacc h
      refine ⟨haccD, ?_⟩
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · exact Nat.dvd_trans hdvd_c haccD
      · exact hrest q hmem
    · split at h
      · exact absurd h.symm hD
      · have hlcm_nz : Nat.lcm acc c.den ≠ 0 := by
          have ha : 0 < acc := Nat.pos_of_ne_zero hacc
          have hc : 0 < c.den := Nat.pos_of_ne_zero c.den_nz
          have hmul : Nat.lcm acc c.den * Nat.gcd acc c.den = acc * c.den := Nat.lcm_mul_gcd acc c.den
          intro h0; rw [h0, Nat.zero_mul] at hmul
          have : 0 < acc * c.den := Nat.mul_pos ha hc
          omega
        have ⟨hlcmD, hrest⟩ := ih (Nat.lcm acc c.den) hlcm_nz h
        refine ⟨Nat.dvd_trans (Nat.dvd_lcm_left acc c.den) hlcmD, ?_⟩
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hmem
        · exact Nat.dvd_trans (Nat.dvd_lcm_right acc c.den) hlcmD
        · exact hrest q hmem

/-! #### Depth-First Power-of-Two Tree Equivalence for `mergeAll` -/

private theorem mergePairs_append_even {xs ys : List TermList} (heven : xs.length % 2 = 0) :
    mergePairs (xs ++ ys) = mergePairs xs ++ mergePairs ys := by
  match xs with
  | [] => rfl
  | [_] => simp at heven
  | a :: b :: rest =>
    simp only [List.cons_append, mergePairs]
    have hrest : rest.length % 2 = 0 := by simp at heven; omega
    rw [mergePairs_append_even hrest]

private theorem mergePairs_length (l : List TermList) :
    (mergePairs l).length = (l.length + 1) / 2 := by
  match l with
  | [] => rfl
  | [_] => simp [mergePairs]
  | _ :: _ :: rest =>
    simp only [mergePairs, List.length_cons, mergePairs_length rest]
    omega

private theorem mergeAll_cons_cons (a b : TermList) (rest : List TermList) :
    mergeAll (a :: b :: rest) = mergeAll (mergePairs (a :: b :: rest)) := by
  rw [mergeAll]

private theorem addMerge_nil_right (xs : TermList) : addMerge xs [] = xs := by
  cases xs <;> simp [addMerge]

private theorem mergeAll_mergePairs_of_ge_two {l : List TermList} (h : 2 ≤ l.length) :
    mergeAll (mergePairs l) = mergeAll l := by
  match l with
  | [] => simp at h
  | [_] => simp at h
  | a :: b :: rest => exact (mergeAll_cons_cons a b rest).symm

private theorem mergeAll_append_pow2 :
    ∀ (p : Nat) (xs ys : List TermList),
      xs.length = 2 ^ p → 0 < ys.length → ys.length ≤ 2 ^ p →
      mergeAll (xs ++ ys) = addMerge (mergeAll xs) (mergeAll ys)
  | 0, xs, ys, hxs, hys_pos, hys_le => by
    match xs, ys with
    | [a], [b] =>
      simp only [List.singleton_append]
      rw [mergeAll_cons_cons]
      simp [mergePairs, mergeAll]
    | [], _ => simp at hxs
    | _ :: _ :: _, _ => simp at hxs
    | _, [] => simp at hys_pos
    | _, _ :: _ :: _ => simp at hys_le
  | p + 1, xs, ys, hxs, hys_pos, hys_le => by
    have hpow : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ]; omega
    have hpow_pos : 0 < 2 ^ p := Nat.two_pow_pos p
    have hxs_ge2 : 2 ≤ xs.length := by omega
    have hxs_even : xs.length % 2 = 0 := by omega
    have happ_ge2 : 2 ≤ (xs ++ ys).length := by simp; omega
    rw [← mergeAll_mergePairs_of_ge_two happ_ge2, mergePairs_append_even hxs_even]
    have hxs' : (mergePairs xs).length = 2 ^ p := by rw [mergePairs_length]; omega
    have hys'_pos : 0 < (mergePairs ys).length := by rw [mergePairs_length]; omega
    have hys'_le : (mergePairs ys).length ≤ 2 ^ p := by rw [mergePairs_length]; omega
    rw [mergeAll_append_pow2 p (mergePairs xs) (mergePairs ys) hxs' hys'_pos hys'_le,
        mergeAll_mergePairs_of_ge_two hxs_ge2]
    by_cases hy1 : ys.length = 1
    · match ys with
      | [b] => rfl
      | [] => simp at hy1
      | _ :: _ :: _ => simp at hy1
    · rw [mergeAll_mergePairs_of_ge_two (by omega)]

/-! #### Path A: Parallel Unboxed `Array Int × Array Int` SOA Kernel -/

/-- Decode parallel scaled integer arrays `(es, cs)` back into a `TermList` (spec helper). -/
def decodeIntRun (de dc : Nat) (es cs : Array Int) : TermList :=
  List.zipWith (fun e c => (mkRat e de, mkRat c dc)) es.toList cs.toList

private theorem decodeIntRun_eq_nil_of_size_eq {de dc : Nat} {es cs : Array Int}
    (h : es.size = 0) : decodeIntRun de dc es cs = [] := by
  have he : es.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
  simp [decodeIntRun, he]

private theorem decodeIntRun_push (de dc : Nat) (es cs : Array Int)
    (hsz : es.size = cs.size) (e c : Int) :
    decodeIntRun de dc (es.push e) (cs.push c) =
      decodeIntRun de dc es cs ++ [(mkRat e de, mkRat c dc)] := by
  unfold decodeIntRun
  simp only [Array.toList_push]
  have hlen : es.toList.length = cs.toList.length := by simpa using hsz
  generalize es.toList = l1, cs.toList = l2 at hlen ⊢
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons] at hlen ⊢
      congr 1
      exact ih ys (by omega)

private theorem zipWith_drop {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) (i : Nat) :
    List.zipWith f (xs.drop i) (ys.drop i) = (List.zipWith f xs ys).drop i := by
  induction i generalizing xs ys with
  | zero => simp
  | succ i ih =>
    cases xs with
    | nil => simp
    | cons x xs' =>
      cases ys with
      | nil => simp
      | cons y ys' => simp [ih]

/-- Lift a `TermList` into parallel unboxed `Array Int`s `(es, cs)` scaled by `(de, dc)`. -/
def liftIntTermsLoop (de dc : Nat) : TermList → Array Int → Array Int → Array Int × Array Int
  | [], es, cs => (es, cs)
  | (e, c) :: rest, es, cs =>
    let ei := if de == 1 then e.num else e.num * Int.ofNat (de / e.den)
    let ci := if dc == 1 then c.num else c.num * Int.ofNat (dc / c.den)
    liftIntTermsLoop de dc rest (es.push ei) (cs.push ci)

/-- Entry point for lifting a `TermList` into parallel unboxed `Array Int`s. -/
@[inline] def liftIntTerms (de dc : Nat) (ts : TermList) : Array Int × Array Int :=
  let n := ts.length
  liftIntTermsLoop de dc ts (Array.mkEmpty n) (Array.mkEmpty (n + 1))

private theorem liftIntTermsLoop_spec (de dc : Nat) (hde : de ≠ 0) (hdc : dc ≠ 0)
    (ts : TermList) (accE accC : Array Int) (hsz : accE.size = accC.size)
    (he_dvd : ∀ p ∈ ts, p.1.den ∣ de) (hc_dvd : ∀ p ∈ ts, p.2.den ∣ dc) :
    let res := liftIntTermsLoop de dc ts accE accC
    res.1.size = res.2.size ∧
      decodeIntRun de dc res.1 res.2 = decodeIntRun de dc accE accC ++ ts := by
  induction ts generalizing accE accC with
  | nil =>
    simp [liftIntTermsLoop, hsz]
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [liftIntTermsLoop]
    have hed : e.den ∣ de := he_dvd (e, c) (List.mem_cons_self ..)
    have hcd : c.den ∣ dc := hc_dvd (e, c) (List.mem_cons_self ..)
    have he_eq : mkRat (if de == 1 then e.num else e.num * Int.ofNat (de / e.den)) de = e := by
      split
      · rename_i h1
        have hde1 : de = 1 := eq_of_beq h1
        subst hde1
        have hden1 : e.den = 1 := Nat.dvd_one.mp hed
        rw [mkRat_one]
        apply Rat.ext <;> simp [Rat.ofInt, hden1]
      · exact mkRat_scaled_eq e hde hed
    have hc_eq : mkRat (if dc == 1 then c.num else c.num * Int.ofNat (dc / c.den)) dc = c := by
      split
      · rename_i h1
        have hdc1 : dc = 1 := eq_of_beq h1
        subst hdc1
        have hden1 : c.den = 1 := Nat.dvd_one.mp hcd
        rw [mkRat_one]
        apply Rat.ext <;> simp [Rat.ofInt, hden1]
      · exact mkRat_scaled_eq c hdc hcd
    let ei : Int := if de == 1 then e.num else e.num * Int.ofNat (de / e.den)
    let ci : Int := if dc == 1 then c.num else c.num * Int.ofNat (dc / c.den)
    have hsz' : (accE.push ei).size = (accC.push ci).size := by simp [hsz]
    have ⟨hs, hd⟩ := ih (accE.push ei) (accC.push ci) hsz'
      (fun q hq => he_dvd q (List.mem_cons_of_mem _ hq))
      (fun q hq => hc_dvd q (List.mem_cons_of_mem _ hq))
    refine ⟨hs, ?_⟩
    rw [hd, decodeIntRun_push _ _ accE accC hsz ei ci, he_eq, hc_eq, List.append_assoc]
    rfl

/-- Append slice `[i..]` of parallel integer arrays `(srcE, srcC)` onto `(accE, accC)`
    (single bounds check via erased `Prop` `hsrc`). -/
def appendIntRunLoop (srcE srcC : Array Int) (hsrc : srcE.size = srcC.size) (i : Nat)
    (accE accC : Array Int) : Array Int × Array Int :=
  if hi : i < srcE.size then
    appendIntRunLoop srcE srcC hsrc (i + 1) (accE.push srcE[i]) (accC.push srcC[i])
  else
    (accE, accC)
termination_by srcE.size - i

private theorem appendIntRunLoop_spec (de dc : Nat) (srcE srcC : Array Int)
    (hsrc : srcE.size = srcC.size) (i : Nat) (accE accC : Array Int)
    (hacc : accE.size = accC.size) :
    let res := appendIntRunLoop srcE srcC hsrc i accE accC
    res.1.size = res.2.size ∧
      decodeIntRun de dc res.1 res.2 =
        decodeIntRun de dc accE accC ++ (decodeIntRun de dc srcE srcC).drop i := by
  unfold appendIntRunLoop
  split
  · rename_i hi
    have hic : i < srcC.size := by omega
    have ⟨hs, hd⟩ := appendIntRunLoop_spec de dc srcE srcC hsrc (i + 1)
      (accE.push srcE[i]) (accC.push srcC[i]) (by simp [hacc])
    refine ⟨hs, ?_⟩
    rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc]
    congr 1
    unfold decodeIntRun
    rw [← zipWith_drop, ← zipWith_drop]
    have hedrop : srcE.toList.drop i = srcE[i] :: srcE.toList.drop (i + 1) := by
      have hi' : i < srcE.toList.length := by simpa using hi
      simpa using List.drop_eq_getElem_cons hi'
    have hcdrop : srcC.toList.drop i = srcC[i] :: srcC.toList.drop (i + 1) := by
      have hic' : i < srcC.toList.length := by simpa using hic
      simpa using List.drop_eq_getElem_cons hic'
    rw [hedrop, hcdrop]
    rfl
  · rename_i hge
    refine ⟨hacc, ?_⟩
    have hdrop : (decodeIntRun de dc srcE srcC).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRun
      simp only [List.length_zipWith, Array.length_toList]
      omega
    simp [hdrop]
termination_by srcE.size - i

/-- Append scaled slice `[i..]` of `(yes, ycs)` shifted by `(ex, cx)` onto `(accE, accC)`
    (single bounds check via erased `Prop` `hy`). -/
def appendScaledIntLoop (ex cx : Int) (yes ycs : Array Int) (hy : yes.size = ycs.size) (i : Nat)
    (accE accC : Array Int) : Array Int × Array Int :=
  if hi : i < yes.size then
    appendScaledIntLoop ex cx yes ycs hy (i + 1)
      (accE.push (ex + yes[i])) (accC.push (cx * ycs[i]))
  else
    (accE, accC)
termination_by yes.size - i

private theorem appendScaledIntLoop_spec (de dcx dcy : Nat) (hde : de ≠ 0)
    (ex cx : Int) (yes ycs : Array Int) (hy : yes.size = ycs.size) (i : Nat)
    (accE accC : Array Int) (hacc : accE.size = accC.size) :
    let res := appendScaledIntLoop ex cx yes ycs hy i accE accC
    res.1.size = res.2.size ∧
      decodeIntRun de (dcx * dcy) res.1 res.2 =
        decodeIntRun de (dcx * dcy) accE accC ++
          ((decodeIntRun de dcy yes ycs).drop i).map
            (fun (ey, cy) => (mkRat ex de + ey, mkRat cx dcx * cy)) := by
  unfold appendScaledIntLoop
  split
  · rename_i hi
    have hic : i < ycs.size := by omega
    have ⟨hs, hd⟩ := appendScaledIntLoop_spec de dcx dcy hde ex cx yes ycs hy (i + 1)
      (accE.push (ex + yes[i])) (accC.push (cx * ycs[i])) (by simp [hacc])
    refine ⟨hs, ?_⟩
    rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc]
    congr 1
    have hdrop : (decodeIntRun de dcy yes ycs).drop i =
        (mkRat yes[i] de, mkRat ycs[i] dcy) :: (decodeIntRun de dcy yes ycs).drop (i + 1) := by
      unfold decodeIntRun
      rw [← zipWith_drop, ← zipWith_drop]
      have hedrop : yes.toList.drop i = yes[i] :: yes.toList.drop (i + 1) := by
        have hi' : i < yes.toList.length := by simpa using hi
        simpa using List.drop_eq_getElem_cons hi'
      have hcdrop : ycs.toList.drop i = ycs[i] :: ycs.toList.drop (i + 1) := by
        have hic' : i < ycs.toList.length := by simpa using hic
        simpa using List.drop_eq_getElem_cons hic'
      rw [hedrop, hcdrop]
      rfl
    rw [hdrop, List.map_cons]
    dsimp only
    rw [mkRat_add_same_den ex yes[i] hde, Rat.mkRat_mul_mkRat]
    rfl
  · rename_i hge
    refine ⟨hacc, ?_⟩
    have hdrop : (decodeIntRun de dcy yes ycs).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRun
      simp only [List.length_zipWith, Array.length_toList]
      omega
    simp [hdrop]
termination_by yes.size - i

/-- Unboxed `Array Int × Array Int` term-scaling kernel (zero `Rat` allocs, distinct `RC=1` buffers). -/
@[inline] def scaleIntRun (ex cx : Int) (yes ycs : Array Int) (hy : yes.size = ycs.size) :
    Array Int × Array Int :=
  if cx == 0 then (#[], #[])
  else appendScaledIntLoop ex cx yes ycs hy 0 (Array.mkEmpty yes.size) (Array.mkEmpty (yes.size + 1))

private theorem scaleIntRun_spec (de dcx dcy : Nat) (hde : de ≠ 0) (hdcx : dcx ≠ 0)
    (ex cx : Int) (yes ycs : Array Int) (hy : yes.size = ycs.size) :
    let res := scaleIntRun ex cx yes ycs hy
    res.1.size = res.2.size ∧
      decodeIntRun de (dcx * dcy) res.1 res.2 =
        scaleTerm (mkRat ex de) (mkRat cx dcx) (decodeIntRun de dcy yes ycs) := by
  unfold scaleIntRun scaleTerm
  have hcz : (cx == 0) = (mkRat cx dcx == 0) := by
    cases h1 : (cx == 0) <;> cases h2 : (mkRat cx dcx == 0) <;> try rfl
    · have h0 : mkRat cx dcx = 0 := eq_of_beq h2
      have hcx : cx = 0 := (Rat.mkRat_eq_zero hdcx).mp h0
      simp [hcx] at h1
    · have hcx : cx = 0 := eq_of_beq h1
      subst hcx; simp at h2
  rw [hcz]
  split
  · exact ⟨rfl, rfl⟩
  · have ⟨hs, hd⟩ := appendScaledIntLoop_spec de dcx dcy hde ex cx yes ycs hy 0
      (Array.mkEmpty yes.size) (Array.mkEmpty (yes.size + 1)) rfl
    refine ⟨hs, ?_⟩
    simpa [decodeIntRun] using hd

/-- Unboxed two-pointer sorted merge over parallel `Array Int × Array Int` runs
    (only 2 bounds checks per iteration via erased `Prop` `hx, hy`). -/
def mergeIntRunLoop (xes xcs yes ycs : Array Int)
    (hx : xes.size = xcs.size) (hy : yes.size = ycs.size) (i j : Nat)
    (accE accC : Array Int) : Array Int × Array Int :=
  if hi : i < xes.size then
    if hj : j < yes.size then
      let ex := xes[i]
      let ey := yes[j]
      if ex > ey then
        mergeIntRunLoop xes xcs yes ycs hx hy (i + 1) j (accE.push ex) (accC.push xcs[i])
      else if ey > ex then
        mergeIntRunLoop xes xcs yes ycs hx hy i (j + 1) (accE.push ey) (accC.push ycs[j])
      else
        let s := xcs[i] + ycs[j]
        if s == 0 then
          mergeIntRunLoop xes xcs yes ycs hx hy (i + 1) (j + 1) accE accC
        else
          mergeIntRunLoop xes xcs yes ycs hx hy (i + 1) (j + 1) (accE.push ex) (accC.push s)
    else appendIntRunLoop xes xcs hx i accE accC
  else appendIntRunLoop yes ycs hy j accE accC
termination_by (xes.size - i) + (yes.size - j)

/-- Entry point for unboxed parallel-`Array Int` sorted merge (distinct `RC=1` buffers). -/
@[inline] def mergeIntRun (rx ry : Array Int × Array Int) : Array Int × Array Int :=
  if hx : rx.1.size = rx.2.size then
    if hy : ry.1.size = ry.2.size then
      let cap := rx.1.size + ry.1.size
      mergeIntRunLoop rx.1 rx.2 ry.1 ry.2 hx hy 0 0 (Array.mkEmpty cap) (Array.mkEmpty (cap + 1))
    else rx
  else ry

private theorem mergeIntRunLoop_spec (de dc : Nat) (hde : de ≠ 0) (hdc : dc ≠ 0)
    (xes xcs yes ycs : Array Int) (hx : xes.size = xcs.size) (hy : yes.size = ycs.size)
    (i j : Nat) (accE accC : Array Int) (hacc : accE.size = accC.size) :
    let res := mergeIntRunLoop xes xcs yes ycs hx hy i j accE accC
    res.1.size = res.2.size ∧
      decodeIntRun de dc res.1 res.2 =
        decodeIntRun de dc accE accC ++
          addMerge ((decodeIntRun de dc xes xcs).drop i) ((decodeIntRun de dc yes ycs).drop j) := by
  unfold mergeIntRunLoop
  split
  · rename_i hi
    have hxdrop : (decodeIntRun de dc xes xcs).drop i =
        (mkRat xes[i] de, mkRat xcs[i] dc) :: (decodeIntRun de dc xes xcs).drop (i + 1) := by
      unfold decodeIntRun
      rw [← zipWith_drop, ← zipWith_drop]
      have hedrop : xes.toList.drop i = xes[i] :: xes.toList.drop (i + 1) := by
        have hi' : i < xes.toList.length := by simpa using hi
        simpa using List.drop_eq_getElem_cons hi'
      have hcdrop : xcs.toList.drop i = xcs[i] :: xcs.toList.drop (i + 1) := by
        have hic' : i < xcs.toList.length := by simp; omega
        simpa using List.drop_eq_getElem_cons hic'
      rw [hedrop, hcdrop]; rfl
    split
    · rename_i hj
      have hydrop : (decodeIntRun de dc yes ycs).drop j =
          (mkRat yes[j] de, mkRat ycs[j] dc) :: (decodeIntRun de dc yes ycs).drop (j + 1) := by
        unfold decodeIntRun
        rw [← zipWith_drop, ← zipWith_drop]
        have hedrop : yes.toList.drop j = yes[j] :: yes.toList.drop (j + 1) := by
          have hj' : j < yes.toList.length := by simpa using hj
          simpa using List.drop_eq_getElem_cons hj'
        have hcdrop : ycs.toList.drop j = ycs[j] :: ycs.toList.drop (j + 1) := by
          have hjc' : j < ycs.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hjc'
        rw [hedrop, hcdrop]; rfl
      dsimp only
      split
      · rename_i hgt
        have hrat_gt : mkRat xes[i] de > mkRat yes[j] de := (mkRat_lt_iff hde).mpr hgt
        have ⟨hs, hd⟩ := mergeIntRunLoop_spec de dc hde hdc xes xcs yes ycs hx hy (i + 1) j
          (accE.push xes[i]) (accC.push xcs[i]) (by simp [hacc])
        refine ⟨hs, ?_⟩
        rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
        simp only [addMerge, hrat_gt, ↓reduceIte]
        rfl
      · split
        · rename_i hngt hlt
          have hrat_ngt : ¬ (mkRat xes[i] de > mkRat yes[j] de) := by
            intro h; exact hngt ((mkRat_lt_iff hde).mp h)
          have hrat_lt : mkRat yes[j] de > mkRat xes[i] de := (mkRat_lt_iff hde).mpr hlt
          have ⟨hs, hd⟩ := mergeIntRunLoop_spec de dc hde hdc xes xcs yes ycs hx hy i (j + 1)
            (accE.push yes[j]) (accC.push ycs[j]) (by simp [hacc])
          refine ⟨hs, ?_⟩
          rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
          simp only [addMerge, hrat_ngt, hrat_lt, ↓reduceIte]
          rfl
        · rename_i hngt hnlt
          have hrat_ngt : ¬ (mkRat xes[i] de > mkRat yes[j] de) := by
            intro h; exact hngt ((mkRat_lt_iff hde).mp h)
          have hrat_nlt : ¬ (mkRat yes[j] de > mkRat xes[i] de) := by
            intro h; exact hnlt ((mkRat_lt_iff hde).mp h)
          have hsum_eq : mkRat xcs[i] dc + mkRat ycs[j] dc = mkRat (xcs[i] + ycs[j]) dc :=
            mkRat_add_same_den _ _ hdc
          have hsz_eq : (xcs[i] + ycs[j] == 0) = (mkRat (xcs[i] + ycs[j]) dc == 0) := by
            cases h1 : (xcs[i] + ycs[j] == 0) <;> cases h2 : (mkRat (xcs[i] + ycs[j]) dc == 0) <;> try rfl
            · have h0 := (Rat.mkRat_eq_zero hdc).mp (eq_of_beq h2); simp [h0] at h1
            · have h0 := eq_of_beq h1; rw [h0] at h2; simp at h2
          split
          · rename_i hz
            have hrz : (mkRat (xcs[i] + ycs[j]) dc == 0) = true := by rw [← hsz_eq]; exact hz
            have ⟨hs, hd⟩ := mergeIntRunLoop_spec de dc hde hdc xes xcs yes ycs hx hy (i + 1) (j + 1)
              accE accC hacc
            refine ⟨hs, ?_⟩
            rw [hd, hxdrop, hydrop]
            simp only [addMerge, hrat_ngt, hrat_nlt, hsum_eq, hrz, ↓reduceIte]
          · rename_i hnz
            have hrnz : (mkRat (xcs[i] + ycs[j]) dc == 0) = false := by
              cases hb : (mkRat (xcs[i] + ycs[j]) dc == 0)
              · rfl
              · rw [← hsz_eq] at hb; exact absurd hb hnz
            have ⟨hs, hd⟩ := mergeIntRunLoop_spec de dc hde hdc xes xcs yes ycs hx hy (i + 1) (j + 1)
              (accE.push xes[i]) (accC.push (xcs[i] + ycs[j])) (by simp [hacc])
            refine ⟨hs, ?_⟩
            rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
            simp only [addMerge, hrat_ngt, hrat_nlt, hsum_eq, hrnz, Bool.false_eq_true, ↓reduceIte]
            rfl
    · rename_i hnj
      have hydrop : (decodeIntRun de dc yes ycs).drop j = [] := by
        apply List.drop_eq_nil_of_le
        unfold decodeIntRun; simp only [List.length_zipWith, Array.length_toList]; omega
      have ⟨hs, hd⟩ := appendIntRunLoop_spec de dc xes xcs hx i accE accC hacc
      refine ⟨hs, ?_⟩
      rw [hd, hydrop, hxdrop]; simp [addMerge]
  · rename_i hni
    have hxdrop : (decodeIntRun de dc xes xcs).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRun; simp only [List.length_zipWith, Array.length_toList]; omega
    have ⟨hs, hd⟩ := appendIntRunLoop_spec de dc yes ycs hy j accE accC hacc
    refine ⟨hs, ?_⟩
    rw [hd, hxdrop]; simp [addMerge]
termination_by (xes.size - i) + (yes.size - j)

private theorem mergeIntRun_spec (de dc : Nat) (hde : de ≠ 0) (hdc : dc ≠ 0)
    (rx ry : Array Int × Array Int) (hx : rx.1.size = rx.2.size) (hy : ry.1.size = ry.2.size) :
    let res := mergeIntRun rx ry
    res.1.size = res.2.size ∧
      decodeIntRun de dc res.1 res.2 =
        addMerge (decodeIntRun de dc rx.1 rx.2) (decodeIntRun de dc ry.1 ry.2) := by
  have ⟨hs, hd⟩ := mergeIntRunLoop_spec de dc hde hdc rx.1 rx.2 ry.1 ry.2 hx hy 0 0
    (Array.mkEmpty (rx.1.size + ry.1.size)) (Array.mkEmpty (rx.1.size + ry.1.size + 1)) rfl
  exact ⟨by simpa [mergeIntRun, hx, hy] using hs, by simpa [mergeIntRun, hx, hy, decodeIntRun] using hd⟩

/-- Fused 2-leaf unboxed scale-and-merge loop: merges `(ex0, cx0) * y` and `(ex1, cx1) * y`
    directly on the fly with zero intermediate leaf array allocations and only 2 bounds checks. -/
def scaleMerge2IntLoop (ex0 cx0 ex1 cx1 : Int) (yes ycs : Array Int) (hy : yes.size = ycs.size)
    (i j : Nat) (accE accC : Array Int) : Array Int × Array Int :=
  if hi : i < yes.size then
    if hj : j < yes.size then
      let e0 := ex0 + yes[i]
      let e1 := ex1 + yes[j]
      if e0 > e1 then
        scaleMerge2IntLoop ex0 cx0 ex1 cx1 yes ycs hy (i + 1) j
          (accE.push e0) (accC.push (cx0 * ycs[i]))
      else if e1 > e0 then
        scaleMerge2IntLoop ex0 cx0 ex1 cx1 yes ycs hy i (j + 1)
          (accE.push e1) (accC.push (cx1 * ycs[j]))
      else
        let s := cx0 * ycs[i] + cx1 * ycs[j]
        if s == 0 then
          scaleMerge2IntLoop ex0 cx0 ex1 cx1 yes ycs hy (i + 1) (j + 1) accE accC
        else
          scaleMerge2IntLoop ex0 cx0 ex1 cx1 yes ycs hy (i + 1) (j + 1)
            (accE.push e0) (accC.push s)
    else appendScaledIntLoop ex0 cx0 yes ycs hy i accE accC
  else appendScaledIntLoop ex1 cx1 yes ycs hy j accE accC
termination_by (yes.size - i) + (yes.size - j)

/-- Fused 2-leaf unboxed scale-and-merge entry point (distinct `RC=1` buffers). -/
@[inline] def scaleMerge2IntRun (ex0 cx0 ex1 cx1 : Int) (yes ycs : Array Int)
    (hy : yes.size = ycs.size) : Array Int × Array Int :=
  if cx0 == 0 then scaleIntRun ex1 cx1 yes ycs hy
  else if cx1 == 0 then scaleIntRun ex0 cx0 yes ycs hy
  else
    let cap := 2 * yes.size
    scaleMerge2IntLoop ex0 cx0 ex1 cx1 yes ycs hy 0 0 (Array.mkEmpty cap) (Array.mkEmpty (cap + 1))

private theorem scaleMerge2IntLoop_spec (de dcx dcy : Nat) (hde : de ≠ 0) (hdcx : dcx ≠ 0)
    (hdcy : dcy ≠ 0) (ex0 cx0 ex1 cx1 : Int) (yes ycs : Array Int)
    (hy : yes.size = ycs.size) (i j : Nat) (accE accC : Array Int)
    (hacc : accE.size = accC.size) :
    let res := scaleMerge2IntLoop ex0 cx0 ex1 cx1 yes ycs hy i j accE accC
    res.1.size = res.2.size ∧
      decodeIntRun de (dcx * dcy) res.1 res.2 =
        decodeIntRun de (dcx * dcy) accE accC ++
          addMerge
            (((decodeIntRun de dcy yes ycs).drop i).map (fun (ey, cy) => (mkRat ex0 de + ey, mkRat cx0 dcx * cy)))
            (((decodeIntRun de dcy yes ycs).drop j).map (fun (ey, cy) => (mkRat ex1 de + ey, mkRat cx1 dcx * cy))) := by
  have hdcp : dcx * dcy ≠ 0 := Nat.mul_ne_zero hdcx hdcy
  unfold scaleMerge2IntLoop
  split
  · rename_i hi
    have hxdrop : ((decodeIntRun de dcy yes ycs).drop i).map
        (fun (ey, cy) => (mkRat ex0 de + ey, mkRat cx0 dcx * cy)) =
        (mkRat (ex0 + yes[i]) de, mkRat (cx0 * ycs[i]) (dcx * dcy)) ::
          ((decodeIntRun de dcy yes ycs).drop (i + 1)).map
            (fun (ey, cy) => (mkRat ex0 de + ey, mkRat cx0 dcx * cy)) := by
      have hd : (decodeIntRun de dcy yes ycs).drop i =
          (mkRat yes[i] de, mkRat ycs[i] dcy) :: (decodeIntRun de dcy yes ycs).drop (i + 1) := by
        unfold decodeIntRun
        rw [← zipWith_drop, ← zipWith_drop]
        have hedrop : yes.toList.drop i = yes[i] :: yes.toList.drop (i + 1) := by
          have hi' : i < yes.toList.length := by simpa using hi
          simpa using List.drop_eq_getElem_cons hi'
        have hcdrop : ycs.toList.drop i = ycs[i] :: ycs.toList.drop (i + 1) := by
          have hic' : i < ycs.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hic'
        rw [hedrop, hcdrop]; rfl
      rw [hd, List.map_cons]
      dsimp only
      rw [mkRat_add_same_den ex0 yes[i] hde, Rat.mkRat_mul_mkRat]
    split
    · rename_i hj
      have hydrop : ((decodeIntRun de dcy yes ycs).drop j).map
          (fun (ey, cy) => (mkRat ex1 de + ey, mkRat cx1 dcx * cy)) =
          (mkRat (ex1 + yes[j]) de, mkRat (cx1 * ycs[j]) (dcx * dcy)) ::
            ((decodeIntRun de dcy yes ycs).drop (j + 1)).map
              (fun (ey, cy) => (mkRat ex1 de + ey, mkRat cx1 dcx * cy)) := by
        have hd : (decodeIntRun de dcy yes ycs).drop j =
            (mkRat yes[j] de, mkRat ycs[j] dcy) :: (decodeIntRun de dcy yes ycs).drop (j + 1) := by
          unfold decodeIntRun
          rw [← zipWith_drop, ← zipWith_drop]
          have hedrop : yes.toList.drop j = yes[j] :: yes.toList.drop (j + 1) := by
            have hj' : j < yes.toList.length := by simpa using hj
            simpa using List.drop_eq_getElem_cons hj'
          have hcdrop : ycs.toList.drop j = ycs[j] :: ycs.toList.drop (j + 1) := by
            have hjc' : j < ycs.toList.length := by simp; omega
            simpa using List.drop_eq_getElem_cons hjc'
          rw [hedrop, hcdrop]; rfl
        rw [hd, List.map_cons]
        dsimp only
        rw [mkRat_add_same_den ex1 yes[j] hde, Rat.mkRat_mul_mkRat]
      dsimp only
      split
      · rename_i hgt
        have hrat_gt : mkRat (ex0 + yes[i]) de > mkRat (ex1 + yes[j]) de := (mkRat_lt_iff hde).mpr hgt
        have ⟨hs, hd⟩ := scaleMerge2IntLoop_spec de dcx dcy hde hdcx hdcy ex0 cx0 ex1 cx1 yes ycs hy
          (i + 1) j (accE.push (ex0 + yes[i])) (accC.push (cx0 * ycs[i])) (by simp [hacc])
        refine ⟨hs, ?_⟩
        rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
        simp only [addMerge, hrat_gt, ↓reduceIte]
        rfl
      · split
        · rename_i hngt hlt
          have hrat_ngt : ¬ (mkRat (ex0 + yes[i]) de > mkRat (ex1 + yes[j]) de) := by
            intro h; exact hngt ((mkRat_lt_iff hde).mp h)
          have hrat_lt : mkRat (ex1 + yes[j]) de > mkRat (ex0 + yes[i]) de := (mkRat_lt_iff hde).mpr hlt
          have ⟨hs, hd⟩ := scaleMerge2IntLoop_spec de dcx dcy hde hdcx hdcy ex0 cx0 ex1 cx1 yes ycs hy
            i (j + 1) (accE.push (ex1 + yes[j])) (accC.push (cx1 * ycs[j])) (by simp [hacc])
          refine ⟨hs, ?_⟩
          rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
          simp only [addMerge, hrat_ngt, hrat_lt, ↓reduceIte]
          rfl
        · rename_i hngt hnlt
          have hrat_ngt : ¬ (mkRat (ex0 + yes[i]) de > mkRat (ex1 + yes[j]) de) := by
            intro h; exact hngt ((mkRat_lt_iff hde).mp h)
          have hrat_nlt : ¬ (mkRat (ex1 + yes[j]) de > mkRat (ex0 + yes[i]) de) := by
            intro h; exact hnlt ((mkRat_lt_iff hde).mp h)
          have hsum_eq : mkRat (cx0 * ycs[i]) (dcx * dcy) + mkRat (cx1 * ycs[j]) (dcx * dcy) =
              mkRat (cx0 * ycs[i] + cx1 * ycs[j]) (dcx * dcy) :=
            mkRat_add_same_den _ _ hdcp
          have hsz_eq : (cx0 * ycs[i] + cx1 * ycs[j] == 0) =
              (mkRat (cx0 * ycs[i] + cx1 * ycs[j]) (dcx * dcy) == 0) := by
            cases h1 : (cx0 * ycs[i] + cx1 * ycs[j] == 0) <;>
              cases h2 : (mkRat (cx0 * ycs[i] + cx1 * ycs[j]) (dcx * dcy) == 0) <;> try rfl
            · have h0 := (Rat.mkRat_eq_zero hdcp).mp (eq_of_beq h2); simp [h0] at h1
            · have h0 := eq_of_beq h1; rw [h0] at h2; simp at h2
          split
          · rename_i hz
            have hrz : (mkRat (cx0 * ycs[i] + cx1 * ycs[j]) (dcx * dcy) == 0) = true := by
              rw [← hsz_eq]; exact hz
            have ⟨hs, hd⟩ := scaleMerge2IntLoop_spec de dcx dcy hde hdcx hdcy ex0 cx0 ex1 cx1 yes ycs hy
              (i + 1) (j + 1) accE accC hacc
            refine ⟨hs, ?_⟩
            rw [hd, hxdrop, hydrop]
            simp only [addMerge, hrat_ngt, hrat_nlt, hsum_eq, hrz, ↓reduceIte]
          · rename_i hnz
            have hrnz : (mkRat (cx0 * ycs[i] + cx1 * ycs[j]) (dcx * dcy) == 0) = false := by
              cases hb : (mkRat (cx0 * ycs[i] + cx1 * ycs[j]) (dcx * dcy) == 0)
              · rfl
              · rw [← hsz_eq] at hb; exact absurd hb hnz
            have ⟨hs, hd⟩ := scaleMerge2IntLoop_spec de dcx dcy hde hdcx hdcy ex0 cx0 ex1 cx1 yes ycs hy
              (i + 1) (j + 1) (accE.push (ex0 + yes[i])) (accC.push (cx0 * ycs[i] + cx1 * ycs[j]))
              (by simp [hacc])
            refine ⟨hs, ?_⟩
            rw [hd, decodeIntRun_push _ _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
            simp only [addMerge, hrat_ngt, hrat_nlt, hsum_eq, hrnz, Bool.false_eq_true, ↓reduceIte]
            rfl
    · rename_i hnj
      have hydrop : (decodeIntRun de dcy yes ycs).drop j = [] := by
        apply List.drop_eq_nil_of_le
        unfold decodeIntRun; simp only [List.length_zipWith, Array.length_toList]; omega
      have ⟨hs, hd⟩ := appendScaledIntLoop_spec de dcx dcy hde ex0 cx0 yes ycs hy i accE accC hacc
      refine ⟨hs, ?_⟩
      rw [hd, hydrop, List.map_nil, hxdrop]; simp [addMerge]
  · rename_i hni
    have hxdrop : (decodeIntRun de dcy yes ycs).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRun; simp only [List.length_zipWith, Array.length_toList]; omega
    have ⟨hs, hd⟩ := appendScaledIntLoop_spec de dcx dcy hde ex1 cx1 yes ycs hy j accE accC hacc
    refine ⟨hs, ?_⟩
    rw [hd, hxdrop, List.map_nil]; simp [addMerge]
termination_by (yes.size - i) + (yes.size - j)

private theorem scaleMerge2IntRun_spec (de dcx dcy : Nat) (hde : de ≠ 0) (hdcx : dcx ≠ 0)
    (hdcy : dcy ≠ 0) (ex0 cx0 ex1 cx1 : Int) (yes ycs : Array Int) (hy : yes.size = ycs.size) :
    let res := scaleMerge2IntRun ex0 cx0 ex1 cx1 yes ycs hy
    res.1.size = res.2.size ∧
      decodeIntRun de (dcx * dcy) res.1 res.2 =
        addMerge
          (scaleTerm (mkRat ex0 de) (mkRat cx0 dcx) (decodeIntRun de dcy yes ycs))
          (scaleTerm (mkRat ex1 de) (mkRat cx1 dcx) (decodeIntRun de dcy yes ycs)) := by
  unfold scaleMerge2IntRun
  have hcz0 : (cx0 == 0) = (mkRat cx0 dcx == 0) := by
    cases h1 : (cx0 == 0) <;> cases h2 : (mkRat cx0 dcx == 0) <;> try rfl
    · have h0 := (Rat.mkRat_eq_zero hdcx).mp (eq_of_beq h2); simp [h0] at h1
    · have h0 := eq_of_beq h1; subst h0; simp at h2
  have hcz1 : (cx1 == 0) = (mkRat cx1 dcx == 0) := by
    cases h1 : (cx1 == 0) <;> cases h2 : (mkRat cx1 dcx == 0) <;> try rfl
    · have h0 := (Rat.mkRat_eq_zero hdcx).mp (eq_of_beq h2); simp [h0] at h1
    · have h0 := eq_of_beq h1; subst h0; simp at h2
  split
  · rename_i hc0
    have ⟨hs, hd⟩ := scaleIntRun_spec de dcx dcy hde hdcx ex1 cx1 yes ycs hy
    refine ⟨hs, ?_⟩
    rw [hd]; unfold scaleTerm; rw [← hcz0, hc0]; simp [addMerge]
  · split
    · rename_i _ hc1
      have ⟨hs, hd⟩ := scaleIntRun_spec de dcx dcy hde hdcx ex0 cx0 yes ycs hy
      refine ⟨hs, ?_⟩
      rw [hd]; unfold scaleTerm; rw [← hcz1, hc1]; simp [addMerge_nil_right]
    · rename_i hnc0 hnc1
      have hrc0 : (mkRat cx0 dcx == 0) = false := by
        cases hb : (mkRat cx0 dcx == 0)
        · rfl
        · rw [← hcz0] at hb; exact absurd hb hnc0
      have hrc1 : (mkRat cx1 dcx == 0) = false := by
        cases hb : (mkRat cx1 dcx == 0)
        · rfl
        · rw [← hcz1] at hb; exact absurd hb hnc1
      have ⟨hs, hd⟩ := scaleMerge2IntLoop_spec de dcx dcy hde hdcx hdcy ex0 cx0 ex1 cx1 yes ycs hy
        0 0 (Array.mkEmpty (2 * yes.size)) (Array.mkEmpty (2 * yes.size + 1)) rfl
      refine ⟨hs, ?_⟩
      unfold scaleTerm
      simpa [decodeIntRun, hrc0, hrc1] using hd

/-- Depth-first L1-cache-resident power-of-two divide-and-conquer sparse multiplication
    on unboxed parallel `Array Int × Array Int` with fused 2-leaf scaling. -/
def mulIntDC (xes xcs yes ycs : Array Int) (hy : yes.size = ycs.size) (lo len : Nat) :
    Array Int × Array Int :=
  if h0 : len = 0 then (#[], #[])
  else if h1 : len = 1 then
    if _hlo : lo < xes.size ∧ lo < xcs.size then
      scaleIntRun xes[lo] xcs[lo] yes ycs hy
    else (#[], #[])
  else if h2 : len = 2 then
    if _hlo2 : lo + 1 < xes.size ∧ lo + 1 < xcs.size then
      scaleMerge2IntRun xes[lo] xcs[lo] xes[lo + 1] xcs[lo + 1] yes ycs hy
    else (#[], #[])
  else
    let p := (len - 1).log2
    let k := 1 <<< p
    have hk_eq : k = 2 ^ p := by simp [k, Nat.shiftLeft_eq]
    have hk_pos : 0 < k := by rw [hk_eq]; exact Nat.two_pow_pos p
    have hk_lt : k < len := by
      have hle : 2 ^ p ≤ len - 1 := Nat.log2_self_le (by omega)
      omega
    have hrem_lt : len - k < len := by omega
    let left := mulIntDC xes xcs yes ycs hy lo k
    let right := mulIntDC xes xcs yes ycs hy (lo + k) (len - k)
    mergeIntRun left right
termination_by len

private theorem mulIntDC_spec (de dcx dcy : Nat) (hde : de ≠ 0) (hdcx : dcx ≠ 0) (hdcy : dcy ≠ 0)
    (xes xcs yes ycs : Array Int) (hx : xes.size = xcs.size) (hy : yes.size = ycs.size)
    (lo len : Nat) (hbound : lo + len ≤ xes.size) :
    (mulIntDC xes xcs yes ycs hy lo len).1.size = (mulIntDC xes xcs yes ycs hy lo len).2.size ∧
      decodeIntRun de (dcx * dcy) (mulIntDC xes xcs yes ycs hy lo len).1
        (mulIntDC xes xcs yes ycs hy lo len).2 =
        mergeAll (((decodeIntRun de dcx xes xcs).drop lo |>.take len).map
          (fun (ex, cx) => scaleTerm ex cx (decodeIntRun de dcy yes ycs))) := by
  have hdcp : dcx * dcy ≠ 0 := Nat.mul_ne_zero hdcx hdcy
  have hslice : ∀ a b, a + b ≤ xes.size →
      ((decodeIntRun de dcx xes xcs).drop a |>.take b).length = b := by
    intro a b hab
    rw [List.length_take, List.length_drop]
    unfold decodeIntRun
    simp only [List.length_zipWith, Array.length_toList]
    omega
  unfold mulIntDC
  split
  · rename_i h0
    subst h0
    exact ⟨rfl, by simp [mergeAll, decodeIntRun]⟩
  · split
    · rename_i _ h1
      subst h1
      have hlo : lo < xes.size ∧ lo < xcs.size := by omega
      simp only [hlo]
      have ⟨hs, hd⟩ := scaleIntRun_spec de dcx dcy hde hdcx xes[lo] xcs[lo] yes ycs hy
      refine ⟨hs, ?_⟩
      have hdrop : (decodeIntRun de dcx xes xcs).drop lo =
          (mkRat xes[lo] de, mkRat xcs[lo] dcx) :: (decodeIntRun de dcx xes xcs).drop (lo + 1) := by
        unfold decodeIntRun
        rw [← zipWith_drop, ← zipWith_drop]
        have hedrop : xes.toList.drop lo = xes[lo] :: xes.toList.drop (lo + 1) := by
          have hi' : lo < xes.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hi'
        have hcdrop : xcs.toList.drop lo = xcs[lo] :: xcs.toList.drop (lo + 1) := by
          have hic' : lo < xcs.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hic'
        rw [hedrop, hcdrop]; rfl
      rw [hdrop]; simp [mergeAll, hd]
    · split
      · rename_i _ _ h2
        subst h2
        have hlo2 : lo + 1 < xes.size ∧ lo + 1 < xcs.size := by omega
        simp only [hlo2]
        have ⟨hs, hd⟩ := scaleMerge2IntRun_spec de dcx dcy hde hdcx hdcy
          xes[lo] xcs[lo] xes[lo + 1] xcs[lo + 1] yes ycs hy
        refine ⟨hs, ?_⟩
        have hdrop0 : (decodeIntRun de dcx xes xcs).drop lo =
            (mkRat xes[lo] de, mkRat xcs[lo] dcx) :: (decodeIntRun de dcx xes xcs).drop (lo + 1) := by
          unfold decodeIntRun
          rw [← zipWith_drop, ← zipWith_drop]
          have hedrop : xes.toList.drop lo = xes[lo] :: xes.toList.drop (lo + 1) := by
            have hi' : lo < xes.toList.length := by simp; omega
            simpa using List.drop_eq_getElem_cons hi'
          have hcdrop : xcs.toList.drop lo = xcs[lo] :: xcs.toList.drop (lo + 1) := by
            have hic' : lo < xcs.toList.length := by simp; omega
            simpa using List.drop_eq_getElem_cons hic'
          rw [hedrop, hcdrop]; rfl
        have hdrop1 : (decodeIntRun de dcx xes xcs).drop (lo + 1) =
            (mkRat xes[lo + 1] de, mkRat xcs[lo + 1] dcx) :: (decodeIntRun de dcx xes xcs).drop (lo + 2) := by
          unfold decodeIntRun
          rw [← zipWith_drop, ← zipWith_drop]
          have hedrop : xes.toList.drop (lo + 1) = xes[lo + 1] :: xes.toList.drop (lo + 2) := by
            have hi' : lo + 1 < xes.toList.length := by simp; omega
            simpa using List.drop_eq_getElem_cons hi'
          have hcdrop : xcs.toList.drop (lo + 1) = xcs[lo + 1] :: xcs.toList.drop (lo + 2) := by
            have hic' : lo + 1 < xcs.toList.length := by simp; omega
            simpa using List.drop_eq_getElem_cons hic'
          rw [hedrop, hcdrop]; rfl
        rw [hdrop0, hdrop1]
        simp only [List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil]
        rw [mergeAll_cons_cons]
        simp [mergePairs, mergeAll, hd]
      · rename_i hne0 hne1 hne2
        dsimp only
        let p := (len - 1).log2
        let k := 1 <<< p
        have hk_eq : k = 2 ^ p := by simp [k, Nat.shiftLeft_eq]
        have hk_pos : 0 < k := by rw [hk_eq]; exact Nat.two_pow_pos p
        have hk_lt : k < len := by
          have hle : 2 ^ p ≤ len - 1 := Nat.log2_self_le (by omega)
          omega
        have hrem_lt : len - k < len := by omega
        have hrem_le : len - k ≤ 2 ^ p := by
          have hlt : len - 1 < 2 ^ (p + 1) := Nat.lt_log2_self
          rw [Nat.pow_succ] at hlt
          omega
        have ⟨hsL, hdL⟩ := mulIntDC_spec de dcx dcy hde hdcx hdcy xes xcs yes ycs hx hy lo k (by omega)
        have ⟨hsR, hdR⟩ := mulIntDC_spec de dcx dcy hde hdcx hdcy xes xcs yes ycs hx hy (lo + k) (len - k) (by omega)
        have ⟨hsM, hdM⟩ := mergeIntRun_spec de (dcx * dcy) hde hdcp
          (mulIntDC xes xcs yes ycs hy lo k) (mulIntDC xes xcs yes ycs hy (lo + k) (len - k)) hsL hsR
        refine ⟨hsM, ?_⟩
        rw [hdM, hdL, hdR]
        have hsplit : ((decodeIntRun de dcx xes xcs).drop lo).take len =
            ((decodeIntRun de dcx xes xcs).drop lo).take k ++
            ((decodeIntRun de dcx xes xcs).drop (lo + k)).take (len - k) := by
          have hlen_sum : len = k + (len - k) := by omega
          calc ((decodeIntRun de dcx xes xcs).drop lo).take len
              = ((decodeIntRun de dcx xes xcs).drop lo).take (k + (len - k)) := by rw [← hlen_sum]
            _ = ((decodeIntRun de dcx xes xcs).drop lo).take k ++
                (((decodeIntRun de dcx xes xcs).drop lo).drop k).take (len - k) := List.take_add
            _ = ((decodeIntRun de dcx xes xcs).drop lo).take k ++
                ((decodeIntRun de dcx xes xcs).drop (lo + k)).take (len - k) := by
                  rw [List.drop_drop, Nat.add_comm]
        rw [hsplit, List.map_append]
        symm
        apply mergeAll_append_pow2 p
        · rw [List.length_map, hslice lo k (by omega), hk_eq]
        · rw [List.length_map, hslice (lo + k) (len - k) (by omega)]; omega
        · rw [List.length_map, hslice (lo + k) (len - k) (by omega)]; exact hrem_le
termination_by len

/-- Backwards tail-recursive decoding loop for `(de = 1, dc = 1)` (zero GCDs, zero reverse). -/
def fromIntRun11Loop (es cs : Array Int) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRun11Loop es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((Rat.ofInt es[i], Rat.ofInt cs[i]) :: acc)

/-- Precomputed `O(1)` GCD and reduced-denominator table for a fixed nonzero denominator `d`
    (`1 < d ≤ 256`), eliminating `Nat.gcd` and denominator division during bulk rational
    reconstruction. All proof fields are `Prop` and erased at runtime. -/
structure RatDenTable (d : Nat) where
  /-- Nonzero denominator witness (erased). -/
  hd : d ≠ 0
  /-- `gcds[r] = Nat.gcd r d` for `0 ≤ r < d`. -/
  gcds : Array Nat
  /-- `dens[r] = d / Nat.gcd r d` for `0 ≤ r < d`. -/
  dens : Array Nat
  /-- Length invariant for `gcds` (erased). -/
  hg_sz : gcds.size = d
  /-- Length invariant for `dens` (erased). -/
  hd_sz : dens.size = d
  /-- Specification of `gcds` (erased). -/
  hg_spec : ∀ (r : Nat) (hr : r < d), gcds[r]'(by omega) = Nat.gcd r d
  /-- Specification of `dens` (erased). -/
  hd_spec : ∀ (r : Nat) (hr : r < d), dens[r]'(by omega) = d / Nat.gcd r d

private def buildRatDenTableLoop (d : Nat) (r : Nat) (gs ds : Array Nat) : Array Nat × Array Nat :=
  if r < d then
    let g := Nat.gcd r d
    buildRatDenTableLoop d (r + 1) (gs.push g) (ds.push (d / g))
  else (gs, ds)
termination_by d - r

private theorem buildRatDenTableLoop_size (d r : Nat) (gs ds : Array Nat)
    (hr : r ≤ d) (hg : gs.size = r) (hd : ds.size = r) :
    (buildRatDenTableLoop d r gs ds).1.size = d ∧
      (buildRatDenTableLoop d r gs ds).2.size = d := by
  unfold buildRatDenTableLoop
  split
  · rename_i hlt
    exact buildRatDenTableLoop_size d (r + 1) (gs.push (Nat.gcd r d)) (ds.push (d / Nat.gcd r d))
      (by omega) (by simp [hg]) (by simp [hd])
  · rename_i hge
    have hrd : r = d := by omega
    subst hrd
    exact ⟨hg, hd⟩
termination_by d - r

private theorem buildRatDenTableLoop_get (d r : Nat) (gs ds : Array Nat)
    (hr : r ≤ d) (hg : gs.size = r) (hd : ds.size = r)
    (hgs : ∀ (k : Nat) (hk : k < r), gs[k]'(by omega) = Nat.gcd k d)
    (hds : ∀ (k : Nat) (hk : k < r), ds[k]'(by omega) = d / Nat.gcd k d)
    (k : Nat) (hk : k < d) :
    (buildRatDenTableLoop d r gs ds).1[k]'(by rw [(buildRatDenTableLoop_size d r gs ds hr hg hd).1]; exact hk) =
        Nat.gcd k d ∧
      (buildRatDenTableLoop d r gs ds).2[k]'(by rw [(buildRatDenTableLoop_size d r gs ds hr hg hd).2]; exact hk) =
        d / Nat.gcd k d := by
  unfold buildRatDenTableLoop
  split
  · rename_i hlt
    dsimp only
    apply buildRatDenTableLoop_get d (r + 1) (gs.push (Nat.gcd r d)) (ds.push (d / Nat.gcd r d))
      (by omega) (by simp [hg]) (by simp [hd])
    · intro m hm
      by_cases hmr : m < r
      · rw [Array.getElem_push_lt (by omega)]; exact hgs m hmr
      · have hmeq : m = r := by omega
        subst hmeq
        simp only [← hg, Array.getElem_push_eq]
    · intro m hm
      by_cases hmr : m < r
      · rw [Array.getElem_push_lt (by omega)]; exact hds m hmr
      · have hmeq : m = r := by omega
        subst hmeq
        simp only [← hd, Array.getElem_push_eq]
    · exact hk
  · rename_i hge
    have hrd : r = d := by omega
    subst hrd
    exact ⟨hgs k hk, hds k hk⟩
termination_by d - r

/-- Construct a verified `RatDenTable d` in `O(d)` time (distinct `RC=1` buffers). -/
def RatDenTable.build (d : Nat) (hd : d ≠ 0) : RatDenTable d :=
  let pair := buildRatDenTableLoop d 0 (Array.mkEmpty d) (Array.mkEmpty (d + 1))
  have hsz := buildRatDenTableLoop_size d 0 (Array.mkEmpty d) (Array.mkEmpty (d + 1))
    (Nat.zero_le d) rfl rfl
  { hd
    gcds := pair.1
    dens := pair.2
    hg_sz := hsz.1
    hd_sz := hsz.2
    hg_spec := fun r hr =>
      (buildRatDenTableLoop_get d 0 (Array.mkEmpty d) (Array.mkEmpty (d + 1))
        (Nat.zero_le d) rfl rfl (fun _ hk => by omega) (fun _ hk => by omega) r hr).1
    hd_spec := fun r hr =>
      (buildRatDenTableLoop_get d 0 (Array.mkEmpty d) (Array.mkEmpty (d + 1))
        (Nat.zero_le d) rfl rfl (fun _ hk => by omega) (fun _ hk => by omega) r hr).2 }

/-- `O(1)` table-driven rational normalization for fixed denominator `d` (zero `Nat.gcd`,
    zero division when coprime, single hardware `tdiv` otherwise). -/
@[inline] def RatDenTable.mkRatFast {d : Nat} (t : RatDenTable d) (n : Int) : Rat :=
  let r := n.natAbs % d
  have hr : r < d := Nat.mod_lt _ (Nat.pos_of_ne_zero t.hd)
  let g := t.gcds[r]'(by rw [t.hg_sz]; exact hr)
  have hg_eq : g = n.natAbs.gcd d := by
    change t.gcds[r]'(by rw [t.hg_sz]; exact hr) = n.natAbs.gcd d
    rw [t.hg_spec r hr, Nat.gcd_comm n.natAbs d, Nat.gcd_rec d n.natAbs]
  if hg1 : g == 1 then
    { num := n
      den := d
      den_nz := t.hd
      reduced := by
        have h1 : g = 1 := eq_of_beq hg1
        rw [Nat.Coprime, ← hg_eq, h1] }
  else if hgd : g == d then
    Rat.ofInt (n.tdiv (Int.ofNat d))
  else
    have hdvd_num : (g : Int) ∣ n := Rat.normalize.dvd_num hg_eq
    have htdiv : n.tdiv (Int.ofNat g) = n / (g : Int) := Int.tdiv_eq_ediv_of_dvd hdvd_num
    have hden_eq : t.dens[r]'(by rw [t.hd_sz]; exact hr) = d / g := by
      rw [t.hd_spec r hr, ← t.hg_spec r hr]
    { num := n.tdiv (Int.ofNat g)
      den := t.dens[r]'(by rw [t.hd_sz]; exact hr)
      den_nz := by rw [hden_eq]; exact Rat.normalize.den_nz t.hd hg_eq
      reduced := by rw [htdiv, hden_eq]; exact Rat.normalize.reduced t.hd hg_eq }

/-- Table-driven `RatDenTable.mkRatFast` is extensionally identical to `mkRat`. -/
theorem RatDenTable.mkRatFast_eq {d : Nat} (t : RatDenTable d) (n : Int) :
    t.mkRatFast n = mkRat n d := by
  unfold RatDenTable.mkRatFast
  dsimp only
  let r := n.natAbs % d
  have hr : r < d := Nat.mod_lt _ (Nat.pos_of_ne_zero t.hd)
  let g := t.gcds[r]'(by rw [t.hg_sz]; exact hr)
  have hg_eq : g = n.natAbs.gcd d := by
    change t.gcds[r]'(by rw [t.hg_sz]; exact hr) = n.natAbs.gcd d
    rw [t.hg_spec r hr, Nat.gcd_comm n.natAbs d, Nat.gcd_rec d n.natAbs]
  have hdvd_num : (g : Int) ∣ n := Rat.normalize.dvd_num hg_eq
  have htdiv : n.tdiv (Int.ofNat g) = n / (g : Int) := Int.tdiv_eq_ediv_of_dvd hdvd_num
  have hgcd_comm : d.gcd n.natAbs = g := by rw [Nat.gcd_comm, ← hg_eq]
  change (if hg1 : g == 1 then _ else if hgd : g == d then _ else _) = mkRat n d
  split
  · rename_i hg1
    have h1 : g = 1 := eq_of_beq hg1
    apply Rat.ext
    · simp [Rat.num_mkRat, t.hd, hgcd_comm, h1]
    · simp [Rat.den_mkRat, t.hd, hgcd_comm, h1]
  · split
    · rename_i _ hgd
      have hdeq : g = d := eq_of_beq hgd
      have hpos : 0 < d := Nat.pos_of_ne_zero t.hd
      apply Rat.ext
      · simp only [Rat.ofInt, Rat.num_mkRat, t.hd, ↓reduceIte, hgcd_comm]
        rw [← hdeq]; exact htdiv
      · simp only [Rat.ofInt, Rat.den_mkRat, t.hd, ↓reduceIte, hgcd_comm, hdeq, Nat.div_self hpos]
    · have hden_eq : t.dens[r]'(by rw [t.hd_sz]; exact hr) = d / g := by
        rw [t.hd_spec r hr, ← t.hg_spec r hr]
      apply Rat.ext
      · simp only [Rat.num_mkRat, t.hd, ↓reduceIte, hgcd_comm]
        exact htdiv
      · simp only [Rat.den_mkRat, t.hd, ↓reduceIte, hgcd_comm]
        exact hden_eq

/-- Backwards tail-recursive decoding loop for `(1 < de ≤ 256, dc = 1)` using `RatDenTable`. -/
def fromIntRunD1TabLoop {de : Nat} (te : RatDenTable de) (es cs : Array Int) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRunD1TabLoop te es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((te.mkRatFast es[i], Rat.ofInt cs[i]) :: acc)

/-- Backwards tail-recursive decoding loop for `(de = 1, 1 < dc ≤ 256)` using `RatDenTable`. -/
def fromIntRun1DTabLoop {dc : Nat} (tc : RatDenTable dc) (es cs : Array Int) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRun1DTabLoop tc es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((Rat.ofInt es[i], tc.mkRatFast cs[i]) :: acc)

/-- Backwards tail-recursive decoding loop for `(de > 1, dc = 1)` (zero coeff GCDs, zero reverse). -/
def fromIntRunD1Loop (de : Nat) (es cs : Array Int) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRunD1Loop de es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((mkRat es[i] de, Rat.ofInt cs[i]) :: acc)

/-- Backwards tail-recursive decoding loop for `(de = 1, dc > 1)` (zero exp GCDs, zero reverse). -/
def fromIntRun1DLoop (dc : Nat) (es cs : Array Int) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRun1DLoop dc es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((Rat.ofInt es[i], mkRat cs[i] dc) :: acc)

/-- Backwards tail-recursive decoding loop for general `(de, dc)` (zero reverse). -/
def fromIntRunDDLoop (de dc : Nat) (es cs : Array Int) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRunDDLoop de dc es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((mkRat es[i] de, mkRat cs[i] dc) :: acc)

/-- Reconstruct a `TermList` from parallel unboxed `Array Int`s `(es, cs)` without `List.reverse`,
    using `O(1)` `RatDenTable` lookup when `1 < de ≤ 256` or `1 < dc ≤ 256`. -/
@[inline] def fromIntRun (de dc : Nat) (es cs : Array Int) : TermList :=
  if h : es.size = cs.size then
    let n := es.size
    if de == 1 then
      if dc == 1 then fromIntRun11Loop es cs n (Nat.le_refl _) (by omega) []
      else if hdc : dc ≠ 0 ∧ dc ≤ 256 then
        let tc := RatDenTable.build dc hdc.1
        fromIntRun1DTabLoop tc es cs n (Nat.le_refl _) (by omega) []
      else fromIntRun1DLoop dc es cs n (Nat.le_refl _) (by omega) []
    else
      if dc == 1 then
        if hde : de ≠ 0 ∧ de ≤ 256 then
          let te := RatDenTable.build de hde.1
          fromIntRunD1TabLoop te es cs n (Nat.le_refl _) (by omega) []
        else fromIntRunD1Loop de es cs n (Nat.le_refl _) (by omega) []
      else fromIntRunDDLoop de dc es cs n (Nat.le_refl _) (by omega) []
  else decodeIntRun de dc es cs

private theorem zipWith_take {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) (i : Nat) :
    List.zipWith f (xs.take i) (ys.take i) = (List.zipWith f xs ys).take i := by
  induction i generalizing xs ys with
  | zero => simp
  | succ i ih =>
    cases xs with
    | nil => simp
    | cons x xs' =>
      cases ys with
      | nil => simp
      | cons y ys' => simp [ih]

private theorem decodeIntRun_take_succ (de dc : Nat) (es cs : Array Int) (i : Nat)
    (he : i < es.size) (hc : i < cs.size) :
    (decodeIntRun de dc es cs).take (i + 1) =
      (decodeIntRun de dc es cs).take i ++ [(mkRat es[i] de, mkRat cs[i] dc)] := by
  unfold decodeIntRun
  rw [← zipWith_take, ← zipWith_take]
  have h1 : es.toList.take (i + 1) = es.toList.take i ++ [es[i]] := by
    have hi' : i < es.toList.length := by simpa using he
    simpa using List.take_succ_eq_append_getElem hi'
  have h2 : cs.toList.take (i + 1) = cs.toList.take i ++ [cs[i]] := by
    have hi' : i < cs.toList.length := by simpa using hc
    simpa using List.take_succ_eq_append_getElem hi'
  rw [h1, h2]
  have hlen : (es.toList.take i).length = (cs.toList.take i).length := by
    simp [List.length_take]; omega
  generalize es.toList.take i = l1, cs.toList.take i = l2 at hlen ⊢
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons] at hlen ⊢
      congr 1; exact ih ys (by omega)

private theorem fromIntRun11Loop_eq (es cs : Array Int) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRun11Loop es cs i he hc acc = (decodeIntRun 1 1 es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRun11Loop]
  | succ i ih =>
    simp only [fromIntRun11Loop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRun_take_succ 1 1 es cs i (by omega) (by omega),
        mkRat_one, mkRat_one, List.append_assoc]
    rfl

private theorem fromIntRunD1Loop_eq (de : Nat) (es cs : Array Int) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRunD1Loop de es cs i he hc acc = (decodeIntRun de 1 es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRunD1Loop]
  | succ i ih =>
    simp only [fromIntRunD1Loop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRun_take_succ de 1 es cs i (by omega) (by omega),
        mkRat_one, List.append_assoc]
    rfl

private theorem fromIntRun1DLoop_eq (dc : Nat) (es cs : Array Int) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRun1DLoop dc es cs i he hc acc = (decodeIntRun 1 dc es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRun1DLoop]
  | succ i ih =>
    simp only [fromIntRun1DLoop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRun_take_succ 1 dc es cs i (by omega) (by omega),
        mkRat_one, List.append_assoc]
    rfl

private theorem fromIntRunDDLoop_eq (de dc : Nat) (es cs : Array Int) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRunDDLoop de dc es cs i he hc acc = (decodeIntRun de dc es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRunDDLoop]
  | succ i ih =>
    simp only [fromIntRunDDLoop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRun_take_succ de dc es cs i (by omega) (by omega),
        List.append_assoc]
    rfl

private theorem fromIntRunD1TabLoop_eq {de : Nat} (te : RatDenTable de) (es cs : Array Int) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRunD1TabLoop te es cs i he hc acc = (decodeIntRun de 1 es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRunD1TabLoop]
  | succ i ih =>
    simp only [fromIntRunD1TabLoop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRun_take_succ de 1 es cs i (by omega) (by omega),
        te.mkRatFast_eq, mkRat_one, List.append_assoc]
    rfl

private theorem fromIntRun1DTabLoop_eq {dc : Nat} (tc : RatDenTable dc) (es cs : Array Int) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRun1DTabLoop tc es cs i he hc acc = (decodeIntRun 1 dc es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRun1DTabLoop]
  | succ i ih =>
    simp only [fromIntRun1DTabLoop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRun_take_succ 1 dc es cs i (by omega) (by omega),
        tc.mkRatFast_eq, mkRat_one, List.append_assoc]
    rfl

private theorem fromIntRun_eq_decode (de dc : Nat) (es cs : Array Int) :
    fromIntRun de dc es cs = decodeIntRun de dc es cs := by
  unfold fromIntRun
  split
  · rename_i hsz
    dsimp only
    have htake : (decodeIntRun de dc es cs).take es.size = decodeIntRun de dc es cs := by
      apply List.take_of_length_le
      unfold decodeIntRun; simp only [List.length_zipWith, Array.length_toList]; omega
    split
    · rename_i hde1
      have hde_eq : de = 1 := eq_of_beq hde1
      subst hde_eq
      split
      · rename_i hdc1
        have hdc_eq : dc = 1 := eq_of_beq hdc1
        subst hdc_eq
        rw [fromIntRun11Loop_eq, htake, List.append_nil]
      · split
        · rw [fromIntRun1DTabLoop_eq, htake, List.append_nil]
        · rw [fromIntRun1DLoop_eq, htake, List.append_nil]
    · split
      · rename_i _ hdc1
        have hdc_eq : dc = 1 := eq_of_beq hdc1
        subst hdc_eq
        split
        · rw [fromIntRunD1TabLoop_eq, htake, List.append_nil]
        · rw [fromIntRunD1Loop_eq, htake, List.append_nil]
      · rw [fromIntRunDDLoop_eq, htake, List.append_nil]
  · rfl

/-! #### Path B: Hybrid Scaled-Exponent `Array Int × Array Rat` SOA Kernel -/

/-- Decode hybrid `(es : Array Int, cs : Array Rat)` back into a `TermList` (spec helper). -/
def decodeIntRatRun (de : Nat) (es : Array Int) (cs : Array Rat) : TermList :=
  List.zipWith (fun e c => (mkRat e de, c)) es.toList cs.toList

private theorem decodeIntRatRun_push (de : Nat) (es : Array Int) (cs : Array Rat)
    (hsz : es.size = cs.size) (e : Int) (c : Rat) :
    decodeIntRatRun de (es.push e) (cs.push c) =
      decodeIntRatRun de es cs ++ [(mkRat e de, c)] := by
  unfold decodeIntRatRun
  simp only [Array.toList_push]
  have hlen : es.toList.length = cs.toList.length := by simpa using hsz
  generalize es.toList = l1, cs.toList = l2 at hlen ⊢
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons] at hlen ⊢
      congr 1; exact ih ys (by omega)

/-- Lift a `TermList` into hybrid `(Array Int, Array Rat)` with exponents scaled by `de`. -/
def liftIntRatTermsLoop (de : Nat) : TermList → Array Int → Array Rat → Array Int × Array Rat
  | [], es, cs => (es, cs)
  | (e, c) :: rest, es, cs =>
    let ei := if de == 1 then e.num else e.num * Int.ofNat (de / e.den)
    liftIntRatTermsLoop de rest (es.push ei) (cs.push c)

/-- Entry point for lifting a `TermList` into hybrid `(Array Int, Array Rat)` (distinct `RC=1` buffers). -/
@[inline] def liftIntRatTerms (de : Nat) (ts : TermList) : Array Int × Array Rat :=
  let n := ts.length
  liftIntRatTermsLoop de ts (Array.mkEmpty n) (Array.mkEmpty (n + 1))

private theorem liftIntRatTermsLoop_spec (de : Nat) (hde : de ≠ 0)
    (ts : TermList) (accE : Array Int) (accC : Array Rat) (hsz : accE.size = accC.size)
    (he_dvd : ∀ p ∈ ts, p.1.den ∣ de) :
    let res := liftIntRatTermsLoop de ts accE accC
    res.1.size = res.2.size ∧
      decodeIntRatRun de res.1 res.2 = decodeIntRatRun de accE accC ++ ts := by
  induction ts generalizing accE accC with
  | nil => simp [liftIntRatTermsLoop, hsz]
  | cons p rest ih =>
    rcases p with ⟨e, c⟩
    simp only [liftIntRatTermsLoop]
    have hed : e.den ∣ de := he_dvd (e, c) (List.mem_cons_self ..)
    have he_eq : mkRat (if de == 1 then e.num else e.num * Int.ofNat (de / e.den)) de = e := by
      split
      · rename_i h1
        have hde1 : de = 1 := eq_of_beq h1
        subst hde1
        have hden1 : e.den = 1 := Nat.dvd_one.mp hed
        rw [mkRat_one]; apply Rat.ext <;> simp [Rat.ofInt, hden1]
      · exact mkRat_scaled_eq e hde hed
    let ei : Int := if de == 1 then e.num else e.num * Int.ofNat (de / e.den)
    have ⟨hs, hd⟩ := ih (accE.push ei) (accC.push c) (by simp [hsz])
      (fun q hq => he_dvd q (List.mem_cons_of_mem _ hq))
    refine ⟨hs, ?_⟩
    rw [hd, decodeIntRatRun_push _ accE accC hsz ei c, he_eq, List.append_assoc]; rfl

/-- Append slice `[i..]` of hybrid `(srcE, srcC)` onto `(accE, accC)`. -/
def appendIntRatLoop (srcE : Array Int) (srcC : Array Rat) (i : Nat)
    (accE : Array Int) (accC : Array Rat) : Array Int × Array Rat :=
  if hi : i < srcE.size then
    if hic : i < srcC.size then
      appendIntRatLoop srcE srcC (i + 1) (accE.push srcE[i]) (accC.push srcC[i])
    else (accE, accC)
  else (accE, accC)
termination_by srcE.size - i

private theorem appendIntRatLoop_spec (de : Nat) (srcE : Array Int) (srcC : Array Rat)
    (hsrc : srcE.size = srcC.size) (i : Nat) (accE : Array Int) (accC : Array Rat)
    (hacc : accE.size = accC.size) :
    let res := appendIntRatLoop srcE srcC i accE accC
    res.1.size = res.2.size ∧
      decodeIntRatRun de res.1 res.2 =
        decodeIntRatRun de accE accC ++ (decodeIntRatRun de srcE srcC).drop i := by
  unfold appendIntRatLoop
  split
  · rename_i hi
    have hic : i < srcC.size := by omega
    simp only [hic, ↓reduceDIte]
    have ⟨hs, hd⟩ := appendIntRatLoop_spec de srcE srcC hsrc (i + 1)
      (accE.push srcE[i]) (accC.push srcC[i]) (by simp [hacc])
    refine ⟨hs, ?_⟩
    rw [hd, decodeIntRatRun_push _ accE accC hacc, List.append_assoc]
    congr 1
    unfold decodeIntRatRun
    rw [← zipWith_drop, ← zipWith_drop]
    have hedrop : srcE.toList.drop i = srcE[i] :: srcE.toList.drop (i + 1) := by
      have hi' : i < srcE.toList.length := by simpa using hi
      simpa using List.drop_eq_getElem_cons hi'
    have hcdrop : srcC.toList.drop i = srcC[i] :: srcC.toList.drop (i + 1) := by
      have hic' : i < srcC.toList.length := by simpa using hic
      simpa using List.drop_eq_getElem_cons hic'
    rw [hedrop, hcdrop]; rfl
  · rename_i hge
    refine ⟨hacc, ?_⟩
    have hdrop : (decodeIntRatRun de srcE srcC).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
    simp [hdrop]
termination_by srcE.size - i

/-- Scale hybrid `(yes, ycs)` by `(ex, cx)`. -/
def scaleIntRatLoop (ex : Int) (cx : Rat) (yes : Array Int) (ycs : Array Rat) (i : Nat)
    (accE : Array Int) (accC : Array Rat) : Array Int × Array Rat :=
  if hi : i < yes.size then
    if hic : i < ycs.size then
      scaleIntRatLoop ex cx yes ycs (i + 1)
        (accE.push (ex + yes[i])) (accC.push (ratMulFast cx ycs[i]))
    else (accE, accC)
  else (accE, accC)
termination_by yes.size - i

/-- Entry point for hybrid scaled-exponent term scaling (distinct `RC=1` buffers). -/
@[inline] def scaleIntRatRun (ex : Int) (cx : Rat) (yes : Array Int) (ycs : Array Rat) :
    Array Int × Array Rat :=
  if cx.num == 0 then (#[], #[])
  else scaleIntRatLoop ex cx yes ycs 0 (Array.mkEmpty yes.size) (Array.mkEmpty (yes.size + 1))

private theorem scaleIntRatLoop_spec (de : Nat) (hde : de ≠ 0) (ex : Int) (cx : Rat)
    (yes : Array Int) (ycs : Array Rat) (hy : yes.size = ycs.size) (i : Nat)
    (accE : Array Int) (accC : Array Rat) (hacc : accE.size = accC.size) :
    let res := scaleIntRatLoop ex cx yes ycs i accE accC
    res.1.size = res.2.size ∧
      decodeIntRatRun de res.1 res.2 =
        decodeIntRatRun de accE accC ++
          ((decodeIntRatRun de yes ycs).drop i).map (fun (ey, cy) => (mkRat ex de + ey, cx * cy)) := by
  unfold scaleIntRatLoop
  split
  · rename_i hi
    have hic : i < ycs.size := by omega
    simp only [hic, ↓reduceDIte]
    have ⟨hs, hd⟩ := scaleIntRatLoop_spec de hde ex cx yes ycs hy (i + 1)
      (accE.push (ex + yes[i])) (accC.push (ratMulFast cx ycs[i])) (by simp [hacc])
    refine ⟨hs, ?_⟩
    rw [hd, decodeIntRatRun_push _ accE accC hacc, List.append_assoc]
    congr 1
    have hdrop : (decodeIntRatRun de yes ycs).drop i =
        (mkRat yes[i] de, ycs[i]) :: (decodeIntRatRun de yes ycs).drop (i + 1) := by
      unfold decodeIntRatRun
      rw [← zipWith_drop, ← zipWith_drop]
      have hedrop : yes.toList.drop i = yes[i] :: yes.toList.drop (i + 1) := by
        have hi' : i < yes.toList.length := by simpa using hi
        simpa using List.drop_eq_getElem_cons hi'
      have hcdrop : ycs.toList.drop i = ycs[i] :: ycs.toList.drop (i + 1) := by
        have hic' : i < ycs.toList.length := by simpa using hic
        simpa using List.drop_eq_getElem_cons hic'
      rw [hedrop, hcdrop]; rfl
    rw [hdrop, List.map_cons, mkRat_add_same_den ex yes[i] hde, ratMulFast_eq]; rfl
  · rename_i hge
    refine ⟨hacc, ?_⟩
    have hdrop : (decodeIntRatRun de yes ycs).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
    simp [hdrop]
termination_by yes.size - i

private theorem scaleIntRatRun_spec (de : Nat) (hde : de ≠ 0) (ex : Int) (cx : Rat)
    (yes : Array Int) (ycs : Array Rat) (hy : yes.size = ycs.size) :
    let res := scaleIntRatRun ex cx yes ycs
    res.1.size = res.2.size ∧
      decodeIntRatRun de res.1 res.2 =
        scaleTerm (mkRat ex de) cx (decodeIntRatRun de yes ycs) := by
  unfold scaleIntRatRun scaleTerm
  rw [rat_num_beq_zero_eq]
  split
  · exact ⟨rfl, rfl⟩
  · have ⟨hs, hd⟩ := scaleIntRatLoop_spec de hde ex cx yes ycs hy 0
      (Array.mkEmpty yes.size) (Array.mkEmpty (yes.size + 1)) rfl
    exact ⟨hs, by simpa [decodeIntRatRun] using hd⟩

/-- Two-pointer sorted merge over hybrid `(Array Int, Array Rat)` runs. -/
def mergeIntRatLoop (xes : Array Int) (xcs : Array Rat) (yes : Array Int) (ycs : Array Rat)
    (i j : Nat) (accE : Array Int) (accC : Array Rat) : Array Int × Array Rat :=
  if hi : i < xes.size then
    if hj : j < yes.size then
      if hic : i < xcs.size then
        if hjc : j < ycs.size then
          let ex := xes[i]
          let ey := yes[j]
          if ex > ey then
            mergeIntRatLoop xes xcs yes ycs (i + 1) j (accE.push ex) (accC.push xcs[i])
          else if ey > ex then
            mergeIntRatLoop xes xcs yes ycs i (j + 1) (accE.push ey) (accC.push ycs[j])
          else
            let s := ratAddFast xcs[i] ycs[j]
            if s.num == 0 then
              mergeIntRatLoop xes xcs yes ycs (i + 1) (j + 1) accE accC
            else
              mergeIntRatLoop xes xcs yes ycs (i + 1) (j + 1) (accE.push ex) (accC.push s)
        else appendIntRatLoop xes xcs i accE accC
      else appendIntRatLoop yes ycs j accE accC
    else appendIntRatLoop xes xcs i accE accC
  else appendIntRatLoop yes ycs j accE accC
termination_by (xes.size - i) + (yes.size - j)

/-- Entry point for hybrid `(Array Int, Array Rat)` sorted merge (distinct `RC=1` buffers). -/
@[inline] def mergeIntRatRun (rx ry : Array Int × Array Rat) : Array Int × Array Rat :=
  let cap := rx.1.size + ry.1.size
  mergeIntRatLoop rx.1 rx.2 ry.1 ry.2 0 0 (Array.mkEmpty cap) (Array.mkEmpty (cap + 1))

private theorem mergeIntRatLoop_spec (de : Nat) (hde : de ≠ 0)
    (xes : Array Int) (xcs : Array Rat) (yes : Array Int) (ycs : Array Rat)
    (hx : xes.size = xcs.size) (hy : yes.size = ycs.size)
    (i j : Nat) (accE : Array Int) (accC : Array Rat) (hacc : accE.size = accC.size) :
    let res := mergeIntRatLoop xes xcs yes ycs i j accE accC
    res.1.size = res.2.size ∧
      decodeIntRatRun de res.1 res.2 =
        decodeIntRatRun de accE accC ++
          addMerge ((decodeIntRatRun de xes xcs).drop i) ((decodeIntRatRun de yes ycs).drop j) := by
  unfold mergeIntRatLoop
  split
  · rename_i hi
    have hxdrop : (decodeIntRatRun de xes xcs).drop i =
        (mkRat xes[i] de, xcs[i]) :: (decodeIntRatRun de xes xcs).drop (i + 1) := by
      unfold decodeIntRatRun
      rw [← zipWith_drop, ← zipWith_drop]
      have hedrop : xes.toList.drop i = xes[i] :: xes.toList.drop (i + 1) := by
        have hi' : i < xes.toList.length := by simpa using hi
        simpa using List.drop_eq_getElem_cons hi'
      have hcdrop : xcs.toList.drop i = xcs[i] :: xcs.toList.drop (i + 1) := by
        have hic' : i < xcs.toList.length := by simp; omega
        simpa using List.drop_eq_getElem_cons hic'
      rw [hedrop, hcdrop]; rfl
    split
    · rename_i hj
      have hic : i < xcs.size := by omega
      have hjc : j < ycs.size := by omega
      simp only [hic, hjc, ↓reduceDIte]
      have hydrop : (decodeIntRatRun de yes ycs).drop j =
          (mkRat yes[j] de, ycs[j]) :: (decodeIntRatRun de yes ycs).drop (j + 1) := by
        unfold decodeIntRatRun
        rw [← zipWith_drop, ← zipWith_drop]
        have hedrop : yes.toList.drop j = yes[j] :: yes.toList.drop (j + 1) := by
          have hj' : j < yes.toList.length := by simpa using hj
          simpa using List.drop_eq_getElem_cons hj'
        have hcdrop : ycs.toList.drop j = ycs[j] :: ycs.toList.drop (j + 1) := by
          have hjc' : j < ycs.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hjc'
        rw [hedrop, hcdrop]; rfl
      split
      · rename_i hgt
        have hrat_gt : mkRat xes[i] de > mkRat yes[j] de := (mkRat_lt_iff hde).mpr hgt
        have ⟨hs, hd⟩ := mergeIntRatLoop_spec de hde xes xcs yes ycs hx hy (i + 1) j
          (accE.push xes[i]) (accC.push xcs[i]) (by simp [hacc])
        refine ⟨hs, ?_⟩
        rw [hd, decodeIntRatRun_push _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
        simp only [addMerge, hrat_gt, ↓reduceIte]; rfl
      · split
        · rename_i hngt hlt
          have hrat_ngt : ¬ (mkRat xes[i] de > mkRat yes[j] de) := by
            intro h; exact hngt ((mkRat_lt_iff hde).mp h)
          have hrat_lt : mkRat yes[j] de > mkRat xes[i] de := (mkRat_lt_iff hde).mpr hlt
          have ⟨hs, hd⟩ := mergeIntRatLoop_spec de hde xes xcs yes ycs hx hy i (j + 1)
            (accE.push yes[j]) (accC.push ycs[j]) (by simp [hacc])
          refine ⟨hs, ?_⟩
          rw [hd, decodeIntRatRun_push _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
          simp only [addMerge, hrat_ngt, hrat_lt, ↓reduceIte]; rfl
        · rename_i hngt hnlt
          have hrat_ngt : ¬ (mkRat xes[i] de > mkRat yes[j] de) := by
            intro h; exact hngt ((mkRat_lt_iff hde).mp h)
          have hrat_nlt : ¬ (mkRat yes[j] de > mkRat xes[i] de) := by
            intro h; exact hnlt ((mkRat_lt_iff hde).mp h)
          rw [ratAddFast_eq, rat_num_beq_zero_eq]
          split
          · rename_i hz
            have ⟨hs, hd⟩ := mergeIntRatLoop_spec de hde xes xcs yes ycs hx hy (i + 1) (j + 1)
              accE accC hacc
            refine ⟨hs, ?_⟩
            rw [hd, hxdrop, hydrop]
            simp only [addMerge, hrat_ngt, hrat_nlt, hz, ↓reduceIte]
          · rename_i hnz
            have ⟨hs, hd⟩ := mergeIntRatLoop_spec de hde xes xcs yes ycs hx hy (i + 1) (j + 1)
              (accE.push xes[i]) (accC.push (xcs[i] + ycs[j])) (by simp [hacc])
            refine ⟨hs, ?_⟩
            rw [hd, decodeIntRatRun_push _ accE accC hacc, List.append_assoc, hxdrop, hydrop]
            simp only [addMerge, hrat_ngt, hrat_nlt, hnz, ↓reduceIte]; rfl
    · rename_i hnj
      have hydrop : (decodeIntRatRun de yes ycs).drop j = [] := by
        apply List.drop_eq_nil_of_le
        unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
      have ⟨hs, hd⟩ := appendIntRatLoop_spec de xes xcs hx i accE accC hacc
      refine ⟨hs, ?_⟩
      rw [hd, hydrop, hxdrop]; simp [addMerge]
  · rename_i hni
    have hxdrop : (decodeIntRatRun de xes xcs).drop i = [] := by
      apply List.drop_eq_nil_of_le
      unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
    have ⟨hs, hd⟩ := appendIntRatLoop_spec de yes ycs hy j accE accC hacc
    refine ⟨hs, ?_⟩
    rw [hd, hxdrop]; simp [addMerge]
termination_by (xes.size - i) + (yes.size - j)

private theorem mergeIntRatRun_spec (de : Nat) (hde : de ≠ 0)
    (rx ry : Array Int × Array Rat) (hx : rx.1.size = rx.2.size) (hy : ry.1.size = ry.2.size) :
    let res := mergeIntRatRun rx ry
    res.1.size = res.2.size ∧
      decodeIntRatRun de res.1 res.2 =
        addMerge (decodeIntRatRun de rx.1 rx.2) (decodeIntRatRun de ry.1 ry.2) := by
  have ⟨hs, hd⟩ := mergeIntRatLoop_spec de hde rx.1 rx.2 ry.1 ry.2 hx hy 0 0
    (Array.mkEmpty (rx.1.size + ry.1.size)) (Array.mkEmpty (rx.1.size + ry.1.size + 1)) rfl
  exact ⟨hs, by simpa [mergeIntRatRun, decodeIntRatRun] using hd⟩

/-- Depth-first power-of-two divide-and-conquer sparse multiplication for hybrid
    `(Array Int, Array Rat)` runs (unboxed `Int` exponents, exact `Rat` coefficients). -/
def mulIntRatDC (xes : Array Int) (xcs : Array Rat) (yes : Array Int) (ycs : Array Rat)
    (lo len : Nat) : Array Int × Array Rat :=
  if h0 : len = 0 then (#[], #[])
  else if h1 : len = 1 then
    if _hlo : lo < xes.size ∧ lo < xcs.size then
      scaleIntRatRun xes[lo] xcs[lo] yes ycs
    else (#[], #[])
  else
    let p := (len - 1).log2
    let k := 1 <<< p
    have hk_eq : k = 2 ^ p := by simp [k, Nat.shiftLeft_eq]
    have hk_pos : 0 < k := by rw [hk_eq]; exact Nat.two_pow_pos p
    have hk_lt : k < len := by
      have hle : 2 ^ p ≤ len - 1 := Nat.log2_self_le (by omega)
      omega
    have hrem_lt : len - k < len := by omega
    let left := mulIntRatDC xes xcs yes ycs lo k
    let right := mulIntRatDC xes xcs yes ycs (lo + k) (len - k)
    mergeIntRatRun left right
termination_by len

private theorem mulIntRatDC_spec (de : Nat) (hde : de ≠ 0)
    (xes : Array Int) (xcs : Array Rat) (yes : Array Int) (ycs : Array Rat)
    (hx : xes.size = xcs.size) (hy : yes.size = ycs.size)
    (lo len : Nat) (hbound : lo + len ≤ xes.size) :
    (mulIntRatDC xes xcs yes ycs lo len).1.size = (mulIntRatDC xes xcs yes ycs lo len).2.size ∧
      decodeIntRatRun de (mulIntRatDC xes xcs yes ycs lo len).1
        (mulIntRatDC xes xcs yes ycs lo len).2 =
        mergeAll (((decodeIntRatRun de xes xcs).drop lo |>.take len).map
          (fun (ex, cx) => scaleTerm ex cx (decodeIntRatRun de yes ycs))) := by
  have hslice : ∀ a b, a + b ≤ xes.size →
      ((decodeIntRatRun de xes xcs).drop a |>.take b).length = b := by
    intro a b hab
    rw [List.length_take, List.length_drop]
    unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
  unfold mulIntRatDC
  split
  · rename_i h0; subst h0; exact ⟨rfl, by simp [mergeAll, decodeIntRatRun]⟩
  · split
    · rename_i _ h1; subst h1
      have hlo : lo < xes.size ∧ lo < xcs.size := by omega
      simp only [hlo]
      have ⟨hs, hd⟩ := scaleIntRatRun_spec de hde xes[lo] xcs[lo] yes ycs hy
      refine ⟨hs, ?_⟩
      have hdrop : (decodeIntRatRun de xes xcs).drop lo =
          (mkRat xes[lo] de, xcs[lo]) :: (decodeIntRatRun de xes xcs).drop (lo + 1) := by
        unfold decodeIntRatRun
        rw [← zipWith_drop, ← zipWith_drop]
        have hedrop : xes.toList.drop lo = xes[lo] :: xes.toList.drop (lo + 1) := by
          have hi' : lo < xes.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hi'
        have hcdrop : xcs.toList.drop lo = xcs[lo] :: xcs.toList.drop (lo + 1) := by
          have hic' : lo < xcs.toList.length := by simp; omega
          simpa using List.drop_eq_getElem_cons hic'
        rw [hedrop, hcdrop]; rfl
      rw [hdrop]; simp [mergeAll, hd]
    · rename_i hne0 hne1
      dsimp only
      let p := (len - 1).log2
      let k := 1 <<< p
      have hk_eq : k = 2 ^ p := by simp [k, Nat.shiftLeft_eq]
      have hk_pos : 0 < k := by rw [hk_eq]; exact Nat.two_pow_pos p
      have hk_lt : k < len := by
        have hle : 2 ^ p ≤ len - 1 := Nat.log2_self_le (by omega)
        omega
      have hrem_lt : len - k < len := by omega
      have hrem_le : len - k ≤ 2 ^ p := by
        have hlt : len - 1 < 2 ^ (p + 1) := Nat.lt_log2_self
        rw [Nat.pow_succ] at hlt
        omega
      have ⟨hsL, hdL⟩ := mulIntRatDC_spec de hde xes xcs yes ycs hx hy lo k (by omega)
      have ⟨hsR, hdR⟩ := mulIntRatDC_spec de hde xes xcs yes ycs hx hy (lo + k) (len - k) (by omega)
      have ⟨hsM, hdM⟩ := mergeIntRatRun_spec de hde
        (mulIntRatDC xes xcs yes ycs lo k) (mulIntRatDC xes xcs yes ycs (lo + k) (len - k)) hsL hsR
      refine ⟨hsM, ?_⟩
      rw [hdM, hdL, hdR]
      have hsplit : ((decodeIntRatRun de xes xcs).drop lo).take len =
          ((decodeIntRatRun de xes xcs).drop lo).take k ++
          ((decodeIntRatRun de xes xcs).drop (lo + k)).take (len - k) := by
        have hlen_sum : len = k + (len - k) := by omega
        calc ((decodeIntRatRun de xes xcs).drop lo).take len
            = ((decodeIntRatRun de xes xcs).drop lo).take (k + (len - k)) := by rw [← hlen_sum]
          _ = ((decodeIntRatRun de xes xcs).drop lo).take k ++
              (((decodeIntRatRun de xes xcs).drop lo).drop k).take (len - k) := List.take_add
          _ = ((decodeIntRatRun de xes xcs).drop lo).take k ++
              ((decodeIntRatRun de xes xcs).drop (lo + k)).take (len - k) := by
                rw [List.drop_drop, Nat.add_comm]
      rw [hsplit, List.map_append]
      symm
      apply mergeAll_append_pow2 p
      · rw [List.length_map, hslice lo k (by omega), hk_eq]
      · rw [List.length_map, hslice (lo + k) (len - k) (by omega)]; omega
      · rw [List.length_map, hslice (lo + k) (len - k) (by omega)]; exact hrem_le
termination_by len

/-- Backwards tail-recursive decoding loop for hybrid `(de = 1, Rat)`. -/
def fromIntRat1Loop (es : Array Int) (cs : Array Rat) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRat1Loop es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((Rat.ofInt es[i], cs[i]) :: acc)

/-- Backwards tail-recursive decoding loop for hybrid `(de > 1, Rat)`. -/
def fromIntRatDLoop (de : Nat) (es : Array Int) (cs : Array Rat) :
    (i : Nat) → i ≤ es.size → i ≤ cs.size → TermList → TermList
  | 0, _, _, acc => acc
  | i + 1, he, hc, acc =>
    fromIntRatDLoop de es cs i (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc)
      ((mkRat es[i] de, cs[i]) :: acc)

/-- Reconstruct a `TermList` from hybrid `(Array Int, Array Rat)` without `List.reverse`. -/
@[inline] def fromIntRatRun (de : Nat) (es : Array Int) (cs : Array Rat) : TermList :=
  if h : es.size = cs.size then
    let n := es.size
    if de == 1 then fromIntRat1Loop es cs n (Nat.le_refl _) (by omega) []
    else fromIntRatDLoop de es cs n (Nat.le_refl _) (by omega) []
  else decodeIntRatRun de es cs

private theorem decodeIntRatRun_take_succ (de : Nat) (es : Array Int) (cs : Array Rat) (i : Nat)
    (he : i < es.size) (hc : i < cs.size) :
    (decodeIntRatRun de es cs).take (i + 1) =
      (decodeIntRatRun de es cs).take i ++ [(mkRat es[i] de, cs[i])] := by
  unfold decodeIntRatRun
  rw [← zipWith_take, ← zipWith_take]
  have h1 : es.toList.take (i + 1) = es.toList.take i ++ [es[i]] := by
    have hi' : i < es.toList.length := by simpa using he
    simpa using List.take_succ_eq_append_getElem hi'
  have h2 : cs.toList.take (i + 1) = cs.toList.take i ++ [cs[i]] := by
    have hi' : i < cs.toList.length := by simpa using hc
    simpa using List.take_succ_eq_append_getElem hi'
  rw [h1, h2]
  have hlen : (es.toList.take i).length = (cs.toList.take i).length := by
    simp [List.length_take]; omega
  generalize es.toList.take i = l1, cs.toList.take i = l2 at hlen ⊢
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons x xs ih =>
    cases l2 with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.cons_append, List.zipWith_cons_cons, List.length_cons] at hlen ⊢
      congr 1; exact ih ys (by omega)

private theorem fromIntRat1Loop_eq (es : Array Int) (cs : Array Rat) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRat1Loop es cs i he hc acc = (decodeIntRatRun 1 es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRat1Loop]
  | succ i ih =>
    simp only [fromIntRat1Loop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRatRun_take_succ 1 es cs i (by omega) (by omega),
        mkRat_one, List.append_assoc]; rfl

private theorem fromIntRatDLoop_eq (de : Nat) (es : Array Int) (cs : Array Rat) (i : Nat)
    (he : i ≤ es.size) (hc : i ≤ cs.size) (acc : TermList) :
    fromIntRatDLoop de es cs i he hc acc = (decodeIntRatRun de es cs).take i ++ acc := by
  induction i generalizing acc with
  | zero => simp [fromIntRatDLoop]
  | succ i ih =>
    simp only [fromIntRatDLoop]
    rw [ih (Nat.le_of_succ_le he) (Nat.le_of_succ_le hc),
        decodeIntRatRun_take_succ de es cs i (by omega) (by omega),
        List.append_assoc]; rfl

private theorem fromIntRatRun_eq_decode (de : Nat) (es : Array Int) (cs : Array Rat) :
    fromIntRatRun de es cs = decodeIntRatRun de es cs := by
  unfold fromIntRatRun
  split
  · rename_i hsz
    dsimp only
    have htake : (decodeIntRatRun de es cs).take es.size = decodeIntRatRun de es cs := by
      apply List.take_of_length_le
      unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
    split
    · rename_i hde1
      have hde_eq : de = 1 := eq_of_beq hde1
      subst hde_eq
      rw [fromIntRat1Loop_eq, htake, List.append_nil]
    · rw [fromIntRatDLoop_eq, htake, List.append_nil]
  · rfl

/-- Helper computing common exponent denominator across both operands (`0` on bound overflow). -/
@[inline] def scanExpLcmBoth (maxDen : Nat) (xs ys : TermList) : Nat :=
  let de1 := scanExpLcm maxDen xs 1
  if de1 == 0 then 0 else scanExpLcm maxDen ys de1

private theorem scanExpLcmBoth_dvd (maxDen : Nat) (xs ys : TermList) (de : Nat)
    (h : scanExpLcmBoth maxDen xs ys = de) (hde : de ≠ 0) :
    (∀ p ∈ xs, p.1.den ∣ de) ∧ (∀ p ∈ ys, p.1.den ∣ de) := by
  unfold scanExpLcmBoth at h
  dsimp only at h
  split at h
  · exact absurd h.symm hde
  · rename_i hne
    have hde1 : scanExpLcm maxDen xs 1 ≠ 0 := by
      intro h0; simp [h0] at hne
    have ⟨_, hxs1⟩ := scanExpLcm_dvd maxDen xs 1 _ (by decide) rfl hde1
    have ⟨hde1_dvd, hys⟩ := scanExpLcm_dvd maxDen ys _ de hde1 h hde
    exact ⟨fun p hp => Nat.dvd_trans (hxs1 p hp) hde1_dvd, hys⟩

/-- Dispatch a general sparse multiply `xs * ys` (with `xs` as outer operand) through:
    1. Pure unboxed `Array Int × Array Int` SOA (`mulIntDC`, fused 2-leaf, L1-cache-resident),
    2. Hybrid scaled-exponent `Array Int × Array Rat` SOA (`mulIntRatDC`),
    3. General `Array (Rat × Rat)` fallback (`mergeAllArr`). -/
def mulTreeOrderedArr (xs ys : TermList) : TermList :=
  let maxDen : Nat := 1 <<< 28
  let de := scanExpLcmBoth maxDen xs ys
  if de != 0 then
    let dcx := scanCoeffLcm maxDen xs 1
    let dcy := scanCoeffLcm maxDen ys 1
    if dcx != 0 && dcy != 0 then
      let (xes, xcs) := liftIntTerms de dcx xs
      let (yes, ycs) := liftIntTerms de dcy ys
      if hy : yes.size = ycs.size then
        let (resE, resC) := mulIntDC xes xcs yes ycs hy 0 xes.size
        fromIntRun de (dcx * dcy) resE resC
      else
        let ysArr := ys.toArray
        (mergeAllArr (xs.map (fun (ex, cx) => scaleTermArr ex cx ysArr))).toList
    else
      let (xes, xcs) := liftIntRatTerms de xs
      let (yes, ycs) := liftIntRatTerms de ys
      let (resE, resC) := mulIntRatDC xes xcs yes ycs 0 xes.size
      fromIntRatRun de resE resC
  else
    let ysArr := ys.toArray
    (mergeAllArr (xs.map (fun (ex, cx) => scaleTermArr ex cx ysArr))).toList

private theorem mulTreeOrderedArr_eq (xs ys : TermList) :
    mulTreeOrderedArr xs ys = mergeAll (xs.map (fun (ex, cx) => scaleTerm ex cx ys)) := by
  unfold mulTreeOrderedArr
  dsimp only
  split
  · rename_i hde_nz
    have hde : scanExpLcmBoth (1 <<< 28) xs ys ≠ 0 := by simpa using hde_nz
    have ⟨hxs_edvd, hys_edvd⟩ := scanExpLcmBoth_dvd (1 <<< 28) xs ys _ rfl hde
    let de := scanExpLcmBoth (1 <<< 28) xs ys
    split
    · rename_i hdc_nz
      simp only [Bool.and_eq_true, bne_iff_ne] at hdc_nz
      rcases hdc_nz with ⟨hdcx, hdcy⟩
      let dcx := scanCoeffLcm (1 <<< 28) xs 1
      let dcy := scanCoeffLcm (1 <<< 28) ys 1
      have ⟨_, hxs_cdvd⟩ := scanCoeffLcm_dvd (1 <<< 28) xs 1 dcx (by decide) rfl hdcx
      have ⟨_, hys_cdvd⟩ := scanCoeffLcm_dvd (1 <<< 28) ys 1 dcy (by decide) rfl hdcy
      have ⟨hxs_sz, hxs_dec⟩ := liftIntTermsLoop_spec de dcx hde hdcx
        xs (Array.mkEmpty xs.length) (Array.mkEmpty (xs.length + 1)) rfl hxs_edvd hxs_cdvd
      have ⟨hys_sz, hys_dec⟩ := liftIntTermsLoop_spec de dcy hde hdcy
        ys (Array.mkEmpty ys.length) (Array.mkEmpty (ys.length + 1)) rfl hys_edvd hys_cdvd
      have hxs_dec' : decodeIntRun de dcx (liftIntTerms de dcx xs).1 (liftIntTerms de dcx xs).2 = xs := by
        simpa [liftIntTerms, decodeIntRun] using hxs_dec
      have hys_dec' : decodeIntRun de dcy (liftIntTerms de dcy ys).1 (liftIntTerms de dcy ys).2 = ys := by
        simpa [liftIntTerms, decodeIntRun] using hys_dec
      have hys_sz' : (liftIntTerms de dcy ys).1.size = (liftIntTerms de dcy ys).2.size := hys_sz
      split
      · rename_i hys_dite
        change fromIntRun de (dcx * dcy) _ _ = _
        rw [fromIntRun_eq_decode]
        have ⟨_, hmul⟩ := mulIntDC_spec de dcx dcy hde hdcx hdcy
          (liftIntTerms de dcx xs).1 (liftIntTerms de dcx xs).2
          (liftIntTerms de dcy ys).1 (liftIntTerms de dcy ys).2
          hxs_sz hys_dite 0 (liftIntTerms de dcx xs).1.size (by omega)
        rw [hmul]
        have htake : ((decodeIntRun de dcx (liftIntTerms de dcx xs).1 (liftIntTerms de dcx xs).2).drop 0).take
            (liftIntTerms de dcx xs).1.size = xs := by
          simp only [List.drop_zero]
          have hlen : (decodeIntRun de dcx (liftIntTerms de dcx xs).1 (liftIntTerms de dcx xs).2).length ≤
              (liftIntTerms de dcx xs).1.size := by
            unfold decodeIntRun; simp only [List.length_zipWith, Array.length_toList]; omega
          rw [List.take_of_length_le hlen]
          exact hxs_dec'
        rw [htake, hys_dec']
      · rename_i hneg
        exact absurd hys_sz' hneg
    · have ⟨hxs_sz, hxs_dec⟩ := liftIntRatTermsLoop_spec de hde
        xs (Array.mkEmpty xs.length) (Array.mkEmpty (xs.length + 1)) rfl hxs_edvd
      have ⟨hys_sz, hys_dec⟩ := liftIntRatTermsLoop_spec de hde
        ys (Array.mkEmpty ys.length) (Array.mkEmpty (ys.length + 1)) rfl hys_edvd
      have hxs_dec' : decodeIntRatRun de (liftIntRatTerms de xs).1 (liftIntRatTerms de xs).2 = xs := by
        simpa [liftIntRatTerms, decodeIntRatRun] using hxs_dec
      have hys_dec' : decodeIntRatRun de (liftIntRatTerms de ys).1 (liftIntRatTerms de ys).2 = ys := by
        simpa [liftIntRatTerms, decodeIntRatRun] using hys_dec
      change fromIntRatRun de _ _ = _
      rw [fromIntRatRun_eq_decode]
      have ⟨_, hmul⟩ := mulIntRatDC_spec de hde
        (liftIntRatTerms de xs).1 (liftIntRatTerms de xs).2
        (liftIntRatTerms de ys).1 (liftIntRatTerms de ys).2
        hxs_sz hys_sz 0 (liftIntRatTerms de xs).1.size (by omega)
      rw [hmul]
      have htake : ((decodeIntRatRun de (liftIntRatTerms de xs).1 (liftIntRatTerms de xs).2).drop 0).take
          (liftIntRatTerms de xs).1.size = xs := by
        simp only [List.drop_zero]
        have hlen : (decodeIntRatRun de (liftIntRatTerms de xs).1 (liftIntRatTerms de xs).2).length ≤
            (liftIntRatTerms de xs).1.size := by
          unfold decodeIntRatRun; simp only [List.length_zipWith, Array.length_toList]; omega
        rw [List.take_of_length_le hlen]
        exact hxs_dec'
      rw [htake, hys_dec']
  · rw [mergeAllArr_toList, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    rcases p with ⟨ex, cx⟩
    simpa using scaleTermArr_toList ex cx ys.toArray

/-- Compiled scaled-SOA contiguous-`Array` kernel for `mulTree` (zero intermediate cons cells,
    common-denominator unboxed `Array Int` SOA with fused 2-leaf depth-first merge). -/
def mulTreeArr (xs ys : TermList) : TermList :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | [(ex, cx)], ys => scaleTerm ex cx ys
  | xs, [(ey, cy)] => scaleTerm ey cy xs
  | xs, ys =>
    if xs.length ≤ ys.length then
      mulTreeOrderedArr xs ys
    else
      mulTreeOrderedArr ys xs

/-- **`@[csimp]` Verified Kernel Replacement (`mulTree → mulTreeArr`)**:
    Replaces linked-list balanced merging inside `mulTree` with scaled-denominator SOA
    depth-first contiguous `Array` merging at compile time while keeping all proofs unchanged. -/
@[csimp] theorem mulTree_eq_mulTreeArr : @mulTree = @mulTreeArr := by
  funext xs ys
  unfold mulTree mulTreeArr
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · split
    · exact (mulTreeOrderedArr_eq xs ys).symm
    · exact (mulTreeOrderedArr_eq ys xs).symm

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
