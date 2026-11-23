import Init.Data.Rat
import LeanInf.LeviCivitaNum
import LeanInf.SortedLC
import LeanInf.Karatsuba
import LeanInf.Kronecker

namespace LeanInf

open TermList Karatsuba Kronecker

/-- Canonical, proof-carrying fast Levi-Civita number.
    Stores nonzero `(exponent, coefficient)` terms in strictly descending exponent order.
    The `wf` proof field is a `Prop` and is completely erased at runtime. -/
structure FastLC where
  /-- Strictly descending list of nonzero `(exponent, coefficient)` terms. -/
  terms : TermList
  /-- Proof that `terms` is strictly descending and contains no zero coefficients. -/
  wf : TermList.WF terms

namespace FastLC

/-- Exact mathematical coefficient of `H^e`. -/
def coeff (x : FastLC) (e : Rat) : Rat :=
  TermList.coeffOf x.terms e

/-- Compiled early-exit tail-recursive coefficient lookup exploiting canonical descending `WF` order. -/
@[inline] def coeffWF (x : FastLC) (e : Rat) : Rat :=
  TermList.coeffOfWF x.terms e

/-- **`@[csimp]` Verified Kernel Replacement (`FastLC.coeff → FastLC.coeffWF`)**:
    Replaces the `O(n)` non-tail-recursive denotational `coeffOf` scan with `O(k)` early-exit
    tail-recursive lookup using `x.wf : TermList.WF x.terms`. -/
@[csimp] theorem coeff_eq_coeffWF : @FastLC.coeff = @FastLC.coeffWF := by
  funext x e
  exact (TermList.coeffOfWF_eq_coeffOf x.wf e).symm

/-- Extensionality: two `FastLC` values are equal iff all their coefficients match. -/
@[ext] theorem ext {x y : FastLC} (h : ∀ e, x.coeff e = y.coeff e) : x = y := by
  cases x; cases y
  congr
  exact TermList.eq_of_wf_of_coeffOf_eq ‹_› ‹_› h

instance : BEq FastLC where
  beq x y := x.terms == y.terms

/-- Structural `BEq` on `FastLC` is sound and complete for semantic equality. -/
theorem beq_iff_eq (x y : FastLC) : (x == y) = true ↔ x = y := by
  change (x.terms == y.terms) = true ↔ x = y
  constructor
  · intro h
    have ht : x.terms = y.terms := eq_of_beq h
    cases x; cases y; simp_all
  · rintro rfl
    exact beq_self_eq_true x.terms

/-- Zero element `0`. -/
def zero : FastLC := ⟨[], trivial⟩

/-- Multiplicative identity `1`. -/
def one : FastLC := ⟨[(0, 1)], ⟨by decide, trivial, trivial⟩⟩

/-- Fundamental infinite hypernatural constant `H = H^1`. -/
def infH : FastLC := ⟨[(1, 1)], ⟨by decide, trivial, trivial⟩⟩

/-- Fundamental positive infinitesimal `ε = H^(-1)`. -/
def infEps : FastLC := ⟨[(-1, 1)], ⟨by decide, trivial, trivial⟩⟩

/-- Alias for `infH` using guillemets so `FastLC.H` is also available. -/
abbrev «H» : FastLC := infH

/-- Alias for `infEps` using guillemets so `FastLC.ε` is also available. -/
abbrev «ε» : FastLC := infEps

/-- Construct a single monomial `c * H^e`. -/
def mono (e c : Rat) : FastLC :=
  if h : c == 0 then zero
  else ⟨[(e, c)], ⟨by intro hc; simp [hc] at h, trivial, trivial⟩⟩

/-- Embed a rational number as a standard (exponent `0`) `FastLC`. -/
def ofRat (r : Rat) : FastLC := mono 0 r

/-- Construct a `FastLC` from an arbitrary unsorted term list via verified `normalize`. -/
def ofTerms (ts : TermList) : FastLC :=
  ⟨TermList.normalize ts, TermList.normalize_wf ts⟩

/-- Convert a legacy HashMap `LeviCivitaNum` into canonical `FastLC`. -/
def ofLeviCivitaNum (x : LeviCivitaNum) : FastLC :=
  let raw := (x.toPolyG.toTerms.map (fun t => (t.exp, t.coeff))).toList
  ofTerms raw

/-- Convert a canonical `FastLC` back into a legacy HashMap `LeviCivitaNum`. -/
def toLeviCivitaNum (x : FastLC) : LeviCivitaNum :=
  LeviCivitaNum.ofArray (x.terms.map (fun (e, c) => ({ exp := e, coeff := c } : Term))).toArray

instance : Zero FastLC where zero := zero
instance : Inhabited FastLC where default := zero
instance : One FastLC where one := one
instance : Coe Rat FastLC where coe := ofRat

instance : OfNat FastLC n where
  ofNat := ofRat (((n : Nat) : Int) : Rat)

instance : OfScientific FastLC where
  ofScientific mantissa exponentSign decimalExponent :=
    ofRat (OfScientific.ofScientific mantissa exponentSign decimalExponent)

/-! ### Core Verified Arithmetic Operations -/

/-- Verified `O(n + m)` addition via two-pointer sorted merge. -/
def add (x y : FastLC) : FastLC :=
  ⟨TermList.addMerge x.terms y.terms, TermList.addMerge_wf x.wf y.wf⟩

/-- Verified `O(n)` negation. -/
def neg (x : FastLC) : FastLC :=
  ⟨TermList.negFast x.terms, TermList.negFast_wf x.wf⟩

/-- Verified `O(n + m)` subtraction. -/
def sub (x y : FastLC) : FastLC :=
  ⟨TermList.subFast x.terms y.terms, TermList.subFast_wf x.wf y.wf⟩

/-- Verified fast multiplication (`mulFastKronecker`: Kronecker GMP + unboxed `Array Int`
    Karatsuba + rational Karatsuba + contiguous `Array` sparse `mulTree`). -/
def mul (x y : FastLC) : FastLC :=
  ⟨Kronecker.mulFastKronecker x.terms y.terms 16,
   Kronecker.mulFastKronecker_wf x.wf y.wf 16⟩

/-- Verified sparse balanced-tree multiplication (`mulTree`) exposed for benchmarking. -/
def mulSparse (x y : FastLC) : FastLC :=
  ⟨TermList.mulTree x.terms y.terms, TermList.mulTree_wf x.wf y.wf⟩

/-- Verified naive reference multiplication (`normalize ∘ mulNaiveTerms`) for benchmarking. -/
def mulNaive (x y : FastLC) : FastLC :=
  ⟨TermList.normalize (TermList.mulNaiveTerms x.terms y.terms),
   TermList.normalize_wf _⟩

instance : Add FastLC where add := add
instance : Neg FastLC where neg := neg
instance : Sub FastLC where sub := sub
instance : Mul FastLC where mul := mul

@[simp] theorem coeff_zero (e : Rat) : (0 : FastLC).coeff e = 0 := rfl

@[simp] theorem coeff_one (e : Rat) : (1 : FastLC).coeff e = if (0 : Rat) == e then 1 else 0 := by
  change TermList.coeffOf (if (1 : Rat) == 0 then [] else [(0, 1)]) e = _
  simp [TermList.coeffOf, Rat.add_zero]

@[simp] theorem coeff_add (x y : FastLC) (e : Rat) :
    (x + y).coeff e = x.coeff e + y.coeff e :=
  TermList.coeffOf_addMerge x.terms y.terms e

@[simp] theorem coeff_neg (x : FastLC) (e : Rat) :
    (-x).coeff e = -(x.coeff e) :=
  TermList.coeffOf_negFast x.terms e

@[simp] theorem coeff_sub (x y : FastLC) (e : Rat) :
    (x - y).coeff e = x.coeff e - y.coeff e :=
  TermList.coeffOf_subFast x.terms y.terms e

theorem coeff_mul (x y : FastLC) (e : Rat) :
    (x * y).coeff e = TermList.coeffOf (TermList.mulNaiveTerms x.terms y.terms) e :=
  Kronecker.coeffOf_mulFastKronecker x.terms y.terms e 16

/-- Verified equivalence: `mul` (Karatsuba + balanced merge) equals `mulNaive` structurally! -/
theorem mul_eq_mulNaive (x y : FastLC) : x * y = mulNaive x y := by
  ext e
  rw [coeff_mul, mulNaive, coeff, TermList.coeffOf_normalize]

/-- Verified equivalence: `mulSparse` equals `mulNaive` structurally! -/
theorem mulSparse_eq_mulNaive (x y : FastLC) : mulSparse x y = mulNaive x y := by
  ext e
  rw [mulSparse, mulNaive, coeff, coeff, TermList.coeffOf_mulTree, TermList.coeffOf_normalize]

/-! ### Verified Commutative Ring Laws on `FastLC` (zero `sorry`) -/

theorem add_comm (x y : FastLC) : x + y = y + x := by
  ext e; simp [Rat.add_comm]

theorem add_assoc (x y z : FastLC) : (x + y) + z = x + (y + z) := by
  ext e; simp [Rat.add_assoc]

theorem zero_add (x : FastLC) : 0 + x = x := by
  ext e; simp [Rat.zero_add]

theorem add_zero (x : FastLC) : x + 0 = x := by
  ext e; simp [Rat.add_zero]

theorem neg_add_cancel (x : FastLC) : -x + x = 0 := by
  ext e; simp [Rat.neg_add_cancel]

theorem add_neg_cancel (x : FastLC) : x + (-x) = 0 := by
  rw [add_comm, neg_add_cancel]

theorem sub_eq_add_neg (x y : FastLC) : x - y = x + (-y) := by
  ext e; simp [Rat.sub_eq_add_neg]

theorem mul_comm (x y : FastLC) : x * y = y * x := by
  ext e
  rw [coeff_mul, coeff_mul, TermList.coeffOf_mulNaiveTerms_comm]

theorem mul_assoc (x y z : FastLC) : (x * y) * z = x * (y * z) := by
  ext e
  rw [coeff_mul, coeff_mul]
  rw [TermList.coeffOf_mulNaiveTerms_congr_left (fun e' => coeff_mul x y e'),
      TermList.coeffOf_mulNaiveTerms_congr_right (fun e' => coeff_mul y z e'),
      TermList.coeffOf_mulNaiveTerms_assoc]

theorem one_mul (x : FastLC) : 1 * x = x := by
  ext e
  rw [coeff_mul]
  change TermList.coeffOf (TermList.mulNaiveTerms [(0, 1)] x.terms) e = x.coeff e
  rw [TermList.coeffOf_mulNaiveTerms_cons, TermList.coeffOf_mulNaiveTerms_nil,
      Rat.one_mul, Rat.add_zero]
  have hsub : e - (0 : Rat) = e := by grind
  rw [hsub]; rfl

theorem mul_one (x : FastLC) : x * 1 = x := by
  rw [mul_comm, one_mul]

theorem mul_zero (x : FastLC) : x * 0 = 0 := by
  ext e
  rw [coeff_mul, coeff_zero]
  change TermList.coeffOf (TermList.mulNaiveTerms x.terms []) e = 0
  rw [TermList.coeffOf_mulNaiveTerms_comm]
  rfl

theorem zero_mul (x : FastLC) : 0 * x = 0 := by
  rw [mul_comm, mul_zero]

theorem mul_add (x y z : FastLC) : x * (y + z) = x * y + x * z := by
  ext e
  rw [coeff_add, coeff_mul, coeff_mul, coeff_mul]
  have hyz : ∀ e', TermList.coeffOf (y + z).terms e' = TermList.coeffOf (y.terms ++ z.terms) e' := by
    intro e'; rw [TermList.coeffOf_append]; exact TermList.coeffOf_addMerge y.terms z.terms e'
  rw [TermList.coeffOf_mulNaiveTerms_congr_right hyz,
      TermList.coeffOf_mulNaiveTerms_comm x.terms (y.terms ++ z.terms),
      TermList.coeffOf_mulNaiveTerms_add_left,
      TermList.coeffOf_mulNaiveTerms_comm y.terms x.terms,
      TermList.coeffOf_mulNaiveTerms_comm z.terms x.terms]

theorem add_mul (x y z : FastLC) : (x + y) * z = x * z + y * z := by
  rw [mul_comm, mul_add, mul_comm z x, mul_comm z y]

theorem mul_sub (x y z : FastLC) : x * (y - z) = x * y - x * z := by
  ext e
  have h : x * (y - z) + x * z = x * y := by
    rw [← mul_add, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
  have he := congrArg (fun a => a.coeff e) h
  simp only [coeff_add, coeff_sub] at he ⊢
  grind

/-- Fundamental Levi-Civita unit cancellation law: `H * ε = 1`. -/
theorem H_mul_eps : infH * infEps = 1 := by
  ext e
  rw [coeff_mul, coeff_one]
  change TermList.coeffOf (TermList.mulNaiveTerms [(1, 1)] [(-1, 1)]) e = _
  simp only [TermList.mulNaiveTerms, List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil,
    List.append_nil, TermList.coeffOf, Rat.add_zero]
  have h0 : (1 : Rat) + (-1 : Rat) = 0 := by grind
  rw [h0]
  grind

/-- Fundamental Levi-Civita unit cancellation law: `ε * H = 1`. -/
theorem eps_mul_H : infEps * infH = 1 := by
  rw [mul_comm]; exact H_mul_eps

/-! ### Verified Refactor 4: Binary Exponentiation (`O(log n)` vs `O(n)`) -/

/-- Original naive `O(n)` linear natural power. -/
def powNaive (x : FastLC) : Nat → FastLC
  | 0 => 1
  | n + 1 => x * powNaive x n

private theorem coeff_powNaive (x : FastLC) (n : Nat) (e : Rat) :
    (powNaive x n).coeff e = TermList.coeffOf (Kronecker.powNaiveTerms x.terms n) e := by
  induction n generalizing e with
  | zero => rfl
  | succ n' ih =>
    rw [powNaive, coeff_mul, Kronecker.powNaiveTerms]
    exact TermList.coeffOf_mulNaiveTerms_congr_right ih e

private def powFastLoop (x : FastLC) (n : Nat) : FastLC :=
  if h0 : n = 0 then 1
  else if h1 : n = 1 then x
  else
    have : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
    let half := powFastLoop x (n / 2)
    let sq := half * half
    if n % 2 == 0 then sq else x * sq
termination_by n

/-- Refactored `O(log n)` exponentiation by squaring: routes grid-aligned integer and
    bounded-LCM rational series through in-array `aPowIntFast` (single-pack GMP Kronecker
    squaring + half-work Karatsuba squaring, zero intermediate `TermList` round-trips),
    monomials through scalar `powRatFast`, and off-grid sparse series through `powFastLoop`. -/
def powFast (x : FastLC) (n : Nat) : FastLC :=
  if n == 0 then 1
  else if n == 1 then x
  else
    match h : Kronecker.powFastGrid x.terms n with
    | some ts => ⟨ts, Kronecker.powFastGrid_wf h⟩
    | none => powFastLoop x n

private theorem powNaive_add (x : FastLC) (a b : Nat) :
    powNaive x (a + b) = powNaive x a * powNaive x b := by
  induction a with
  | zero => simp [powNaive, one_mul]
  | succ a' ih =>
    have hsucc : a' + 1 + b = (a' + b) + 1 := by omega
    rw [hsucc, powNaive, powNaive, ih, mul_assoc]

private theorem powFastLoop_eq_powNaive (x : FastLC) (n : Nat) :
    powFastLoop x n = powNaive x n := by
  unfold powFastLoop
  split
  · rename_i h0; subst h0; rfl
  · rename_i hne0
    split
    · rename_i h1; subst h1; exact (mul_one x).symm
    · rename_i hne1
      have hlt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have ih := powFastLoop_eq_powNaive x (n / 2)
      dsimp only
      rw [ih, ← powNaive_add]
      by_cases heven : n % 2 = 0
      · have hmod : (n % 2 == 0) = true := by simp [heven]
        have hsum : n / 2 + n / 2 = n := by omega
        simp [hmod, hsum]
      · have hmod : (n % 2 == 0) = false := by
          cases hb : (n % 2 == 0)
          · rfl
          · exact absurd (eq_of_beq hb) heven
        have hsum : n = (n / 2 + n / 2) + 1 := by omega
        simp only [hmod, Bool.false_eq_true, ↓reduceIte]
        have hpow : x * powNaive x (n / 2 + n / 2) = powNaive x n := by
          change powNaive x ((n / 2 + n / 2) + 1) = powNaive x n
          exact congrArg (powNaive x) hsum.symm
        exact hpow
termination_by n

/-- **Binary Exponentiation Equivalence Theorem (zero `sorry`)**:
    `powFast x n` is structurally identical to `powNaive x n` for every `x : FastLC` and `n : Nat`. -/
theorem powFast_eq_powNaive (x : FastLC) (n : Nat) : powFast x n = powNaive x n := by
  unfold powFast
  split
  · rename_i h0
    have hn : n = 0 := eq_of_beq h0
    subst hn; rfl
  · split
    · rename_i h1
      have hn : n = 1 := eq_of_beq h1
      subst hn; exact (mul_one x).symm
    · split
      · rename_i ts hgrid
        ext e
        change TermList.coeffOf ts e = (powNaive x n).coeff e
        rw [Kronecker.coeffOf_powFastGrid hgrid e, coeff_powNaive]
      · exact powFastLoop_eq_powNaive x n

instance : HPow FastLC Nat FastLC where
  hPow := powFast

/-! ### Verified Refactor 5: Newton-Raphson Quadratic Convergence Theorem -/

/-- One Newton-Raphson reciprocal step: `y_{k+1} = y_k * (2 - u * y_k)`. -/
def newtonStep (u y : FastLC) : FastLC :=
  y * ((2 : FastLC) - u * y)

/-- **Newton Residual Squaring Theorem (zero `sorry`)**:
    For any `u, y : FastLC`, one Newton step squares the multiplicative residual:
    `1 - u * (y * (2 - u * y)) = (1 - u * y)²`. -/
theorem newton_residual_squares (u y : FastLC) :
    (1 : FastLC) - u * newtonStep u y = ((1 : FastLC) - u * y) * ((1 : FastLC) - u * y) := by
  unfold newtonStep
  have h2 : (2 : FastLC) = (1 : FastLC) + (1 : FastLC) := by
    ext e
    rw [coeff_add, coeff_one]
    change TermList.coeffOf [(0, 2)] e = _
    simp only [TermList.coeffOf, Rat.add_zero]
    split <;> grind
  rw [h2]
  let p := u * y
  have hL : u * (y * ((1 : FastLC) + 1 - p)) = p * ((1 : FastLC) + 1 - p) := by
    rw [← mul_assoc]
  change (1 : FastLC) - u * (y * ((1 : FastLC) + 1 - p)) = ((1 : FastLC) - p) * ((1 : FastLC) - p)
  rw [hL]
  ext e
  have h1 : (p * ((1 : FastLC) + 1 - p)).coeff e =
      (p + p - p * p).coeff e := by
    rw [mul_sub, mul_add, mul_one]
  have h2' : (((1 : FastLC) - p) * ((1 : FastLC) - p)).coeff e =
      ((1 : FastLC) - p - (p - p * p)).coeff e := by
    rw [sub_eq_add_neg (1 : FastLC) p, add_mul, one_mul]
    have hneg : ((-p) * ((1 : FastLC) + -p)) = -(p * ((1 : FastLC) - p)) := by
      rw [← sub_eq_add_neg]
      ext e'
      have hsum : (-p) * ((1 : FastLC) - p) + p * ((1 : FastLC) - p) = 0 := by
        rw [← add_mul, neg_add_cancel, zero_mul]
      have hhe := congrArg (fun a => a.coeff e') hsum
      simp only [coeff_add, coeff_zero, coeff_neg] at hhe ⊢
      grind
    rw [hneg, mul_sub, mul_one, ← sub_eq_add_neg, ← sub_eq_add_neg]
  simp only [coeff_sub, h1, h2', coeff_add]
  grind

/-- Valuation upper bound: every nonzero term in `x` has exponent `≤ bound`. -/
def AllLe (bound : Rat) (x : FastLC) : Prop :=
  ∀ e, e > bound → x.coeff e = 0

/-- **Valuation Squaring Theorem (zero `sorry`)**:
    If `r` has all terms at exponent `≤ -d` (`d > 0`), then `r * r` has all terms at
    exponent `≤ -2 * d` (i.e., Newton-Raphson DOUBLES the order of infinitesimal accuracy
    at every iteration!). -/
theorem mul_allLe {a b : Rat} {x y : FastLC} (hx : AllLe a x) (hy : AllLe b y) :
    AllLe (a + b) (x * y) := by
  intro e he
  rw [coeff_mul]
  suffices h : ∀ ts : TermList, (∀ ex, ex > a → TermList.coeffOf ts ex = 0) →
      TermList.WF ts →
      TermList.coeffOf (TermList.mulNaiveTerms ts y.terms) e = 0 by
    exact h x.terms hx x.wf
  intro ts hts hwf
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    rcases p with ⟨ex, cx⟩
    rw [TermList.coeffOf_mulNaiveTerms_cons]
    have hex : ex ≤ a := by
      by_cases hgt : ex > a
      · have h0 := hts ex hgt
        rw [TermList.coeffOf_cons_head_of_wf hwf] at h0
        exact absurd h0 hwf.1
      · grind
    have hey : e - ex > b := by grind
    have hy0 : TermList.coeffOf y.terms (e - ex) = 0 := hy (e - ex) hey
    have hrest : ∀ ex', ex' > a → TermList.coeffOf rest ex' = 0 := by
      intro ex' hex'
      have h0 := hts ex' hex'
      have hne : (ex == ex') = false := by
        cases hb : (ex == ex')
        · rfl
        · have : ex = ex' := eq_of_beq hb
          grind
      simp [TermList.coeffOf, hne, Rat.zero_add] at h0
      exact h0
    rw [hy0, Rat.mul_zero, Rat.zero_add]
    exact ih hrest hwf.2.2

/-- **Quadratic Convergence of Newton Inversion (zero `sorry`)**:
    If `1 - u * y` is `O(ε^d)` (all exponents `≤ -d`), then after a single Newton step
    `y' = y * (2 - u * y)`, the new residual `1 - u * y'` is `O(ε^(2d))` (all exponents `≤ -2d`)! -/
theorem newton_order_doubles {d : Rat} {u y : FastLC}
    (hres : AllLe (-d) ((1 : FastLC) - u * y)) :
    AllLe (-(d + d)) ((1 : FastLC) - u * newtonStep u y) := by
  rw [newton_residual_squares]
  have hsum : -(d + d) = (-d) + (-d) := by grind
  rw [hsum]
  exact mul_allLe hres hres

/-! ### Order, Sign, Truncation, Inversion, Transcendentals & Finite Evaluation -/

/-- `O(1)` signum (`-1`, `0`, or `1`) via verified `signumFast`. -/
def signum (x : FastLC) : Int :=
  TermList.signumFast x.terms

/-- `O(1)` leading (largest-exponent) nonzero term. -/
def leadingTerm (x : FastLC) : Option (Rat × Rat) :=
  TermList.leadingTermFast x.terms

/-- `O(1)` dominant exponent (order in `H`), if nonzero. -/
def order (x : FastLC) : Option Rat :=
  x.leadingTerm.map Prod.fst

/-- Check whether `x` is zero (`O(1)`). -/
def isZero (x : FastLC) : Bool := x.terms.isEmpty

/-- Check whether `x` is infinitesimal (every term has exponent `< 0`). -/
def isInfinitesimal (x : FastLC) : Bool :=
  match x.terms with
  | [] => true
  | (e, _) :: _ => e < 0

/-- Check whether `x` is finite (every term has exponent `≤ 0`). -/
def isFinite (x : FastLC) : Bool :=
  match x.terms with
  | [] => true
  | (e, _) :: _ => e ≤ 0

/-- Check whether `x` is infinite (dominant exponent `> 0`). -/
def isInfinite (x : FastLC) : Bool :=
  match x.terms with
  | [] => false
  | (e, _) :: _ => e > 0

/-- Standard part `st(x)` for finite Levi-Civita numbers (coefficient of `H^0`). -/
def stdPart (x : FastLC) : Option Rat :=
  if x.isFinite then some (x.coeff 0) else none

/-- Absolute value `|x|` in the Levi-Civita ordered field. -/
def abs (x : FastLC) : FastLC :=
  if x.signum < 0 then -x else x

instance : LT FastLC where
  lt x y := (x - y).signum = -1

instance : LE FastLC where
  le x y := (x - y).signum ≤ 0

instance : DecidableRel (@LT.lt FastLC _) :=
  fun x y => decEq ((x - y).signum) (-1)

instance : DecidableRel (@LE.le FastLC _) :=
  fun x y => inferInstanceAs (Decidable ((x - y).signum ≤ 0))

/-- Truncate to the `maxTerms` largest-exponent terms (preserves `WF`). -/
def truncate (maxTerms : Nat) (x : FastLC) : FastLC :=
  ⟨TermList.truncate maxTerms x.terms, TermList.truncate_wf maxTerms x.wf⟩

/-- Keep only terms with exponent `≥ minExp` in `O(k)` time (preserves `WF`, zero re-sorting). -/
def dropBelow (minExp : Rat) (x : FastLC) : FastLC :=
  ⟨TermList.takeWhileGe minExp x.terms, TermList.takeWhileGe_wf minExp x.wf⟩

/-- Exact coefficient specification of `dropBelow`. -/
theorem coeff_dropBelow (minExp : Rat) (x : FastLC) (e : Rat) :
    (x.dropBelow minExp).coeff e = if e ≥ minExp then x.coeff e else 0 :=
  TermList.coeffOf_takeWhileGe minExp x.wf e

/-- Truncate relative to the leading exponent `e0`: keep terms with exponent `> e0 - relOrder`,
    and cap total terms at `relOrder`, in `O(k)` time without re-sorting. -/
def truncateRel (relOrder : Nat) (x : FastLC) : FastLC :=
  match x.leadingTerm with
  | none => zero
  | some (e0, _) =>
    let cutoff : Rat := e0 - (relOrder : Rat)
    ⟨TermList.takeWhileGt cutoff relOrder x.terms, TermList.takeWhileGt_wf cutoff relOrder x.wf⟩

/-- Fast precision-sliced Newton-Raphson multiplicative inverse (`O(log order)` multiplications),
    using residual form `y' = y + y * (1 - u * y)` and `O(k)` `dropBelow` slicing.
    Returns `.error` on division by zero. -/
def invNewton (x : FastLC) (order : Nat := 12) : Except String FastLC :=
  match x.leadingTerm with
  | none => .error "Division by zero"
  | some (e0, c0) =>
    let isUnitLead := e0.num == 0 && c0.num == 1 && c0.den == 1
    let invLead := if isUnitLead then (1 : FastLC) else mono (-e0) c0⁻¹
    let u := if isUnitLead then x else invLead * x
    let delta := u - 1
    match delta.leadingTerm with
    | none => .ok invLead
    | some (ed, _) =>
      let stepD : Rat := if ed < 0 then -ed else 1
      Id.run do
        let mut y : FastLC := 1
        let mut prec : Nat := 1
        while prec < order do
          let next := min (prec * 2) order
          let minE : Rat := -(stepD * ((next : Rat) - 1))
          let uStep := u.dropBelow minE
          let uy := (uStep * y).dropBelow minE
          let res := (1 : FastLC) - uy
          if res.isZero then break
          let corr := (y * res).dropBelow minE
          y := (y + corr).truncate next
          prec := next
        let out := if isUnitLead then y else invLead * y
        return .ok (out.truncate order)

/-- Divide two `FastLC` numbers using Newton-Raphson inversion. -/
def divNewton (x y : FastLC) (order : Nat := 12) : Except String FastLC := do
  let invY ← invNewton y order
  return (x * invY).truncate order

/-- Total `Inv` instance defaulting to 12-term Newton-Raphson inversion (`0⁻¹ = 0`). -/
instance : Inv FastLC where
  inv x := match invNewton x 12 with
    | .ok r => r
    | .error _ => zero

instance : Div FastLC where
  div x y := (x * y⁻¹).truncate 12

/-- Convert a finite `Float` to a clean bounded-denominator `Rat` (up to `10^10` precision). -/
def ratOfFloat (f : Float) (scale : Nat := 10000000000) : Rat :=
  if f.isNaN || f.isInf then 0
  else
    let scaled := (f * Float.ofNat scale).round
    let num : Int :=
      if scaled < 0.0 then -Int.ofNat ((-scaled).toUInt64.toNat)
      else Int.ofNat (scaled.toUInt64.toNat)
    mkRat num scale

/-- Overflow-safe conversion of an arbitrary-precision `Rat` to IEEE-754 `Float`
    using bit-length normalization (never overflows to `Inf / Inf = NaN` even when
    numerator and denominator exceed `2^1024`). -/
def ratToFloat (r : Rat) : Float :=
  if r.num == 0 then 0.0
  else
    let a := r.num.natAbs
    let b := r.den
    let la := a.log2
    let lb := b.log2
    let sa := if la > 53 then la - 53 else 0
    let sb := if lb > 53 then lb - 53 else 0
    let aTop := a >>> sa
    let bTop := b >>> sb
    let mant := (Float.ofNat aTop) / (Float.ofNat bTop)
    let expDiff : Int := Int.ofNat sa - Int.ofNat sb
    let scaled := Float.scaleB mant expDiff
    if r.num < 0 then -scaled else scaled

/-- **Finite Specialization (`H ↦ N`, `ε ↦ 1/N`)**:
    Replace the unlimited constant `H` with a chosen large finite number `bigN > 0`,
    scaling every term `c * H^e` relative to `bigN` as `c * bigN^e`. -/
def evalFinite (x : FastLC) (bigN : Float) : Float :=
  x.terms.foldl (init := 0.0) fun acc (e, c) =>
    let cf := ratToFloat c
    let ef := ratToFloat e
    acc + cf * Float.pow bigN ef

/-- Split a finite `FastLC` into its standard part `a0` and strictly infinitesimal tail `δ`. -/
def splitFinite (x : FastLC) : Except String (Rat × FastLC) :=
  if !x.isFinite then
    .error "Expected finite Levi-Civita number (got infinite term)"
  else
    let a0 := x.coeff 0
    let tail := x - ofRat a0
    .ok (a0, tail)

/-- Exponential `exp(x)` on finite Levi-Civita numbers via `e^(a0 + δ) = e^a0 * ∑ δ^k / k!`.
    When `a0 = 0`, `e^0 = 1` so all series coefficients are 100% exact rationals! -/
def expOrder (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let (a0, delta) ← splitFinite x
  let scale : FastLC :=
    if a0 == 0 then 1
    else ofRat (ratOfFloat (Float.exp (ratToFloat a0)))
  Id.run do
    let mut sum : FastLC := 1
    let mut term : FastLC := 1
    for k in [1:order] do
      term := (term * delta * ofRat (mkRat 1 k)).truncate order
      if term.isZero then break
      sum := (sum + term).truncate order
    return .ok ((scale * sum).truncate order)

/-- Natural logarithm `ln(x)` for positive finite Levi-Civita numbers (or general positive LC
    when standard part dominates; `ln(H)` is outside the Levi-Civita field). -/
def lnOrder (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  if x.signum ≤ 0 then
    throw "ln requires a strictly positive argument"
  if !x.isFinite then
    throw "ln of an infinite number is outside the Levi-Civita field"
  let (a0, delta) ← splitFinite x
  if a0 ≤ 0 then
    throw "ln of an infinitesimal is outside the Levi-Civita field"
  let u := (delta * ofRat a0⁻¹).truncate order
  let base : FastLC :=
    if a0 == 1 then 0 else ofRat (ratOfFloat (Float.log (ratToFloat a0)))
  Id.run do
    let mut sum : FastLC := base
    let mut powU : FastLC := 1
    for k in [1:order] do
      powU := (powU * u).truncate order
      if powU.isZero then break
      let sign : Int := if k % 2 == 1 then 1 else -1
      let term := (powU * ofRat (mkRat sign k)).truncate order
      sum := (sum + term).truncate order
    return .ok sum

/-- Sine `sin(x)` on finite Levi-Civita numbers via angle-addition and exact Taylor series. -/
def sinOrder (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let (a0, delta) ← splitFinite x
  let sinA : FastLC := if a0 == 0 then 0 else ofRat (ratOfFloat (Float.sin (ratToFloat a0)))
  let cosA : FastLC := if a0 == 0 then 1 else ofRat (ratOfFloat (Float.cos (ratToFloat a0)))
  Id.run do
    let mut sinD : FastLC := 0
    let mut cosD : FastLC := 1
    let mut powD : FastLC := 1
    let mut fact : Nat := 1
    for k in [1:order] do
      powD := (powD * delta).truncate order
      fact := fact * k
      if powD.isZero then break
      match k % 4 with
      | 1 => sinD := (sinD + powD * ofRat (mkRat 1 fact)).truncate order
      | 2 => cosD := (cosD - powD * ofRat (mkRat 1 fact)).truncate order
      | 3 => sinD := (sinD - powD * ofRat (mkRat 1 fact)).truncate order
      | _ => cosD := (cosD + powD * ofRat (mkRat 1 fact)).truncate order
    return .ok ((sinA * cosD + cosA * sinD).truncate order)

/-- Cosine `cos(x)` on finite Levi-Civita numbers via angle-addition and exact Taylor series. -/
def cosOrder (x : FastLC) (order : Nat := 10) : Except String FastLC := do
  let (a0, delta) ← splitFinite x
  let sinA : FastLC := if a0 == 0 then 0 else ofRat (ratOfFloat (Float.sin (ratToFloat a0)))
  let cosA : FastLC := if a0 == 0 then 1 else ofRat (ratOfFloat (Float.cos (ratToFloat a0)))
  Id.run do
    let mut sinD : FastLC := 0
    let mut cosD : FastLC := 1
    let mut powD : FastLC := 1
    let mut fact : Nat := 1
    for k in [1:order] do
      powD := (powD * delta).truncate order
      fact := fact * k
      if powD.isZero then break
      match k % 4 with
      | 1 => sinD := (sinD + powD * ofRat (mkRat 1 fact)).truncate order
      | 2 => cosD := (cosD - powD * ofRat (mkRat 1 fact)).truncate order
      | 3 => sinD := (sinD - powD * ofRat (mkRat 1 fact)).truncate order
      | _ => cosD := (cosD + powD * ofRat (mkRat 1 fact)).truncate order
    return .ok ((cosA * cosD - sinA * sinD).truncate order)

/-- Rational power `x^r` for positive Levi-Civita numbers (or any integer `r` on nonzero `x`)
    via leading-term factoring and generalized binomial series `(1 + δ)^r = ∑ C(r, k) δ^k`. -/
def powRatOrder (x : FastLC) (r : Rat) (order : Nat := 10) : Except String FastLC := do
  if r == 0 then return 1
  if r.den == 1 then
    if r.num ≥ 0 then
      return (x.powFast r.num.toNat).truncate order
    else
      let invX ← invNewton x order
      return (invX.powFast r.num.natAbs).truncate order
  match x.leadingTerm with
  | none =>
    if r > 0 then return zero else throw "Zero raised to negative power"
  | some (e0, c0) =>
    if c0 < 0 then throw "Fractional power of negative Levi-Civita number is not real"
    let leadCoeff : Rat :=
      if c0 == 1 then 1
      else ratOfFloat (Float.pow (ratToFloat c0) (ratToFloat r))
    let leadPow := mono (e0 * r) leadCoeff
    let delta := (mono (-e0) c0⁻¹ * x) - 1
    if delta.isZero then return leadPow
    Id.run do
      let mut sum : FastLC := 1
      let mut term : FastLC := 1
      let mut binom : Rat := 1
      for k in [1:order] do
        binom := binom * (r - ((k - 1 : Nat) : Rat)) * mkRat 1 k
        term := (term * delta).truncate order
        if term.isZero then break
        sum := (sum + term * ofRat binom).truncate order
      return .ok ((leadPow * sum).truncate order)

/-- Square root `√x` for nonnegative Levi-Civita numbers (works on `H`, `ε`, `1 + ε`, etc.!). -/
def sqrtOrder (x : FastLC) (order : Nat := 10) : Except String FastLC :=
  if x.isZero then .ok zero
  else if x.signum < 0 then .error "sqrt of negative Levi-Civita number"
  else powRatOrder x (mkRat 1 2) order

/-! ### Clean Mathematical Formatting -/

private def fmtRatAbs (c : Rat) : String :=
  if c.den == 1 then s!"{c.num.natAbs}"
  else s!"({c.num.natAbs}/{c.den})"

/-- Pretty-print a canonical `FastLC` in clean human mathematical notation
    (e.g., `(1/4)H - (1/48)ε`, `H + 2 - 3ε²`). -/
def pretty (x : FastLC) : String :=
  match x.terms with
  | [] => "0"
  | first :: rest =>
    let fmtTerm (isFirst : Bool) (e c : Rat) : String :=
      let neg := c < 0
      let absC := if neg then -c else c
      let unit := PolynomialG.fmtUnitExp e
      let mag :=
        if unit == "" then
          if absC.den == 1 then s!"{absC.num}" else s!"{absC.num}/{absC.den}"
        else if absC == 1 then unit
        else s!"{fmtRatAbs absC}{unit}"
      if isFirst then
        if neg then s!"-{mag}" else mag
      else
        if neg then s!" - {mag}" else s!" + {mag}"
    let headStr := fmtTerm true first.1 first.2
    rest.foldl (init := headStr) fun acc (e, c) => acc ++ fmtTerm false e c

/-- Decimal-friendly pretty-printing (shows floating-point coefficients alongside `H`/`ε`). -/
def prettyApprox (x : FastLC) (decimals : Nat := 6) : String :=
  let fmtFloat (f : Float) : String :=
    let p10 := Float.pow 10.0 (Float.ofNat decimals)
    let r := (f * p10).round / p10
    s!"{r}"
  match x.terms with
  | [] => "0"
  | first :: rest =>
    let fmtTerm (isFirst : Bool) (e c : Rat) : String :=
      let f := ratToFloat c
      let neg := f < 0.0
      let absF := if neg then -f else f
      let unit := PolynomialG.fmtUnitExp e
      let mag :=
        if unit == "" then fmtFloat absF
        else if (absF - 1.0).abs < 1e-12 then unit
        else s!"{fmtFloat absF}{unit}"
      if isFirst then
        if neg then s!"-{mag}" else mag
      else
        if neg then s!" - {mag}" else s!" + {mag}"
    let headStr := fmtTerm true first.1 first.2
    rest.foldl (init := headStr) fun acc (e, c) => acc ++ fmtTerm false e c

instance : ToString FastLC where
  toString := pretty

instance : Repr FastLC where
  reprPrec x _ := s!"FastLC({x.pretty})"

end FastLC
end LeanInf
