import LeanInf.LeviCivitaNum
import LeanInf.Basic
import Init.Data.Rat
-- import Std.Tactic.Grind
import Std.Data.HashMap
-- HashMap lemmas module name varies by std4 version; try both if present
-- If unavailable, this import is ignored by the build.
-- Note: some nightly toolchains bundle lemmas into the base module.
-- import Std.Data.HashMap.Lemmas

open LeviCivitaNum

namespace LeanInf

/-! Lemma skeletons for sign/invariant preservation. We discharge many of these
    using `grind` once we provide small helper facts. For now, we also expose
    a few arithmetic facts to help `grind` close simple branches. -/

-- Basic arithmetic reflection helpers
@[simp, grind] theorem decide_lt_true {x y : Rat} (h : x < y) : decide (x < y) = true := by grind


@[simp, grind] theorem decide_gt_true {x y : Rat} (h : x > y) : decide (x > y) = true := by grind


@[simp, grind] theorem decide_neg_one_lt_zero : decide ((-1 : Rat) < 0) = true := by decide

@[simp, grind] theorem decide_one_gt_zero : decide ((1 : Rat) > 0) = true := by decide

-- Quick check for HashMap lemma prerequisites on our key type
#synth BEq Exponent
#synth Hashable Exponent
#synth EquivBEq Exponent
#synth LawfulHashable Exponent

-- Prop-level invariants on keys
def KeysNeg (m : Std.HashMap Exponent Coeff) : Prop :=
  ∀ e, m.contains e = true → decide (e < 0) = true

def KeysPos (m : Std.HashMap Exponent Coeff) : Prop :=
  ∀ e, m.contains e = true → decide (e > 0) = true

-- 1) Insert preserves key-sign predicates when the inserted key has the right sign
@[grind] theorem keysNeg_insert
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff)
    (h : KeysNeg m)
    (e : Exponent) (he : e < 0) (c : Coeff)
  : KeysNeg (m.insert e c) := by
  intro e' hce'
  have hx := (Std.HashMap.contains_insert (m := m) (k := e) (a := e') (v := c))
  -- (m.insert e c).contains e' = (e == e' || m.contains e')
  have := congrArg id (hx) -- keep hx for rewriting
  -- rewrite the assumption hce' via `contains_insert`
  -- Use cases on `e == e'`
  cases hbeq : (e == e') with
  | false =>
      -- then (m.insert e c).contains e' = m.contains e'
      have : m.contains e' = true := by
        -- from hce' and contains_insert
        simpa [hbeq, Bool.false_or] using hce'
      -- apply the inductive hypothesis on m
      exact h e' this
  | true =>
      -- then e' == e, so e' = e (under EquivBEq); use he
      have : e' = e := (Std.eq_of_beq_true hbeq)
      subst this
      simpa using (decide_lt_true he)

@[grind] theorem keysPos_insert
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff)
    (h : KeysPos m)
    (e : Exponent) (he : e > 0) (c : Coeff)
  : KeysPos (m.insert e c) := by
  intro e' hce'
  have hx := (Std.HashMap.contains_insert (m := m) (k := e) (a := e') (v := c))
  cases hbeq : (e == e') with
  | false =>
      have : m.contains e' = true := by simpa [hbeq, Bool.false_or] using hce'
      exact h e' this
  | true =>
      have : e' = e := (Std.eq_of_beq_true hbeq)
      subst this
      simpa using (decide_gt_true he)

-- 2) Mapping values preserves key-based predicates
@[grind] theorem keysNeg_map
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff)
    (h : KeysNeg m)
    (g : Coeff → Coeff)
  : KeysNeg (m.map (fun _ v => g v)) := by
  intro e hcont
  -- contains_map: (m.map f).contains k = m.contains k
  have hx := (Std.HashMap.contains_map (m := m) (f := fun _ v => g v) (k := e))
  -- rewrite hcont using hx
  have : m.contains e = true := by simpa [hx] using hcont
  exact h e this

@[grind] theorem keysPos_map
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff)
    (h : KeysPos m)
    (g : Coeff → Coeff)
  : KeysPos (m.map (fun _ v => g v)) := by
  intro e hcont
  have hx := (Std.HashMap.contains_map (m := m) (f := fun _ v => g v) (k := e))
  have : m.contains e = true := by simpa [hx] using hcont
  exact h e this

-- A specialized additive merge built from a list fold over the RHS map
def mergeAdd (a b : Std.HashMap Exponent Coeff) : Std.HashMap Exponent Coeff :=
  (b.toList).foldl (fun r (p : Exponent × Coeff) =>
    let k := p.1
    let v := p.2
    let prev := r.getD k 0
    r.insert k (prev + v)) a

-- Helper: membership in toList implies contains = true
@[grind]
theorem contains_of_mem_toList
    [EquivBEq Exponent] [LawfulHashable Exponent]
    {b : Std.HashMap Exponent Coeff} {k : Exponent} {v : Coeff}
  : (⟨k, v⟩ ∈ b.toList) → b.contains k = true := by
  intro hmem
  -- From membership in toList, we get both getKey? and get? are `some`.
  have hkv : b.getKey? k = some k ∧ b[k]? = some v := by
    simpa using (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some (m := b) (k := k) (v := v)).mp hmem
  have hget : b[k]?.isSome = true := by
    -- get? = some v implies isSome = true
    cases hkv.right with
    | rfl => simp
  -- contains equals isSome get?
  simpa [Std.HashMap.contains_eq_isSome_getElem? (m := b) (a := k)] using hget

-- 3) Merge-add preserves key-based invariants (negative keys)
@[grind]
theorem keysNeg_mergeAdd
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (a b : Std.HashMap Exponent Coeff)
    (ha : KeysNeg a) (hb : KeysNeg b)
  : KeysNeg (mergeAdd a b) := by
  -- unfold and induct over `b.toList`
  unfold mergeAdd
  generalize hL : b.toList = l
  revert a ha
  induction l with
  | nil => intro a ha; simpa using ha
  | @cons p ps ih =>
      intro a ha
      cases p with
      | mk k v =>
        -- Show `decide (k < 0) = true` using `hb` and membership in `b.toList`
        have : decide (k < 0) = true := by
          -- k,v is head of b.toList, hence member
          have : (⟨k, v⟩ ∈ b.toList) := by simpa [hL] using (List.mem_cons_self _ _)
          have hk : b.contains k = true := contains_of_mem_toList (b := b) (k := k) (v := v) this
          exact hb k hk
        -- Apply keysNeg_insert for the head, then recurse
        have hstep : KeysNeg ((a.insert k (a.getD k 0 + v))) := by
          -- keysNeg_insert requires providing instances and ha
          refine (keysNeg_insert (m := a) (h := ?_) (e := k) (he := ?_) (c := (a.getD k 0 + v))) ?_ ?_ ?_
          · exact inferInstance
          · exact inferInstance
          · exact ha
          · -- he: k<0
            -- from `decide (k < 0) = true`, extract proof
            have := this
            -- turn decide true into Prop
            exact of_decide_eq_true this
        -- now apply IH to the tail with the updated a
        simpa using ih _ hstep

-- 3) Merge-add preserves key-based invariants (positive keys)
@[grind]
theorem keysPos_mergeAdd
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (a b : Std.HashMap Exponent Coeff)
    (ha : KeysPos a) (hb : KeysPos b)
  : KeysPos (mergeAdd a b) := by
  unfold mergeAdd
  generalize hL : b.toList = l
  revert a ha
  induction l with
  | nil => intro a ha; simpa using ha
  | @cons p ps ih =>
      intro a ha
      cases p with
      | mk k v =>
        have : decide (k > 0) = true := by
          have : (⟨k, v⟩ ∈ b.toList) := by simpa [hL] using (List.mem_cons_self _ _)
          have hk : b.contains k = true := contains_of_mem_toList (b := b) (k := k) (v := v) this
          exact hb k hk
        have hstep : KeysPos ((a.insert k (a.getD k 0 + v))) := by
          refine (keysPos_insert (m := a) (h := ?_) (e := k) (he := ?_) (c := (a.getD k 0 + v))) ?_ ?_ ?_
          · exact inferInstance
          · exact inferInstance
          · exact ha
          · have := this; exact of_decide_eq_true this
        simpa using ih _ hstep

@[grind]
theorem keysPos_collectPos
    [Std.EquivBEq Exponent] [Std.LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) : KeysPos (collectPos m) := by
  unfold collectPos
  generalize hL : m.toList = l
  revert hL
  revert m
  refine List.rec (motive := fun l => ∀ m, m.toList = l → KeysPos ((m.toList.foldl (fun r p => let k := p.1; let v := p.2; if decide (k > 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)))) ?base ?step
  · intro m hL; intro e hc
    have : (Std.HashMap.emptyWithCapacity : Std.HashMap Exponent Coeff).contains e = false := by
      simpa using (Std.HashMap.contains_emptyWithCapacity (a := e) (c := 0))
    -- premise impossible; close trivially
    exact (False.elim (by cases (Bool.eq_true_eq_coe.mp hc)))
  · intro p ps ih m hL
    cases p with
    | mk k v =>
      dsimp
      by_cases hk : decide (k > 0)
      · intro e hc
        have hx := (Std.HashMap.contains_insert (m := (ps.foldl (fun r p => let k := p.1; let v := p.2; if decide (k > 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity))) (k := k) (a := e) (v := v))
        cases hbeq : (k == e) with
        | false =>
          have hc' : (ps.foldl (fun r p => let k := p.1; let v := p.2; if decide (k > 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)).contains e = true := by
            simpa [hbeq, Bool.false_or] using hc
          exact (ih m rfl) e hc'
        | true =>
          have heq : e = k := (Std.eq_of_beq_true hbeq).symm
          subst heq
          exact of_decide_eq_true hk |> decide_gt_true
      · intro e hc
        exact (ih m rfl) e hc

-- Collect negatives/positives by folding over toList with decide-guards
def collectNeg (m : Std.HashMap Exponent Coeff) : Std.HashMap Exponent Coeff :=
  (m.toList).foldl (fun r (p : Exponent × Coeff) =>
    let k := p.1; let v := p.2
    if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)

def collectPos (m : Std.HashMap Exponent Coeff) : Std.HashMap Exponent Coeff :=
  (m.toList).foldl (fun r (p : Exponent × Coeff) =>
    let k := p.1; let v := p.2
    if decide (k > 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)

@[grind]
theorem keysNeg_collectNeg
    [Std.EquivBEq Exponent] [Std.LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) : KeysNeg (collectNeg m) := by
  unfold collectNeg
  generalize hL : m.toList = l
  revert hL
  revert m
  -- Prove by induction over the list
  refine List.rec (motive := fun l => ∀ m, m.toList = l → KeysNeg ((m.toList.foldl (fun r p => let k := p.1; let v := p.2; if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)))) ?base ?step
  · intro m hL; intro e hc; 
    -- empty => contains false, contradiction gives trivial
    -- But since map is empty, contains e = false, so premise can't happen; ex falso
    -- use cases on contains
    have : (Std.HashMap.emptyWithCapacity : Std.HashMap Exponent Coeff).contains e = false := by
      simpa using (Std.HashMap.contains_emptyWithCapacity (a := e) (c := 0))
    -- rewrite hc leads to false = true, contradiction
    have := congrArg id (by exact this)
    -- derive any; or just exact by cases
    simpa using (False.elim (by cases (Bool.eq_true_eq_coe.mp hc)))
  · intro p ps ih m hL
    cases p with
    | mk k v =>
      dsimp
      by_cases hk : decide (k < 0)
      · -- insert k v
        intro e hc
        -- Membership can be either k or from previous fold; use contains_insert
        have hx := (Std.HashMap.contains_insert (m := (ps.foldl (fun r p => let k := p.1; let v := p.2; if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity))) (k := k) (a := e) (v := (let _ := v; (Std.HashMap.emptyWithCapacity).getD k 0 + v)))
        -- split on e==k
        cases hbeq : (k == e) with
        | false =>
          -- then membership reduces to previous fold; apply IH
          have hc' : (ps.foldl (fun r p => let k := p.1; let v := p.2; if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)).contains e = true := by
            simpa [hbeq, Bool.false_or] using hc
          have ihKeys := ih m rfl
          exact ihKeys e hc'
        | true =>
          -- e = k, use hk to obtain k<0
          have heq : e = k := (Std.eq_of_beq_true hbeq).symm
          subst heq
          exact of_decide_eq_true hk |> decide_lt_true
      · -- skip insert, use IH directly
        intro e hc
        have ihKeys := ih m rfl
        exact ihKeys e hc

-- HashMap-level helpers
section AllBridges

variable [Std.EquivBEq Exponent] [Std.LawfulHashable Exponent]

private theorem list_all_keys_true_of_fold_true
    (P : Exponent → Bool)
    (l : List (Exponent × Coeff))
    (h : l.foldl (fun acc (p : Exponent × Coeff) => acc && P p.1) true = true)
  : ∀ (k : Exponent) (v : Coeff), (k, v) ∈ l → P k = true := by
  intro k v hk
  revert h
  induction l with
  | nil =>
      intro h; cases hk
  | @cons p ps ih =>
      intro h
      cases hk with
      | head =>
          -- p = (k, v)
          cases p with
          | mk k' v' =>
            -- foldl true becomes (true && P k') for head
            have : P k' = true := by
              -- from h: (true && P k') && rest = true ⇒ P k' = true
              -- simp reduces the fold at head
              simp [List.foldl, Bool.and_eq_true] at h
              exact h.left
            -- substitute k' = k and v' = v
            simpa using this
      | tail hmem =>
          -- use ih on tail with the reduced fold hypothesis
          cases p with
          | mk k' v' =>
            -- from h: (true && P k') && fold ps = true ⇒ fold ps = true
            have hps : ps.foldl (fun acc (q : Exponent × Coeff) => acc && P q.1) (true && P k') = true := by
              simpa [List.foldl] using h
            -- simplify accumulator
            have hps' : ps.foldl (fun acc (q : Exponent × Coeff) => acc && P q.1) true = true := by
              -- if P k' is true, we can drop the initial (true && ...)
              have hk' : P k' = true := by
                -- deduce from h using and-true characterization
                have : (true && P k') && ps.foldl (fun acc (q : Exponent × Coeff) => acc && P q.1) true = true := by
                  simpa [List.foldl] using h
                -- from (a && b) = true ⇒ a = true ∧ b = true
                have : true && P k' = true ∧ ps.foldl (fun acc (q : Exponent × Coeff) => acc && P q.1) true = true := by
                  simpa [Bool.and_eq_true] using this
                exact this.left
              -- now drop the initial true &&
              simpa [List.foldl, hk', Bool.true_and] using hps
            exact ih hps' _ _ hmem

private theorem list_fold_true_of_all_keys_true
    (P : Exponent → Bool)
    (l : List (Exponent × Coeff))
    (hall : ∀ (k : Exponent) (v : Coeff), (k, v) ∈ l → P k = true)
  : l.foldl (fun acc (p : Exponent × Coeff) => acc && P p.1) true = true := by
  induction l with
  | nil => simp
  | @cons p ps ih =>
      cases p with
      | mk k v =>
        have hk : P k = true := hall k v (by simp)
        have hps : ∀ k v, (k, v) ∈ ps → P k = true := by
          intro k' v' hmem
          exact hall k' v' (by simp [hmem])
        have ih' := ih hps
        simpa [List.foldl, hk, Bool.true_and] using ih'

@[simp] theorem all_keys_true_iff_forall_contains
    (m : Std.HashMap Exponent Coeff) (P : Exponent → Bool)
  : m.all (fun e _ => P e) = true ↔ ∀ e, m.contains e = true → P e = true := by
  constructor
  · intro hAll e hcont
    -- rewrite `all` via fold over toList, then pick the pair carrying `e`
    have hfold : m.toList.foldl (fun acc (p : Exponent × Coeff) => acc && P p.1) true = true := by
      simpa [Std.HashMap.all] using (Std.HashMap.fold_eq_foldl_toList (m := m) (f := fun acc e v => acc && P e) (init := true))
        ▸ hAll
    -- from contains, get a value and membership in toArray/toList
    have hget : m[e]?.isSome = true := by
      simpa [Std.HashMap.contains_eq_isSome_getElem? (m := m) (a := e)] using hcont
    rcases m[e]? with
    | none => cases hget
    | some v =>
      -- we have (some v); use wrapper lemma to get existence of beq-related key in toArray
      have : ∃ e', e == e' ∧ (e', v) ∈ m.toArray := by
        simpa using (Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toArray (m := m) (k := e) (v := v))
      rcases this with ⟨e', heq, hmemArr⟩
      -- move to toList
      have hmemList : (e', v) ∈ m.toList := by
        simpa [← Std.HashMap.toArray_toList (m := m)] using hmemArr
      -- fold true ⇒ predicate true for every pair in toList
      have hpair : P e' = true :=
        list_all_keys_true_of_fold_true P m.toList hfold e' v hmemList
      -- EquivBEq gives equality from (==) = true
      have : e = e' := (Std.eq_of_beq_true heq)
      simpa [this] using hpair
  · intro hKeys
    -- Show all pairs in toList satisfy P on keys, then fold is true
    have hallPairs : ∀ k v, (k, v) ∈ m.toList → P k = true := by
      intro k v hmem
      have : m.contains k = true := by
        -- reuse earlier bridge from membership
        exact contains_of_mem_toList (b := m) (k := k) (v := v) (by simpa using hmem)
      exact hKeys k this
    -- fold over toList and rebuild `all`
    have : m.toList.foldl (fun acc (p : Exponent × Coeff) => acc && P p.1) true = true :=
      list_fold_true_of_all_keys_true P m.toList hallPairs
    simpa [Std.HashMap.all] using (Std.HashMap.fold_eq_foldl_toList (m := m) (f := fun acc e v => acc && P e) (init := true)).symm ▸ this

end AllBridges

-- HashMap-level helpers
theorem all_neg_insert
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e < 0)) = true)
    (e : Exponent) (he : e < 0) (c : Coeff)
  : (m.insert e c).all (fun e' _ => decide (e' < 0)) = true := by
  have hKeys : KeysNeg m := by
    -- translate boolean invariant to Prop invariant
    intro e' hce'
    have := (all_keys_true_iff_forall_contains (m := m) (P := fun x => decide (x < 0))).mp h_all
    exact this e' hce'
  -- insert preserves KeysNeg
  have hKeys' := keysNeg_insert (m := m) (h := hKeys) (e := e) (he := he) (c := c)
  -- translate back to `all = true`
  have : ∀ e', (Std.HashMap.insert m e c).contains e' = true → decide (e' < 0) = true := hKeys'
  exact (all_keys_true_iff_forall_contains (m := m.insert e c) (P := fun x => decide (x < 0))).mpr this

theorem all_pos_insert
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e > 0)) = true)
    (e : Exponent) (he : e > 0) (c : Coeff)
  : (m.insert e c).all (fun e' _ => decide (e' > 0)) = true := by
  have hKeys : KeysPos m := by
    intro e' hce'
    have := (all_keys_true_iff_forall_contains (m := m) (P := fun x => decide (x > 0))).mp h_all
    exact this e' hce'
  have hKeys' := keysPos_insert (m := m) (h := hKeys) (e := e) (he := he) (c := c)
  have : ∀ e', (Std.HashMap.insert m e c).contains e' = true → decide (e' > 0) = true := hKeys'
  exact (all_keys_true_iff_forall_contains (m := m.insert e c) (P := fun x => decide (x > 0))).mpr this

theorem all_neg_merge
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e < 0)) = true)
    (hb : b.all (fun e _ => decide (e < 0)) = true)
    (f : Exponent → Coeff → Coeff → Coeff)
  : (Std.HashMap.mergeWith a b f).all (fun e _ => decide (e < 0)) = true := by
  -- Translate lhs/rhs invariants to Prop form
  have hA : KeysNeg a := (all_keys_true_iff_forall_contains (m := a) (P := fun x => decide (x < 0))).mp ha
  have hB : KeysNeg b := (all_keys_true_iff_forall_contains (m := b) (P := fun x => decide (x < 0))).mp hb
  -- Prove Prop-level invariant for mergeWith, then translate back to Bool
  -- mergeWith is implemented as a fold over `b.toList` (see Basic.lean)
  have : KeysNeg (Std.HashMap.mergeWith a b f) := by
    -- Unfold mergeWith (fold over toList) and induct
    dsimp [Std.HashMap.mergeWith]
    generalize hL : b.toList = l
    revert a hA
    induction l with
    | nil => intro a hA; simpa using hA
    | @cons p ps ih =>
        intro a hA
        cases p with
        | mk k v =>
          -- `k` is from `b`, so `k<0`
          have hk' : decide (k < 0) = true := by
            have : (⟨k, v⟩ ∈ b.toList) := by simpa [hL] using (List.mem_cons_self _ _)
            have hk : b.contains k = true := contains_of_mem_toList (b := b) (k := k) (v := v) this
            exact hB k hk
          -- One step of the fold
          have hstep : KeysNeg (match a.get? k with
                                | none => a.insert k v
                                | some vp => a.insert k (f k vp v)) := by
            -- Both branches are `insert k _` and preserve the key invariant
            refine ?_ 
            -- Use `keysNeg_insert` with `he : k < 0`
            refine (keysNeg_insert (m := a) (h := hA) (e := k) (he := ?_) (c := (match a.get? k with | none => v | some vp => f k vp v))) ?_ ?_ ?_
            · exact inferInstance
            · exact inferInstance
            · exact of_decide_eq_true hk'
          -- Recurse
          have hrec := ih (match a.get? k with | none => a.insert k v | some vp => a.insert k (f k vp v)) hstep
          simpa using hrec
  exact (all_keys_true_iff_forall_contains (m := Std.HashMap.mergeWith a b f) (P := fun x => decide (x < 0))).mpr this

theorem all_pos_merge
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e > 0)) = true)
    (hb : b.all (fun e _ => decide (e > 0)) = true)
    (f : Exponent → Coeff → Coeff → Coeff)
  : (Std.HashMap.mergeWith a b f).all (fun e _ => decide (e > 0)) = true := by
  have hA : KeysPos a := (all_keys_true_iff_forall_contains (m := a) (P := fun x => decide (x > 0))).mp ha
  have hB : KeysPos b := (all_keys_true_iff_forall_contains (m := b) (P := fun x => decide (x > 0))).mp hb
  have : KeysPos (Std.HashMap.mergeWith a b f) := by
    dsimp [Std.HashMap.mergeWith]
    generalize hL : b.toList = l
    revert a hA
    induction l with
    | nil => intro a hA; simpa using hA
    | @cons p ps ih =>
        intro a hA
        cases p with
        | mk k v =>
          have hk' : decide (k > 0) = true := by
            have : (⟨k, v⟩ ∈ b.toList) := by simpa [hL] using (List.mem_cons_self _ _)
            have hk : b.contains k = true := contains_of_mem_toList (b := b) (k := k) (v := v) this
            exact hB k hk
          have hstep : KeysPos (match a.get? k with
                                | none => a.insert k v
                                | some vp => a.insert k (f k vp v)) := by
            refine (keysPos_insert (m := a) (h := hA) (e := k) (he := ?_) (c := (match a.get? k with | none => v | some vp => f k vp v))) ?_ ?_ ?_
            · exact inferInstance
            · exact inferInstance
            · exact of_decide_eq_true hk'
          have hrec := ih (match a.get? k with | none => a.insert k v | some vp => a.insert k (f k vp v)) hstep
          simpa using hrec
  exact (all_keys_true_iff_forall_contains (m := Std.HashMap.mergeWith a b f) (P := fun x => decide (x > 0))).mpr this

-- Specialized merges used in code: combining coefficients by addition
theorem all_neg_merge_add
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e < 0)) = true)
    (hb : b.all (fun e _ => decide (e < 0)) = true)
  : (Std.HashMap.mergeWith a b (fun _ x y => x + y)).all (fun e _ => decide (e < 0)) = true := by
  -- Convert to Prop invariants
  have hA : KeysNeg a := (all_keys_true_iff_forall_contains (m := a) (P := fun x => decide (x < 0))).mp ha
  have hB : KeysNeg b := (all_keys_true_iff_forall_contains (m := b) (P := fun x => decide (x < 0))).mp hb
  -- Use previously proved Prop-level mergeAdd invariant
  have hM := keysNeg_mergeAdd (a := a) (b := b) (ha := hA) (hb := hB)
  -- Translate back to boolean `all` for the merged map
  exact (all_keys_true_iff_forall_contains (m := Std.HashMap.mergeWith a b (fun _ x y => x + y)) (P := fun x => decide (x < 0))).mpr hM

theorem all_pos_merge_add
    (a b : Std.HashMap Exponent Coeff)
    (ha : a.all (fun e _ => decide (e > 0)) = true)
    (hb : b.all (fun e _ => decide (e > 0)) = true)
  : (Std.HashMap.mergeWith a b (fun _ x y => x + y)).all (fun e _ => decide (e > 0)) = true := by
  have hA : KeysPos a := (all_keys_true_iff_forall_contains (m := a) (P := fun x => decide (x > 0))).mp ha
  have hB : KeysPos b := (all_keys_true_iff_forall_contains (m := b) (P := fun x => decide (x > 0))).mp hb
  have hM := keysPos_mergeAdd (a := a) (b := b) (ha := hA) (hb := hB)
  exact (all_keys_true_iff_forall_contains (m := Std.HashMap.mergeWith a b (fun _ x y => x + y)) (P := fun x => decide (x > 0))).mpr hM

-- Mapping values does not affect key-based invariants
theorem all_neg_map_values
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e < 0)) = true)
    (g : Coeff → Coeff)
  : (m.map (fun _ v => g v)).all (fun e _ => decide (e < 0)) = true := by
  -- boolean → Prop
  have hKeys : KeysNeg m := (all_keys_true_iff_forall_contains (m := m) (P := fun x => decide (x < 0))).mp h_all
  -- map preserves keys (Prop form)
  have hKeys' := keysNeg_map (m := m) (h := hKeys) (g := g)
  -- Prop → boolean
  exact (all_keys_true_iff_forall_contains (m := m.map (fun _ v => g v)) (P := fun x => decide (x < 0))).mpr hKeys'

theorem all_pos_map_values
    (m : Std.HashMap Exponent Coeff)
    (h_all : m.all (fun e _ => decide (e > 0)) = true)
    (g : Coeff → Coeff)
  : (m.map (fun _ v => g v)).all (fun e _ => decide (e > 0)) = true := by
  have hKeys : KeysPos m := (all_keys_true_iff_forall_contains (m := m) (P := fun x => decide (x > 0))).mp h_all
  have hKeys' := keysPos_map (m := m) (h := hKeys) (g := g)
  exact (all_keys_true_iff_forall_contains (m := m.map (fun _ v => g v)) (P := fun x => decide (x > 0))).mpr hKeys'

-- Sign preservation at the LC level (skeletons)
theorem sign_preserved_by_infinitesimal_insert
    (x : LeviCivitaNum)
    (e : Exponent) (c : Coeff)
    (hneg : e < 0)
    (hle : ∀ e', x.infinitesimal.coeffs.contains e' → e ≤ e')
  : (signum x) = (signum { x with infinitesimal := ⟨x.infinitesimal.coeffs.insert e c⟩ }) := by
  -- Will follow from ordering of exponents and first-nonzero-term reasoning
  sorry

theorem sign_preserved_by_infinite_insert
    (x : LeviCivitaNum)
    (e : Exponent) (c : Coeff)
    (hpos : e > 0)
    (hle : ∀ e', x.infinite.coeffs.contains e' → e ≥ e')
  : (signum x) = (signum { x with infinite := ⟨x.infinite.coeffs.insert e c⟩ }) := by
  sorry

end LeanInf
