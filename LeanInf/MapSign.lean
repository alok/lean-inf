import LeanInf.Basic
import LeanInf.CoeffLike
import Std.Data.HashMap
import Init.Data.Rat

namespace LeanInf

abbrev Exponent := Rat
abbrev Coeff := Rat

-- Arithmetic helpers
@[simp, grind] theorem decide_lt_true {x y : Exponent} (h : x < y) : decide (x < y) = true := by
  simpa using (decide_eq_true h)
@[simp, grind] theorem decide_gt_true {x y : Exponent} (h : x > y) : decide (x > y) = true := by
  simpa using (decide_eq_true h)

def KeysNeg (m : Std.HashMap Exponent Coeff) : Prop :=
  ∀ e, m.contains e = true → decide (e < 0) = true
def KeysPos (m : Std.HashMap Exponent Coeff) : Prop :=
  ∀ e, m.contains e = true → decide (e > 0) = true

@[grind] theorem keysNeg_insert
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) (h : KeysNeg m)
    (e : Exponent) (he : e < 0) (c : Coeff) :
  KeysNeg (m.insert e c) := by
  intro e' hce'
  have hx := (Std.HashMap.contains_insert (m := m) (k := e) (a := e') (v := c))
  cases hbeq : (e == e') with
  | false =>
      have : m.contains e' = true := by simpa [hbeq, Bool.false_or] using hce'
      exact h e' this
  | true =>
      have : e' = e := (Std.eq_of_beq_true hbeq)
      subst this
      simpa using (decide_lt_true he)

@[grind] theorem keysPos_insert
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) (h : KeysPos m)
    (e : Exponent) (he : e > 0) (c : Coeff) :
  KeysPos (m.insert e c) := by
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

@[grind] theorem keysNeg_map
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) (h : KeysNeg m) (g : Coeff → Coeff) :
  KeysNeg (m.map (fun _ v => g v)) := by
  intro e hcont
  have hx := (Std.HashMap.contains_map (m := m) (f := fun _ v => g v) (k := e))
  have : m.contains e = true := by simpa [hx] using hcont
  exact h e this

@[grind] theorem keysPos_map
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) (h : KeysPos m) (g : Coeff → Coeff) :
  KeysPos (m.map (fun _ v => g v)) := by
  intro e hcont
  have hx := (Std.HashMap.contains_map (m := m) (f := fun _ v => g v) (k := e))
  have : m.contains e = true := by simpa [hx] using hcont
  exact h e this

-- Membership bridge
@[grind]
theorem contains_of_mem_toList
    [EquivBEq Exponent] [LawfulHashable Exponent]
    {b : Std.HashMap Exponent Coeff} {k : Exponent} {v : Coeff}
  : (⟨k, v⟩ ∈ b.toList) → b.contains k = true := by
  intro hmem
  have hkv : b.getKey? k = some k ∧ b[k]? = some v := by
    simpa using (Std.HashMap.mem_toList_iff_getKey?_eq_some_and_getElem?_eq_some (m := b) (k := k) (v := v)).mp hmem
  have hget : b[k]?.isSome = true := by cases hkv.right with | rfl => simp
  simpa [Std.HashMap.contains_eq_isSome_getElem? (m := b) (a := k)] using hget

-- Merge-add (fold) for invariant-preserving merge
def mergeAdd (a b : Std.HashMap Exponent Coeff) : Std.HashMap Exponent Coeff :=
  (b.toList).foldl (fun r (p : Exponent × Coeff) =>
    let k := p.1; let v := p.2
    let prev := r.getD k 0
    r.insert k (prev + v)) a

-- General merge with an arbitrary combiner, implemented via Std.HashMap.mergeWith
def mergeWith (a b : Std.HashMap Exponent Coeff) (f : Exponent → Coeff → Coeff → Coeff) : Std.HashMap Exponent Coeff :=
  Std.HashMap.mergeWith a b f

@[grind]
theorem keysNeg_mergeAdd
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (a b : Std.HashMap Exponent Coeff)
    (ha : KeysNeg a) (hb : KeysNeg b) :
  KeysNeg (mergeAdd a b) := by
  unfold mergeAdd
  generalize hL : b.toList = l
  revert a ha
  induction l with
  | nil => intro a ha; simpa using ha
  | @cons p ps ih =>
      intro a ha
      cases p with
      | mk k v =>
        have : decide (k < 0) = true := by
          have : (⟨k, v⟩ ∈ b.toList) := by simpa [hL] using (List.mem_cons_self _ _)
          have hk : b.contains k = true := contains_of_mem_toList (b := b) (k := k) (v := v) this
          exact hb k hk
        have hstep : KeysNeg ((a.insert k (a.getD k 0 + v))) := by
          refine (keysNeg_insert (m := a) (h := ha) (e := k) (he := ?_) (c := (a.getD k 0 + v)))
          exact of_decide_eq_true this
        simpa using ih _ hstep

@[grind]
theorem keysPos_mergeAdd
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (a b : Std.HashMap Exponent Coeff)
    (ha : KeysPos a) (hb : KeysPos b) :
  KeysPos (mergeAdd a b) := by
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
          refine (keysPos_insert (m := a) (h := ha) (e := k) (he := ?_) (c := (a.getD k 0 + v)))
          exact of_decide_eq_true this
        simpa using ih _ hstep

@[grind]
theorem keysNeg_mergeWith
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (a b : Std.HashMap Exponent Coeff)
    (ha : KeysNeg a) (hb : KeysNeg b) (f : Exponent → Coeff → Coeff → Coeff) :
  KeysNeg (mergeWith a b f) := by
  dsimp [mergeWith]
  -- mergeWith implemented in Std via fold over b.toList; induct over it
  generalize hL : b.toList = l
  revert a ha
  induction l with
  | nil => intro a ha; simpa using ha
  | @cons p ps ih =>
      intro a ha
      cases p with
      | mk k v =>
        have : decide (k < 0) = true := by
          have : (⟨k, v⟩ ∈ b.toList) := by simpa [hL] using (List.mem_cons_self _ _)
          have hk : b.contains k = true := contains_of_mem_toList (b := b) (k := k) (v := v) this
          exact hb k hk
        -- One fold step is an insert at key k with some value
        have hstep : KeysNeg (match a.get? k with
                              | none => a.insert k v
                              | some vp => a.insert k (f k vp v)) := by
          refine (keysNeg_insert (m := a) (h := ha) (e := k) (he := ?_) (c := (match a.get? k with | none => v | some vp => f k vp v))) ?_ ?_ ?_
          · exact inferInstance
          · exact inferInstance
          · exact of_decide_eq_true this
        -- Recurse
        simpa using ih _ hstep

@[grind]
theorem keysPos_mergeWith
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (a b : Std.HashMap Exponent Coeff)
    (ha : KeysPos a) (hb : KeysPos b) (f : Exponent → Coeff → Coeff → Coeff) :
  KeysPos (mergeWith a b f) := by
  dsimp [mergeWith]
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
        have hstep : KeysPos (match a.get? k with
                              | none => a.insert k v
                              | some vp => a.insert k (f k vp v)) := by
          refine (keysPos_insert (m := a) (h := ha) (e := k) (he := ?_) (c := (match a.get? k with | none => v | some vp => f k vp v))) ?_ ?_ ?_
          · exact inferInstance
          · exact inferInstance
          · exact of_decide_eq_true this
        simpa using ih _ hstep

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
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) : KeysNeg (collectNeg m) := by
  unfold collectNeg
  generalize hL : m.toList = l
  revert hL
  revert m
  refine List.rec (motive := fun l => ∀ m, m.toList = l → KeysNeg ((m.toList.foldl (fun r p => let k := p.1; let v := p.2; if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)))) ?base ?step
  · intro m hL; intro e hc; cases hc
  · intro p ps ih m hL; cases p with | mk k v =>
    dsimp
    by_cases hk : decide (k < 0)
    · intro e hc
      have hx := (Std.HashMap.contains_insert (m := (ps.foldl (fun r p => let k := p.1; let v := p.2; if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity))) (k := k) (a := e) (v := v))
      cases hbeq : (k == e) with
      | false =>
          have hc' : (ps.foldl (fun r p => let k := p.1; let v := p.2; if decide (k < 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)).contains e = true := by
            simpa [hbeq, Bool.false_or] using hc
          exact (ih m rfl) e hc'
      | true =>
          have heq : e = k := (Std.eq_of_beq_true hbeq).symm
          subst heq
          exact of_decide_eq_true hk |> decide_lt_true
    · intro e hc
      exact (ih m rfl) e hc

@[grind]
theorem keysPos_collectPos
    [EquivBEq Exponent] [LawfulHashable Exponent]
    (m : Std.HashMap Exponent Coeff) : KeysPos (collectPos m) := by
  unfold collectPos
  generalize hL : m.toList = l
  revert hL
  revert m
  refine List.rec (motive := fun l => ∀ m, m.toList = l → KeysPos ((m.toList.foldl (fun r p => let k := p.1; let v := p.2; if decide (k > 0) then r.insert k v else r) (Std.HashMap.emptyWithCapacity)))) ?base ?step
  · intro m hL; intro e hc; cases hc
  · intro p ps ih m hL; cases p with | mk k v =>
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

end LeanInf
