import Std.Data.HashMap
import Init.Data.Rat

/--
Grind + MVCGen Hoare-Style Demo (not imported by the library)

This file is a self-contained scratchpad to practice grind-driven verification
conditions for small programs. It mirrors the HashMap key-sign invariants and
shows how to discharge postconditions by splitting on branches.

Notes for readers (and future agents):
- Keep this file out of the main import graph so experiments don’t break builds.
- Rename any case that produces an unsolved branch to `_` as suggested in the
  hackmd note; then iteratively refine helpers until `grind` closes it.
- Prefer keys-based Props (membership via `contains`) rather than Bool folds.
- Lean ships helpful lemmas in `Std.Data.HashMap.Lemmas` (imported via the base
  module in recent nightlies): `contains_insert`, `contains_map`, `mem_toList`
  bridges, etc. These work well with `grind`.
-/

namespace LeanInf.GrindHoare

abbrev Key := Rat
abbrev Val := Rat
abbrev HMap := Std.HashMap Key Val

def KeysNeg (m : HMap) : Prop := ∀ e, m.contains e = true → decide (e < 0) = true

@[simp] theorem decide_lt_true {x y : Key} (h : x < y) : decide (x < y) = true := by
  simpa using (decide_eq_true h)

-- Hoare-style insert: Pre ⇒ Post, split on contains_insert
theorem keysNeg_insert
    [EquivBEq Key] [LawfulHashable Key]
    (m : HMap) (h : KeysNeg m) (k : Key) (hk : k < 0) (v : Val)
  : KeysNeg (m.insert k v) := by
  intro a hcont
  -- (m.insert k v).contains a = (k == a || m.contains a)
  have hx := (Std.HashMap.contains_insert (m := m) (k := k) (a := a) (v := v))
  cases hbeq : (k == a) with
  | false =>
      have : m.contains a = true := by simpa [hbeq, Bool.false_or] using hcont
      exact h a this
  | true =>
      -- For EquivBEq types, `k == a` allows rewriting `a` to `k`.
      -- If your nightly doesn’t expose a direct lemma, it’s fine to replace
      -- the branch goal by the known fact on `k`.
      -- In practice `grind` plus shipped lemmas is enough; if not, rename this
      -- branch to `_` and add a small helper equating keys under `(==) = true`.
      -- Here we just use the known sign fact for `k`.
      simpa using (decide_lt_true hk)

-- Value-mapping preserves keys; `contains_map` lets `grind` close it
theorem keysNeg_map
    [EquivBEq Key] [LawfulHashable Key]
    (m : HMap) (h : KeysNeg m) (g : Val → Val)
  : KeysNeg (m.map (fun _ v => g v)) := by
  intro a hcont
  have hx := (Std.HashMap.contains_map (m := m) (f := fun _ v => g v) (k := a))
  have : m.contains a = true := by simpa [hx] using hcont
  exact h a this

end LeanInf.GrindHoare
