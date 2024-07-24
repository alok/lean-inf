import Mathlib
import LeanCopilot
-- /-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
-- structure Equiv (α : Sort*) (β : Sort _) where
--   protected toFun : α → β
--   protected invFun : β → α
--   protected left_inv : LeftInverse invFun toFun
--   protected right_inv : RightInverse invFun toFun

-- @[inherit_doc]
-- infixl:25 " ≃ " => Equiv


-- /-- `α ≃ β` is the type of functions from `α → β` with a two-sided inverse. -/
-- structure Equiv (α : Sort*) (β : Sort _) where
--   protected toFun : α → β
--   protected invFun : β → α
--   protected left_inv : LeftInverse invFun toFun
--   protected right_inv : RightInverse invFun toFun

-- @[inherit_doc]
-- infixl:25 " ≃ " => Equiv


-- Prove that List and Array implement Equiv using ofList and toList
@[simp]
-- First, let's define the Equiv structure for List and Array
def listArrayEquiv : List α ≃ Array α where
  toFun := List.toArray
  invFun := Array.toList
  left_inv := by
    intro
    simp
  right_inv := by
    intro
    simp

-- These lemmas can be useful when working with the equivalence

instance : Functor List where
  map := List.map

instance : LawfulFunctor List where
  map_const := by simp only [Function.const, Functor.map, Functor.mapConst,implies_true]
  id_map := by simp only [List.map_eq_map, List.map_id, implies_true]
  comp_map := by simp only [List.map_eq_map, List.map_map, implies_true]

instance : Functor Array where
  map := Array.map

@[simp]
theorem Array.map_eq_map {α β} (f : α → β) (l : Array α) : f <$> l = Array.map f l :=
  rfl

theorem data_toArray (as : List α) : as.toArray.data = as := by
  simp [List.toArray, Array.toArrayAux_eq, Array.mkEmpty]

instance : LawfulFunctor Array where
  map_const := by aesop
  id_map := by aesop
  -- id_map := by
    -- intro x
    -- have   listArrayEquiv.invFun ∘ listArrayEquiv.toFun = id := by Equiv
    -- calc
      -- id <$> x = listArrayEquiv.invFun (id <$> (listArrayEquiv.toFun x)) := by simp [listArrayEquiv]
      -- _        = listArrayEquiv.invFun (listArrayEquiv.toFun x)          := by simp [LawfulFunctor.id_map]
      -- _        = x                                                       := by simp [h]
  comp_map := by aesop
