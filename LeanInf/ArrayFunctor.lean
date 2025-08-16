-- Keep imports lean to maintain nightly compatibility
-- import Mathlib
-- import LeanCopilot -- disabled while building on latest nightly
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

-- Instances for Functor/List/Array already exist in core Lean.
-- We avoid redefining them to prevent conflicts on nightly.
