import Lake
open Lake DSL

-- Keep dependencies minimal while targeting nightly Lean.
-- mathlib and LeanCopilot are disabled to avoid Lake API incompatibilities.
-- aesop is also disabled; we avoid using it in proofs for now.
package LeanInf where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩,
    ⟨`doc.verso, true⟩
  ]

@[default_target]
lean_lib LeanInf where

@[default_target]
lean_exe inf where
  root := `Main
