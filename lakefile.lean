import Lake
open Lake DSL

package LeanInf where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

@[default_target]
lean_lib LeanInf where

@[default_target]
lean_exe inf where
  root := `Main
