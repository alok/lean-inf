import Lake
open Lake DSL

package leanInfFloatProofs where
  -- Reuse FloatLib's pre-downloaded & pre-built Mathlib + transitive deps (zero extra downloads)
  packagesDir := "../../FloatLib/.lake/packages"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`linter.missingDocs, true⟩
  ]

require LeanInf from ".."
require floatlib from "../../FloatLib"

@[default_target]
lean_lib FloatProofs where
  roots := #[`FloatProofs]
