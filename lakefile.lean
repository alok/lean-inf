import Lake
open Lake DSL

-- Keep dependencies minimal while targeting nightly Lean.
-- mathlib and LeanCopilot are disabled to avoid Lake API incompatibilities.
-- aesop is also disabled; we avoid using it in proofs for now.
package "lean-inf" where
  -- add package configuration options here

lean_lib «LeanInf» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-inf" where
  root := `Main
