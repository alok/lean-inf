import Lake
open Lake DSL

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git"
require Parser from git "https://github.com/fgdorais/lean4-parser" @ "main"
require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.4.1"
package "lean-inf" where
  -- add package configuration options here

lean_lib «LeanInf» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-inf" where
  root := `Main
