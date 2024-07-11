import Lake
open Lake DSL

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git"

package "lean-inf" where
  -- add package configuration options here

lean_lib «LeanInf» where
  -- add library configuration options here

@[default_target]
lean_exe "lean-inf" where
  root := `Main
