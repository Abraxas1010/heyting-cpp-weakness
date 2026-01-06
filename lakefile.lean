import Lake
open Lake DSL

package «HeytingCPPWeakness» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

@[default_target]
lean_lib «HeytingLean» where

lean_exe cpp_smoke where
  root := `HeytingLean.CPP.Smoke
