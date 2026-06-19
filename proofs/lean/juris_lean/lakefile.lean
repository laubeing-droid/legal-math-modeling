import Lake
open Lake DSL

package «juris_lean»

@[default_target]
lean_lib «JurisLean»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0"
