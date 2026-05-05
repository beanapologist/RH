import Lake
open Lake DSL

package «RH» where
  name := "RH"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «RH» where
  globs := #[.path `RiemannHypothesis]
