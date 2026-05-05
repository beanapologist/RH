import Lake
open Lake DSL

package «RH» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «RH» where
  globs := #[.one `RiemannHypothesis]
