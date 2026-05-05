# RH

This repository contains a Lean 4 / Mathlib formalization of a conditional proof
of the Riemann Hypothesis.

The current development does not claim an unconditional machine-checked proof of
RH. Instead, it formalizes the geometric, factorization, symmetry, and endpoint
packaging arguments, and reduces the final RH conclusion to a small set of
explicit analytic boundary axioms recorded in `RH.lean`.

In particular, the final RH-style step is isolated as the rigidity boundary
`xi_real_rigidity`, together with several named analytic continuation,
log-derivative, and convergence assumptions. The file is therefore best read as
an explicit formal reduction of RH to those remaining analytic ingredients.

Main file:

- `RH.lean`

Packaged endpoint:

- `rh_endpoint_master`

Explicit reduction theorem:

- `RH_reduction_to_rigidity_boundary`