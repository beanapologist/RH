# RH: A Geometric Reduction of the Riemann Hypothesis

[![Lean CI](https://github.com/beanapologist/RH/actions/workflows/lean-ci.yml/badge.svg?branch=main)](https://github.com/beanapologist/RH/actions/workflows/lean-ci.yml)

This repository contains a Lean 4 / Mathlib formalization of a geometric reduction of the Riemann Hypothesis.

The current development does not claim an unconditional machine-checked proof of RH. Instead, it formalizes the geometric, factorization, symmetry, and endpoint packaging arguments, and reduces the RH conclusion to a small set of explicit analytic boundary axioms.

## Architecture

**Primary endpoint route (window-limit frontier):**
- `conditional_RH` — Main theorem: Every nontrivial-strip zero of ζ lies on Re(s) = 1/2
- Routes through `conditional_RH_via_window_limits` using the **window-limit frontier**
- Grounded in analytic theory: ζ-zeros are limits of finite-window zeros, phase-lock persists at limits
- Requires: `zeta_zero_is_limit_of_window_zeros`, `phase_lock_from_window_limit`

**Extended endpoint:**
- `rh_endpoint_master` — Same conclusion packaged with geometric/analytic bridge data
- Routes through `conditional_RH_via_window_limits_with_bridge`
- Output includes critical-line rigidity, phase-lock closure, defect bounds, and coherence norm

**Alternative strong-defect route:** 
- `conditional_RH_from_strong_defect_frontier` — Purely algebraic rigidity via defect factorization
- Valid but more abstract; use if you prefer source/medium/sink narrative
- Requires: `xi_defect_profile_nonzero_off_critical`, `xi_partial_defect2D_window_tendsto_zero`

## Geometric Bridge

The canonical source factor **B = 1 + i** connects to the unit-circle crossing locus:

- Normalized form equals `sourcePhase(π/4)` — a unit-circle phase point
- Lies on the geometric locus where **x = y** on the circle **x² + y² = 1**
- Exact two-way characterization of the locus by two phase points: `sourcePhase(π/4)` and `sourcePhase(5π/4)`
- See: `canonical_source_direction_eq_sourcePhase_pi_div_four` and `unit_circle_re_eq_im_iff_eq_sourcePhase_pi_div_four_or_five_pi_div_four`

## Status

**Formally Proved (no `sorry`):**
- Geometric framework: factorization, magnitude balance, coherence symmetry, critical-line forced σ = 1/2
- Cartesian/polar channel decomposition, prime-wise decomposition
- Finite-window refinement identities and phase-velocity relations
- Endpoint packaging and bridge data coherence
- Unit-circle crossing locus characterization

**Not Formalized (explicit boundary axioms):**
- **Window-limit frontier:** `zeta_zero_is_limit_of_window_zeros`, `phase_lock_from_window_limit`
- **Strong-defect frontier:** `xi_defect_profile_nonzero_off_critical`, `xi_partial_defect2D_window_tendsto_zero`
- **Supporting boundaries:** xi log-derivative formula, phase velocity on critical line, completed ζ / Hurwitz conditions, Cauchy tail control, phase-lock shift constant

See end of `RH.lean` for full inventory.

## Files

- `RH.lean` — Main formalization (3626 lines)
- `lakefile.lean` — Lake build configuration
- `lean-toolchain` — Lean version specification
- `.github/workflows/lean-ci.yml` — CI/CD workflow

## Build

```bash
lake build
```

## Main Entry Points

- `conditional_RH` — Primary RH endpoint (window-limit frontier)
- `rh_endpoint_master` — Extended endpoint with bridge data
- `RH_reduction_to_rigidity_boundary` — Explicit reduction theorem
- `canonical_source_direction_eq_sourcePhase_pi_div_four` — Canonical source ↔ unit-circle crossing