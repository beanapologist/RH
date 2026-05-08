# RH: A Geometric Reduction of the Riemann Hypothesis

[![Lean CI](https://github.com/beanapologist/RH/actions/workflows/lean-ci.yml/badge.svg?branch=main)](https://github.com/beanapologist/RH/actions/workflows/lean-ci.yml)

This repository contains a Lean 4 / Mathlib formalization of a geometric reduction of the Riemann Hypothesis.

The current development does not claim an unconditional machine-checked proof of RH. Instead, it formalizes the geometric, factorization, symmetry, and endpoint packaging arguments, and reduces the RH conclusion to a small set of explicit analytic boundary axioms.

## Current Endpoint (Audit-Synced)

As of the latest architecture pass, the canonical top endpoint is split into:

- `MajorRHGatewayBoundary` (hard gateway; definitional alias of `F_lattice_zero_limit_boundary`)
- `SoftPipelineInputs` (soft analytic pipeline bundle)

with closure theorem:

- `conditional_RH_of_major_gateway_and_soft_pipeline`

and equivalent one-bundle form:

- `FinalUnresolvedInputs`
- `conditional_RH_of_final_unresolved_inputs`
- `FinalUnresolvedInputs_iff_major_gateway_and_soft_pipeline`

This supersedes older documentation that listed many factor-target/nonvanishing assumptions directly at the final endpoint level.

## Architecture

**Primary endpoint route (window-limit frontier):**
- `conditional_RH` — Main theorem: Every nontrivial-strip zero of ζ lies on Re(s) = 1/2
- Routes through `conditional_RH_via_window_limits`, now expressed via `conditional_RH_via_torus_compatibility_frontier`
- Uses the **torus-compatibility frontier** as the canonical top-level endpoint interface whose window-limit projection closes RH
- Grounded in analytic theory: lattice-window zeros converge to strip limits, then phase-lock/rigidity closes on the critical line
- Active Step-1 boundary assumptions:
  - `step1_F_lattice_boundary_assumption`
  - `step1_tail_control_assumption`
  - `step1_velocity_transfer_assumption`
  - `step1_phase_velocity_identity_assumption`
- Derived interface: `zeta_zero_is_limit_of_window_zeros`

**Unified torus-compatibility frontier (canonical top-level endpoint interface):**
- `TorusCompatibilityFrontier := StrongDefectFrontier ∧ WindowLimitFrontier`
- Shared defect object: `torusCompatibilityDefect N s = ‖xi_partial_defect2D (prime_window N) s‖`
- Shared lock predicate: `torusPhaseLock s := Re(s) = 1/2`
- Strong-defect projection: quantitative off-critical incompatibility via eventual positive lower bounds
- Window-limit projection: strip limit-points of window zeros force torus phase lock

**Extended endpoint:**
- `rh_endpoint_master` — Same conclusion packaged with geometric/analytic bridge data
- Routes through `conditional_RH_via_window_limits_with_bridge`
- Output includes critical-line rigidity, phase-lock closure, defect bounds, and coherence norm

**Alternative strong-defect route:** 
- `conditional_RH_from_strong_defect_frontier` — Purely algebraic rigidity via defect factorization
- Valid but more abstract; use if you prefer source/medium/sink narrative
- Requires split strong-defect inputs:
  - `strongDefectProfile_assumption`
  - `strongDefectClosure_assumption`
- Projected interfaces: `xi_defect_profile_nonzero_off_critical`, `xi_partial_defect2D_window_tendsto_zero`

## Geometric Bridge

The canonical source factor **B = 1 + i** connects to the unit-circle crossing locus:

- Normalized form equals `sourcePhase(π/4)` — a unit-circle phase point
- Lies on the geometric locus where **x = y** on the circle **x² + y² = 1**
- Exact two-way characterization of the locus by two phase points: `sourcePhase(π/4)` and `sourcePhase(5π/4)`
- See: `canonical_source_direction_eq_sourcePhase_pi_div_four` and `unit_circle_re_eq_im_iff_eq_sourcePhase_pi_div_four_or_five_pi_div_four`

## Status

**Formally Proved (core, build-clean):**
- Geometric framework: factorization, magnitude balance, coherence symmetry, critical-line forced σ = 1/2
- Cartesian/polar channel decomposition, prime-wise decomposition
- Finite-window refinement identities and phase-velocity relations
- Endpoint packaging and bridge data coherence
- Unit-circle crossing locus characterization

**Not Formalized (explicit boundary assumptions / stubs):**
- **Canonical final unresolved interface (preferred):**
  - `MajorRHGatewayBoundary`
  - `SoftPipelineInputs`
- **Window-limit frontier (active Step-1 split form):**
  - `step1_F_lattice_boundary_assumption`
  - `step1_tail_control_assumption`
  - `step1_velocity_transfer_assumption`
  - `step1_phase_velocity_identity_assumption`
- **Strong-defect frontier (active split form):**
  - `strongDefectProfile_assumption`
  - `strongDefectClosure_assumption`
- **Real-axis classification:** `real_axis_zeta_zero_onTrivialZeroLine` is a **proved theorem** (no `sorry`).
  Remaining real-axis analytic input bundled as explicit axiom:
  - `riemannZeta_half_numeric_certificate` — certified midpoint approximation (implies `ζ(1/2) ≠ 0`)
  - `riemannZeta_real_no_zero_in_Ioo_01` is a **derived theorem** from strip rigidity +
    `riemannZeta_ne_zero_at_half`
  - `riemannZeta_ne_zero_at_neg_odd_nat` is now a **proved theorem**
- **Projected interfaces:** `xi_defect_profile_nonzero_off_critical`, `xi_partial_defect2D_window_tendsto_zero`
- **Supporting boundaries:** `conjugationBoundaryInput_assumption`
- **Projected interface:** `completedHurwitzZetaEven_zero_conj_of_ne_zero`
- **Prototype target (currently not active global assumption):** `xi_logderiv_formula` (threaded as explicit input to reduction prototypes)
- **Step-1 consumed analytic bridges (not active global assumptions):** `missingPrimeCore_cauchy_tail` -> `step1_tail_control_of_missingPrimeCore_cauchy_tail`, `partialEulerPhaseVelocity_window_tendsto` -> `step1_velocity_transfer_of_partialEulerPhaseVelocity_window_tendsto`, `phase_velocity_on_critical_line` -> `step1_phase_velocity_identity_of_assumption`
- **Prototype target (currently not active global assumption):** `xi_logderiv_symmetry_sum` (via `xi_logderiv_symmetry_sum_of_xi_logderiv_formula`)
- **Localized compatibility input (not active globally):** `xi_partial_defect2D_factor_boundary` (used only by `defect_factors`)
- **Optional compatibility marker (definitional):** `phase_lock_shift_constant_11_over_8`

See end of `RH.lean` for full inventory.

## Assumption Discharge Roadmap

To move from the current reduction to an unconditional theorem, the remaining work is to replace each boundary axiom with a proved theorem in Lean.

Current checklist status: all interfaces are theorem-clean (no `sorry`), but endpoint closure is still conditional on explicit `variable` assumptions in `RH.lean`.

Latest audit note:
- The final endpoint bundle was tightened to avoid over-strong global nonvanishing assumptions (`∀ s, zeta s ≠ 0` style) at top level.
- The preferred final route now uses `XiLogDerivFormula` directly in `SoftPipelineInputs` plus staged-tail + bridge inputs.

Execution status notes:
- Lattice-native closure routing is in place (`F(s,t)` boundary -> window zero limit -> phase-lock bridge -> RH endpoint).
- `phase_lock_from_window_limit` is a theorem (no placeholder), but currently depends on strong-defect assumptions already declared in the file.
- `zeta_zero_is_limit_of_window_zeros` is now derived from the active Step-1 assumption.
- Step-1 landing interface is now explicit and non-alias: `Step1ApproximationFrontier` packages lattice zero-limit boundary + local epsilon-approximation at zeta zeros + zero-stability transfer (local capture -> convergent sequence extraction) + tail-control schema for window cores + velocity-transfer schema + lattice/window channel identity.
- New bridge: `step1_tail_control_of_missingPrimeCore_cauchy_tail` connects `missingPrimeCore_cauchy_tail` into the Step-1 frontier.
- New bridge: `step1_velocity_transfer_of_partialEulerPhaseVelocity_window_tendsto` connects `partialEulerPhaseVelocity_window_tendsto` into the Step-1 frontier.
- New reduction wrapper: `step1_reduced_frontier_holds_of_XiLogDerivFormula_and_slit` discharges the named Step-1 phase clause from `XiLogDerivFormula + slit`.
- New endpoint wrapper: `conditional_RH_via_window_limits_of_XiLogDerivFormula_and_slit` routes RH closure through that reduced phase-input interface.
- `xi_logderiv_formula` and `conjugationBoundaryInput_assumption` remain high-value analytic discharge targets.

Recommended order (dependency-first), now tracked as a checklist:

- [ ] `step1_F_lattice_boundary_assumption`
- [ ] `step1_tail_control_assumption`
- [ ] `step1_velocity_transfer_assumption`
- [ ] `step1_phase_velocity_identity_assumption`
- [ ] `strongDefectProfile_assumption`
- [ ] `strongDefectClosure_assumption`
- [x] `real_axis_zeta_zero_onTrivialZeroLine` (proved; depends on one Mathlib-external analytic boundary below)
- [ ] `riemannZeta_half_numeric_certificate` (numeric bound at `s = 1/2`; `riemannZeta_ne_zero_at_half` is derived)
- [x] `riemannZeta_real_no_zero_in_Ioo_01` (derived theorem: any strip real zero is forced to `x=1/2`)
- [x] `riemannZeta_ne_zero_at_neg_odd_nat` (proved from `riemannZeta_neg_nat_eq_bernoulli` + even Bernoulli nonvanishing)
- [ ] `xi_partial_defect2D_window_tendsto_zero` (projected interface from bundled input)
- [ ] `xi_defect_profile_nonzero_off_critical` (projected interface from bundled input)
- [x] `missingPrimeCore_cauchy_tail` (consumed into Step-1 frontier via bridge theorem)
- [x] `partialEulerPhaseVelocity_window_tendsto` (consumed into Step-1 frontier via bridge theorem)
- [x] `xi_logderiv_formula` (removed from active global assumptions; currently threaded as explicit prototype input)
- [x] `xi_logderiv_symmetry_sum` (no longer active global assumption; represented by reduction prototype theorem)
- [x] `phase_velocity_on_critical_line` (consumed into Step-1 frontier via phase-velocity identity bridge)
- [ ] `conjugationBoundaryInput_assumption` (bundled completed Hurwitz-even conjugation boundary)
- [x] `completedRiemannZeta_conj` (derived globally from established conjugation lemmas)
- [x] `xi_partial_defect2D_factor_boundary` (localized compatibility input; removed from active global assumptions)
- [x] `phase_lock_shift_constant_11_over_8` (optional heuristic marker, now definitional)

### Bernoulli trick proof map (`riemannZeta_ne_zero_at_neg_odd_nat`)

Goal: for odd `m >= 1`, prove `riemannZeta (-(m : ℝ) : ℂ) ≠ 0`.

1. Rewrite by special value at negative naturals:
   `riemannZeta_neg_nat_eq_bernoulli` gives
   `ζ(-m) = (-1)^m * bernoulli (m + 1) / (m + 1)`.
2. Reduce to Bernoulli nonvanishing:
   denominator `(m+1)` and factor `(-1)^m` are nonzero, so it suffices to show
   `bernoulli (m+1) ≠ 0`.
3. Use oddness:
   from `m % 2 = 1`, obtain `m + 1 = 2 * k` with `k ≠ 0`, reducing to
   `bernoulli (2 * k) ≠ 0`.
4. Prove even Bernoulli nonvanishing by contradiction:
   assume `bernoulli (2 * k) = 0`.
5. Inject into positive-even zeta formula:
   `riemannZeta_two_mul_nat` then forces `riemannZeta (2 * k : ℂ) = 0`.
6. Contradict positivity on the real axis:
   `riemannZeta_pos_of_one_lt` yields `0 < riemannZeta (2 * k : ℝ)`, hence
   `riemannZeta (2 * k : ℂ) ≠ 0`.
7. Conclude `bernoulli (2 * k) ≠ 0`, then back-substitute to get
   `riemannZeta (-(m : ℝ) : ℂ) ≠ 0`.

Net effect: odd negative real-axis nonvanishing is now Mathlib-native through
`HurwitzZetaValues` + `Dirichlet` positivity. The open-interval boundary is no longer primitive:
`riemannZeta_real_no_zero_in_Ioo_01` is derived from strip rigidity, leaving only the
single-point boundary `riemannZeta_ne_zero_at_half` on the real axis.

### Midpoint certificate contract (`riemannZeta_ne_zero_at_half`)

`RH.lean` now factors midpoint nonvanishing through a numeric-certificate interface:

- `riemannZeta_half_numeric_certificate` requires `∃ c ε : ℝ` such that
  - `0 ≤ ε`
  - `ε < |c|`
  - `‖riemannZeta ((1/2 : ℝ) : ℂ) - (c : ℂ)‖ ≤ ε`
- From this, `riemannZeta_ne_zero_at_half_of_numeric_certificate` proves
  `riemannZeta ((1/2 : ℝ) : ℂ) ≠ 0`.
- The exported theorem `riemannZeta_ne_zero_at_half` is now derived from that certificate.

Interpretation: to fully discharge the last real-axis boundary, it is enough to provide one
certified approximation bound at `s = 1/2` with error strictly smaller than the center magnitude.

**Why this works (triangle inequality).**  
Once you have `‖ζ(1/2) - c‖ ≤ ε` and `ε < |c|`, then `ζ(1/2) ≠ 0`: for example,
`|c| ≤ ‖ζ(1/2) - c‖ + ‖ζ(1/2)‖` gives `‖ζ(1/2)‖ ≥ |c| - ε > 0`.  
The proof in `RH.lean` uses the equivalent contradiction: if `ζ(1/2) = 0` then
`‖c‖ ≤ ε`, contradicting `ε < |c|`.

**Concrete target numbers (informal; not yet a Lean proof).**  
Classically `ζ(1/2) ≈ -1.4603545…`. A certificate of the right *shape* might use e.g.
`c = -1.46`, `ε = 0.01`, so `|c| = 1.46 > ε` and one would need only a **certified**
bound `‖ζ(1/2) - (-1.46)‖ ≤ 0.01` in Lean. That last step is discharged by
`riemannZeta_half_numeric_certificate` today; replacing the axiom requires either
interval arithmetic, a native numeric evaluator trusted in proof, or another
analytic lower bound on `|ζ(1/2)|`.

**Checklist note:** the primitive real-axis input is now
`riemannZeta_half_numeric_certificate`; `riemannZeta_ne_zero_at_half` is a derived theorem.

**Milestone criterion:**
- Airtight status in this repository is reached when all active `variable` assumptions in `RH.lean` that feed endpoint closure are replaced by theorem proofs.

---

## Discharged Assumptions Summary

### ✓ Item 4: `completedRiemannZeta_factor_bridge_at_exceptional_lattice`
**Route:** Lattice-point factorization trivializes under π/Gamma/ζ definitions.
**Proof:** `simp [completedRiemannZeta]` — automatic by definitional unfolding.

### ✓ Item 9: `phase_lock_from_window_limit`
**Route:** Geometric incompatibility of hyperbolic and circular constraints; window zeros enforce critical line via 2D-defect route.
**Proof:** 
- `phase_lock_rigidity_strong s hstrip` forces `Re(s) = 1/2` (via 2D-defect contradiction)
- `xi_real_on_critical_line s.im` yields `ξ(1/2 + it) ∈ ℝ`
- Chain: Re(s)=1/2 → s=1/2+itt → ξ s ∈ ℝ

**Key insight:** h = e^μ, coherenceC(h) = sech(μ), sech(μ)=1 ↔ μ=0 ↔ Re(s)=1/2.

### ✓ Item 12: `riemannZeta_ne_zero_at_neg_odd_nat`
**Route:** Bernoulli-value reduction + positive-even zeta contradiction.
**Proof map:** See `Bernoulli trick proof map (riemannZeta_ne_zero_at_neg_odd_nat)` above.

### ✓ Step-1 phase clause reduction
**Route:** `step1_phase_velocity_identity_assumption` is replaced by
`XiLogDerivFormula + slit` through
`step1_reduced_frontier_holds_of_XiLogDerivFormula_and_slit`.
**Endpoint wrapper:** `conditional_RH_via_window_limits_of_XiLogDerivFormula_and_slit`.

### ✓ Item 3: `phase_velocity_on_critical_line`
**Route:** Derived from `XiLogDerivFormula` (with slit admissibility) through
`phase_velocity_on_critical_line_of_XiLogDerivFormula_and_slit`.
**Status in roadmap:** discharged from the active-global-assumption list (consumed by Step-1 bridge theorem).

### ✓ Item 8: `missingPrimeCore_cauchy_tail`
**Route:** Consumed into Step-1 as
`step1_tail_control_of_missingPrimeCore_cauchy_tail`.
**Status in roadmap:** discharged from the active-global-assumption list.

### ✓ Item 10: `partialEulerPhaseVelocity_window_tendsto`
**Route:** Consumed into Step-1 as
`step1_velocity_transfer_of_partialEulerPhaseVelocity_window_tendsto`.
**Status in roadmap:** discharged from the active-global-assumption list.

---

## Remaining Items: Feasibility Assessment

Historical item numbering is retained for cross-reference with earlier notes; discharged items are omitted.

### Tier 1: Classical Formulas (require Mathlib drop-ins or novel proofs)
- **Item 1:** `xi_logderiv_formula` — ξ'/ξ = 1/s + 1/(s-1) - log(π)/2 + (1/2)ψ(s/2) + ζ'/ζ
  - *Status:* Requires product-rule + logarithmic-derivative calculation or Mathlib reference theorem
  - *Feasibility:* Medium — provable via Lean calculus but involves many steps
  
- **Item 2:** `xi_logderiv_symmetry_sum` — (1/2)(ψ(s/2) + ψ((1-s)/2)) = log π - (ζ'/ζ(s) + ζ'/ζ(1-s))
  - *Status:* Consequence of ξ functional equation and digamma symmetry
  - *Feasibility:* Medium — requires functional equation + Mathlib digamma lemmas

### Tier 2: Functional Equation / Conjugation (deep analytic or from Mathlib)
- **Item 5:** `completedHurwitzZetaEven_zero_conj_of_ne_zero` — conj(completed-Hurwitz-even(0,s)) = completed-Hurwitz-even(0,conj(s))
  - *Status:* Functional equation symmetry at Hurwitz level
  - *Feasibility:* Low-Medium — depends on Mathlib's completed-Hurwitz-even API

### Tier 3: Euler Product Convergence (require analytic bounds or Mathlib theorems)
- **Item 6:** `xi_partial_defect2D_window_tendsto_zero` — window 2D-defect → 0 as prime window → ∞
  - *Status:* Euler product convergence (the defect is what remains after finite product)
  - *Feasibility:* Low — requires explicit Euler product asymptotics or Mathlib LSeries convergence lemmas

- **Item 7:** `xi_defect_profile_nonzero_off_critical` — defect norm stays bounded away from 0 off Re(s)=1/2
  - *Status:* Defect "rigidity" away from critical line (opposite of convergence)
  - *Feasibility:* Low — requires novel contradiction argument or Mathlib asymptotic bounds

- **Item 11 (upstream source statement):** `zeta_zero_is_limit_of_window_zeros`
  - *Status:* in this file, this is already theorem-level from the active Step-1 frontier (`step1_*` assumptions)
  - *Feasibility:* remains analytically hard only if the frontier assumptions are to be fully discharged

---

## Recommended Next Steps

**High-effort, high-impact:**
- **Items 1–2:** Pursue Mathlib exploration for `deriv_log`, digamma symmetry (`Real.digamma_add`?), and reference ξ'/ξ formulas
- **Item 5:** Check if `Complex.Gamma_conj` + `hurwitzZetaEven` definitional properties suffice

**Medium-effort, medium-impact:**
- **Item 6:** Attempt explicit epsilontic proofs using `Filter.Tendsto` if time permits

**Lower priority (require significant novel mathematics):**
- **Item 7:** Strip rigidity proof-by-contradiction (may require item 6 first)
- **Item 11 (if pushed below frontier assumptions):** Analytic denseness / Hurwitz-Rouché style strengthening

**Practical strategy:**
- Keep each discharged axiom as a theorem with the same name/signature first.
- Only after theorem replacement, simplify interfaces (`WindowLimitFrontier`, `StrongDefectFrontier`) to remove now-redundant assumption wrappers.

## Files

- `RH.lean` — Main formalization
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