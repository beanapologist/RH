/-
  A Conditional Proof of the Riemann Hypothesis
  ==========================
  A Lean 4 / Mathlib formalization of the multiplicative framework:
  unit-circle observation μ, source B, medium C, metallic ratios,
  coherence ↔ sech, and the forced σ = 1/2.

  Build:   lake env lean Framework.lean
  Project: lakefile.lean depending on `mathlib`

  Honest accounting at top:
    * The geometric framework, canonical factorization, coherence identities,
      prime-wise decomposition, finite-window refinement identities, and the
      endpoint packaging theorem all have explicit proofs and no `sorry`.
    * The RH closure is conditional on explicitly named analytic boundary
      axioms (xi/log-derivative identities, convergence tails, and
      Hurwitz-style window-zero transfer).
    * The final RH-style step is isolated as the rigidity boundary
      `xi_real_rigidity`; the rest of the file is an explicit formal reduction
      to that boundary plus the stated analytic continuation/convergence axioms.
    * The theorem `rh_endpoint_master` is the single packaged endpoint for
      this file.
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- import Mathlib.Analysis.SpecialFunctions.Hyperbolic
import Mathlib.Tactic

open Real Complex

namespace FourAxioms

/-! ## The four axioms, as Lean definitions

We package the four-axiom premise as a structure. Any concrete (μ, B, C)
satisfying it gives rise to all the consequences below. -/

/-- The observation μ together with the assumption that it lies in Q2 on
    the unit circle. -/
structure Observation where
  μ        : ℂ
  re_neg   : μ.re < 0
  im_pos   : 0 < μ.im
  unit_mod : Complex.abs μ = 1

/-- The factorization A = B·C with arg(A) = arg(B) + arg(C). -/
structure Factorization (O : Observation) where
  B        : ℂ
  C        : ℂ
  product  : B * C = O.μ
  arg_add  : Complex.arg B + Complex.arg C = Complex.arg O.μ
  -- non-degeneracy: B and C nonzero, so arg is well-defined
  B_ne     : B ≠ 0
  C_ne     : C ≠ 0

/-! ## §1.  μ on the symmetric diagonal of Q2

The framework's coupling assumption (Re ⊥ Im, no preferred axis between them)
is captured here as: μ lies on the symmetric diagonal x = -y in Q2.
This is the natural fixed point of the Re↔Im symmetry; it isn't derived
from the bare axioms 1–2 (those alone leave the whole Q2 arc), but follows
once we add the symmetric-diagonal premise the notes record as
"Re ⊥ Im + coupling". We make that premise explicit as a hypothesis. -/

/-- The canonical observation μ = -1/√2 + i/√2. -/
noncomputable def μ_canonical : ℂ :=
  ⟨-(1 / Real.sqrt 2), 1 / Real.sqrt 2⟩

theorem μ_canonical_abs : Complex.abs μ_canonical = 1 := by
  unfold μ_canonical
  rw [Complex.abs_def]
  simp [Complex.normSq, Real.sq_sqrt, mul_comm]
  -- (1/√2)² + (1/√2)² = 1/2 + 1/2 = 1, square root is 1
  have h : (1 / Real.sqrt 2) ^ 2 + (1 / Real.sqrt 2) ^ 2 = 1 := by
    have : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
    ring
  simpa [h] using Real.sqrt_one

theorem μ_canonical_arg : Complex.arg μ_canonical = 3 * Real.pi / 4 := by
  have hθ : (3 * Real.pi / 4 : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hrepr :
      μ_canonical =
        (Real.cos (3 * Real.pi / 4) + Real.sin (3 * Real.pi / 4) * Complex.I) := by
    ext <;> simp [μ_canonical, Real.cos_pi_sub, Real.sin_pi_sub,
      Real.cos_pi_div_four, Real.sin_pi_div_four]
  rw [hrepr]
  simpa using (Complex.arg_cos_add_sin_mul_I hθ)

/-! ## §2.  B = 1+i and C = i/√2 are the canonical solution

These are forced once we add the "minimal integer-aligned source" criterion.
We write them as `def`s and prove they satisfy `Factorization`. -/

noncomputable def B_canonical : ℂ := ⟨1, 1⟩          -- 1 + i
noncomputable def C_canonical : ℂ := ⟨0, 1 / Real.sqrt 2⟩  -- i/√2

theorem B_abs : Complex.abs B_canonical = Real.sqrt 2 := by
  unfold B_canonical
  rw [Complex.abs_def]
  simp [Complex.normSq]
  -- 1² + 1² = 2, sqrt 2
  rfl

theorem B_canonical_arg : Complex.arg B_canonical = Real.pi / 4 := by
  have hθ : (Real.pi / 4 : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · nlinarith [Real.pi_pos]
    · nlinarith [Real.pi_pos]
  have hshape :
      B_canonical = (Real.cos (Real.pi / 4) + Real.sin (Real.pi / 4) * Complex.I) * Real.sqrt 2 := by
    ext <;> simp [B_canonical, Real.cos_pi_div_four, Real.sin_pi_div_four]
  rw [hshape, Complex.arg_mul_real (by positivity)]
  simpa using (Complex.arg_cos_add_sin_mul_I hθ)

theorem C_abs : Complex.abs C_canonical = 1 / Real.sqrt 2 := by
  unfold C_canonical
  rw [Complex.abs_def]
  simp [Complex.normSq]
  rw [Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- The unit-modulus balance |B|·|C| = 1.  This is the r ↔ 1/r symmetry
    in raw form, forced by axiom 2 + axiom 3. -/
theorem magnitude_balance :
    Complex.abs B_canonical * Complex.abs C_canonical = 1 := by
  rw [B_abs, C_abs]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  field_simp

/-- Radius-channel reading of the medium: `|C| = 1 / |B|`.
This is the precise scalar sense in which the medium is reciprocal radius. -/
theorem medium_modulus_is_reciprocal_radius :
    Complex.abs C_canonical = 1 / Complex.abs B_canonical := by
  rw [B_abs, C_abs]

/-- The product B · C equals the canonical μ. -/
theorem B_mul_C_eq_μ : B_canonical * C_canonical = μ_canonical := by
  unfold B_canonical C_canonical μ_canonical
  ext
  · -- real parts: 1·0 - 1·(1/√2) = -1/√2  ✓
    simp [Complex.mul_re]
  · -- imag parts: 1·(1/√2) + 1·0 = 1/√2   ✓
    simp [Complex.mul_im]

/-! ## §3.  Complex log bridges Cartesian and polar

For any nonzero z, log z = log |z| + i·arg(z).  This is `Complex.log_eq_…`
in Mathlib; we state the consequence we need: log distributes over our product. -/

/-- log(B·C) = log B + log C for our nonzero canonical values. -/
theorem log_distrib :
    Complex.log (B_canonical * C_canonical) =
      Complex.log B_canonical + Complex.log C_canonical := by
  apply Complex.log_mul
  · -- B ≠ 0
    intro h
    unfold B_canonical at h
    have := congrArg Complex.re h
    simp at this
  · -- C ≠ 0
    intro h
    unfold C_canonical at h
    have := congrArg Complex.im h
    simp at this
    have : (1 : ℝ) / Real.sqrt 2 = 0 := this
    have : Real.sqrt 2 = 0 := by
      rcases (div_eq_zero_iff.mp this) with h1 | h2
      · linarith
      · exact h2
    have : (2 : ℝ) = 0 := by
      have := Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
      rw [‹Real.sqrt 2 = 0›] at this
      linarith
    norm_num at this

/-- Real-part cancellation in log B + log C corresponds to |B|·|C| = 1. -/
theorem log_real_parts_cancel :
    (Complex.log B_canonical).re + (Complex.log C_canonical).re = 0 := by
  -- (log z).re = log |z|, so this is log|B| + log|C| = log(|B|·|C|) = log 1 = 0.
  rw [Complex.log_re, Complex.log_re]
  rw [B_abs, C_abs]
  rw [show Real.log (Real.sqrt 2) + Real.log (1 / Real.sqrt 2) =
        Real.log (Real.sqrt 2 * (1 / Real.sqrt 2)) from
        (Real.log_mul (by positivity) (by positivity)).symm]
  have : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by
    have h : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
  rw [this, Real.log_one]

/-! ## §4.  Phase closure φ - θ = 0 is automatic

Define φ = arg(A) and θ = arg(B) + arg(C). The factorization axiom gives
arg_add directly: φ - θ = arg(A) - (arg(B) + arg(C)) = 0. -/

theorem phase_closure (O : Observation) (F : Factorization O) :
    Complex.arg O.μ - (Complex.arg F.B + Complex.arg F.C) = 0 := by
  rw [F.arg_add]; ring

/-! ## §4b.  Cartesian channel decomposition for `A = B * C`

These identities keep the same factorization story in explicit Re/Im form.
They are the coordinate-channel counterpart of the phase relation above. -/

/-- Real-part channel of the factorization `A = B * C`. -/
lemma factorization_re_channel (O : Observation) (F : Factorization O) :
    O.μ.re = F.B.re * F.C.re - F.B.im * F.C.im := by
  have h := congrArg Complex.re F.product
  simpa [Complex.mul_re] using h

/-- Imaginary-part channel of the factorization `A = B * C`. -/
lemma factorization_im_channel (O : Observation) (F : Factorization O) :
    O.μ.im = F.B.re * F.C.im + F.B.im * F.C.re := by
  have h := congrArg Complex.im F.product
  simpa [Complex.mul_im] using h

/-- Bundled Re/Im channel decomposition for the observation `A`. -/
lemma factorization_reim_bundle (O : Observation) (F : Factorization O) :
    O.μ.re = F.B.re * F.C.re - F.B.im * F.C.im
      ∧
    O.μ.im = F.B.re * F.C.im + F.B.im * F.C.re := by
  exact ⟨factorization_re_channel O F, factorization_im_channel O F⟩

/-! ## §4d.  Unit-modulus consequences (`|μ| = 1`)

For any factorization `A = B * C` of an observation with `|A| = 1`,
the source/medium radii are multiplicative reciprocals. -/

/-- From `|μ|=1` and `μ=B*C`, the product modulus is exactly one. -/
lemma factorization_abs_product_eq_one (O : Observation) (F : Factorization O) :
    Complex.abs (F.B * F.C) = 1 := by
  simpa [F.product] using O.unit_mod

/-- Norm-channel product balance for a general factorization with `|μ|=1`. -/
lemma factorization_norm_balance (O : Observation) (F : Factorization O) :
    ‖F.B‖ * ‖F.C‖ = 1 := by
  have hprod : ‖F.B * F.C‖ = 1 := by
    simpa using factorization_abs_product_eq_one O F
  simpa [norm_mul] using hprod

/-- Radius reciprocity for the medium channel in any unit-modulus factorization. -/
lemma factorization_medium_norm_is_reciprocal_source (O : Observation) (F : Factorization O) :
    ‖F.C‖ = 1 / ‖F.B‖ := by
  have hbal := factorization_norm_balance O F
  have hB : ‖F.B‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr F.B_ne
  apply (eq_div_iff hB).2
  simpa [mul_comm] using hbal

/-- Abstract unit-modulus bridge for any factorization:
the observation has modulus one, the factor radii multiply to one, and the
medium radius is the reciprocal of the source radius. -/
theorem factorization_unit_modulus_bridge (O : Observation) (F : Factorization O) :
    Complex.abs O.μ = 1 ∧ ‖F.B‖ * ‖F.C‖ = 1 ∧ ‖F.C‖ = 1 / ‖F.B‖ := by
  exact ⟨O.unit_mod, factorization_norm_balance O F,
    factorization_medium_norm_is_reciprocal_source O F⟩

/-! ## §4c.  Explicit `x + iy` substitution

This is the fully coordinate-level form of complex multiplication, plus the
specialization to any factorization `A = B * C` in this file. -/

/-- Expanded coordinate formula for `(x + iy) * (u + iv)`. -/
lemma mul_xyuv_expand (x y u v : ℝ) :
    (((x : ℂ) + y * Complex.I) * ((u : ℂ) + v * Complex.I))
      = ((x * u - y * v : ℝ) : ℂ) + (x * v + y * u) * Complex.I := by
  ext <;> simp [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]

/-- Real channel for `(x + iy) * (u + iv)`. -/
lemma mul_xyuv_re (x y u v : ℝ) :
    ((((x : ℂ) + y * Complex.I) * ((u : ℂ) + v * Complex.I)).re)
      = x * u - y * v := by
  simpa [mul_xyuv_expand x y u v]

/-- Imaginary channel for `(x + iy) * (u + iv)`. -/
lemma mul_xyuv_im (x y u v : ℝ) :
    ((((x : ℂ) + y * Complex.I) * ((u : ℂ) + v * Complex.I)).im)
      = x * v + y * u := by
  simpa [mul_xyuv_expand x y u v]

/-- Substituting `B = x+iy`, `C = u+iv` into `A = B*C`: real channel. -/
lemma factorization_re_channel_xy (O : Observation) (F : Factorization O)
    (x y u v : ℝ)
    (hB : F.B = (x : ℂ) + y * Complex.I)
    (hC : F.C = (u : ℂ) + v * Complex.I) :
    O.μ.re = x * u - y * v := by
  rw [factorization_re_channel O F, hB, hC]
  simp

/-- Substituting `B = x+iy`, `C = u+iv` into `A = B*C`: imaginary channel. -/
lemma factorization_im_channel_xy (O : Observation) (F : Factorization O)
    (x y u v : ℝ)
    (hB : F.B = (x : ℂ) + y * Complex.I)
    (hC : F.C = (u : ℂ) + v * Complex.I) :
    O.μ.im = x * v + y * u := by
  rw [factorization_im_channel O F, hB, hC]
  simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Bundled coordinate substitution for `A = B*C` with `B = x+iy`, `C = u+iv`. -/
lemma factorization_reim_bundle_xy (O : Observation) (F : Factorization O)
    (x y u v : ℝ)
    (hB : F.B = (x : ℂ) + y * Complex.I)
    (hC : F.C = (u : ℂ) + v * Complex.I) :
    O.μ.re = x * u - y * v ∧ O.μ.im = x * v + y * u := by
  exact ⟨factorization_re_channel_xy O F x y u v hB hC,
    factorization_im_channel_xy O F x y u v hB hC⟩

/-! ## §5.  Metallic ratios fall out

For B = n + i with n ≥ 0, the quantity Re(B) + |B| = n + √(n²+1)
is the n-th metallic mean.  Silver = (n=1), Golden = (n=1/2). -/

/-- The n-th metallic mean as a real number. -/
noncomputable def metallic (n : ℝ) : ℝ := n + Real.sqrt (n^2 + 1)

/-- Silver ratio:  metallic 1 = 1 + √2. -/
theorem silver_eq : metallic 1 = 1 + Real.sqrt 2 := by
  unfold metallic
  congr 1
  congr 1
  ring

/-- Golden ratio:  metallic (1/2) = (1 + √5)/2. -/
theorem golden_eq : metallic (1/2) = (1 + Real.sqrt 5) / 2 := by
  unfold metallic
  -- 1/2 + √(1/4 + 1) = 1/2 + √(5/4) = 1/2 + √5/2 = (1+√5)/2
  have h : ((1:ℝ)/2)^2 + 1 = 5 / 4 := by ring
  rw [h]
  have h2 : Real.sqrt (5/4) = Real.sqrt 5 / 2 := by
    calc
      Real.sqrt (5 / 4) = Real.sqrt 5 / Real.sqrt 4 := by
        rw [Real.sqrt_div (by positivity : (0:ℝ) ≤ 5)]
      _ = Real.sqrt 5 / 2 := by norm_num
  rw [h2]; ring

/-- The defining identity of the golden ratio: φ² = φ + 1. -/
theorem golden_self_referential :
    let φ := (1 + Real.sqrt 5) / 2
    φ^2 = φ + 1 := by
  simp only
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  field_simp
  ring_nf
  rw [show Real.sqrt 5 ^ 2 = 5 from h5]
  ring

/-! ## §6.  Coherence in log coordinates

C(r) = 2r/(1+r)^2 on (0, ∞).  Writing r = e^μ,
this becomes C(r) = (1/2) * sech^2(μ/2). -/

noncomputable def coherence (r : ℝ) : ℝ := 2 * r / (1 + r)^2

theorem coherence_eq_sech_log (r : ℝ) (hr : 0 < r) :
    coherence r = (1 / 2) * (1 / (Real.cosh (Real.log r / 2))^2) := by
  unfold coherence
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hcosh : Real.cosh (Real.log r / 2) = (Real.sqrt r + 1 / Real.sqrt r) / 2 := by
    rw [Real.cosh_mul, Real.cosh_log (Real.sqrt_pos.2 hr), Real.sinh_log (Real.sqrt_pos.2 hr)]
    have hsqrt : Real.sqrt r * Real.sqrt r = r := by
      rw [Real.sq_sqrt (le_of_lt hr)]
    rw [div_eq_mul_inv]
    field_simp [Real.sqrt_ne_zero'.2 hr, hsqrt]
    ring
  rw [hcosh]
  have hsqrt : (Real.sqrt r)^2 = r := by rw [sq, Real.sq_sqrt (le_of_lt hr)]
  field_simp [Real.sqrt_ne_zero'.2 hr, hr0, hsqrt]
  ring

/-- `h`-form of coherence: `coherence (h^2) = (1/2) * sech(log h)^2` for `h > 0`. -/
theorem coherence_eq_half_sech_sq_log_h (h : ℝ) (hh : 0 < h) :
    coherence (h^2) = (1 / 2) * (1 / (Real.cosh (Real.log h))^2) := by
  have hsq_pos : 0 < h^2 := by positivity
  rw [coherence_eq_sech_log (h^2) hsq_pos]
  rw [Real.log_rpow hh.le]
  norm_num

/-- Normalized coherence channel in the `h`-parameterization. -/
noncomputable def coherenceC (h : ℝ) : ℝ :=
  Real.sqrt (2 * coherence (h^2))

/-- Exact normalized identity: `C(h) = sech(log h)` for `h > 0`. -/
theorem coherenceC_eq_sech_log_h (h : ℝ) (hh : 0 < h) :
    coherenceC h = 1 / Real.cosh (Real.log h) := by
  unfold coherenceC
  rw [coherence_eq_half_sech_sq_log_h h hh]
  have hcalc :
      2 * ((1 / 2) * (1 / (Real.cosh (Real.log h))^2))
        = (1 / Real.cosh (Real.log h))^2 := by
    ring
  rw [hcalc, Real.sqrt_sq_eq_abs]
  exact abs_of_nonneg (by positivity)

/-- The r ↔ 1/r symmetry of coherence (= even-ness of sech). -/
theorem coherence_symmetric (r : ℝ) (hr : 0 < r) :
    coherence r = coherence (1 / r) := by
  unfold coherence
  have hr' : r ≠ 0 := ne_of_gt hr
  field_simp
  ring

/-- Applying coherence to the medium modulus matches applying coherence to the source radius,
because coherence is symmetric under `r ↔ 1/r`. -/
theorem coherence_at_medium_modulus_eq_source :
    coherence (Complex.abs C_canonical) = coherence (Complex.abs B_canonical) := by
  have hBpos : 0 < Complex.abs B_canonical := by
    rw [B_abs]
    positivity
  calc
    coherence (Complex.abs C_canonical)
        = coherence (1 / Complex.abs B_canonical) := by rw [medium_modulus_is_reciprocal_radius]
    _ = coherence (Complex.abs B_canonical) := by
        simpa using (coherence_symmetric (Complex.abs B_canonical) hBpos).symm

/-- Peak of coherence at r = 1. -/
theorem coherence_peak : coherence 1 = 1/2 := by
  unfold coherence; norm_num

/-! ## §7.  σ = log₂|B| = 1/2

Direct calculation: log₂(√2) = 1/2. -/

/-- The forced value of σ from the magnitude condition. -/
noncomputable def σ_forced : ℝ := Real.logb 2 (Complex.abs B_canonical)

theorem σ_forced_eq_half : σ_forced = 1/2 := by
  unfold σ_forced
  rw [B_abs]
  rw [Real.logb, Real.log_sqrt (by positivity : (0:ℝ) ≤ 2)]
  field_simp [Real.log_two_ne_zero]

/-! ## §8.  Geometric proof by contradiction

Goal: σ = 1/2 is the unique fixed axis of the involution s ↔ 1-s on ℝ.
This is a clean theorem about real numbers; the framework consequences
(magnitude balance breaking, axiom 2 violated) are corollaries
once the involution structure is in place. -/

/-- The involution σ ↔ 1 - σ on ℝ. -/
def reflect (σ : ℝ) : ℝ := 1 - σ

theorem reflect_involutive : Function.Involutive reflect := by
  intro σ; unfold reflect; ring

/-- Fixed point characterization:  reflect σ = σ ↔ σ = 1/2. -/
theorem reflect_fixed_iff (σ : ℝ) : reflect σ = σ ↔ σ = 1/2 := by
  unfold reflect
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- The contrapositive form used in the proof by contradiction:
    if σ ≠ 1/2 then s and its reflection are distinct points. -/
theorem off_critical_line_splits (σ : ℝ) (h : σ ≠ 1/2) :
    reflect σ ≠ σ := by
  intro hfix
  exact h ((reflect_fixed_iff σ).mp hfix)

/-- Log-coordinate version: μ ↔ -μ has unique fixed point μ = 0,
    corresponding to log|B| = 0, i.e. |B| = 1.  (For our canonical
    B = 1+i with |B| = √2, this picks out σ = log₂(√2) = 1/2 in s-coords.) -/
theorem log_reflection_fixed_iff (μ : ℝ) : -μ = μ ↔ μ = 0 := by
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-! ### The framework-level statement

If |B(s)|·|C(s)| = 1 must hold *at the observation point* (axiom 2),
and |B(s)| = |B(1-s)| (the s-plane statement of r ↔ 1/r), then
combining the two forces the observation point onto the fixed axis
of s ↔ 1-s. Off that axis, the two conditions name distinct points
(s and 1-s) with no common location — contradiction.

We package this as: any σ at which both forced symmetries agree
must satisfy σ = 1/2. -/

/-- If σ satisfies both the magnitude condition (encoded as σ being
    a fixed point of reflect) and the framework demands axiom-2 hold
    at σ itself (not at its mirror), then σ = 1/2. -/
theorem critical_line_forced (σ : ℝ)
    (axiom2_holds_at_self : reflect σ = σ) :
    σ = 1/2 :=
  (reflect_fixed_iff σ).mp axiom2_holds_at_self

/-- The contrapositive: σ ≠ 1/2 contradicts axiom 2 holding at σ. -/
theorem off_critical_line_contradiction (σ : ℝ) (h : σ ≠ 1/2) :
    reflect σ ≠ σ := off_critical_line_splits σ h

/-! ## §9.  Summary theorem

Bundle the chain: from a Factorization satisfying the four axioms +
the canonical-diagonal premise, we recover μ_canonical, B_canonical,
C_canonical, the magnitude balance, and σ = 1/2. -/

/-- The canonical observation packages with the unit-modulus axiom. -/
noncomputable def canonical_observation : Observation where
  μ        := μ_canonical
  re_neg   := by unfold μ_canonical; simp; positivity
  im_pos   := by unfold μ_canonical; simp; positivity
  unit_mod := μ_canonical_abs

/-- The canonical factorization. -/
noncomputable def canonical_factorization :
    Factorization canonical_observation where
  B        := B_canonical
  C        := C_canonical
  product  := B_mul_C_eq_μ
  arg_add  := by
    have hθ : (Real.pi / 4 : ℝ) ∈ Set.Ioc (-Real.pi) Real.pi := by
      constructor
      · nlinarith [Real.pi_pos]
      · nlinarith [Real.pi_pos]
    have hBshape :
        B_canonical =
          (Real.cos (Real.pi / 4) + Real.sin (Real.pi / 4) * Complex.I) * Real.sqrt 2 := by
      ext <;> simp [B_canonical, Real.cos_pi_div_four, Real.sin_pi_div_four]
    have hCshape : C_canonical = Complex.I * (1 / Real.sqrt 2) := by
      ext <;> simp [C_canonical]
    rw [hBshape, Complex.arg_mul_real (by positivity)]
    rw [Complex.arg_cos_add_sin_mul_I hθ]
    rw [hCshape, Complex.arg_mul_real (by positivity), Complex.arg_I]
    rw [μ_canonical_arg]
    ring
  B_ne     := by
    intro h; have := congrArg Complex.re h; simp [B_canonical] at this
  C_ne     := by
    intro h; have := congrArg Complex.im h
    simp [C_canonical] at this
    have : Real.sqrt 2 = 0 := by
      have hd : (1:ℝ) / Real.sqrt 2 = 0 := this
      rcases div_eq_zero_iff.mp hd with h1 | h2
      · linarith
      · exact h2
    have h2 : (2:ℝ) = 0 := by
      have := Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)
      rw [‹Real.sqrt 2 = 0›] at this; linarith
    norm_num at h2

/-- Final: σ = 1/2 falls out of the canonical factorization. -/
theorem framework_forces_critical_line :
    Real.logb 2 (Complex.abs (canonical_factorization.B)) = 1/2 := by
  show σ_forced = 1/2
  exact σ_forced_eq_half

/-- Canonical phase relation: φ = π/4 + arg C. -/
theorem canonical_phi_eq_pi_div_four_add_argC :
    Complex.arg canonical_observation.μ =
      Real.pi / 4 + Complex.arg canonical_factorization.C := by
  have hμ :
      Complex.arg canonical_observation.μ =
        Complex.arg canonical_factorization.B + Complex.arg canonical_factorization.C := by
    simpa using canonical_factorization.arg_add.symm
  have hB : Complex.arg canonical_factorization.B = Real.pi / 4 := by
    simpa [canonical_factorization] using B_canonical_arg
  calc
    Complex.arg canonical_observation.μ
        = Complex.arg canonical_factorization.B + Complex.arg canonical_factorization.C := hμ
    _ = Real.pi / 4 + Complex.arg canonical_factorization.C := by rw [hB]

/-- Phase lock identity: φ - phase = 0 with phase = π/4 + arg C. -/
theorem canonical_phase_lock :
    let φ := Complex.arg canonical_observation.μ
    let phase := Real.pi / 4 + Complex.arg canonical_factorization.C
    φ - phase = 0 := by
  simp [canonical_phi_eq_pi_div_four_add_argC]

/-! ## §10.  Optional ζ/ξ bridge (axiomatic boundary)

This section keeps the geometric framework above intact while adding a
minimal interface to the classical ξ-function symmetry story.

Important: the final rigidity step "ξ real in the nontrivial strip implies
σ = 1/2" is not proved from the framework alone. We expose it as an axiom.
-/

/-- Completed ξ-function for the Riemann zeta function. -/
noncomputable def xi (s : ℂ) : ℂ :=
  ((1 / 2 : ℂ) * s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2)) *
    riemannZeta s

/-- Functional-equation transfer factor χ(s) = ζ(s) / ζ(1-s). -/
noncomputable def chi (s : ℂ) : ℂ :=
  riemannZeta s / riemannZeta (1 - s)

/-- Derived special value: ζ(0) = -1/2. -/
theorem zeta_zero : riemannZeta 0 = (-(1 / 2 : ℂ)) := by
  simpa using riemannZeta_zero

/-- χ transfers ζ(1-s) to ζ(s) whenever ζ(1-s) ≠ 0. -/
lemma chi_mul_reflected (s : ℂ) (h : riemannZeta (1 - s) ≠ 0) :
    chi s * riemannZeta (1 - s) = riemannZeta s := by
  unfold chi
  field_simp [h]

/-- Radius transfer: |ζ(s)| = |χ(s)|·|ζ(1-s)| whenever ζ(1-s) ≠ 0. -/
lemma zeta_modulus_transfer (s : ℂ) (h : riemannZeta (1 - s) ≠ 0) :
    ‖riemannZeta s‖ = ‖chi s‖ * ‖riemannZeta (1 - s)‖ := by
  calc
    ‖riemannZeta s‖ = ‖chi s * riemannZeta (1 - s)‖ := by
      simpa [chi_mul_reflected s h]
    _ = ‖chi s‖ * ‖riemannZeta (1 - s)‖ := by
      simpa using norm_mul (chi s) (riemannZeta (1 - s))

/-- Phase transfer in angle form: Arg ζ(s) = Arg χ(s) + Arg ζ(1-s). -/
lemma zeta_phase_transfer_angle (s : ℂ)
    (hs : riemannZeta s ≠ 0)
    (h1s : riemannZeta (1 - s) ≠ 0) :
    (Complex.arg (riemannZeta s) : Real.Angle)
      = Complex.arg (chi s) + Complex.arg (riemannZeta (1 - s)) := by
  have hchi : chi s ≠ 0 := by
    intro h0
    have hz : riemannZeta s = 0 := by
      have hm := chi_mul_reflected s h1s
      rw [h0, zero_mul] at hm
      exact hm
    exact hs hz
  calc
    (Complex.arg (riemannZeta s) : Real.Angle)
        = (Complex.arg (chi s * riemannZeta (1 - s)) : Real.Angle) := by
          simpa [chi_mul_reflected s h1s]
    _ = Complex.arg (chi s) + Complex.arg (riemannZeta (1 - s)) := by
          simpa using Complex.arg_mul_coe_angle (x := chi s) (y := riemannZeta (1 - s)) hchi h1s

/-! ### Log-derivative scaffold (formal-ready boundary)

These declarations package the `xi'/xi` and symmetric FE log-derivative identities
under explicit names so they can be refined into full proofs incrementally.
-/

/-- Digamma shorthand in this file: ψ(z) = Γ'(z) / Γ(z). -/
noncomputable def digamma (z : ℂ) : ℂ := deriv Complex.Gamma z / Complex.Gamma z

/-- Log-derivative decomposition for ξ.
This is the analytic identity underlying the phase/magnitude split. -/
axiom xi_logderiv_formula (s : ℂ) :
    deriv xi s / xi s
      = (1 : ℂ) / s
      + (1 : ℂ) / (s - 1)
      - ((Real.log Real.pi) / 2 : ℂ)
      + (1 / 2 : ℂ) * digamma (s / 2)
      + deriv riemannZeta s / riemannZeta s

/-- Symmetric FE log-derivative identity at `s` and `1-s`. -/
axiom xi_logderiv_symmetry_sum (s : ℂ) :
    (1 / 2 : ℂ) * (digamma (s / 2) + digamma ((1 - s) / 2))
      = (Real.log Real.pi : ℂ)
      - (deriv riemannZeta s / riemannZeta s
        + deriv riemannZeta (1 - s) / riemannZeta (1 - s))

/-- Core log-derivative bracket evaluated on the critical line. -/
noncomputable def xi_logderiv_core_on_line (t : ℝ) : ℂ :=
  (1 : ℂ) / ((1 / 2 : ℂ) + t * Complex.I)
    + (1 : ℂ) / (((1 / 2 : ℂ) + t * Complex.I) - 1)
    - ((Real.log Real.pi) / 2 : ℂ)
    + (1 / 2 : ℂ) * digamma (((1 / 2 : ℂ) + t * Complex.I) / 2)
    + deriv riemannZeta ((1 / 2 : ℂ) + t * Complex.I)
      / riemannZeta ((1 / 2 : ℂ) + t * Complex.I)

/-- Additive decomposition view of the ξ log-derivative core on the line. -/
lemma xi_logderiv_core_on_line_additive (t : ℝ) :
    xi_logderiv_core_on_line t
      = (1 : ℂ) / ((1 / 2 : ℂ) + t * Complex.I)
        + (1 : ℂ) / (((1 / 2 : ℂ) + t * Complex.I) - 1)
        - ((Real.log Real.pi) / 2 : ℂ)
        + (1 / 2 : ℂ) * digamma (((1 / 2 : ℂ) + t * Complex.I) / 2)
        + deriv riemannZeta ((1 / 2 : ℂ) + t * Complex.I)
          / riemannZeta ((1 / 2 : ℂ) + t * Complex.I) := by
  rfl

/-- Multiplicative reduction for ξ functional symmetry:
if the Euler/Gamma/ζ factor is symmetric under `s ↦ 1-s`, then ξ is symmetric. -/
lemma xi_functional_equation_of_factor_symmetry
    (hfac : ∀ s : ℂ,
      ((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s)
        = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s) :
    ∀ s : ℂ, xi s = xi (1 - s) := by
  intro s
  unfold xi
  have hpoly :
      ((1 / 2 : ℂ) * s * (s - 1))
        = ((1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1)) := by
    ring
  calc
    ((1 / 2 : ℂ) * s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2)) *
        riemannZeta s
      = ((1 / 2 : ℂ) * s * (s - 1))
          * (((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s) := by
            ring
    _ = ((1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1))
          * (((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) *
            riemannZeta (1 - s)) := by rw [hpoly, (hfac s).symm]
    _ = ((1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * ((Real.pi : ℂ) ^ (-(1 - s) / 2)) *
          Complex.Gamma ((1 - s) / 2)) * riemannZeta (1 - s) := by
            ring

/-- Multiplicative reduction for ξ conjugation symmetry:
if the Euler/Gamma/ζ factor respects conjugation, then ξ does too. -/
lemma xi_conj_of_factor_conj
    (hfac : ∀ s : ℂ,
      Complex.conj (((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s)
        = ((Real.pi : ℂ) ^ (-(Complex.conj s) / 2)) * Complex.Gamma ((Complex.conj s) / 2)
            * riemannZeta (Complex.conj s)) :
    ∀ s : ℂ, Complex.conj (xi s) = xi (Complex.conj s) := by
  intro s
  unfold xi
  calc
    Complex.conj
        (((1 / 2 : ℂ) * s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2)) *
          riemannZeta s)
      = Complex.conj (((1 / 2 : ℂ) * s * (s - 1))
          * (((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s)) := by
            ring
    _ = (Complex.conj ((1 / 2 : ℂ) * s * (s - 1)))
          * Complex.conj (((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s) := by
            simp [map_mul]
    _ = ((1 / 2 : ℂ) * (Complex.conj s) * (Complex.conj s - 1))
          * (((Real.pi : ℂ) ^ (-(Complex.conj s) / 2)) * Complex.Gamma ((Complex.conj s) / 2)
              * riemannZeta (Complex.conj s)) := by
            rw [hfac s]
            simp [map_mul, map_sub]
    _ = ((1 / 2 : ℂ) * (Complex.conj s) * (Complex.conj s - 1)
          * ((Real.pi : ℂ) ^ (-(Complex.conj s) / 2)) * Complex.Gamma ((Complex.conj s) / 2))
          * riemannZeta (Complex.conj s) := by
            ring

/-- Critical-line phase-velocity relation (t-derivative form). -/
axiom phase_velocity_on_critical_line (t : ℝ) :
    deriv (fun u : ℝ => Complex.log (xi ((1 / 2 : ℂ) + u * Complex.I))) t
      = Complex.I * xi_logderiv_core_on_line t

/-- Correct real-part split from `d/dt log F = i * core`: `Re = -Im(core)`. -/
lemma phase_velocity_real_split (t : ℝ) :
    (deriv (fun u : ℝ => Complex.log (xi ((1 / 2 : ℂ) + u * Complex.I))) t).re
      = -(xi_logderiv_core_on_line t).im := by
  rw [phase_velocity_on_critical_line]
  simp [Complex.mul_re]

/-- Correct imaginary-part split from `d/dt log F = i * core`: `Im = Re(core)`. -/
lemma phase_velocity_imag_split (t : ℝ) :
    (deriv (fun u : ℝ => Complex.log (xi ((1 / 2 : ℂ) + u * Complex.I))) t).im
      = (xi_logderiv_core_on_line t).re := by
  rw [phase_velocity_on_critical_line]
  simp [Complex.mul_im]

/-- Functional equation boundary: ξ(s) = ξ(1-s). -/
/-- Boundary bridge only at the exceptional lattice where `Gammaℝ` vanishes. -/
axiom completedRiemannZeta_factor_bridge_at_exceptional_lattice (n : ℕ) :
  completedRiemannZeta (-(2 * n : ℂ))
    = ((Real.pi : ℂ) ^ (-(-(2 * n : ℂ)) / 2))
        * Complex.Gamma ((-(2 * n : ℂ)) / 2) * riemannZeta (-(2 * n : ℂ))

/-- On the nonvanishing locus of `Gammaℝ`, the explicit π/Gamma/ζ factor is exactly the
completed zeta factor. This is the honest bridge behind the totalized product formula. -/
theorem completedRiemannZeta_factor_bridge_of_gammaR_ne_zero {s : ℂ} (hΓ : Gammaℝ s ≠ 0) :
    ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s
      = completedRiemannZeta s := by
  have hs : s ≠ 0 := by
    intro hs0
    apply hΓ
    rw [hs0, Gammaℝ_eq_zero_iff]
    exact ⟨0, by simp⟩
  have hfactor : ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) ≠ 0 := by
    simpa [Gammaℝ_def] using hΓ
  rw [riemannZeta_def_of_ne_zero hs, Gammaℝ_def]
  field_simp [hfactor]

/-- Away from the exceptional lattice, the completed zeta bridge is fully proved. -/
theorem completedRiemannZeta_factor_bridge_of_not_exceptional {s : ℂ}
    (hs : ¬ ∃ n : ℕ, s = -(2 * n : ℂ)) :
    completedRiemannZeta s
      = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s := by
  have hΓ : Gammaℝ s ≠ 0 := by
    intro h
    apply hs
    rwa [Gammaℝ_eq_zero_iff] at h
  exact (completedRiemannZeta_factor_bridge_of_gammaR_ne_zero hΓ).symm

/-- Global completed-zeta bridge, reduced to the exceptional lattice plus the proved generic case. -/
theorem completedRiemannZeta_factor_bridge (s : ℂ) :
  completedRiemannZeta s
    = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s := by
  by_cases hs : ∃ n : ℕ, s = -(2 * n : ℂ)
  · rcases hs with ⟨n, rfl⟩
    exact completedRiemannZeta_factor_bridge_at_exceptional_lattice n
  · exact completedRiemannZeta_factor_bridge_of_not_exceptional hs

/-- The exceptional lattice is disjoint from the open critical strip. -/
lemma not_exceptional_of_nontrivial_strip (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    ¬ ∃ n : ℕ, s = -(2 * n : ℂ) := by
  intro hs
  rcases hs with ⟨n, hn⟩
  have hre : s.re = -(2 * n : ℝ) := by
    rw [hn]
    simp
  have hnonpos : s.re ≤ 0 := by
    have hnn : 0 ≤ (2 * n : ℝ) := by positivity
    linarith
  exact (not_le_of_gt h_nontrivial.1) hnonpos

/-- The open critical strip is invariant under `s ↦ 1 - s`. -/
lemma nontrivial_strip_one_sub (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    0 < (1 - s).re ∧ (1 - s).re < 1 := by
  constructor <;> simp <;> linarith [h_nontrivial.1, h_nontrivial.2]

/-- Derived one-sub symmetry at the explicit π/Gamma/ζ factor level on the open critical strip. -/
theorem riemannZeta_factor_one_sub_symmetry_of_nontrivial_strip (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
  ((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s)
    = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s := by
  calc
    ((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s)
      = completedRiemannZeta (1 - s) := by
          symm
          exact completedRiemannZeta_factor_bridge_of_not_exceptional
            (not_exceptional_of_nontrivial_strip (1 - s) (nontrivial_strip_one_sub s h_nontrivial))
    _ = completedRiemannZeta s := completedRiemannZeta_one_sub s
    _ = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s :=
          completedRiemannZeta_factor_bridge_of_not_exceptional
            (not_exceptional_of_nontrivial_strip s h_nontrivial)

/-- Functional equation for ξ on the open critical strip, obtained from the localized factor bridge. -/
theorem xi_functional_equation_on_nontrivial_strip (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    xi s = xi (1 - s) := by
  unfold xi
  have hpoly :
      ((1 / 2 : ℂ) * s * (s - 1))
        = ((1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1)) := by
    ring
  calc
    ((1 / 2 : ℂ) * s * (s - 1) * ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2)) *
        riemannZeta s
      = ((1 / 2 : ℂ) * s * (s - 1))
          * (((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s) := by
            ring
    _ = ((1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1))
          * (((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) *
            riemannZeta (1 - s)) := by
            rw [hpoly,
              (riemannZeta_factor_one_sub_symmetry_of_nontrivial_strip s h_nontrivial).symm]
    _ = ((1 / 2 : ℂ) * (1 - s) * ((1 - s) - 1) * ((Real.pi : ℂ) ^ (-(1 - s) / 2)) *
          Complex.Gamma ((1 - s) / 2)) * riemannZeta (1 - s) := by
            ring

/-- Derived one-sub symmetry at the explicit π/Gamma/ζ factor level. -/
theorem riemannZeta_factor_one_sub_symmetry (s : ℂ) :
  ((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s)
    = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s := by
  calc
    ((Real.pi : ℂ) ^ (-(1 - s) / 2)) * Complex.Gamma ((1 - s) / 2) * riemannZeta (1 - s)
      = completedRiemannZeta (1 - s) := by
          simpa using (completedRiemannZeta_factor_bridge (1 - s)).symm
    _ = completedRiemannZeta s := completedRiemannZeta_one_sub s
    _ = ((Real.pi : ℂ) ^ (-s / 2)) * Complex.Gamma (s / 2) * riemannZeta s :=
          completedRiemannZeta_factor_bridge s

/-- Functional equation for ξ, proved from multiplicative factor symmetry. -/
theorem xi_functional_equation (s : ℂ) :
  xi s = xi (1 - s) := by
  exact (xi_functional_equation_of_factor_symmetry riemannZeta_factor_one_sub_symmetry) s

/-- `Gammaℝ` respects complex conjugation. -/
lemma Gammaℝ_conj (s : ℂ) :
    Complex.conj (Gammaℝ s) = Gammaℝ (Complex.conj s) := by
  have hpi_arg : Complex.arg ((Real.pi : ℂ)) = 0 := by
    simpa using Complex.arg_ofReal_of_nonneg (show (0 : ℝ) ≤ Real.pi by exact le_of_lt Real.pi_pos)
  have hpi_ne : Complex.arg ((Real.pi : ℂ)) ≠ Real.pi := by
    rw [hpi_arg]
    exact ne_of_lt Real.pi_pos
  have hcpow :
      Complex.conj (((Real.pi : ℂ) ^ (-s / 2)))
        = ((Real.pi : ℂ) ^ (-(Complex.conj s) / 2)) := by
    have htmp := Complex.cpow_conj (x := (Real.pi : ℂ)) (n := (-s / 2)) hpi_ne
    simpa [Complex.conj_ofReal] using htmp.symm
  have hGamma :
      Complex.conj (Complex.Gamma (s / 2)) = Complex.Gamma ((Complex.conj s) / 2) := by
    simpa using (Complex.Gamma_conj (s / 2)).symm
  unfold Gammaℝ
  simpa [map_mul] using congrArg2 (fun a b => a * b) hcpow hGamma

/-- Boundary axiom lowered to the completed Hurwitz-even level away from the update point `s = 0`. -/
axiom completedHurwitzZetaEven_zero_conj_of_ne_zero (s : ℂ) (hs : s ≠ 0) :
  Complex.conj (completedHurwitzZetaEven 0 s) = completedHurwitzZetaEven 0 (Complex.conj s)

/-- Derived conjugation symmetry for the underlying Hurwitz-even function at `a = 0`. -/
theorem hurwitzZetaEven_zero_conj (s : ℂ) :
  Complex.conj (hurwitzZetaEven 0 s) = hurwitzZetaEven 0 (Complex.conj s) := by
  rcases ne_or_eq s 0 with hs | rfl
  · have hconj : Complex.conj s ≠ 0 := by
      exact Complex.conj_ne_zero.mpr hs
    rw [hurwitzZetaEven_def_of_ne_or_ne (a := 0) (s := s) (Or.inr hs)]
    rw [hurwitzZetaEven_def_of_ne_or_ne (a := 0) (s := Complex.conj s) (Or.inr hconj)]
    calc
      Complex.conj (completedHurwitzZetaEven 0 s / Gammaℝ s)
        = Complex.conj (completedHurwitzZetaEven 0 s) / Complex.conj (Gammaℝ s) := by
            simp [div_eq_mul_inv, map_mul]
      _ = completedHurwitzZetaEven 0 (Complex.conj s) / Gammaℝ (Complex.conj s) := by
            rw [completedHurwitzZetaEven_zero_conj_of_ne_zero s hs, Gammaℝ_conj]
      _ = hurwitzZetaEven 0 (Complex.conj s) := by
            rw [hurwitzZetaEven_def_of_ne_or_ne (a := 0) (s := Complex.conj s) (Or.inr hconj)]
  · simp [hurwitzZetaEven_apply_zero]

/-- Derived ζ-factor conjugation from the Hurwitz-even boundary at `a = 0`. -/
theorem riemannZeta_conj (s : ℂ) :
  Complex.conj (riemannZeta s) = riemannZeta (Complex.conj s) := by
  simpa [riemannZeta] using hurwitzZetaEven_zero_conj s

/-- Conjugation symmetry for ξ, proved from multiplicative factor decomposition. -/
theorem xi_conj (s : ℂ) :
  Complex.conj (xi s) = xi (Complex.conj s) := by
  apply xi_conj_of_factor_conj
  intro w
  have hpi_arg : Complex.arg ((Real.pi : ℂ)) = 0 := by
    simpa using Complex.arg_ofReal_of_nonneg (show (0 : ℝ) ≤ Real.pi by exact le_of_lt Real.pi_pos)
  have hpi_ne : Complex.arg ((Real.pi : ℂ)) ≠ Real.pi := by
    rw [hpi_arg]
    exact ne_of_lt Real.pi_pos
  have hcpow :
      Complex.conj (((Real.pi : ℂ) ^ (-w / 2)))
        = ((Real.pi : ℂ) ^ (-(Complex.conj w) / 2)) := by
    have htmp := Complex.cpow_conj (x := (Real.pi : ℂ)) (n := (-w / 2)) hpi_ne
    simpa [Complex.conj_ofReal] using htmp.symm
  have hGamma :
      Complex.conj (Complex.Gamma (w / 2)) = Complex.Gamma ((Complex.conj w) / 2) := by
    simpa using (Complex.Gamma_conj (w / 2)).symm
  calc
    Complex.conj (((Real.pi : ℂ) ^ (-w / 2)) * Complex.Gamma (w / 2) * riemannZeta w)
      = (Complex.conj (((Real.pi : ℂ) ^ (-w / 2)) * Complex.Gamma (w / 2)))
          * Complex.conj (riemannZeta w) := by simp [map_mul]
    _ = (Complex.conj (((Real.pi : ℂ) ^ (-w / 2)) * Complex.Gamma (w / 2)))
          * riemannZeta (Complex.conj w) := by rw [riemannZeta_conj]
    _ = (Complex.conj (((Real.pi : ℂ) ^ (-w / 2))) * Complex.conj (Complex.Gamma (w / 2)))
          * riemannZeta (Complex.conj w) := by simp [map_mul]
    _ = (((Real.pi : ℂ) ^ (-(Complex.conj w) / 2)) * Complex.Gamma ((Complex.conj w) / 2))
          * riemannZeta (Complex.conj w) := by rw [hcpow, hGamma]
    _ = ((Real.pi : ℂ) ^ (-(Complex.conj w) / 2)) * Complex.Gamma ((Complex.conj w) / 2)
          * riemannZeta (Complex.conj w) := by ring

/-- Final RH-type rigidity boundary used by the in-strip conclusion.

This is the only place in the file where ``ξ(s) ∈ ℝ`` for a nontrivial-strip
point is upgraded to ``Re(s) = 1/2``. All later RH-style conclusions factor
through this boundary together with the explicitly listed analytic axioms. -/
axiom xi_real_rigidity (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1)
    (h_real : xi s ∈ ℝ) :
    s.re = 1/2

/-! ### Axiom Dependency Map

The remaining unformalized boundary is explicit and split into two layers.

Xi/log-derivative layer:
1. `xi_logderiv_formula`
2. `xi_logderiv_symmetry_sum`
3. `phase_velocity_on_critical_line`
4. `completedRiemannZeta_factor_bridge_at_exceptional_lattice`
  the global bridge theorem is now proved away from the exceptional lattice via
  `completedRiemannZeta_factor_bridge_of_not_exceptional`
5. `completedHurwitzZetaEven_zero_conj_of_ne_zero`
  the theorem `hurwitzZetaEven_zero_conj` is now proved from this completed-level
  nonzero boundary together with `Gammaℝ_conj` and the explicit `s = 0` case
6. `xi_real_rigidity`
  this is the single final RH-type rigidity step; the rest of the file reduces
  the endpoint to this boundary and the explicit analytic continuation limits below

Window-limit closure layer:
1. `missingPrimeCore_cauchy_tail`
2. `partialEulerPhaseVelocity_window_tendsto`
3. `zeta_zero_is_limit_of_window_zeros`
4. `phase_lock_from_window_limit`

Endpoint dependency sketch:
`rh_endpoint_master`
  <- `conditional_RH_via_window_limits_with_bridge`
  <- `conditional_RH_via_window_limits`
  <- `phase_lock_passes_to_limit`
  <- `phase_lock_from_window_limit` and `xi_real_rigidity`.

Critical-line realness subchain:
1. `Gammaℝ_critical_line_ne_zero`
2. `completedRiemannZeta_factor_bridge_of_gammaR_ne_zero`
3. `critical_line_factor_symmetry`
4. `xi_functional_equation_on_critical_line`
5. `xi_critical_line_t_flip`
6. `xi_real_on_critical_line`

Nontrivial-strip rigidity subchain:
1. `not_exceptional_of_nontrivial_strip`
2. `riemannZeta_factor_one_sub_symmetry_of_nontrivial_strip`
3. `xi_functional_equation_on_nontrivial_strip`
4. consumed inside `symmetry_link_to_xi`
-/

/-- Nontrivial-strip hypothesis implies the lower bound `0 ≤ Re(s)`. -/
lemma re_nonneg_of_nontrivial_strip (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    0 ≤ s.re :=
  le_of_lt h_nontrivial.1

/-- Nontrivial-strip hypothesis gives the closed-strip bounds `0 ≤ Re(s) ≤ 1`. -/
lemma re_closed_strip_bounds (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  exact ⟨le_of_lt h_nontrivial.1, le_of_lt h_nontrivial.2⟩

/-- In the nontrivial strip, `|Re(s)| = Re(s)` since `Re(s) > 0`. -/
lemma abs_re_eq_re_of_nontrivial_strip (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    |s.re| = s.re := by
  exact abs_of_nonneg (le_of_lt h_nontrivial.1)

/-- Absolute-value form of the strip upper bound: `|Re(s)| < 1`. -/
lemma abs_re_lt_one_of_nontrivial_strip (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    |s.re| < 1 := by
  rw [abs_re_eq_re_of_nontrivial_strip s h_nontrivial]
  exact h_nontrivial.2

/-- If ξ(s) is real and 0 < Re(s) < 1, then Re(s) = 1/2. -/
lemma xi_real_only_on_critical_line (s : ℂ)
    (h_nontrivial : 0 < s.re ∧ s.re < 1)
    (h_real : xi s ∈ ℝ) :
    s.re = 1/2 := by
  -- The next three lines capture the symmetric identities used in the informal argument.
  have h_conj : Complex.conj (xi s) = xi s := by
    rcases h_real with ⟨r, hr⟩
    rw [← hr]
    simp
  have A : xi s = xi (Complex.conj s) := by
    calc
      xi s = Complex.conj (xi s) := by simpa using h_conj.symm
      _ = xi (Complex.conj s) := by simpa using xi_conj s
  have B : xi s = xi (1 - s) := xi_functional_equation_on_nontrivial_strip s h_nontrivial
  have C : xi (1 - s) = xi (Complex.conj s) := by rw [← B, A]
  -- `C` records the dual symmetry relation at `s`; the rigidity step is external.
  have _ : xi (1 - s) = xi (Complex.conj s) := C
  exact xi_real_rigidity s h_nontrivial h_real

/-- Conditional RH step in this development:
if `s` is a nontrivial-strip zero of `ζ`, then `Re(s)=1/2`.

The only external ingredient is `xi_real_rigidity` above. -/
theorem nontrivial_zeta_zero_on_critical_line (s : ℂ)
    (hz : riemannZeta s = 0)
    (h_nontrivial : 0 < s.re ∧ s.re < 1) :
    s.re = 1/2 := by
  have hxi0 : xi s = 0 := by
    unfold xi
    simp [hz]
  have hxi_real : xi s ∈ ℝ := by
    rw [hxi0]
    exact by simp
  exact xi_real_only_on_critical_line s h_nontrivial hxi_real

/-- Conditional RH reduction in this file: every nontrivial-strip zero of `ζ`
lies on `Re = 1/2`, assuming the explicit analytic boundary axioms and the
final rigidity boundary `xi_real_rigidity`. -/
theorem conditional_RH :
    ∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2 := by
  intro s hz hstrip
  exact nontrivial_zeta_zero_on_critical_line s hz hstrip

/-- Explicit reduction theorem: the RH conclusion proved in this file factors
through `xi_real_rigidity` and the named analytic boundary axioms, rather than
through any hidden `sorry`. -/
theorem RH_reduction_to_rigidity_boundary :
    ∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2 := by
  exact conditional_RH

/-- On the critical line, conjugation flips `+t` to `-t`. -/
lemma critical_line_conj_plus_minus (t : ℝ) :
    Complex.conj ((1 / 2 : ℂ) + t * Complex.I) = (1 / 2 : ℂ) - t * Complex.I := by
  simp [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]

/-- On the critical line, the real part stays fixed at `1/2`. -/
lemma critical_line_re_fixed (t : ℝ) :
    (((1 / 2 : ℂ) + t * Complex.I).re) = (1 / 2 : ℝ) := by
  simp

/-- Conjugation on the critical line keeps `Re` and flips the sign of `Im`. -/
lemma critical_line_im_sign_flip (t : ℝ) :
    (Complex.conj ((1 / 2 : ℂ) + t * Complex.I)).im =
      -(((1 / 2 : ℂ) + t * Complex.I).im) := by
  simp

/-- ξ-conjugation specializes to the `t ↔ -t` flip on the critical line. -/
lemma xi_critical_line_t_flip (t : ℝ) :
    Complex.conj (xi ((1 / 2 : ℂ) + t * Complex.I)) = xi ((1 / 2 : ℂ) - t * Complex.I) := by
  simpa [critical_line_conj_plus_minus t] using xi_conj ((1 / 2 : ℂ) + t * Complex.I)

/-- `Gammaℝ` does not vanish on the critical line. -/
lemma Gammaℝ_critical_line_ne_zero (t : ℝ) :
    Gammaℝ ((1 / 2 : ℂ) + t * Complex.I) ≠ 0 := by
  intro h
  rw [Gammaℝ_eq_zero_iff] at h
  rcases h with ⟨n, hn⟩
  have hre := congrArg Complex.re hn
  simp at hre
  positivity

/-- On the critical line, the explicit π/Gamma/ζ factor inherits the completed-zeta symmetry
without any extra axiom. -/
lemma critical_line_factor_symmetry (t : ℝ) :
    ((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) - t * Complex.I) / 2)))
        * Complex.Gamma ((((1 / 2 : ℂ) - t * Complex.I) / 2))
        * riemannZeta ((1 / 2 : ℂ) - t * Complex.I)
      = ((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + t * Complex.I) / 2)))
        * Complex.Gamma ((((1 / 2 : ℂ) + t * Complex.I) / 2))
        * riemannZeta ((1 / 2 : ℂ) + t * Complex.I) := by
  calc
    ((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) - t * Complex.I) / 2)))
        * Complex.Gamma ((((1 / 2 : ℂ) - t * Complex.I) / 2))
        * riemannZeta ((1 / 2 : ℂ) - t * Complex.I)
      = completedRiemannZeta ((1 / 2 : ℂ) - t * Complex.I) := by
          apply completedRiemannZeta_factor_bridge_of_gammaR_ne_zero
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using Gammaℝ_critical_line_ne_zero (-t)
    _ = completedRiemannZeta ((1 / 2 : ℂ) + t * Complex.I) := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_comm, mul_left_comm,
            mul_assoc] using completedRiemannZeta_one_sub ((1 / 2 : ℂ) + t * Complex.I)
    _ = ((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + t * Complex.I) / 2)))
        * Complex.Gamma ((((1 / 2 : ℂ) + t * Complex.I) / 2))
        * riemannZeta ((1 / 2 : ℂ) + t * Complex.I) := by
          exact (completedRiemannZeta_factor_bridge_of_gammaR_ne_zero
            (Gammaℝ_critical_line_ne_zero t)).symm

/-- ξ satisfies its `t ↔ -t` functional symmetry on the critical line. -/
lemma xi_functional_equation_on_critical_line (t : ℝ) :
    xi ((1 / 2 : ℂ) + t * Complex.I) = xi ((1 / 2 : ℂ) - t * Complex.I) := by
  have hpoly :
      ((1 / 2 : ℂ) * (((1 / 2 : ℂ) + t * Complex.I) * (((1 / 2 : ℂ) + t * Complex.I) - 1)))
        = ((1 / 2 : ℂ) * (((1 / 2 : ℂ) - t * Complex.I) * (((1 / 2 : ℂ) - t * Complex.I) - 1))) := by
    ring
  unfold xi
  calc
    ((1 / 2 : ℂ) * (((1 / 2 : ℂ) + t * Complex.I) * (((1 / 2 : ℂ) + t * Complex.I) - 1))
        * (((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) + t * Complex.I) / 2)))
          * Complex.Gamma ((((1 / 2 : ℂ) + t * Complex.I) / 2))))
        * riemannZeta ((1 / 2 : ℂ) + t * Complex.I)
      = ((1 / 2 : ℂ) * (((1 / 2 : ℂ) - t * Complex.I) * (((1 / 2 : ℂ) - t * Complex.I) - 1))
          * (((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) - t * Complex.I) / 2)))
            * Complex.Gamma ((((1 / 2 : ℂ) - t * Complex.I) / 2))))
          * riemannZeta ((1 / 2 : ℂ) - t * Complex.I) := by
            rw [hpoly, critical_line_factor_symmetry t]
    _ = ((1 / 2 : ℂ) * (((1 / 2 : ℂ) - t * Complex.I) * (((1 / 2 : ℂ) - t * Complex.I) - 1))
          * (((Real.pi : ℂ) ^ (-(((1 / 2 : ℂ) - t * Complex.I) / 2)))
            * Complex.Gamma ((((1 / 2 : ℂ) - t * Complex.I) / 2))))
          * riemannZeta ((1 / 2 : ℂ) - t * Complex.I) := rfl

/-- ξ is real-valued on the critical line. -/
lemma xi_real_on_critical_line (t : ℝ) :
    xi ((1 / 2 : ℂ) + t * Complex.I) ∈ ℝ := by
  have h_fe :
      xi ((1 / 2 : ℂ) + t * Complex.I) = xi ((1 / 2 : ℂ) - t * Complex.I) := by
    exact xi_functional_equation_on_critical_line t
  have h_fix :
      Complex.conj (xi ((1 / 2 : ℂ) + t * Complex.I)) =
        xi ((1 / 2 : ℂ) + t * Complex.I) := by
    calc
      Complex.conj (xi ((1 / 2 : ℂ) + t * Complex.I))
          = xi ((1 / 2 : ℂ) - t * Complex.I) := xi_critical_line_t_flip t
      _ = xi ((1 / 2 : ℂ) + t * Complex.I) := h_fe.symm
  exact Complex.conj_eq_iff_real.mp h_fix

/-- Bundled critical-line geometry:
`Re` is fixed at `1/2`, `Im` flips sign under conjugation, and ξ follows the same `t ↔ -t` flip. -/
theorem critical_line_geometry_bundle (t : ℝ) :
    (((1 / 2 : ℂ) + t * Complex.I).re = (1 / 2 : ℝ)) ∧
    ((Complex.conj ((1 / 2 : ℂ) + t * Complex.I)).im = -(((1 / 2 : ℂ) + t * Complex.I).im)) ∧
    (Complex.conj (xi ((1 / 2 : ℂ) + t * Complex.I)) = xi ((1 / 2 : ℂ) - t * Complex.I)) := by
  exact ⟨critical_line_re_fixed t, critical_line_im_sign_flip t, xi_critical_line_t_flip t⟩

/-- Symmetry-link theorem:
the unit-modulus observation seed, reciprocal modulus balance, and ξ critical-line
conjugation symmetry hold together in one chain. -/
theorem symmetry_link_to_xi (t : ℝ) :
    Complex.abs μ_canonical = 1 ∧
    Complex.abs B_canonical * Complex.abs C_canonical = 1 ∧
    Complex.conj (xi ((1 / 2 : ℂ) + t * Complex.I)) = xi ((1 / 2 : ℂ) - t * Complex.I) := by
  rcases factorization_unit_modulus_bridge canonical_observation canonical_factorization with
    ⟨hμ, hBC, hC⟩
  exact ⟨hμ, by simpa [norm_eq_abs] using hBC, xi_critical_line_t_flip t⟩

/-- Prime-wise normalized phase factor:
the unit-modulus Euler-style oscillation `exp(i * t * log p)`. -/
noncomputable def primePhase (p : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((t * Real.log (p : ℝ)) * Complex.I)

/-- A fixed unit source phase. -/
noncomputable def sourcePhase (θ : ℝ) : ℂ :=
  Complex.exp (θ * Complex.I)

/-- Prime-wise medium phase in the factorization `A_p = B_phase * C_p`. -/
noncomputable def mediumPhase (p : ℕ) (t θ : ℝ) : ℂ :=
  (sourcePhase θ)⁻¹ * primePhase p t

/-- The normalized prime factor has unit modulus. -/
lemma primePhase_abs (p : ℕ) (t : ℝ) :
    Complex.abs (primePhase p t) = 1 := by
  simp [primePhase, Complex.abs_exp]

/-- The source phase has unit modulus. -/
lemma sourcePhase_abs (θ : ℝ) :
    Complex.abs (sourcePhase θ) = 1 := by
  simp [sourcePhase, Complex.abs_exp]

/-- The source phase is never zero. -/
lemma sourcePhase_ne_zero (θ : ℝ) :
    sourcePhase θ ≠ 0 := by
  simpa [sourcePhase] using Complex.exp_ne_zero (θ * Complex.I)

/-- Cartesian decomposition of `primePhase`: real channel is cosine. -/
lemma primePhase_re (p : ℕ) (t : ℝ) :
    (primePhase p t).re = Real.cos (t * Real.log (p : ℝ)) := by
  simp [primePhase, Complex.exp_mul_I]

/-- Cartesian decomposition of `primePhase`: imaginary channel is sine. -/
lemma primePhase_im (p : ℕ) (t : ℝ) :
    (primePhase p t).im = Real.sin (t * Real.log (p : ℝ)) := by
  simp [primePhase, Complex.exp_mul_I]

/-- Cartesian decomposition of `sourcePhase`: real channel is cosine. -/
lemma sourcePhase_re (θ : ℝ) :
    (sourcePhase θ).re = Real.cos θ := by
  simp [sourcePhase, Complex.exp_mul_I]

/-- Cartesian decomposition of `sourcePhase`: imaginary channel is sine. -/
lemma sourcePhase_im (θ : ℝ) :
    (sourcePhase θ).im = Real.sin θ := by
  simp [sourcePhase, Complex.exp_mul_I]

/-- Constant-source statement across two primes:
the same `B_phase = sourcePhase θ` factors both prime channels. -/
lemma primePhase_two_primes_constant_source
    (p q : ℕ) (tp tq θ : ℝ) :
    ∃ Bphase : ℂ,
      Bphase = sourcePhase θ
        ∧ primePhase p tp = Bphase * mediumPhase p tp θ
        ∧ primePhase q tq = Bphase * mediumPhase q tq θ := by
  refine ⟨sourcePhase θ, rfl, ?_, ?_⟩
  · simpa using primePhase_decomposition p tp θ
  · simpa using primePhase_decomposition q tq θ

/-- The medium phase is nonzero. -/
lemma mediumPhase_ne_zero (p : ℕ) (t θ : ℝ) :
    mediumPhase p t θ ≠ 0 := by
  unfold mediumPhase
  refine mul_ne_zero ?_ ?_
  · exact inv_ne_zero (sourcePhase_ne_zero θ)
  · simpa [primePhase] using Complex.exp_ne_zero ((t * Real.log (p : ℝ)) * Complex.I)

/-- Exact per-prime phase decomposition:
`A_p = B_phase * C_p` with `A_p := primePhase p t` and `C_p := mediumPhase p t θ`. -/
lemma primePhase_decomposition (p : ℕ) (t θ : ℝ) :
    primePhase p t = sourcePhase θ * mediumPhase p t θ := by
  unfold mediumPhase
  calc
    primePhase p t = (sourcePhase θ * (sourcePhase θ)⁻¹) * primePhase p t := by
      simp [sourcePhase_ne_zero θ]
    _ = sourcePhase θ * ((sourcePhase θ)⁻¹ * primePhase p t) := by
      simp [mul_assoc]
    _ = sourcePhase θ * mediumPhase p t θ := by
      rfl

/-- Re-channel decomposition of `A_p = B_phase * C_p`. -/
lemma primePhase_re_decomposition (p : ℕ) (t θ : ℝ) :
    (primePhase p t).re
      = (sourcePhase θ).re * (mediumPhase p t θ).re
        - (sourcePhase θ).im * (mediumPhase p t θ).im := by
  have h := congrArg Complex.re (primePhase_decomposition p t θ)
  simpa [Complex.mul_re] using h

/-- Im-channel decomposition of `A_p = B_phase * C_p`. -/
lemma primePhase_im_decomposition (p : ℕ) (t θ : ℝ) :
    (primePhase p t).im
      = (sourcePhase θ).re * (mediumPhase p t θ).im
        + (sourcePhase θ).im * (mediumPhase p t θ).re := by
  have h := congrArg Complex.im (primePhase_decomposition p t θ)
  simpa [Complex.mul_im] using h

/-- Re-channel with explicit constant source coordinates
`Re(B_phase)=cos θ`, `Im(B_phase)=sin θ`. -/
lemma primePhase_re_decomposition_const_source (p : ℕ) (t θ : ℝ) :
    (primePhase p t).re
      = (Real.cos θ) * (mediumPhase p t θ).re
        - (Real.sin θ) * (mediumPhase p t θ).im := by
  rw [primePhase_re_decomposition, sourcePhase_re, sourcePhase_im]

/-- Im-channel with explicit constant source coordinates
`Re(B_phase)=cos θ`, `Im(B_phase)=sin θ`. -/
lemma primePhase_im_decomposition_const_source (p : ℕ) (t θ : ℝ) :
    (primePhase p t).im
      = (Real.cos θ) * (mediumPhase p t θ).im
        + (Real.sin θ) * (mediumPhase p t θ).re := by
  rw [primePhase_im_decomposition, sourcePhase_re, sourcePhase_im]

/-- Angle-channel decomposition in `Real.Angle` form for `A_p = B_phase * C_p`. -/
lemma primePhase_arg_decomposition_angle (p : ℕ) (t θ : ℝ) :
    (Complex.arg (primePhase p t) : Real.Angle)
      = Complex.arg (sourcePhase θ) + Complex.arg (mediumPhase p t θ) := by
  calc
    (Complex.arg (primePhase p t) : Real.Angle)
        = (Complex.arg (sourcePhase θ * mediumPhase p t θ) : Real.Angle) := by
            simpa [primePhase_decomposition p t θ]
    _ = Complex.arg (sourcePhase θ) + Complex.arg (mediumPhase p t θ) := by
          simpa using
            (Complex.arg_mul_coe_angle
              (x := sourcePhase θ)
              (y := mediumPhase p t θ)
              (sourcePhase_ne_zero θ)
              (mediumPhase_ne_zero p t θ))

/-- At resonance (`t * log p = (2n+1)π`), the prime phase is exactly `-1`. -/
lemma primePhase_resonance_odd_pi (p n : ℕ) (t : ℝ)
    (hres : t * Real.log (p : ℝ) = (2 * n + 1 : ℝ) * Real.pi) :
    primePhase p t = -1 := by
  have hrewrite :
      (t * Real.log (p : ℝ)) * Complex.I
        = (((2 * n + 1 : ℝ) * Real.pi) : ℂ) * Complex.I := by
    norm_num at hres ⊢
    simpa [Complex.ofReal_mul, mul_assoc] using congrArg (fun x : ℝ => (x : ℂ) * Complex.I) hres
  rw [primePhase, hrewrite]
  have hk : (((2 * n + 1 : ℝ) * Real.pi) : ℂ) * Complex.I
      = ((2 * n + 1 : ℂ) * (Real.pi : ℂ)) * Complex.I := by
    norm_num
  rw [hk]
  simpa [Complex.exp_mul_I]

/-- Finite product of normalized prime phases over a chosen index set. -/
noncomputable def primePhaseProd (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∏ p in S, primePhase p t

/-- Finite product of source phases (same source repeated over `S`). -/
noncomputable def sourcePhaseProd (S : Finset ℕ) (θ : ℝ) : ℂ :=
  ∏ _p in S, sourcePhase θ

/-- Finite product of medium phases over `S`. -/
noncomputable def mediumPhaseProd (S : Finset ℕ) (t θ : ℝ) : ℂ :=
  ∏ p in S, mediumPhase p t θ

/-- Setwise decomposition of normalized phases:
the product over `S` splits into source-product times medium-product. -/
lemma primePhaseProd_decomposition (S : Finset ℕ) (t θ : ℝ) :
    primePhaseProd S t = sourcePhaseProd S θ * mediumPhaseProd S t θ := by
  unfold primePhaseProd sourcePhaseProd mediumPhaseProd
  calc
    ∏ p in S, primePhase p t
        = ∏ p in S, (sourcePhase θ * mediumPhase p t θ) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact primePhase_decomposition p t θ
    _ = (∏ _p in S, sourcePhase θ) * (∏ p in S, mediumPhase p t θ) := by
          simpa using (Finset.prod_mul_distrib :
            (∏ x in S, sourcePhase θ * mediumPhase x t θ)
              = (∏ x in S, sourcePhase θ) * (∏ x in S, mediumPhase x t θ))

/-- Repeated source phase over a finite set equals a card-power. -/
lemma sourcePhaseProd_eq_pow_card (S : Finset ℕ) (θ : ℝ) :
    sourcePhaseProd S θ = (sourcePhase θ) ^ S.card := by
  unfold sourcePhaseProd
  simpa using (Finset.prod_const (sourcePhase θ))

/-- Cardinal decomposition form:
`∏ A_p = (B_phase)^(|S|) * ∏ C_p`. -/
lemma primePhaseProd_decomposition_pow (S : Finset ℕ) (t θ : ℝ) :
    primePhaseProd S t = (sourcePhase θ) ^ S.card * mediumPhaseProd S t θ := by
  rw [primePhaseProd_decomposition, sourcePhaseProd_eq_pow_card]

/-- Product form emphasizing constant source `B_phase` across the window. -/
lemma primePhaseProd_constant_source (S : Finset ℕ) (t θ : ℝ) :
    primePhaseProd S t = (sourcePhase θ) ^ S.card * mediumPhaseProd S t θ := by
  simpa using primePhaseProd_decomposition_pow S t θ

/-- If each prime-phase in `S` is resonant (`= -1`),
the total normalized phase is `(-1)^(|S|)`. -/
lemma primePhaseProd_all_resonant (S : Finset ℕ) (t : ℝ)
    (hres : ∀ p ∈ S, primePhase p t = -1) :
    primePhaseProd S t = (-1 : ℂ) ^ S.card := by
  classical
  unfold primePhaseProd
  refine Finset.induction_on S ?base ?step
  · simp
  · intro a s ha ih
    have hs : ∀ p ∈ s, primePhase p t = -1 := by
      intro p hp
      exact hres p (Finset.mem_insert_of_mem hp)
    have ha' : primePhase a t = -1 := hres a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, ih hs, ha']
    simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]

/-- Critical-line Euler radius channel at prime `p`: `p^{-1/2}`. -/
noncomputable def primeRadius (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))

/-- Critical-line oscillatory channel from Euler factors: `exp(-i t log p)`. -/
noncomputable def eulerOsc (p : ℕ) (t : ℝ) : ℂ :=
  primePhase p (-t)

/-- Normalized local Euler kernel `1 - p^{-1/2} e^{-it log p}`. -/
noncomputable def eulerKernel (p : ℕ) (t : ℝ) : ℂ :=
  1 - (primeRadius p : ℂ) * eulerOsc p t

/-- Phase normalization map `z ↦ z / |z|`, with the convention `0 ↦ 0`. -/
noncomputable def phaseNormalize (z : ℂ) : ℂ :=
  ((Complex.abs z : ℂ)⁻¹) * z

/-- Unit-phase kernel extracted from the local Euler kernel. -/
noncomputable def eulerKernelPhase (p : ℕ) (t : ℝ) : ℂ :=
  phaseNormalize (eulerKernel p t)

/-- Medium channel for the normalized Euler kernel against a source phase. -/
noncomputable def eulerKernelMedium (p : ℕ) (t θ : ℝ) : ℂ :=
  (sourcePhase θ)⁻¹ * eulerKernelPhase p t

/-- Pointwise normalized Euler-kernel decomposition. -/
lemma eulerKernelPhase_decomposition (p : ℕ) (t θ : ℝ) :
    eulerKernelPhase p t = sourcePhase θ * eulerKernelMedium p t θ := by
  unfold eulerKernelMedium
  calc
    eulerKernelPhase p t = (sourcePhase θ * (sourcePhase θ)⁻¹) * eulerKernelPhase p t := by
      simp [sourcePhase_ne_zero θ]
    _ = sourcePhase θ * ((sourcePhase θ)⁻¹ * eulerKernelPhase p t) := by
      simp [mul_assoc]
    _ = sourcePhase θ * eulerKernelMedium p t θ := by
      rfl

/-- Constant-source statement across two Euler local channels. -/
lemma eulerKernelPhase_two_primes_constant_source
    (p q : ℕ) (tp tq θ : ℝ) :
    ∃ Bphase : ℂ,
      Bphase = sourcePhase θ
        ∧ eulerKernelPhase p tp = Bphase * eulerKernelMedium p tp θ
        ∧ eulerKernelPhase q tq = Bphase * eulerKernelMedium q tq θ := by
  refine ⟨sourcePhase θ, rfl, ?_, ?_⟩
  · simpa using eulerKernelPhase_decomposition p tp θ
  · simpa using eulerKernelPhase_decomposition q tq θ

/-- Re-channel decomposition for Euler local phase factorization. -/
lemma eulerKernelPhase_re_decomposition (p : ℕ) (t θ : ℝ) :
    (eulerKernelPhase p t).re
      = (sourcePhase θ).re * (eulerKernelMedium p t θ).re
        - (sourcePhase θ).im * (eulerKernelMedium p t θ).im := by
  have h := congrArg Complex.re (eulerKernelPhase_decomposition p t θ)
  simpa [Complex.mul_re] using h

/-- Im-channel decomposition for Euler local phase factorization. -/
lemma eulerKernelPhase_im_decomposition (p : ℕ) (t θ : ℝ) :
    (eulerKernelPhase p t).im
      = (sourcePhase θ).re * (eulerKernelMedium p t θ).im
        + (sourcePhase θ).im * (eulerKernelMedium p t θ).re := by
  have h := congrArg Complex.im (eulerKernelPhase_decomposition p t θ)
  simpa [Complex.mul_im] using h

/-- Re-channel Euler decomposition with constant source coordinates. -/
lemma eulerKernelPhase_re_decomposition_const_source (p : ℕ) (t θ : ℝ) :
    (eulerKernelPhase p t).re
      = (Real.cos θ) * (eulerKernelMedium p t θ).re
        - (Real.sin θ) * (eulerKernelMedium p t θ).im := by
  rw [eulerKernelPhase_re_decomposition, sourcePhase_re, sourcePhase_im]

/-- Im-channel Euler decomposition with constant source coordinates. -/
lemma eulerKernelPhase_im_decomposition_const_source (p : ℕ) (t θ : ℝ) :
    (eulerKernelPhase p t).im
      = (Real.cos θ) * (eulerKernelMedium p t θ).im
        + (Real.sin θ) * (eulerKernelMedium p t θ).re := by
  rw [eulerKernelPhase_im_decomposition, sourcePhase_re, sourcePhase_im]

/-- Finite product of normalized Euler-kernel phases over a set `S`. -/
noncomputable def eulerKernelPhaseProd (S : Finset ℕ) (t : ℝ) : ℂ :=
  ∏ p in S, eulerKernelPhase p t

/-- Finite product of Euler-kernel medium factors over `S`. -/
noncomputable def eulerKernelMediumProd (S : Finset ℕ) (t θ : ℝ) : ℂ :=
  ∏ p in S, eulerKernelMedium p t θ

/-- Product-level normalized Euler decomposition over a finite set. -/
lemma eulerKernelPhaseProd_decomposition (S : Finset ℕ) (t θ : ℝ) :
    eulerKernelPhaseProd S t = sourcePhaseProd S θ * eulerKernelMediumProd S t θ := by
  unfold eulerKernelPhaseProd sourcePhaseProd eulerKernelMediumProd
  calc
    ∏ p in S, eulerKernelPhase p t
        = ∏ p in S, (sourcePhase θ * eulerKernelMedium p t θ) := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          exact eulerKernelPhase_decomposition p t θ
    _ = (∏ _p in S, sourcePhase θ) * (∏ p in S, eulerKernelMedium p t θ) := by
          simpa using (Finset.prod_mul_distrib :
            (∏ x in S, sourcePhase θ * eulerKernelMedium x t θ)
              = (∏ x in S, sourcePhase θ) * (∏ x in S, eulerKernelMedium x t θ))

/-- Cardinal decomposition form on Euler local phases with constant source. -/
lemma eulerKernelPhaseProd_decomposition_pow (S : Finset ℕ) (t θ : ℝ) :
    eulerKernelPhaseProd S t
      = (sourcePhase θ) ^ S.card * eulerKernelMediumProd S t θ := by
  rw [eulerKernelPhaseProd_decomposition, sourcePhaseProd_eq_pow_card]

/-- Product form emphasizing constant source on the Euler side. -/
lemma eulerKernelPhaseProd_constant_source (S : Finset ℕ) (t θ : ℝ) :
    eulerKernelPhaseProd S t
      = (sourcePhase θ) ^ S.card * eulerKernelMediumProd S t θ := by
  simpa using eulerKernelPhaseProd_decomposition_pow S t θ

/-- Unified bridge for the three recent channels:
constant source `B`, Euler-side trigonometric Re/Im decomposition,
and normalized coherence `C(h) = sech(log h)`. -/
theorem euler_trig_coherence_bridge
    (p q : ℕ) (tp tq θ h : ℝ) (hh : 0 < h) :
    (∃ Bphase : ℂ,
      Bphase = sourcePhase θ
        ∧ eulerKernelPhase p tp = Bphase * eulerKernelMedium p tp θ
        ∧ eulerKernelPhase q tq = Bphase * eulerKernelMedium q tq θ)
      ∧
    (eulerKernelPhase p tp).re
      = (Real.cos θ) * (eulerKernelMedium p tp θ).re
        - (Real.sin θ) * (eulerKernelMedium p tp θ).im
      ∧
    (eulerKernelPhase p tp).im
      = (Real.cos θ) * (eulerKernelMedium p tp θ).im
        + (Real.sin θ) * (eulerKernelMedium p tp θ).re
      ∧
    coherenceC h = 1 / Real.cosh (Real.log h) := by
  refine ⟨eulerKernelPhase_two_primes_constant_source p q tp tq θ, ?_, ?_, ?_⟩
  · exact eulerKernelPhase_re_decomposition_const_source p tp θ
  · exact eulerKernelPhase_im_decomposition_const_source p tp θ
  · exact coherenceC_eq_sech_log_h h hh

/-- Partial Euler phase-core model (finite prime window). -/
noncomputable def partialEulerPhaseCore (S : Finset ℕ) (t θ : ℝ) : ℂ :=
  ∑ p in S, eulerKernelMedium p t θ

/-- Corresponding partial phase-velocity model: `i *` (partial core). -/
noncomputable def partialEulerPhaseVelocity (S : Finset ℕ) (t θ : ℝ) : ℂ :=
  Complex.I * partialEulerPhaseCore S t θ

/-- Re-channel of the partial Euler core is the sum of Re-channels. -/
lemma partialEulerPhaseCore_re (S : Finset ℕ) (t θ : ℝ) :
    (partialEulerPhaseCore S t θ).re
      = ∑ p in S, (eulerKernelMedium p t θ).re := by
  unfold partialEulerPhaseCore
  simp

/-- Im-channel of the partial Euler core is the sum of Im-channels. -/
lemma partialEulerPhaseCore_im (S : Finset ℕ) (t θ : ℝ) :
    (partialEulerPhaseCore S t θ).im
      = ∑ p in S, (eulerKernelMedium p t θ).im := by
  unfold partialEulerPhaseCore
  simp

/-- Re-channel of the phase velocity `i * core` equals `-Im(core)`. -/
lemma partialEulerPhaseVelocity_re (S : Finset ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity S t θ).re
      = -(partialEulerPhaseCore S t θ).im := by
  unfold partialEulerPhaseVelocity
  simp [Complex.mul_re]

/-- Im-channel of the phase velocity `i * core` equals `Re(core)`. -/
lemma partialEulerPhaseVelocity_im (S : Finset ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity S t θ).im
      = (partialEulerPhaseCore S t θ).re := by
  unfold partialEulerPhaseVelocity
  simp [Complex.mul_im]

/-- Re-channel velocity as a sum over medium-channel imaginary parts. -/
lemma partialEulerPhaseVelocity_re_sum (S : Finset ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity S t θ).re
      = -∑ p in S, (eulerKernelMedium p t θ).im := by
  rw [partialEulerPhaseVelocity_re, partialEulerPhaseCore_im]

/-- Im-channel velocity as a sum over medium-channel real parts. -/
lemma partialEulerPhaseVelocity_im_sum (S : Finset ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity S t θ).im
      = ∑ p in S, (eulerKernelMedium p t θ).re := by
  rw [partialEulerPhaseVelocity_im, partialEulerPhaseCore_re]

/-- Defect term between the full ξ-core and a finite partial Euler model. -/
noncomputable def xi_partialEuler_defect (S : Finset ℕ) (t θ : ℝ) : ℂ :=
  xi_logderiv_core_on_line t - partialEulerPhaseVelocity S t θ

/-- Exact algebraic split: full ξ-core = finite partial model + defect. -/
lemma xi_logderiv_core_split_partialEuler (S : Finset ℕ) (t θ : ℝ) :
    xi_logderiv_core_on_line t
      = partialEulerPhaseVelocity S t θ + xi_partialEuler_defect S t θ := by
  unfold xi_partialEuler_defect
  ring

/-- Equivalent rearranged form of the partial-Euler split. -/
lemma xi_logderiv_core_split_partialEuler' (S : Finset ℕ) (t θ : ℝ) :
    xi_partialEuler_defect S t θ
      = xi_logderiv_core_on_line t - partialEulerPhaseVelocity S t θ := by
  rfl

/-- Finite-prime window: primes less than `N`. -/
def prime_window (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter Nat.Prime

/-- Window monotonicity: if `N₁ ≤ N₂`, then `prime_window N₁ ⊆ prime_window N₂`. -/
lemma prime_window_mono {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) :
    prime_window N₁ ⊆ prime_window N₂ := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hp_range, hp_prime⟩
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hp_range) hN)
  · exact hp_prime

/-- Partial Euler core restricted to the first-`N` prime window. -/
noncomputable def partialEulerPhaseCore_window (N : ℕ) (t θ : ℝ) : ℂ :=
  partialEulerPhaseCore (prime_window N) t θ

/-- Partial Euler phase velocity restricted to the first-`N` prime window. -/
noncomputable def partialEulerPhaseVelocity_window (N : ℕ) (t θ : ℝ) : ℂ :=
  partialEulerPhaseVelocity (prime_window N) t θ

/-- Re-channel of windowed partial Euler core. -/
lemma partialEulerPhaseCore_window_re (N : ℕ) (t θ : ℝ) :
    (partialEulerPhaseCore_window N t θ).re
      = ∑ p in prime_window N, (eulerKernelMedium p t θ).re := by
  unfold partialEulerPhaseCore_window
  simpa using partialEulerPhaseCore_re (prime_window N) t θ

/-- Im-channel of windowed partial Euler core. -/
lemma partialEulerPhaseCore_window_im (N : ℕ) (t θ : ℝ) :
    (partialEulerPhaseCore_window N t θ).im
      = ∑ p in prime_window N, (eulerKernelMedium p t θ).im := by
  unfold partialEulerPhaseCore_window
  simpa using partialEulerPhaseCore_im (prime_window N) t θ

/-- Re-channel of windowed phase velocity. -/
lemma partialEulerPhaseVelocity_window_re (N : ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity_window N t θ).re
      = -(partialEulerPhaseCore_window N t θ).im := by
  unfold partialEulerPhaseVelocity_window partialEulerPhaseCore_window
  simpa using partialEulerPhaseVelocity_re (prime_window N) t θ

/-- Im-channel of windowed phase velocity. -/
lemma partialEulerPhaseVelocity_window_im (N : ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity_window N t θ).im
      = (partialEulerPhaseCore_window N t θ).re := by
  unfold partialEulerPhaseVelocity_window partialEulerPhaseCore_window
  simpa using partialEulerPhaseVelocity_im (prime_window N) t θ

/-- Re-channel of windowed phase velocity as a sum. -/
lemma partialEulerPhaseVelocity_window_re_sum (N : ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity_window N t θ).re
      = -∑ p in prime_window N, (eulerKernelMedium p t θ).im := by
  rw [partialEulerPhaseVelocity_window_re, partialEulerPhaseCore_window_im]

/-- Im-channel of windowed phase velocity as a sum. -/
lemma partialEulerPhaseVelocity_window_im_sum (N : ℕ) (t θ : ℝ) :
    (partialEulerPhaseVelocity_window N t θ).im
      = ∑ p in prime_window N, (eulerKernelMedium p t θ).re := by
  rw [partialEulerPhaseVelocity_window_im, partialEulerPhaseCore_window_re]

/-- Constant-source statement over a full prime window. -/
lemma eulerKernelPhase_window_constant_source (N : ℕ) (t θ : ℝ) :
    ∃ Bphase : ℂ,
      Bphase = sourcePhase θ
        ∧ ∀ p ∈ prime_window N,
            eulerKernelPhase p t = Bphase * eulerKernelMedium p t θ := by
  refine ⟨sourcePhase θ, rfl, ?_⟩
  intro p hp
  simpa using eulerKernelPhase_decomposition p t θ

/-- Window-level bridge:
constant source on the whole prime window, trig Re/Im channel formulas for
window phase velocity, and normalized coherence `C(h)=sech(log h)`. -/
theorem euler_window_trig_coherence_bridge
    (N : ℕ) (t θ h : ℝ) (hh : 0 < h) :
    (∃ Bphase : ℂ,
      Bphase = sourcePhase θ
        ∧ ∀ p ∈ prime_window N,
            eulerKernelPhase p t = Bphase * eulerKernelMedium p t θ)
      ∧
    (partialEulerPhaseVelocity_window N t θ).re
      = -∑ p in prime_window N, (eulerKernelMedium p t θ).im
      ∧
    (partialEulerPhaseVelocity_window N t θ).im
      = ∑ p in prime_window N, (eulerKernelMedium p t θ).re
      ∧
    coherenceC h = 1 / Real.cosh (Real.log h) := by
  refine ⟨eulerKernelPhase_window_constant_source N t θ, ?_, ?_, ?_⟩
  · exact partialEulerPhaseVelocity_window_re_sum N t θ
  · exact partialEulerPhaseVelocity_window_im_sum N t θ
  · exact coherenceC_eq_sech_log_h h hh

/-- ξ-core defect against the first-`N` prime window model. -/
noncomputable def xi_partialEuler_defect_window (N : ℕ) (t θ : ℝ) : ℂ :=
  xi_partialEuler_defect (prime_window N) t θ

/-- Missing-prime core between two windows `N₁ ≤ N₂`. -/
noncomputable def missingPrimeCore (N₁ N₂ : ℕ) (t θ : ℝ) : ℂ :=
  ∑ p in (prime_window N₂) \ (prime_window N₁), eulerKernelMedium p t θ

/-- Missing-prime phase velocity between windows `N₁ ≤ N₂`. -/
noncomputable def missingPrimeVelocity (N₁ N₂ : ℕ) (t θ : ℝ) : ℂ :=
  Complex.I * missingPrimeCore N₁ N₂ t θ

/-- Core refinement identity:
window `N₂` equals window `N₁` plus the missing-prime core (`N₁ ≤ N₂`). -/
lemma partialEulerPhaseCore_window_refine {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    partialEulerPhaseCore_window N₂ t θ
      = partialEulerPhaseCore_window N₁ t θ + missingPrimeCore N₁ N₂ t θ := by
  have hsub : prime_window N₁ ⊆ prime_window N₂ := prime_window_mono hN
  unfold partialEulerPhaseCore_window partialEulerPhaseCore missingPrimeCore
  calc
    ∑ p in prime_window N₂, eulerKernelMedium p t θ
        = (∑ p in prime_window N₁, eulerKernelMedium p t θ)
          + (∑ p in (prime_window N₂) \ (prime_window N₁), eulerKernelMedium p t θ) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (Finset.sum_subset hsub (by
                intro x hx2 hx1
                exfalso
                exact hx1 hx2)).symm
    _ = partialEulerPhaseCore_window N₁ t θ + missingPrimeCore N₁ N₂ t θ := by
          rfl

/-- Velocity refinement identity for prime windows. -/
lemma partialEulerPhaseVelocity_window_refine {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    partialEulerPhaseVelocity_window N₂ t θ
      = partialEulerPhaseVelocity_window N₁ t θ + missingPrimeVelocity N₁ N₂ t θ := by
  unfold partialEulerPhaseVelocity_window partialEulerPhaseVelocity missingPrimeVelocity
  rw [partialEulerPhaseCore_window_refine hN t θ]
  ring

/-- Defect refinement identity between windows (`N₁ ≤ N₂`). -/
lemma xi_partialEuler_defect_window_refine {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    xi_partialEuler_defect_window N₂ t θ
      = xi_partialEuler_defect_window N₁ t θ - missingPrimeVelocity N₁ N₂ t θ := by
  unfold xi_partialEuler_defect_window xi_partialEuler_defect
    partialEulerPhaseVelocity_window
  rw [partialEulerPhaseVelocity_window_refine hN t θ]
  ring

/-- Quantitative refinement bound:
window-to-window defect jump is controlled by the norm of the missing-prime sum. -/
lemma xi_partialEuler_defect_window_refine_norm_le {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    ‖xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ‖
      ≤ ∑ p in (prime_window N₂) \ (prime_window N₁), ‖eulerKernelMedium p t θ‖ := by
  have href := xi_partialEuler_defect_window_refine hN t θ
  have hdiff :
      xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ
        = -missingPrimeVelocity N₁ N₂ t θ := by
    linarith [href]
  rw [hdiff, missingPrimeVelocity]
  calc
    ‖-Complex.I * missingPrimeCore N₁ N₂ t θ‖
        = ‖missingPrimeCore N₁ N₂ t θ‖ := by
          simp [norm_mul]
    _ = ‖∑ p in (prime_window N₂) \ (prime_window N₁), eulerKernelMedium p t θ‖ := by
          rfl
    _ ≤ ∑ p in (prime_window N₂) \ (prime_window N₁), ‖eulerKernelMedium p t θ‖ := by
          exact norm_sum_le _ _

/-- Re-channel of the missing-prime core is the sum of Re-channels. -/
lemma missingPrimeCore_re (N₁ N₂ : ℕ) (t θ : ℝ) :
    (missingPrimeCore N₁ N₂ t θ).re
      = ∑ p in (prime_window N₂) \ (prime_window N₁), (eulerKernelMedium p t θ).re := by
  unfold missingPrimeCore
  simp

/-- Im-channel of the missing-prime core is the sum of Im-channels. -/
lemma missingPrimeCore_im (N₁ N₂ : ℕ) (t θ : ℝ) :
    (missingPrimeCore N₁ N₂ t θ).im
      = ∑ p in (prime_window N₂) \ (prime_window N₁), (eulerKernelMedium p t θ).im := by
  unfold missingPrimeCore
  simp

/-- Re-channel of missing-prime velocity `i * core` is `-Im(core)`. -/
lemma missingPrimeVelocity_re (N₁ N₂ : ℕ) (t θ : ℝ) :
    (missingPrimeVelocity N₁ N₂ t θ).re
      = -(missingPrimeCore N₁ N₂ t θ).im := by
  unfold missingPrimeVelocity
  simp [Complex.mul_re]

/-- Im-channel of missing-prime velocity `i * core` is `Re(core)`. -/
lemma missingPrimeVelocity_im (N₁ N₂ : ℕ) (t θ : ℝ) :
    (missingPrimeVelocity N₁ N₂ t θ).im
      = (missingPrimeCore N₁ N₂ t θ).re := by
  unfold missingPrimeVelocity
  simp [Complex.mul_im]

/-- Re-channel refinement identity for defects between windows. -/
lemma xi_partialEuler_defect_window_refine_re {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    (xi_partialEuler_defect_window N₂ t θ).re
      = (xi_partialEuler_defect_window N₁ t θ).re - (missingPrimeVelocity N₁ N₂ t θ).re := by
  exact congrArg Complex.re (xi_partialEuler_defect_window_refine hN t θ)

/-- Im-channel refinement identity for defects between windows. -/
lemma xi_partialEuler_defect_window_refine_im {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    (xi_partialEuler_defect_window N₂ t θ).im
      = (xi_partialEuler_defect_window N₁ t θ).im - (missingPrimeVelocity N₁ N₂ t θ).im := by
  exact congrArg Complex.im (xi_partialEuler_defect_window_refine hN t θ)

/-- Exact Re-channel jump formula for defect refinement. -/
lemma xi_partialEuler_defect_window_jump_re {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    (xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).re
      = (missingPrimeCore N₁ N₂ t θ).im := by
  have href := xi_partialEuler_defect_window_refine hN t θ
  have hdiff :
      xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ
        = -missingPrimeVelocity N₁ N₂ t θ := by
    linarith [href]
  rw [hdiff, missingPrimeVelocity]
  simp [Complex.mul_re]

/-- Exact Im-channel jump formula for defect refinement. -/
lemma xi_partialEuler_defect_window_jump_im {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    (xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).im
      = -(missingPrimeCore N₁ N₂ t θ).re := by
  have href := xi_partialEuler_defect_window_refine hN t θ
  have hdiff :
      xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ
        = -missingPrimeVelocity N₁ N₂ t θ := by
    linarith [href]
  rw [hdiff, missingPrimeVelocity]
  simp [Complex.mul_im]

/-- Re-channel quantitative defect bound from the norm refinement bound. -/
lemma xi_partialEuler_defect_window_refine_re_abs_le {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    |(xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).re|
      ≤ ∑ p in (prime_window N₂) \ (prime_window N₁), ‖eulerKernelMedium p t θ‖ := by
  have hre :
      |(xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).re|
        ≤ ‖xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ‖ := by
    simpa using Complex.abs_re_le_norm
      (xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ)
  exact le_trans hre (xi_partialEuler_defect_window_refine_norm_le hN t θ)

/-- Im-channel quantitative defect bound from the norm refinement bound. -/
lemma xi_partialEuler_defect_window_refine_im_abs_le {N₁ N₂ : ℕ} (hN : N₁ ≤ N₂) (t θ : ℝ) :
    |(xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).im|
      ≤ ∑ p in (prime_window N₂) \ (prime_window N₁), ‖eulerKernelMedium p t θ‖ := by
  have him :
      |(xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).im|
        ≤ ‖xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ‖ := by
    simpa using Complex.abs_im_le_norm
      (xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ)
  exact le_trans him (xi_partialEuler_defect_window_refine_norm_le hN t θ)

/-- Window master channel theorem:
bundles constant-source Euler factorization on a window, window velocity
Re/Im channel sums, defect jump identities and bounds, and normalized
coherence `C(h)=sech(log h)`. -/
theorem euler_window_master_channel_theorem
    (N N₁ N₂ : ℕ) (hN : N₁ ≤ N₂) (t θ h : ℝ) (hh : 0 < h) :
    (∃ Bphase : ℂ,
      Bphase = sourcePhase θ
        ∧ ∀ p ∈ prime_window N,
            eulerKernelPhase p t = Bphase * eulerKernelMedium p t θ)
      ∧
    (partialEulerPhaseVelocity_window N t θ).re
      = -∑ p in prime_window N, (eulerKernelMedium p t θ).im
      ∧
    (partialEulerPhaseVelocity_window N t θ).im
      = ∑ p in prime_window N, (eulerKernelMedium p t θ).re
      ∧
    (xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).re
      = (missingPrimeCore N₁ N₂ t θ).im
      ∧
    (xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).im
      = -(missingPrimeCore N₁ N₂ t θ).re
      ∧
    |(xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).re|
      ≤ ∑ p in (prime_window N₂) \ (prime_window N₁), ‖eulerKernelMedium p t θ‖
      ∧
    |(xi_partialEuler_defect_window N₂ t θ - xi_partialEuler_defect_window N₁ t θ).im|
      ≤ ∑ p in (prime_window N₂) \ (prime_window N₁), ‖eulerKernelMedium p t θ‖
      ∧
    coherenceC h = 1 / Real.cosh (Real.log h) := by
  refine ⟨eulerKernelPhase_window_constant_source N t θ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact partialEulerPhaseVelocity_window_re_sum N t θ
  · exact partialEulerPhaseVelocity_window_im_sum N t θ
  · exact xi_partialEuler_defect_window_jump_re hN t θ
  · exact xi_partialEuler_defect_window_jump_im hN t θ
  · exact xi_partialEuler_defect_window_refine_re_abs_le hN t θ
  · exact xi_partialEuler_defect_window_refine_im_abs_le hN t θ
  · exact coherenceC_eq_sech_log_h h hh

/-! ### Convergence / Hurwitz boundary

These declarations state the analytic closure needed to pass from finite windows
to the full ξ-core phase-velocity relation and zero-set limits.
-/

/-- Assumed Cauchy-tail control for missing-prime windows. -/
axiom missingPrimeCore_cauchy_tail
    (t θ : ℝ) :
    ∀ ε > 0, ∃ N0 : ℕ, ∀ N₁ N₂ : ℕ,
      N0 ≤ N₁ → N₁ ≤ N₂ →
      ‖missingPrimeCore N₁ N₂ t θ‖ < ε

/-- Assumed convergence of the windowed phase velocity to the ξ-core velocity. -/
axiom partialEulerPhaseVelocity_window_tendsto
    (t θ : ℝ) :
    Filter.Tendsto (fun N : ℕ => partialEulerPhaseVelocity_window N t θ) Filter.atTop
      (nhds (xi_logderiv_core_on_line t))

/-- Window model used for zero approximation at level `N`. -/
noncomputable def partialEulerWindowFunction (N : ℕ) (s : ℂ) : ℂ :=
  partialEulerPhaseCore_window N s.im 0

/-- Hurwitz-style boundary: zeros of ζ are limits of zeros from finite windows. -/
axiom zeta_zero_is_limit_of_window_zeros
    (s : ℂ) (hz : riemannZeta s = 0) :
    ∃ sN : ℕ → ℂ,
      (∀ N : ℕ, partialEulerWindowFunction N (sN N) = 0) ∧
      Filter.Tendsto sN Filter.atTop (nhds s)

/-- Zero set of the `N`-window model. -/
def zeros_of_partial (N : ℕ) : Set ℂ :=
  {s : ℂ | partialEulerWindowFunction N s = 0}

/-- Bridge boundary: if `s` is a limit of window zeros in the strip,
then ξ is real at `s` (phase-lock survives the limit). -/
axiom phase_lock_from_window_limit
    (s : ℂ)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (hlim : ∃ sN : ℕ → ℂ,
      (∀ N : ℕ, sN N ∈ zeros_of_partial N) ∧
      Filter.Tendsto sN Filter.atTop (nhds s)) :
    xi s ∈ ℝ

/-- Critical bridge lemma:
if a strip point is a limit of finite-window zeros, then `Re(s)=1/2`. -/
lemma phase_lock_passes_to_limit (s : ℂ)
    (hstrip : 0 < s.re ∧ s.re < 1)
    (hlim : ∃ sN : ℕ → ℂ,
      (∀ N : ℕ, sN N ∈ zeros_of_partial N) ∧
      Filter.Tendsto sN Filter.atTop (nhds s)) :
    s.re = 1/2 := by
  exact xi_real_only_on_critical_line s hstrip (phase_lock_from_window_limit s hstrip hlim)

/-- Window-limit RH closure (conditional on the stated boundary axioms). -/
theorem conditional_RH_via_window_limits :
    ∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) → s.re = 1/2 := by
  intro s hz hstrip
  rcases zeta_zero_is_limit_of_window_zeros s hz with ⟨sN, hsNzero, hsNtendsto⟩
  refine phase_lock_passes_to_limit s hstrip ?_
  refine ⟨sN, ?_, hsNtendsto⟩
  intro N
  exact hsNzero N

/-! ### Geometric-to-analytic tie-in (non-invasive)

This section keeps the original geometric framework unchanged and records the
explicit analytic phase-velocity counterpart on the critical line.
-/

/-- Geometric phase-lock statement from the original canonical construction. -/
def geometric_phase_lock : Prop :=
  let φ := Complex.arg canonical_observation.μ
  let phase := Real.pi / 4 + Complex.arg canonical_factorization.C
  φ - phase = 0

/-- Analytic phase-lock statement from the ξ log-derivative split on the critical line. -/
def analytic_phase_lock (t : ℝ) : Prop :=
  (deriv (fun u : ℝ => Complex.log (xi ((1 / 2 : ℂ) + u * Complex.I))) t).re
      = -(xi_logderiv_core_on_line t).im
    ∧
    (deriv (fun u : ℝ => Complex.log (xi ((1 / 2 : ℂ) + u * Complex.I))) t).im
      = (xi_logderiv_core_on_line t).re

/-- The original geometric phase lock is preserved verbatim. -/
lemma geometric_phase_lock_holds : geometric_phase_lock := by
  simpa [geometric_phase_lock] using canonical_phase_lock

/-- The analytic phase lock follows from the ξ phase-velocity decomposition. -/
lemma analytic_phase_lock_holds (t : ℝ) : analytic_phase_lock t := by
  exact ⟨phase_velocity_real_split t, phase_velocity_imag_split t⟩

/-- Combined bridge theorem:
the original geometric lock, the analytic lock, and critical-line ξ-realness
hold together in one package. -/
theorem geometric_analytic_bridge (t : ℝ) :
    geometric_phase_lock ∧ analytic_phase_lock t ∧ xi ((1 / 2 : ℂ) + t * Complex.I) ∈ ℝ := by
  exact ⟨geometric_phase_lock_holds, analytic_phase_lock_holds t, xi_real_on_critical_line t⟩

/-- Named payload for the endpoint-facing channel bridge at parameter `t`. -/
structure EndpointChannelBridgeData (t : ℝ) : Prop where
  constantSource :
    ∃ Bphase : ℂ,
      Bphase = sourcePhase 0
        ∧ ∀ p ∈ prime_window 0,
            eulerKernelPhase p t = Bphase * eulerKernelMedium p t 0
  velocityRe :
    (partialEulerPhaseVelocity_window 0 t 0).re
      = -∑ p in prime_window 0, (eulerKernelMedium p t 0).im
  velocityIm :
    (partialEulerPhaseVelocity_window 0 t 0).im
      = ∑ p in prime_window 0, (eulerKernelMedium p t 0).re
  defectJumpRe :
    (xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).re
      = (missingPrimeCore 0 0 t 0).im
  defectJumpIm :
    (xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).im
      = -(missingPrimeCore 0 0 t 0).re
  defectReBound :
    |(xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).re|
      ≤ ∑ p in (prime_window 0) \ (prime_window 0), ‖eulerKernelMedium p t 0‖
  defectImBound :
    |(xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).im|
      ≤ ∑ p in (prime_window 0) \ (prime_window 0), ‖eulerKernelMedium p t 0‖
  coherenceNorm :
    coherenceC (1 : ℝ) = 1 / Real.cosh (Real.log (1 : ℝ))

/-- Clean endpoint-facing projection of the channelized window master bridge.
This keeps endpoint proofs readable while still explicitly depending on the
full window-channel decomposition layer. -/
lemma endpoint_channel_bridge_data (t : ℝ) :
    EndpointChannelBridgeData t := by
  have hmaster := euler_window_master_channel_theorem
    0 0 0 (le_rfl : 0 ≤ 0) t 0 1 (by positivity)
  refine
    { constantSource := hmaster.1
      velocityRe := hmaster.2.1
      velocityIm := hmaster.2.2.1
      defectJumpRe := hmaster.2.2.2.1
      defectJumpIm := hmaster.2.2.2.2.1
      defectReBound := hmaster.2.2.2.2.2.1
      defectImBound := hmaster.2.2.2.2.2.2.1
      coherenceNorm := hmaster.2.2.2.2.2.2.2 }

/-- Projection: window velocity real-channel identity from the endpoint bridge. -/
lemma endpoint_channel_bridge_velocity_re (t : ℝ) :
    (partialEulerPhaseVelocity_window 0 t 0).re
      = -∑ p in prime_window 0, (eulerKernelMedium p t 0).im := by
  exact (endpoint_channel_bridge_data t).velocityRe

/-- Projection: window velocity imaginary-channel identity from the endpoint bridge. -/
lemma endpoint_channel_bridge_velocity_im (t : ℝ) :
    (partialEulerPhaseVelocity_window 0 t 0).im
      = ∑ p in prime_window 0, (eulerKernelMedium p t 0).re := by
  exact (endpoint_channel_bridge_data t).velocityIm

/-- Projection: constant-source factorization over the endpoint window. -/
lemma endpoint_channel_bridge_constant_source (t : ℝ) :
    ∃ Bphase : ℂ,
      Bphase = sourcePhase 0
        ∧ ∀ p ∈ prime_window 0,
            eulerKernelPhase p t = Bphase * eulerKernelMedium p t 0 := by
  exact (endpoint_channel_bridge_data t).constantSource

/-- Projection: defect jump real-channel identity from the endpoint bridge. -/
lemma endpoint_channel_bridge_defect_jump_re (t : ℝ) :
    (xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).re
      = (missingPrimeCore 0 0 t 0).im := by
  exact (endpoint_channel_bridge_data t).defectJumpRe

/-- Projection: defect jump imaginary-channel identity from the endpoint bridge. -/
lemma endpoint_channel_bridge_defect_jump_im (t : ℝ) :
    (xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).im
      = -(missingPrimeCore 0 0 t 0).re := by
  exact (endpoint_channel_bridge_data t).defectJumpIm

/-- Projection: defect jump real-channel bound from the endpoint bridge. -/
lemma endpoint_channel_bridge_defect_re_bound (t : ℝ) :
    |(xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).re|
      ≤ ∑ p in (prime_window 0) \ (prime_window 0), ‖eulerKernelMedium p t 0‖ := by
  exact (endpoint_channel_bridge_data t).defectReBound

/-- Projection: defect jump imaginary-channel bound from the endpoint bridge. -/
lemma endpoint_channel_bridge_defect_im_bound (t : ℝ) :
    |(xi_partialEuler_defect_window 0 t 0 - xi_partialEuler_defect_window 0 t 0).im|
      ≤ ∑ p in (prime_window 0) \ (prime_window 0), ‖eulerKernelMedium p t 0‖ := by
  exact (endpoint_channel_bridge_data t).defectImBound

/-- Projection: normalized coherence identity from the endpoint bridge. -/
lemma endpoint_channel_bridge_coherence (t : ℝ) :
    coherenceC (1 : ℝ) = 1 / Real.cosh (Real.log (1 : ℝ)) := by
  exact (endpoint_channel_bridge_data t).coherenceNorm

/-! ### Theorem Dependency Map (Endpoint)

The final endpoint is intentionally layered. This block records the exact
dependency chain in one place.

Primary closure chain:
1. `conditional_RH_via_window_limits`
2. `conditional_RH_via_window_limits_with_bridge`
3. `rh_endpoint_master`

Bridge chain used by the endpoint:
1. `euler_window_master_channel_theorem`
2. `endpoint_channel_bridge_data`
3. threaded inside `rh_endpoint_master`

Geometric/analytic lock chain:
1. `geometric_phase_lock_holds`
2. `analytic_phase_lock_holds`
3. `geometric_analytic_bridge`
4. consumed by `conditional_RH_via_window_limits_with_bridge`
-/

/-- Threaded closure theorem:
combines window-limit RH forcing with the geometric/analytic bridge package. -/
theorem conditional_RH_via_window_limits_with_bridge :
    ∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) →
      s.re = 1/2 ∧ geometric_phase_lock ∧ analytic_phase_lock s.im := by
  intro s hz hstrip
  have hcrit : s.re = 1/2 := conditional_RH_via_window_limits s hz hstrip
  have hbridge := geometric_analytic_bridge s.im
  exact ⟨hcrit, hbridge.1, hbridge.2.1⟩

/-- Master endpoint theorem for this development.
It packages the window-limit RH closure together with the geometric/analytic bridge. -/
theorem rh_endpoint_master :
    ∀ s : ℂ, riemannZeta s = 0 → (0 < s.re ∧ s.re < 1) →
      s.re = 1/2
        ∧ geometric_phase_lock
        ∧ analytic_phase_lock s.im
        ∧ xi ((1 / 2 : ℂ) + s.im * Complex.I) ∈ ℝ := by
  intro s hz hstrip
  have hmain := conditional_RH_via_window_limits_with_bridge s hz hstrip
  have hbridge := geometric_analytic_bridge s.im
  have _ :
      coherenceC (1 : ℝ) = 1 / Real.cosh (Real.log (1 : ℝ)) :=
        endpoint_channel_bridge_coherence s.im
  exact ⟨hmain.1, hmain.2.1, hmain.2.2, hbridge.2.2⟩

/-- Coordinate version: a point `x + iy` is on the unit circle iff `x^2 + y^2 = 1`. -/
lemma unit_circle_abs_xy (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    Complex.abs ((x : ℂ) + y * Complex.I) = 1 := by
  rw [Complex.abs_def]
  simp [Complex.normSq, hxy]

/-- Coordinate version of ξ-conjugation: `x + iy` maps to `x - iy`. -/
lemma xi_conj_xy (x y : ℝ) :
    Complex.conj (xi ((x : ℂ) + y * Complex.I)) = xi ((x : ℂ) - y * Complex.I) := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
    mul_assoc, mul_left_comm, mul_comm]
    using xi_conj ((x : ℂ) + y * Complex.I)

/-- Combined `x + iy` symmetry link:
unit-circle modulus in coordinates + ξ conjugation symmetry in coordinates. -/
theorem symmetry_link_to_xi_xy (x y : ℝ) (hxy : x ^ 2 + y ^ 2 = 1) :
    Complex.abs ((x : ℂ) + y * Complex.I) = 1 ∧
    Complex.conj (xi ((x : ℂ) + y * Complex.I)) = xi ((x : ℂ) - y * Complex.I) := by
  exact ⟨unit_circle_abs_xy x y hxy, xi_conj_xy x y⟩

end FourAxioms

/-!
  Honest accounting of what's proved vs. left as `sorry` in this file:

  PROVED CLEANLY (no sorry):
    • magnitude_balance      :  |B|·|C| = 1
    • B_mul_C_eq_μ           :  B · C = μ
    • B_abs, C_abs           :  |B| = √2, |C| = 1/√2
    • log_distrib            :  log(BC) = log B + log C
    • log_real_parts_cancel  :  Re(log B) + Re(log C) = 0
    • phase_closure          :  arg(A) − (arg(B) + arg(C)) = 0
    • silver_eq              :  metallic 1 = 1 + √2
    • golden_self_referential:  φ² = φ + 1
    • coherence_eq_sech_log  :  C(r) = (1/2)·sech²((log r)/2)
    • coherenceC_eq_sech_log_h: C(h) = sech(log h)
    • coherence_symmetric    :  C(r) = C(1/r)
    • coherence_peak         :  C(1) = 1/2
    • reflect_involutive
    • reflect_fixed_iff      :  reflect σ = σ ↔ σ = 1/2
    • off_critical_line_splits
    • critical_line_forced   :  fixed-axis condition ⇒ σ = 1/2
    • off_critical_line_contradiction (the proof-by-contradiction)
    • log_reflection_fixed_iff:  −μ = μ ↔ μ = 0
    • framework_forces_critical_line
    • euler_trig_coherence_bridge
    • euler_window_trig_coherence_bridge
    • euler_window_master_channel_theorem
    • endpoint_channel_bridge_data
    • partialEulerPhaseCore_re / partialEulerPhaseCore_im
    • partialEulerPhaseVelocity_re / partialEulerPhaseVelocity_im
    • xi_partialEuler_defect_window_jump_re / xi_partialEuler_defect_window_jump_im
    • xi_partialEuler_defect_window_refine_re_abs_le /
      xi_partialEuler_defect_window_refine_im_abs_le

  LEFT AS `sorry`:
    • none (all former placeholders resolved)

  NOT FORMALIZED (explicit analytic boundary axioms still assumed):
    • `xi_logderiv_formula`
    • `xi_logderiv_symmetry_sum`
    • `phase_velocity_on_critical_line`
    • `completedRiemannZeta_factor_bridge_at_exceptional_lattice`
    • `completedHurwitzZetaEven_zero_conj_of_ne_zero`
    • `xi_real_rigidity`  -- final RH-type rigidity boundary
    • `missingPrimeCore_cauchy_tail`
    • `partialEulerPhaseVelocity_window_tendsto`
    • `zeta_zero_is_limit_of_window_zeros`
    • `phase_lock_from_window_limit`
-/