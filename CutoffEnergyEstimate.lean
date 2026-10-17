module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import SpectralCutoffGeometry
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith

/-!
# An actual smooth-cutoff derivative-energy estimate

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.
The cutoff is the literal `spectralCutoff R ε hR hε`, not abstract energy data.
At any differentiability point of the actual function `f`, the product rule
and the cutoff's actual derivative give the derivative of `χ * f`. Because
`v * Dχ = 0` by the concrete support geometry, the error term is exactly
`(f - v) * Dχ`, bounded by the GLOBAL BCF uniform distance.

The estimate below is derived from the triangle inequality, `0 ≤ χ ≤ 1`,
and the ordinary scalar Young inequality. Rademacher then supplies the a.e.
differentiability point without a gradient convergence assumption.

This file proves pointwise-at-differentiability and complete a.e. estimates.
It deliberately does not import the entire original project to prove real
gradient-integral finiteness. No spectral estimate, cutoff energy estimate,
Sobolev limit, gradient convergence, or Faber--Krahn is assumed as input.
Actual compilation and axiom inspection remain required.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped NNReal

namespace FaberKrahnDevelopment.EuclideanReflection

/-- At an actual differentiability point the cutoff product satisfies the
desired energy estimate. The limiting function needs no derivative here. -/
lemma norm_fderiv_spectralCutoff_mul_sq_le
    {R ε δ : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hδ : 0 < δ)
    {f v : Plane →ᵇ ℝ} (hv : ∀ x, R < ‖x‖ → v x = 0)
    {x : Plane} (hf : DifferentiableAt ℝ (f : Plane → ℝ) x) :
    ‖fderiv ℝ (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2 ≤
      (1 + δ) * ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 +
        (1 + δ⁻¹) * (dist f v) ^ 2 *
          ‖fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x‖ ^ 2 := by
  let χ := spectralCutoff R ε hR hε
  have hχC : ContDiff ℝ 1 (χ : Plane → ℝ) := χ.contDiff
  have hχ : DifferentiableAt ℝ (χ : Plane → ℝ) x :=
    hχC.differentiable_one x
  have hχx : χ x ∈ Icc (0 : ℝ) 1 := spectralCutoff_mem_Icc R ε hR hε x
  have hvD : v x • fderiv ℝ (χ : Plane → ℝ) x = 0 :=
    value_smul_fderiv_spectralCutoff_eq_zero hR hε hv x
  have hcancel : f x • fderiv ℝ (χ : Plane → ℝ) x =
      (f x - v x) • fderiv ℝ (χ : Plane → ℝ) x := by
    rw [sub_smul, hvD, sub_zero]
  have hprod : fderiv ℝ (fun y => χ y * f y) x =
      χ x • fderiv ℝ (f : Plane → ℝ) x +
        (f x - v x) • fderiv ℝ (χ : Plane → ℝ) x := by
    rw [fderiv_fun_mul hχ hf, hcancel]
  have hfirst : ‖χ x • fderiv ℝ (f : Plane → ℝ) x‖ ≤
      ‖fderiv ℝ (f : Plane → ℝ) x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hχx.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hχx.2
  have hpoint : |f x - v x| ≤ dist f v := by
    simpa only [Real.dist_eq] using
      (BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := v) x)
  have hsecond : ‖(f x - v x) • fderiv ℝ (χ : Plane → ℝ) x‖ ≤
      dist f v * ‖fderiv ℝ (χ : Plane → ℝ) x‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hpoint (norm_nonneg _)
  have hsum : ‖fderiv ℝ (fun y => χ y * f y) x‖ ≤
      ‖fderiv ℝ (f : Plane → ℝ) x‖ +
        dist f v * ‖fderiv ℝ (χ : Plane → ℝ) x‖ := by
    rw [hprod]
    exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)
  have hsquare : ‖fderiv ℝ (fun y => χ y * f y) x‖ ^ 2 ≤
      (‖fderiv ℝ (f : Plane → ℝ) x‖ +
        dist f v * ‖fderiv ℝ (χ : Plane → ℝ) x‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _)
      (add_nonneg (norm_nonneg _) (mul_nonneg dist_nonneg (norm_nonneg _)))).2 hsum
  have hYoung := two_mul_le_add_mul_sq
    (a := ‖fderiv ℝ (f : Plane → ℝ) x‖)
    (b := dist f v * ‖fderiv ℝ (χ : Plane → ℝ) x‖) hδ
  have hbound : ‖fderiv ℝ (fun y => χ y * f y) x‖ ^ 2 ≤
      (1 + δ) * ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 +
        (1 + δ⁻¹) * (dist f v * ‖fderiv ℝ (χ : Plane → ℝ) x‖) ^ 2 := by
    nlinarith
  simpa only [mul_pow, mul_assoc] using hbound

/-- The complete almost-everywhere estimate uses only the actual Lipschitz
regularity of `f`, plus the limiting function's literal support information. -/
lemma ae_norm_fderiv_spectralCutoff_mul_sq_le
    {R ε δ : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hδ : 0 < δ)
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hv : ∀ x, R < ‖x‖ → v x = 0) :
    ∀ᵐ x ∂volume,
      ‖fderiv ℝ (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2 ≤
        (1 + δ) * ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 +
          (1 + δ⁻¹) * (dist f v) ^ 2 *
            ‖fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x‖ ^ 2 := by
  filter_upwards [hf.ae_differentiableAt (μ := (volume : Measure Plane))] with x hfx
  exact norm_fderiv_spectralCutoff_mul_sq_le hR hε hδ hv hfx

/-- One common full-measure differentiability set supports every `δ > 0`.
No countable or uncountable intersection of δ-dependent exceptional sets is used. -/
lemma ae_forall_delta_norm_fderiv_spectralCutoff_mul_sq_le
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hv : ∀ x, R < ‖x‖ → v x = 0) :
    ∀ᵐ x ∂volume, ∀ δ : ℝ, 0 < δ →
      ‖fderiv ℝ (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2 ≤
        (1 + δ) * ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 +
          (1 + δ⁻¹) * (dist f v) ^ 2 *
            ‖fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x‖ ^ 2 := by
  filter_upwards [hf.ae_differentiableAt (μ := (volume : Measure Plane))] with x hfx
  intro δ hδ
  exact norm_fderiv_spectralCutoff_mul_sq_le hR hε hδ hv hfx

end FaberKrahnDevelopment.EuclideanReflection

end

end
