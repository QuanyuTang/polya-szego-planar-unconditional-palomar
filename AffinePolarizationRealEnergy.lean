module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationEnergyTransport
public import PolarizationLipschitz
public import EuclideanReflectionContraction
public import PolarizedOpenDomain
public import CompactLipOriginalH01Energy
public import Mathlib.Tactic.Linarith

/-!
# Actual real mass and gradient energy under arbitrary affine polarization

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The halfspace and reflection are the original explicit constructions, with
an arbitrary actual unit normal and arbitrary real offset. The input is a
nonnegative globally Lipschitz compactly supported function. Its literal
polarization is again globally Lipschitz and compactly supported. Its real
square mass and real squared-fderivative integrals equal those of the input.

All four real densities are genuinely integrable. Value integrability is
produced from compact continuity; gradient integrability comes from the two
actual L2 fderiv coordinates, via CompactLipOriginalH01Energy. The paired
max/min law and the actual reflection derivative-pair theorem are then
transported through measure preservation. The proof cancels a real factor
2 only after establishing these finite real integrals.

No OriginHalfspace restriction, sign of the offset, centered support ball,
ExtMollification, assumed energy identity, or assumed integrability enters
the roots. No MainResults, Core2--4, or FiniteOrbitEnergies is imported.
The three scalar/transport helpers are copied from the independently
verified v4.28 FiniteOrbitEnergies proof, in a fresh namespace.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal Topology

namespace FaberKrahnDevelopment.AffineRealEnergy

open EuclideanReflection

/-- Pure scalar sorting preserves the pair of actual squares. -/
lemma sorted_square_pair (a b : ℝ) :
    max a b ^ 2 + min a b ^ 2 = a ^ 2 + b ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_left hab]
    exact add_comm _ _
  · rw [max_eq_left hba, min_eq_right hba]

lemma square_twoPointPolarization_pair {α : Type*} {H : Set α} {τ : α → α}
    {f : α → ℝ} (hInv : Function.Involutive τ) {x : α}
    (hSwap : τ x ∈ H ↔ x ∉ H) :
    twoPointPolarization H τ f x ^ 2 + twoPointPolarization H τ f (τ x) ^ 2 =
      f x ^ 2 + f (τ x) ^ 2 := by
  classical
  by_cases hx : x ∈ H
  · have hτx : τ x ∉ H := fun hτx => (hSwap.mp hτx) hx
    simp only [twoPointPolarization, if_pos hx, if_neg hτx, hInv x]
    rw [min_comm (f (τ x)) (f x)]
    exact sorted_square_pair (f x) (f (τ x))
  · have hτx : τ x ∈ H := hSwap.mpr hx
    simp only [twoPointPolarization, if_neg hx, if_pos hτx, hInv x]
    simpa only [min_comm, add_comm] using sorted_square_pair (f (τ x)) (f x)

/-- Real pair transport, with integrability explicitly required of both
densities. The actual applications below produce every such requirement. -/
lemma integral_eq_of_ae_involution_pair_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {τ : α → α}
    (hτ : MeasurePreserving τ μ μ) (hInv : Function.Involutive τ)
    {p q : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hPair : ∀ᵐ x ∂μ, p x + p (τ x) = q x + q (τ x)) :
    (∫ x, p x ∂μ) = ∫ x, q x ∂μ := by
  let e : α ≃ᵐ α := MeasurableEquiv.ofInvolutive τ hInv hτ.measurable
  have hpτ : Integrable (fun x => p (τ x)) μ := hτ.integrable_comp_of_integrable hp
  have hqτ : Integrable (fun x => q (τ x)) μ := hτ.integrable_comp_of_integrable hq
  have hip : (∫ x, p (τ x) ∂μ) = ∫ x, p x ∂μ :=
    hτ.integral_comp e.measurableEmbedding p
  have hiq : (∫ x, q (τ x) ∂μ) = ∫ x, q x ∂μ :=
    hτ.integral_comp e.measurableEmbedding q
  have hIntegral : (∫ x, p x + p (τ x) ∂μ) = ∫ x, q x + q (τ x) ∂μ :=
    integral_congr_ae hPair
  rw [integral_add hp hpτ, integral_add hq hqτ, hip, hiq] at hIntegral
  linarith

/-- The actual isometry, involution and cross-side contraction produce the
same global Lipschitz constant for arbitrary affine offset. -/
lemma lipschitzWith_polarization (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (twoPointPolarization (halfspace ν c) (reflection ν c) f) :=
  lipschitzWith_twoPointPolarization (reflection_isometry ν c)
    (reflection_involutive ν c) (reflection_cross_dist_le ν c) hf

/-- Compactness is produced by the actual polarized-support theorem on
the full open plane; no centered support or offset condition is needed. -/
lemma hasCompactSupport_polarization (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} (hfN : ∀ x, 0 ≤ f x) (hc : HasCompactSupport f) :
    HasCompactSupport (twoPointPolarization (halfspace ν c) (reflection ν c) f) := by
  exact (PolarizedOpenDomain.polarization_hasCompactSupport_inside ν c
    (Ω := univ) hfN hc (subset_univ _)).1

lemma integrable_square_of_lipschitz_compact {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hc : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2) volume :=
  (Buckling.CompactLipOriginalH01.value_memLp hf hc).integrable_sq

/-- All four densities have ordinary finite real integrals, independently
of either preservation identity. -/
theorem integrable_polarization_energies (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hc : HasCompactSupport f) (hfN : ∀ x, 0 ≤ f x) :
    Integrable (fun x => f x ^ 2) volume ∧
      Integrable (fun x => twoPointPolarization (halfspace ν c) (reflection ν c) f x ^ 2)
        volume ∧
      Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) volume ∧
      Integrable (fun x =>
        ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f) x‖ ^ 2)
        volume := by
  have hpL := lipschitzWith_polarization ν c hf
  have hpC := hasCompactSupport_polarization ν c hfN hc
  exact ⟨integrable_square_of_lipschitz_compact hf hc,
    integrable_square_of_lipschitz_compact hpL hpC,
    Buckling.CompactLipOriginalH01.integrable_gradient_sq hf hc,
    Buckling.CompactLipOriginalH01.integrable_gradient_sq hpL hpC⟩

/-- Arbitrary affine polarization preserves the actual real square mass. -/
theorem integral_sq_polarization (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hc : HasCompactSupport f) (hfN : ∀ x, 0 ≤ f x) :
    (∫ x, twoPointPolarization (halfspace ν c) (reflection ν c) f x ^ 2) =
      ∫ x, f x ^ 2 := by
  have hI := integrable_polarization_energies ν c hf hc hfN
  apply integral_eq_of_ae_involution_pair_eq
    (reflection_measurePreserving ν c) (reflection_involutive ν c) hI.2.1 hI.1
  filter_upwards [reflection_ae_swap ν c] with x hx
  exact square_twoPointPolarization_pair (reflection_involutive ν c) hx

/-- Arbitrary affine polarization preserves the actual real gradient energy. -/
theorem integral_gradient_sq_polarization (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hc : HasCompactSupport f) (hfN : ∀ x, 0 ≤ f x) :
    (∫ x, ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f) x‖ ^ 2) =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hI := integrable_polarization_energies ν c hf hc hfN
  exact integral_eq_of_ae_involution_pair_eq
    (reflection_measurePreserving ν c) (reflection_involutive ν c) hI.2.2.2 hI.2.2.1
    (ae_norm_fderiv_polarization_pair ν c hf)

/-- The two real equalities together, with only the natural function and
reflection inputs and no energy or integrability premise. -/
theorem polarization_real_energies (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hc : HasCompactSupport f) (hfN : ∀ x, 0 ≤ f x) :
    ((∫ x, twoPointPolarization (halfspace ν c) (reflection ν c) f x ^ 2) =
      ∫ x, f x ^ 2) ∧
    ((∫ x, ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f) x‖ ^ 2) =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2) :=
  ⟨integral_sq_polarization ν c hf hc hfN,
    integral_gradient_sq_polarization ν c hf hc hfN⟩

end FaberKrahnDevelopment.AffineRealEnergy

end

end
