module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationMeasure
public import PolarizationMoment
public import Mathlib.Tactic.Linarith

/-!
# Integrating the paired sorting inequality

SOURCE_DRAFT (2026-10-17), awaiting compilation and axiom inspection.
This module is not imported by the production buckling project.

For a measure-preserving involution which swaps the sides a.e., the actual
max/min polarization decreases an integrable weighted moment whenever the
weight is smaller on the chosen side. Integrability here is the ordinary
well-definedness condition for the two weighted integrals; compact support
and boundedness will produce it in the intended Euclidean application.
No decrease or global energy theorem is supplied as an input.

Equality gives a.e. equality of paired weighted sums. Strict radial weights
and continuity still have to be connected to pointwise reflection ordering;
that stronger conclusion is not silently assumed or asserted here.
-/

@[expose] public section

open Set MeasureTheory Filter

namespace FaberKrahnDevelopment

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The literal two-point weighted sum decreases off the swapping exception. -/
lemma weighted_polarization_pair_le {H : Set α} {τ : α → α}
    {f w : α → ℝ} (hInv : Function.Involutive τ)
    (hWeight : ∀ x ∈ H, w x ≤ w (τ x)) {x : α}
    (hSwap : τ x ∈ H ↔ x ∉ H) :
    twoPointPolarization H τ f x * w x +
        twoPointPolarization H τ f (τ x) * w (τ x) ≤
      f x * w x + f (τ x) * w (τ x) := by
  classical
  by_cases hx : x ∈ H
  · have hτx : τ x ∉ H := by
      intro hτx
      exact (hSwap.mp hτx) hx
    simp only [twoPointPolarization, if_pos hx, if_neg hτx, hInv x]
    rw [min_comm (f (τ x)) (f x)]
    exact sorted_weighted_pair_le (f x) (f (τ x)) (w x) (w (τ x)) (hWeight x hx)
  · have hτx : τ x ∈ H := hSwap.mpr hx
    have hw : w (τ x) ≤ w x := by simpa only [hInv x] using hWeight (τ x) hτx
    simp only [twoPointPolarization, if_neg hx, if_pos hτx, hInv x]
    have h := sorted_weighted_pair_le (f (τ x)) (f x) (w (τ x)) (w x) hw
    rw [min_comm (f x) (f (τ x)), add_comm] 
    simpa only [add_comm] using h

lemma ae_weighted_polarization_pair_le {H : Set α} {τ : α → α}
    {f w : α → ℝ} (hInv : Function.Involutive τ)
    (hWeight : ∀ x ∈ H, w x ≤ w (τ x))
    (hSwap : ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H) :
    ∀ᵐ x ∂μ,
      twoPointPolarization H τ f x * w x +
          twoPointPolarization H τ f (τ x) * w (τ x) ≤
        f x * w x + f (τ x) * w (τ x) :=
  hSwap.mono fun _ hx => weighted_polarization_pair_le hInv hWeight hx

/-- The actual weighted integral decreases under the natural side ordering of
the weight. Both weighted products are required to be genuinely integrable. -/
lemma integral_weighted_polarization_le {H : Set α} {τ : α → α}
    {f w : α → ℝ} (hτ : MeasurePreserving τ μ μ)
    (hInv : Function.Involutive τ)
    (hSwap : ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H)
    (hWeight : ∀ x ∈ H, w x ≤ w (τ x))
    (hf : Integrable (fun x => f x * w x) μ)
    (hp : Integrable (fun x => twoPointPolarization H τ f x * w x) μ) :
    ∫ x, twoPointPolarization H τ f x * w x ∂μ ≤ ∫ x, f x * w x ∂μ := by
  let p := twoPointPolarization H τ f
  let e : α ≃ᵐ α := MeasurableEquiv.ofInvolutive τ hInv hτ.measurable
  have hfτ : Integrable (fun x => f (τ x) * w (τ x)) μ :=
    hτ.integrable_comp_of_integrable hf
  have hpτ : Integrable (fun x => p (τ x) * w (τ x)) μ :=
    hτ.integrable_comp_of_integrable hp
  have hif : (∫ x, f (τ x) * w (τ x) ∂μ) = ∫ x, f x * w x ∂μ :=
    hτ.integral_comp e.measurableEmbedding (fun x => f x * w x)
  have hip : (∫ x, p (τ x) * w (τ x) ∂μ) = ∫ x, p x * w x ∂μ :=
    hτ.integral_comp e.measurableEmbedding (fun x => p x * w x)
  have hsum := integral_mono_ae (hp.add hpτ) (hf.add hfτ)
    (ae_weighted_polarization_pair_le (f := f) hInv hWeight hSwap)
  change (∫ x, p x * w x + p (τ x) * w (τ x) ∂μ) ≤
    ∫ x, f x * w x + f (τ x) * w (τ x) ∂μ at hsum
  rw [integral_add hp hpτ, integral_add hf hfτ, hip, hif] at hsum
  change (∫ x, p x * w x ∂μ) ≤ ∫ x, f x * w x ∂μ
  linarith

/-- If the two genuine integrable moments agree, the paired sorting inequality
is an equality almost everywhere. This is derived from the integral equality. -/
lemma ae_weighted_polarization_pair_eq_of_integral_eq {H : Set α} {τ : α → α}
    {f w : α → ℝ} (hτ : MeasurePreserving τ μ μ)
    (hInv : Function.Involutive τ)
    (hSwap : ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H)
    (hWeight : ∀ x ∈ H, w x ≤ w (τ x))
    (hf : Integrable (fun x => f x * w x) μ)
    (hp : Integrable (fun x => twoPointPolarization H τ f x * w x) μ)
    (heq : (∫ x, twoPointPolarization H τ f x * w x ∂μ) =
      ∫ x, f x * w x ∂μ) :
    ∀ᵐ x ∂μ,
      twoPointPolarization H τ f x * w x +
          twoPointPolarization H τ f (τ x) * w (τ x) =
        f x * w x + f (τ x) * w (τ x) := by
  let p := twoPointPolarization H τ f
  let e : α ≃ᵐ α := MeasurableEquiv.ofInvolutive τ hInv hτ.measurable
  have hfτ : Integrable (fun x => f (τ x) * w (τ x)) μ :=
    hτ.integrable_comp_of_integrable hf
  have hpτ : Integrable (fun x => p (τ x) * w (τ x)) μ :=
    hτ.integrable_comp_of_integrable hp
  have hif : (∫ x, f (τ x) * w (τ x) ∂μ) = ∫ x, f x * w x ∂μ :=
    hτ.integral_comp e.measurableEmbedding (fun x => f x * w x)
  have hip : (∫ x, p (τ x) * w (τ x) ∂μ) = ∫ x, p x * w x ∂μ :=
    hτ.integral_comp e.measurableEmbedding (fun x => p x * w x)
  apply (integral_eq_iff_of_ae_le (hp.add hpτ) (hf.add hfτ)
    (ae_weighted_polarization_pair_le (f := f) hInv hWeight hSwap)).mp
  change (∫ x, p x * w x + p (τ x) * w (τ x) ∂μ) =
    ∫ x, f x * w x + f (τ x) * w (τ x) ∂μ
  rw [integral_add hp hpτ, integral_add hf hfτ, hip, hif]
  change (∫ x, p x * w x ∂μ) + (∫ x, p x * w x ∂μ) =
    (∫ x, f x * w x ∂μ) + (∫ x, f x * w x ∂μ)
  rw [heq]

end FaberKrahnDevelopment
