module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationEnergy
public import Mathlib.Algebra.Order.Group.Abs

/-!
# Absolute value preserves the energy of a Lipschitz scalar function

SOURCE_DRAFT (2026-10-17), not compiled and not imported by production.

The nonnegative starting function for polarization is the literal absolute
value of the original test function. Its Lipschitz bound and square integral
are unchanged. At a.e. point, the existing max/min derivative-pair theorem
applied to f and -f shows that the derivative of |f| is either Df or -Df.
No assertion that the zero set has measure zero is used.

These statements do not supply a rearrangement limit or Faber--Krahn.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal

namespace FaberKrahnDevelopment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma lipschitzWith_absoluteValue {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (fun x => |f x|) := by
  simpa only [max_self, Pi.neg_apply, ← abs_eq_max_neg] using hf.max hf.neg

section AlmostEverywhere

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Absolute value changes the derivative only by a sign almost everywhere. -/
lemma ae_fderiv_absoluteValue_eq_or_neg {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, fderiv ℝ (fun y => |f y|) x = fderiv ℝ f x ∨
      fderiv ℝ (fun y => |f y|) x = -fderiv ℝ f x := by
  have hfn : LipschitzWith K (fun x => -f x) := hf.neg
  have hMax : LipschitzWith K (fun x => max (f x) (-f x)) := by
    simpa only [max_self] using hf.max hfn
  have hMin : LipschitzWith K (fun x => min (f x) (-f x)) := by
    simpa only [max_self] using hf.min hfn
  filter_upwards [hf.ae_differentiableAt (μ := μ), hfn.ae_differentiableAt (μ := μ),
    hMax.ae_differentiableAt (μ := μ), hMin.ae_differentiableAt (μ := μ)]
      with x hfx hfnx hMx hmx
  have habs : (fun y => max (f y) (-f y)) = (fun y => |f y|) := by
    funext y
    exact (abs_eq_max_neg : |f y| = max (f y) (-f y)).symm
  rcases fderiv_max_min_eq_or hfx hfnx hMx hmx with h | h
  · exact Or.inl (habs ▸ h.1)
  · exact Or.inr ((habs ▸ h.1).trans fderiv_fun_neg)

lemma ae_norm_fderiv_absoluteValue {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∀ᵐ x ∂μ, ‖fderiv ℝ (fun y => |f y|) x‖ = ‖fderiv ℝ f x‖ := by
  filter_upwards [ae_fderiv_absoluteValue_eq_or_neg (μ := μ) hf] with x hx
  rcases hx with h | h
  · rw [h]
  · rw [h, norm_neg]

lemma integral_norm_fderiv_absoluteValue_sq {f : E → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    (∫ x, ‖fderiv ℝ (fun y => |f y|) x‖ ^ 2 ∂μ) =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ := by
  apply integral_congr_ae
  exact (ae_norm_fderiv_absoluteValue (μ := μ) hf).mono
    (fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)

end AlmostEverywhere

lemma integral_absoluteValue_sq [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    (∫ x, |f x| ^ 2 ∂μ) = ∫ x, f x ^ 2 ∂μ := by
  congr 1
  funext x
  exact sq_abs (f x)

end FaberKrahnDevelopment
