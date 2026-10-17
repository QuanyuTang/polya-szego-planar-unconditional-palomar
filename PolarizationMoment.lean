module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Tactic.Ring

/-!
# Weighted moments in the uniform topology and two-point sorting

SOURCE_DRAFT (2026-10-17), not compiled and not imported by production.

An integrable weight defines an actual continuous moment functional on global
bounded continuous functions, with an explicit uniform Lipschitz bound. A
separate scalar identity computes exactly how sorting decreases the moment
when the larger weight is paired with the smaller function value.

The intended weight is the squared radius restricted to the common compact
support ball. This file does not yet prove the global change-of-variables
formula for affine polarization, strict moment decrease, or that an orbit
minimizer is reflection ordered. Those remain real producer obligations.
-/

@[expose] public section

open MeasureTheory Filter BoundedContinuousFunction
open scoped NNReal

namespace FaberKrahnDevelopment

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X}

/-- Integration against the literal weight, not a chosen minimizer oracle. -/
noncomputable def weightedMoment (μ : Measure X) (w : X → ℝ) (f : X →ᵇ ℝ) : ℝ :=
  ∫ x, w x * f x ∂μ

lemma integrable_weight_mul_boundedContinuous {w : X → ℝ}
    (hw : Integrable w μ) (f : X →ᵇ ℝ) : Integrable (fun x => w x * f x) μ :=
  hw.mul_bdd f.continuous.measurable.aestronglyMeasurable
    (Eventually.of_forall fun x => f.norm_coe_le_norm x)

/-- Exact quantitative continuity of an integrable weighted moment. -/
lemma dist_weightedMoment_le {w : X → ℝ} (hw : Integrable w μ)
    (f g : X →ᵇ ℝ) :
    dist (weightedMoment μ w f) (weightedMoment μ w g) ≤
      (∫ x, ‖w x‖ ∂μ) * dist f g := by
  have hf := integrable_weight_mul_boundedContinuous hw f
  have hg := integrable_weight_mul_boundedContinuous hw g
  rw [dist_eq_norm, weightedMoment, weightedMoment, ← integral_sub hf hg]
  have hbound : ∀ᵐ x ∂μ,
      ‖w x * f x - w x * g x‖ ≤ ‖w x‖ * dist f g := by
    exact Eventually.of_forall fun x => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [dist_eq_norm] using (dist_coe_le_dist (f := f) (g := g) x))
        (norm_nonneg _)
  calc
    ‖∫ x, w x * f x - w x * g x ∂μ‖ ≤
        ∫ x, ‖w x‖ * dist f g ∂μ :=
      norm_integral_le_of_norm_le (hw.norm.mul_const _) hbound
    _ = (∫ x, ‖w x‖ ∂μ) * dist f g := integral_mul_const _ _

lemma lipschitzWith_weightedMoment {w : X → ℝ} (hw : Integrable w μ) :
    LipschitzWith ⟨∫ x, ‖w x‖ ∂μ, integral_nonneg fun x => norm_nonneg _⟩
      (weightedMoment μ w) :=
  LipschitzWith.of_dist_le_mul (dist_weightedMoment_le hw)

lemma continuous_weightedMoment {w : X → ℝ} (hw : Integrable w μ) :
    Continuous (weightedMoment μ w) :=
  (lipschitzWith_weightedMoment hw).continuous

/-- The exact gain of sorting a pair against two fixed real weights. -/
lemma sorted_weighted_pair_gap (a b s t : ℝ) :
    a * s + b * t - (max a b * s + min a b * t) =
      max 0 (b - a) * (t - s) := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab, min_eq_left hab, max_eq_right (sub_nonneg.mpr hab)]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [max_eq_left hba, min_eq_right hba, max_eq_left (sub_nonpos.mpr hba)]
    ring

lemma sorted_weighted_pair_le (a b s t : ℝ) (hst : s ≤ t) :
    max a b * s + min a b * t ≤ a * s + b * t := by
  have hgap := sorted_weighted_pair_gap a b s t
  have hnonneg := mul_nonneg (le_max_left (0 : ℝ) (b - a)) (sub_nonneg.mpr hst)
  exact sub_nonneg.mp (hgap.symm ▸ hnonneg)

lemma sorted_weighted_pair_lt (a b s t : ℝ) (hab : a < b) (hst : s < t) :
    max a b * s + min a b * t < a * s + b * t := by
  have hgap := sorted_weighted_pair_gap a b s t
  have hpositive : 0 < max 0 (b - a) * (t - s) :=
    mul_pos ((sub_pos.mpr hab).trans_le (le_max_right _ _)) (sub_pos.mpr hst)
  exact sub_pos.mp (hgap.symm ▸ hpositive)

end FaberKrahnDevelopment
