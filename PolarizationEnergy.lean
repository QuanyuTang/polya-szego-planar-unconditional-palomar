module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Local max/min derivative energy identity

Development status (2026-10-17): SOURCE_DRAFT, not yet compiled. This isolated
file is not imported by the production buckling project and makes no claim of
having completed a Faber--Krahn proof.

At a point where two real functions and their max/min are differentiable, the
two max/min derivatives are the two original derivatives, in some order.
At equal values this follows from Fermat's theorem applied to max(f,g)-f
and g-min(f,g), which are nonnegative and vanish at the point. No regularity
assumption on the coincidence set is used.

For Lipschitz functions on a finite-dimensional real normed space,
Rademacher's theorem supplies all four differentiability hypotheses a.e.
This file stops at the a.e. squared derivative-norm identity. Reflection
composition, measure transport, global Sobolev polarization, and the final
Faber--Krahn estimate are not asserted here.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology NNReal

namespace FaberKrahnDevelopment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a point where `f`, `g`, their maximum and their minimum are
differentiable, max/min preserve the unordered pair of derivatives. -/
lemma fderiv_max_min_eq_or {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hmax : DifferentiableAt ℝ (fun y => max (f y) (g y)) x)
    (hmin : DifferentiableAt ℝ (fun y => min (f y) (g y)) x) :
    (fderiv ℝ (fun y => max (f y) (g y)) x = fderiv ℝ f x ∧
      fderiv ℝ (fun y => min (f y) (g y)) x = fderiv ℝ g x) ∨
    (fderiv ℝ (fun y => max (f y) (g y)) x = fderiv ℝ g x ∧
      fderiv ℝ (fun y => min (f y) (g y)) x = fderiv ℝ f x) := by
  rcases lt_trichotomy (f x) (g x) with hlt | heq | hgt
  · have hfg : ∀ᶠ y in 𝓝 x, f y < g y :=
      hf.continuousAt.eventually_lt hg.continuousAt hlt
    have hmaxEq : (fun y => max (f y) (g y)) =ᶠ[𝓝 x] g :=
      hfg.mono fun y hy => max_eq_right hy.le
    have hminEq : (fun y => min (f y) (g y)) =ᶠ[𝓝 x] f :=
      hfg.mono fun y hy => min_eq_left hy.le
    exact Or.inr ⟨hmaxEq.fderiv_eq, hminEq.fderiv_eq⟩
  · have hMaxMinusF : IsLocalMin (fun y => max (f y) (g y) - f y) x := by
      refine Filter.Eventually.of_forall fun y => ?_
      change max (f x) (g x) - f x ≤ max (f y) (g y) - f y
      rw [heq, max_self, sub_self]
      exact sub_nonneg.mpr (le_max_left (f y) (g y))
    have hGMinusMin : IsLocalMin (fun y => g y - min (f y) (g y)) x := by
      refine Filter.Eventually.of_forall fun y => ?_
      change g x - min (f x) (g x) ≤ g y - min (f y) (g y)
      rw [heq, min_self, sub_self]
      exact sub_nonneg.mpr (min_le_right (f y) (g y))
    have hMaxDeriv :
        fderiv ℝ (fun y => max (f y) (g y)) x = fderiv ℝ f x := by
      apply sub_eq_zero.mp
      exact hMaxMinusF.hasFDerivAt_eq_zero
        (hmax.hasFDerivAt.sub hf.hasFDerivAt)
    have hGDeriv :
        fderiv ℝ g x = fderiv ℝ (fun y => min (f y) (g y)) x := by
      apply sub_eq_zero.mp
      exact hGMinusMin.hasFDerivAt_eq_zero
        (hg.hasFDerivAt.sub hmin.hasFDerivAt)
    exact Or.inl ⟨hMaxDeriv, hGDeriv.symm⟩
  · have hgf : ∀ᶠ y in 𝓝 x, g y < f y :=
      hg.continuousAt.eventually_lt hf.continuousAt hgt
    have hmaxEq : (fun y => max (f y) (g y)) =ᶠ[𝓝 x] f :=
      hgf.mono fun y hy => max_eq_left hy.le
    have hminEq : (fun y => min (f y) (g y)) =ᶠ[𝓝 x] g :=
      hgf.mono fun y hy => min_eq_right hy.le
    exact Or.inl ⟨hmaxEq.fderiv_eq, hminEq.fderiv_eq⟩

/-- The pointwise squared derivative-norm sum is unchanged by max/min at
points where all four functions are differentiable. -/
lemma norm_fderiv_max_sq_add_min_sq {f g : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hmax : DifferentiableAt ℝ (fun y => max (f y) (g y)) x)
    (hmin : DifferentiableAt ℝ (fun y => min (f y) (g y)) x) :
    ‖fderiv ℝ (fun y => max (f y) (g y)) x‖ ^ 2 +
        ‖fderiv ℝ (fun y => min (f y) (g y)) x‖ ^ 2 =
      ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ g x‖ ^ 2 := by
  rcases fderiv_max_min_eq_or hf hg hmax hmin with h | h
  · rw [h.1, h.2]
  · rw [h.1, h.2]
    exact add_comm _ _

section AlmostEverywhere

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {μ : Measure E} [Measure.IsAddHaarMeasure μ]

/-- Rademacher supplies differentiability of `f`, `g`, max and min on a common
full-measure set. No geometric assumption on `{x | f x = g x}` is needed. -/
lemma ae_norm_fderiv_max_sq_add_min_sq {f g : E → ℝ} {Cf Cg : ℝ≥0}
    (hf : LipschitzWith Cf f) (hg : LipschitzWith Cg g) :
    ∀ᵐ x ∂μ,
      ‖fderiv ℝ (fun y => max (f y) (g y)) x‖ ^ 2 +
          ‖fderiv ℝ (fun y => min (f y) (g y)) x‖ ^ 2 =
        ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ g x‖ ^ 2 := by
  filter_upwards [hf.ae_differentiableAt (μ := μ), hg.ae_differentiableAt (μ := μ),
    (hf.max hg).ae_differentiableAt (μ := μ),
    (hf.min hg).ae_differentiableAt (μ := μ)] with x hfx hgx hmaxx hminx
  exact norm_fderiv_max_sq_add_min_sq hfx hgx hmaxx hminx

end AlmostEverywhere

end FaberKrahnDevelopment
