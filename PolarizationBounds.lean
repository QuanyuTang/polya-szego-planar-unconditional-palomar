module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationLipschitz
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Pointwise bounds, uniform stability and common support of polarization

SOURCE_DRAFT (2026-10-17), awaiting native compilation and axiom inspection.
This file is not imported by the production buckling project.

The definition is the same literal two-point sorting as in PolarizationMeasure.
Its interval bounds and stability are purely pointwise. For common support in
a ball, nonnegativity and the actual outward radial comparison on the chosen
side suffice. That comparison has a separate concrete producer for Euclidean
reflections with the origin in the chosen halfspace; it is not an assumed
rearrangement or Faber--Krahn theorem.
-/

@[expose] public section

open Set

namespace FaberKrahnDevelopment

variable {α : Type*}

/-- Sorting two values retains a literal common pointwise interval. -/
lemma twoPointPolarization_mem_Icc {H : Set α} {τ : α → α} {f : α → ℝ}
    {a b : ℝ} (hf : ∀ x, f x ∈ Icc a b) (x : α) :
    twoPointPolarization H τ f x ∈ Icc a b := by
  classical
  by_cases hx : x ∈ H
  · rw [twoPointPolarization, if_pos hx]
    exact ⟨(hf x).1.trans (le_max_left _ _), max_le (hf x).2 (hf (τ x)).2⟩
  · rw [twoPointPolarization, if_neg hx]
    exact ⟨le_min (hf x).1 (hf (τ x)).1, (min_le_left _ _).trans (hf x).2⟩

lemma twoPointPolarization_nonneg {H : Set α} {τ : α → α} {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) (x : α) : 0 ≤ twoPointPolarization H τ f x := by
  classical
  by_cases hx : x ∈ H
  · rw [twoPointPolarization, if_pos hx]
    exact (hf x).trans (le_max_left _ _)
  · rw [twoPointPolarization, if_neg hx]
    exact le_min (hf x) (hf (τ x))

/-- Sorting is nonexpansive for a uniform pointwise distance bound. No
regularity, reflection identity or measure assumption is needed. -/
lemma dist_twoPointPolarization_le_of_forall {H : Set α} {τ : α → α}
    {f g : α → ℝ} {r : ℝ} (hfg : ∀ x, dist (f x) (g x) ≤ r) (x : α) :
    dist (twoPointPolarization H τ f x) (twoPointPolarization H τ g x) ≤ r := by
  classical
  have hx : |f x - g x| ≤ r := by simpa only [Real.dist_eq] using hfg x
  have hτx : |f (τ x) - g (τ x)| ≤ r := by
    simpa only [Real.dist_eq] using hfg (τ x)
  by_cases hH : x ∈ H
  · simp only [twoPointPolarization, if_pos hH, Real.dist_eq]
    exact (abs_max_sub_max_le_max _ _ _ _).trans (max_le hx hτx)
  · simp only [twoPointPolarization, if_neg hH, Real.dist_eq]
    exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le hx hτx)

section Normed

variable {E : Type*} [NormedAddCommGroup E]

/-- Nonnegative polarization retains a common centered support ball when
the partner of a point on the chosen side is at least as far from zero. -/
lemma twoPointPolarization_eq_zero_of_radius_lt {H : Set E} {τ : E → E}
    {f : E → ℝ} {S : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hzero : ∀ x, S < ‖x‖ → f x = 0)
    (hRadial : ∀ x ∈ H, ‖x‖ ≤ ‖τ x‖) {x : E} (hx : S < ‖x‖) :
    twoPointPolarization H τ f x = 0 := by
  classical
  by_cases hH : x ∈ H
  · have hτ : f (τ x) = 0 := hzero (τ x) (hx.trans_le (hRadial x hH))
    simp only [twoPointPolarization, if_pos hH, hzero x hx, hτ, max_self]
  · rw [twoPointPolarization, if_neg hH, hzero x hx]
    exact min_eq_left (hf (τ x))

end Normed

end FaberKrahnDevelopment
