module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationMeasure
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Two-point polarization preserves a Lipschitz constant

Development status (2026-10-17): SOURCE_DRAFT, not yet compiled. This isolated
module uses the literal `twoPointPolarization` definition from the separate
measure module, whose successful compilation is not assumed here.

The geometric inputs are an isometric involution and the cross-side distance
contraction of a reflection. Same-side pairs use max/min Lipschitz estimates.
For opposite sides, all four possible source-value pairs satisfy the original
Lipschitz bound. No Sobolev energy or Faber--Krahn estimate is an input.

This module does not construct the Euclidean reflection or establish the
cross-side contraction for a concrete halfspace. Those geometric producers
remain separate work.
-/

@[expose] public section

open scoped NNReal

namespace FaberKrahnDevelopment

variable {α : Type*} [PseudoMetricSpace α]

/-- Under an isometric involution the two cross distances agree. -/
lemma dist_reflected_left_eq {τ : α → α} (hτ : Isometry τ)
    (hInv : Function.Involutive τ) (x y : α) :
    dist (τ x) y = dist x (τ y) := by
  simpa only [hInv y] using hτ.dist_eq x (τ y)

/-- A max/min pair satisfies a common distance bound if each of the four
possible original-value pairs satisfies that bound. -/
lemma dist_max_min_le_of_four {a b c d r : ℝ}
    (hac : dist a c ≤ r) (had : dist a d ≤ r)
    (hbc : dist b c ≤ r) (hbd : dist b d ≤ r) :
    dist (max a b) (min c d) ≤ r := by
  rcases max_choice a b with hmax | hmax
  · rw [hmax]
    rcases min_choice c d with hmin | hmin
    · rw [hmin]
      exact hac
    · rw [hmin]
      exact had
  · rw [hmax]
    rcases min_choice c d with hmin | hmin
    · rw [hmin]
      exact hbc
    · rw [hmin]
      exact hbd

/-- The original Lipschitz estimate survives for a pair on opposite sides.
The reflected/reflected pair uses isometry, and the remaining reflected pair
uses the cross-distance identity from involutivity. -/
lemma dist_twoPointPolarization_cross_le {H : Set α} {τ : α → α}
    {f : α → ℝ} {K : ℝ≥0} (hτ : Isometry τ) (hInv : Function.Involutive τ)
    (hCross : ∀ x y, x ∈ H → y ∉ H → dist x (τ y) ≤ dist x y)
    (hf : LipschitzWith K f) {x y : α} (hx : x ∈ H) (hy : y ∉ H) :
    dist (twoPointPolarization H τ f x) (twoPointPolarization H τ f y) ≤
      (K : ℝ) * dist x y := by
  classical
  simp only [twoPointPolarization, if_pos hx, if_neg hy]
  apply dist_max_min_le_of_four
  · exact hf.dist_le_mul x y
  · exact (hf.dist_le_mul x (τ y)).trans
      (mul_le_mul_of_nonneg_left (hCross x y hx hy) K.2)
  · calc
      dist (f (τ x)) (f y) ≤ (K : ℝ) * dist (τ x) y := hf.dist_le_mul (τ x) y
      _ = (K : ℝ) * dist x (τ y) := by rw [dist_reflected_left_eq hτ hInv x y]
      _ ≤ (K : ℝ) * dist x y :=
        mul_le_mul_of_nonneg_left (hCross x y hx hy) K.2
  · simpa only [hτ.dist_eq x y] using hf.dist_le_mul (τ x) (τ y)

/-- An isometric reflection with cross-side distance contraction preserves
the Lipschitz constant of every real-valued Lipschitz function under two-point
max/min polarization. No measure-theoretic or energy estimate is assumed. -/
lemma lipschitzWith_twoPointPolarization {H : Set α} {τ : α → α}
    {f : α → ℝ} {K : ℝ≥0} (hτ : Isometry τ) (hInv : Function.Involutive τ)
    (hCross : ∀ x y, x ∈ H → y ∉ H → dist x (τ y) ≤ dist x y)
    (hf : LipschitzWith K f) :
    LipschitzWith K (twoPointPolarization H τ f) := by
  classical
  have hfτ : LipschitzWith K (fun x => f (τ x)) := by
    simpa only [mul_one, Function.comp_def] using hf.comp hτ.lipschitz
  have hmax : LipschitzWith K (fun x => max (f x) (f (τ x))) := by
    simpa only [max_self] using hf.max hfτ
  have hmin : LipschitzWith K (fun x => min (f x) (f (τ x))) := by
    simpa only [max_self] using hf.min hfτ
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ H
  · by_cases hy : y ∈ H
    · simpa only [twoPointPolarization, if_pos hx, if_pos hy] using hmax.dist_le_mul x y
    · exact dist_twoPointPolarization_cross_le hτ hInv hCross hf hx hy
  · by_cases hy : y ∈ H
    · calc
        dist (twoPointPolarization H τ f x) (twoPointPolarization H τ f y) =
            dist (twoPointPolarization H τ f y) (twoPointPolarization H τ f x) := dist_comm _ _
        _ ≤ (K : ℝ) * dist y x :=
          dist_twoPointPolarization_cross_le hτ hInv hCross hf hy hx
        _ = (K : ℝ) * dist x y := by rw [dist_comm y x]
    · simpa only [twoPointPolarization, if_neg hx, if_neg hy] using hmin.dist_le_mul x y

end FaberKrahnDevelopment
