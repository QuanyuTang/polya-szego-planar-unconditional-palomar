module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EuclideanReflection
public import Mathlib.Tactic.Module

/-!
# Explicit reflection formula and cross-halfspace distance contraction

SOURCE_DRAFT (2026-10-17), not compiled. This file is isolated from production.
The imported reflection is constructed from Mathlib orthogonal reflection and
translation, with a genuine unit normal. No geometric contraction assumption
or theorem-shaped result bundle is used below.

The closed halfspace is `c ≤ ⟪ν, x⟫`, so for a cross-side pair the signed
factors satisfy `c - ⟪ν, x⟫ ≤ 0 ≤ c - ⟪ν, y⟫`. The exact squared-distance
difference is `4 * (c - ⟪ν, x⟫) * (c - ⟪ν, y⟫)`.

Actual Lean elaboration and axiom inspection remain necessary. This module
does not assert a Sobolev estimate, Schwarz rearrangement, or Faber--Krahn.
-/

@[expose] public section

noncomputable section

open Set
open scoped RealInnerProductSpace InnerProductSpace

namespace FaberKrahnDevelopment.EuclideanReflection

/-- The concrete linear reflection subtracts twice the normal component. -/
lemma linearReflection_eq_sub_smul (ν : UnitNormal) (x : Plane) :
    linearReflection ν x = x - (2 * ⟪(ν : Plane), x⟫_ℝ) • (ν : Plane) := by
  have hproj : (ℝ ∙ (ν : Plane)).starProjection x =
      ⟪(ν : Plane), x⟫_ℝ • (ν : Plane) :=
    Submodule.starProjection_unit_singleton ℝ ν.property x
  change (ℝ ∙ (ν : Plane))ᗮ.reflection x =
    x - (2 * ⟪(ν : Plane), x⟫_ℝ) • (ν : Plane)
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_apply, hproj]
  module

/-- The affine reflection written as a normal displacement from the point. -/
lemma reflection_eq_add_smul (ν : UnitNormal) (c : ℝ) (x : Plane) :
    reflection ν c x = x + (2 * (c - ⟪(ν : Plane), x⟫_ℝ)) • (ν : Plane) := by
  simp only [reflection, linearReflection_eq_sub_smul, inner_sub_right,
    real_inner_smul_right, inner_normal_self, mul_one]
  module

lemma reflection_eq_sub_smul (ν : UnitNormal) (c : ℝ) (x : Plane) :
    reflection ν c x = x - (2 * (⟪(ν : Plane), x⟫_ℝ - c)) • (ν : Plane) := by
  rw [reflection_eq_add_smul]
  module

/-- Expansion of an actual displacement in a unit normal direction. -/
lemma norm_sub_smul_normal_sq (ν : UnitNormal) (z : Plane) (t : ℝ) :
    ‖z - t • (ν : Plane)‖ ^ 2 =
      ‖z‖ ^ 2 - 2 * t * ⟪(ν : Plane), z⟫_ℝ + t ^ 2 := by
  have hnorm : ‖t • (ν : Plane)‖ ^ 2 = t ^ 2 := by
    rw [norm_smul, ν.property, mul_one, Real.norm_eq_abs, sq_abs]
  rw [norm_sub_sq_real, real_inner_smul_right,
    real_inner_comm z (ν : Plane), hnorm]
  ring

/-- Exact squared-distance difference; no halfspace membership is assumed. -/
lemma reflection_cross_dist_sq_sub (ν : UnitNormal) (c : ℝ) (x y : Plane) :
    dist x (reflection ν c y) ^ 2 - dist x y ^ 2 =
      4 * (c - ⟪(ν : Plane), x⟫_ℝ) * (c - ⟪(ν : Plane), y⟫_ℝ) := by
  have hvec :
      x - (y - (2 * (⟪(ν : Plane), y⟫_ℝ - c)) • (ν : Plane)) =
        (x - y) - (2 * (c - ⟪(ν : Plane), y⟫_ℝ)) • (ν : Plane) := by
    module
  rw [dist_eq_norm, reflection_eq_sub_smul, hvec,
    norm_sub_smul_normal_sq, dist_eq_norm, inner_sub_right]
  ring

/-- Contraction for points in the two weak opposite closed halfspaces. -/
lemma reflection_cross_dist_le_of_le (ν : UnitNormal) (c : ℝ) (x y : Plane)
    (hx : c ≤ ⟪(ν : Plane), x⟫_ℝ) (hy : ⟪(ν : Plane), y⟫_ℝ ≤ c) :
    dist x (reflection ν c y) ≤ dist x y := by
  have hproduct : (c - ⟪(ν : Plane), x⟫_ℝ) *
      (c - ⟪(ν : Plane), y⟫_ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) (sub_nonneg.mpr hy)
  have hdiff := reflection_cross_dist_sq_sub ν c x y
  apply le_of_sq_le_sq _ dist_nonneg
  nlinarith

/-- The precise geometric input expected by `PolarizationLipschitz`.
The orientation uses the closed positive halfspace from `EuclideanReflection`. -/
lemma reflection_cross_dist_le (ν : UnitNormal) (c : ℝ) :
    ∀ x y, x ∈ halfspace ν c → y ∉ halfspace ν c →
      dist x (reflection ν c y) ≤ dist x y := by
  intro x y hx hy
  change c ≤ ⟪(ν : Plane), x⟫_ℝ at hx
  change ¬ c ≤ ⟪(ν : Plane), y⟫_ℝ at hy
  exact reflection_cross_dist_le_of_le ν c x y hx (le_of_lt (lt_of_not_ge hy))

/-- When the positive side is oriented towards the origin, its offset is nonpositive. -/
lemma zero_mem_halfspace_iff (ν : UnitNormal) (c : ℝ) :
    (0 : Plane) ∈ halfspace ν c ↔ c ≤ 0 := by
  simp only [halfspace, mem_setOf_eq, inner_zero_right]

/-- Exact radial squared-norm change under the concrete affine reflection. -/
lemma reflection_norm_sq_sub (ν : UnitNormal) (c : ℝ) (x : Plane) :
    ‖reflection ν c x‖ ^ 2 - ‖x‖ ^ 2 =
      4 * c * (c - ⟪(ν : Plane), x⟫_ℝ) := by
  simpa only [dist_zero_left, inner_zero_right, sub_zero] using
    reflection_cross_dist_sq_sub ν c (0 : Plane) x

/-- A point on the origin-containing side is no farther from the origin than
its reflected partner. This is the orientation used by radial polarization. -/
lemma norm_le_norm_reflection_of_mem (ν : UnitNormal) (c : ℝ)
    (hc : c ≤ 0) {x : Plane} (hx : x ∈ halfspace ν c) :
    ‖x‖ ≤ ‖reflection ν c x‖ := by
  change c ≤ ⟪(ν : Plane), x⟫_ℝ at hx
  have hproduct : 0 ≤ c * (c - ⟪(ν : Plane), x⟫_ℝ) :=
    mul_nonneg_of_nonpos_of_nonpos hc (sub_nonpos.mpr hx)
  have hdiff := reflection_norm_sq_sub ν c x
  apply le_of_sq_le_sq _ (norm_nonneg _)
  nlinarith

/-- For a point on the other side, reflection towards the origin cannot
increase its distance from the origin. -/
lemma norm_reflection_le_of_le (ν : UnitNormal) (c : ℝ)
    (hc : c ≤ 0) {x : Plane} (hx : ⟪(ν : Plane), x⟫_ℝ ≤ c) :
    ‖reflection ν c x‖ ≤ ‖x‖ := by
  have hproduct : c * (c - ⟪(ν : Plane), x⟫_ℝ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hc (sub_nonneg.mpr hx)
  have hdiff := reflection_norm_sq_sub ν c x
  apply le_of_sq_le_sq _ (norm_nonneg _)
  nlinarith

end FaberKrahnDevelopment.EuclideanReflection

end

end
