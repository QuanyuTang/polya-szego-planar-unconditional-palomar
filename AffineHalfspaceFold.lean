module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizedOpenDomain
public import EuclideanReflectionContraction
public import Mathlib.Topology.Order.Lattice

/-!
# Actual folding into an arbitrary closed affine halfspace

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The actual fold moves x by twice its negative signed distance in the
given actual unit-normal direction. It fixes the closed chosen halfspace,
equals the actual affine reflection on the other side, and is continuous.
Its image of every set Omega is exactly the chosen-side part of the union
of Omega and its actual reflected preimage. No openness, connectedness,
boundedness, or sign of the affine offset is assumed for that equality.

The normal-push identities use the actual unit-normal norm and inner
product, so strict-side membership and the exact displacement distance
are produced rather than taken as geometric hypotheses.
-/

@[expose] public section

noncomputable section

open Set
open scoped RealInnerProductSpace InnerProductSpace

namespace FaberKrahnDevelopment.AffineHalfspaceFold

open EuclideanReflection PolarizedOpenDomain

def fold (ν : UnitNormal) (c : ℝ) (x : Plane) : Plane :=
  x + (2 * max (c - ⟪(ν : Plane), x⟫_ℝ) 0) • (ν : Plane)

lemma continuous_fold (ν : UnitNormal) (c : ℝ) : Continuous (fold ν c) := by
  have hi : Continuous (fun x : Plane => ⟪(ν : Plane), x⟫_ℝ) :=
    continuous_const.inner continuous_id
  have hm : Continuous (fun x : Plane => max (c - ⟪(ν : Plane), x⟫_ℝ) 0) :=
    (continuous_const.fun_sub hi).sup continuous_const
  have hc : Continuous (fun x : Plane => (2 : ℝ) * max (c - ⟪(ν : Plane), x⟫_ℝ) 0) :=
    continuous_const.fun_mul hm
  exact continuous_id.fun_add (hc.fun_smul continuous_const)

lemma fold_eq_self_of_mem (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : x ∈ halfspace ν c) : fold ν c x = x := by
  change c ≤ ⟪(ν : Plane), x⟫_ℝ at hx
  simp only [fold, max_eq_right (sub_nonpos.mpr hx), mul_zero, zero_smul, add_zero]

/-- The weak opposite side is allowed, since the actual reflection fixes
the boundary. This avoids introducing a strictness condition at the fold. -/
lemma fold_eq_reflection_of_le (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : ⟪(ν : Plane), x⟫_ℝ ≤ c) : fold ν c x = reflection ν c x := by
  rw [reflection_eq_add_smul]
  simp only [fold, max_eq_left (sub_nonneg.mpr hx)]

lemma fold_eq_reflection_of_not_mem (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : x ∉ halfspace ν c) : fold ν c x = reflection ν c x := by
  change ¬ c ≤ ⟪(ν : Plane), x⟫_ℝ at hx
  exact fold_eq_reflection_of_le ν c (lt_of_not_ge hx).le

lemma fold_eq_self_or_reflection (ν : UnitNormal) (c : ℝ) (x : Plane) :
    fold ν c x = x ∨ fold ν c x = reflection ν c x := by
  by_cases hx : x ∈ halfspace ν c
  · exact Or.inl (fold_eq_self_of_mem ν c hx)
  · exact Or.inr (fold_eq_reflection_of_not_mem ν c hx)

lemma inner_fold (ν : UnitNormal) (c : ℝ) (x : Plane) :
    ⟪(ν : Plane), fold ν c x⟫_ℝ =
      ⟪(ν : Plane), x⟫_ℝ + 2 * max (c - ⟪(ν : Plane), x⟫_ℝ) 0 := by
  simp only [fold, inner_add_right, real_inner_smul_right, inner_normal_self, mul_one]

lemma fold_mem_halfspace (ν : UnitNormal) (c : ℝ) (x : Plane) :
    fold ν c x ∈ halfspace ν c := by
  by_cases hx : x ∈ halfspace ν c
  · rw [fold_eq_self_of_mem ν c hx]
    exact hx
  · rw [fold_eq_reflection_of_not_mem ν c hx, reflection_mem_halfspace_iff]
    change ¬ c ≤ ⟪(ν : Plane), x⟫_ℝ at hx
    exact (lt_of_not_ge hx).le

lemma fold_fold (ν : UnitNormal) (c : ℝ) (x : Plane) :
    fold ν c (fold ν c x) = fold ν c x :=
  fold_eq_self_of_mem ν c (fold_mem_halfspace ν c x)

lemma fold_reflection_of_mem (ν : UnitNormal) (c : ℝ) {p : Plane}
    (hp : p ∈ halfspace ν c) : fold ν c (reflection ν c p) = p := by
  have hσ : ⟪(ν : Plane), reflection ν c p⟫_ℝ ≤ c := by
    rw [inner_reflection]
    change c ≤ ⟪(ν : Plane), p⟫_ℝ at hp
    linarith
  rw [fold_eq_reflection_of_le ν c hσ, reflection_reflection]

/-- Every folded point coming from Omega lies in the actual union with its
reflected preimage. Omega is arbitrary here. -/
lemma fold_mem_union (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) {x : Plane}
    (hx : x ∈ Ω) : fold ν c x ∈ Ω ∪ reflection ν c ⁻¹' Ω := by
  by_cases hH : x ∈ halfspace ν c
  · left
    rwa [fold_eq_self_of_mem ν c hH]
  · right
    change reflection ν c (fold ν c x) ∈ Ω
    rwa [fold_eq_reflection_of_not_mem ν c hH, reflection_reflection]

/-- An actual preimage in Omega for every actual union point on the closed
chosen side. Boundary points are included without extra assumptions. -/
theorem exists_fold_preimage (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) {p : Plane}
    (hp : p ∈ Ω ∪ reflection ν c ⁻¹' Ω) (hH : p ∈ halfspace ν c) :
    ∃ a ∈ Ω, fold ν c a = p := by
  rcases hp with hp | hp
  · exact ⟨p, hp, fold_eq_self_of_mem ν c hH⟩
  · exact ⟨reflection ν c p, hp, fold_reflection_of_mem ν c hH⟩

theorem exists_fold_preimage_of_mem_strictSide (ν : UnitNormal) (c : ℝ)
    (Ω : Set Plane) {p : Plane} (hp : p ∈ Ω ∪ reflection ν c ⁻¹' Ω)
    (hS : p ∈ strictSide ν c) : ∃ a ∈ Ω, fold ν c a = p := by
  apply exists_fold_preimage ν c Ω hp
  change c < ⟪(ν : Plane), p⟫_ℝ at hS
  exact hS.le

theorem fold_image_eq (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) :
    fold ν c '' Ω = (Ω ∪ reflection ν c ⁻¹' Ω) ∩ halfspace ν c := by
  ext p
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨fold_mem_union ν c Ω ha, fold_mem_halfspace ν c a⟩
  · rintro ⟨hp, hH⟩
    obtain ⟨a, ha, hfa⟩ := exists_fold_preimage ν c Ω hp hH
    exact ⟨a, ha, hfa⟩

lemma inner_normal_push (ν : UnitNormal) (x : Plane) (t : ℝ) :
    ⟪(ν : Plane), x + t • (ν : Plane)⟫_ℝ = ⟪(ν : Plane), x⟫_ℝ + t := by
  simp only [inner_add_right, real_inner_smul_right, inner_normal_self, mul_one]

lemma normal_push_mem_strictSide (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : x ∈ halfspace ν c) {t : ℝ} (ht : 0 < t) :
    x + t • (ν : Plane) ∈ strictSide ν c := by
  change c < ⟪(ν : Plane), x + t • (ν : Plane)⟫_ℝ
  rw [inner_normal_push]
  change c ≤ ⟪(ν : Plane), x⟫_ℝ at hx
  linarith

lemma dist_normal_push (ν : UnitNormal) (x : Plane) (t : ℝ) :
    dist (x + t • (ν : Plane)) x = |t| := by
  rw [dist_eq_norm, add_sub_cancel_left, norm_smul, ν.property, mul_one, Real.norm_eq_abs]

lemma continuous_normal_push (ν : UnitNormal) (t : ℝ) :
    Continuous (fun x : Plane => x + t • (ν : Plane)) :=
  continuous_id.fun_add continuous_const

lemma continuous_push_parameter (ν : UnitNormal) (x : Plane) :
    Continuous (fun t : ℝ => x + t • (ν : Plane)) :=
  continuous_const.fun_add (continuous_id.fun_smul continuous_const)

end FaberKrahnDevelopment.AffineHalfspaceFold

end

end
