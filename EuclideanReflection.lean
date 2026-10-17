module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Affine hyperplane reflections in the Euclidean plane

SOURCE_DRAFT (2026-10-17): drafted against the actual local Mathlib v4.28
sources, but not compiled yet. Quarantined from the production development.

The normal is a literal unit vector, not a package of geometric conclusions.
Reflection is constructed by translating to the hyperplane through zero,
applying Mathlib's orthogonal linear reflection, and translating back.
The halfspace is closed, so its fixed boundary must be removed before an
exact complement-swapping statement holds. That boundary is proved null
using the Haar-measure theorem for a proper linear subspace and translation.

These are geometric inputs for two-point polarization. No rearrangement
energy estimate, compactness, Faber--Krahn theorem, or manuscript root is
asserted here. Compilation and axiom inspection are still required before
any declaration in this file may be marked verified.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace InnerProductSpace

namespace FaberKrahnDevelopment.EuclideanReflection

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The ordinary unit normal vectors of the Euclidean plane. -/
abbrev UnitNormal := {ν : Plane // ‖ν‖ = 1}

/-- Linear reflection in the line orthogonal to the given normal. -/
def linearReflection (ν : UnitNormal) : Plane ≃ₗᵢ[ℝ] Plane :=
  (ℝ ∙ (ν : Plane))ᗮ.reflection

/-- Reflection in the affine line `⟪ν, x⟫ = c`. -/
def reflection (ν : UnitNormal) (c : ℝ) (x : Plane) : Plane :=
  c • (ν : Plane) + linearReflection ν (x - c • (ν : Plane))

/-- The closed halfspace on the positive side of the reflecting line. -/
def halfspace (ν : UnitNormal) (c : ℝ) : Set Plane :=
  {x | c ≤ ⟪(ν : Plane), x⟫_ℝ}

/-- The fixed hyperplane of the affine reflection. -/
def hyperplane (ν : UnitNormal) (c : ℝ) : Set Plane :=
  {x | ⟪(ν : Plane), x⟫_ℝ = c}

lemma inner_normal_self (ν : UnitNormal) : ⟪(ν : Plane), (ν : Plane)⟫_ℝ = 1 := by
  rw [real_inner_self_eq_norm_sq, ν.property]
  norm_num

@[simp] lemma linearReflection_normal (ν : UnitNormal) :
    linearReflection ν (ν : Plane) = -(ν : Plane) := by
  exact Submodule.reflection_orthogonalComplement_singleton_eq_neg (ν : Plane)

lemma inner_linearReflection (ν : UnitNormal) (x : Plane) :
    ⟪(ν : Plane), linearReflection ν x⟫_ℝ = -⟪(ν : Plane), x⟫_ℝ := by
  have h := (linearReflection ν).inner_map_map (ν : Plane) x
  rw [linearReflection_normal, inner_neg_left] at h
  linarith

lemma inner_reflection (ν : UnitNormal) (c : ℝ) (x : Plane) :
    ⟪(ν : Plane), reflection ν c x⟫_ℝ = 2 * c - ⟪(ν : Plane), x⟫_ℝ := by
  simp only [reflection, inner_add_right, inner_linearReflection, inner_sub_right,
    real_inner_smul_right, inner_normal_self]
  ring

@[simp] lemma reflection_reflection (ν : UnitNormal) (c : ℝ) (x : Plane) :
    reflection ν c (reflection ν c x) = x := by
  simp only [reflection, add_sub_cancel_left]
  simp only [linearReflection, Submodule.reflection_reflection]
  abel

lemma reflection_involutive (ν : UnitNormal) (c : ℝ) :
    Function.Involutive (reflection ν c) :=
  reflection_reflection ν c

lemma reflection_isometry (ν : UnitNormal) (c : ℝ) : Isometry (reflection ν c) := by
  apply Isometry.of_dist_eq
  intro x y
  simp only [reflection, dist_add_left, (linearReflection ν).dist_map, dist_sub_right]

lemma reflection_measurePreserving (ν : UnitNormal) (c : ℝ) :
    MeasurePreserving (reflection ν c) volume volume := by
  have hsub : MeasurePreserving (fun x : Plane => x - c • (ν : Plane)) volume volume :=
    measurePreserving_sub_right volume (c • (ν : Plane))
  have hlinear : MeasurePreserving (linearReflection ν) volume volume :=
    (linearReflection ν).measurePreserving
  have hadd : MeasurePreserving (fun x : Plane => c • (ν : Plane) + x) volume volume :=
    measurePreserving_add_left volume (c • (ν : Plane))
  change MeasurePreserving
    (fun x : Plane => c • (ν : Plane) + linearReflection ν (x - c • (ν : Plane)))
    volume volume
  simpa only [Function.comp_def] using hadd.comp (hlinear.comp hsub)

lemma reflection_measurable (ν : UnitNormal) (c : ℝ) : Measurable (reflection ν c) :=
  (reflection_measurePreserving ν c).measurable

lemma halfspace_isClosed (ν : UnitNormal) (c : ℝ) : IsClosed (halfspace ν c) := by
  exact isClosed_le continuous_const (continuous_const.inner continuous_id)

lemma halfspace_measurableSet (ν : UnitNormal) (c : ℝ) : MeasurableSet (halfspace ν c) :=
  (halfspace_isClosed ν c).measurableSet

lemma hyperplane_isClosed (ν : UnitNormal) (c : ℝ) : IsClosed (hyperplane ν c) := by
  exact isClosed_eq (continuous_const.inner continuous_id) continuous_const

lemma hyperplane_measurableSet (ν : UnitNormal) (c : ℝ) :
    MeasurableSet (hyperplane ν c) :=
  (hyperplane_isClosed ν c).measurableSet

/-- The affine hyperplane is the translate of the normal's orthogonal line. -/
lemma hyperplane_eq_preimage (ν : UnitNormal) (c : ℝ) :
    hyperplane ν c =
      (fun x : Plane => x - c • (ν : Plane)) ⁻¹'
        ((ℝ ∙ (ν : Plane))ᗮ : Set Plane) := by
  ext x
  change (⟪(ν : Plane), x⟫_ℝ = c) ↔
    x - c • (ν : Plane) ∈ (ℝ ∙ (ν : Plane))ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
    real_inner_smul_right, inner_normal_self, mul_one, sub_eq_zero]

lemma orthogonalLine_ne_top (ν : UnitNormal) : (ℝ ∙ (ν : Plane))ᗮ ≠ ⊤ := by
  intro htop
  have hmem : (ν : Plane) ∈ (ℝ ∙ (ν : Plane))ᗮ := by
    rw [htop]
    trivial
  have hzero : ⟪(ν : Plane), (ν : Plane)⟫_ℝ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  rw [inner_normal_self] at hzero
  norm_num at hzero

lemma hyperplane_volume_zero (ν : UnitNormal) (c : ℝ) : volume (hyperplane ν c) = 0 := by
  rw [hyperplane_eq_preimage]
  have hsub : MeasurePreserving (fun x : Plane => x - c • (ν : Plane)) volume volume :=
    measurePreserving_sub_right volume (c • (ν : Plane))
  rw [hsub.measure_preimage
    (Submodule.isClosed_orthogonal (ℝ ∙ (ν : Plane))).measurableSet.nullMeasurableSet]
  exact Measure.addHaar_submodule volume (ℝ ∙ (ν : Plane))ᗮ (orthogonalLine_ne_top ν)

lemma reflection_mem_halfspace_iff (ν : UnitNormal) (c : ℝ) (x : Plane) :
    reflection ν c x ∈ halfspace ν c ↔ ⟪(ν : Plane), x⟫_ℝ ≤ c := by
  change c ≤ ⟪(ν : Plane), reflection ν c x⟫_ℝ ↔ ⟪(ν : Plane), x⟫_ℝ ≤ c
  rw [inner_reflection]
  constructor <;> intro h <;> linarith

/-- The two closed sides differ from true complementary sides only on the fixed line. -/
lemma reflection_swap_off_hyperplane (ν : UnitNormal) (c : ℝ) (x : Plane)
    (hx : x ∉ hyperplane ν c) :
    reflection ν c x ∈ halfspace ν c ↔ x ∉ halfspace ν c := by
  rw [reflection_mem_halfspace_iff]
  change ⟪(ν : Plane), x⟫_ℝ ≤ c ↔ ¬ c ≤ ⟪(ν : Plane), x⟫_ℝ
  change ⟪(ν : Plane), x⟫_ℝ ≠ c at hx
  constructor
  · intro hle hge
    exact hx (le_antisymm hle hge)
  · intro hnot
    exact (lt_of_not_ge hnot).le

/-- Actual geometric a.e. side swapping, suitable as polarization input. -/
lemma reflection_ae_swap (ν : UnitNormal) (c : ℝ) :
    ∀ᵐ x ∂volume, reflection ν c x ∈ halfspace ν c ↔ x ∉ halfspace ν c := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hyperplane_volume_zero ν c)] with x hx
  exact reflection_swap_off_hyperplane ν c x hx

end FaberKrahnDevelopment.EuclideanReflection

end

end
