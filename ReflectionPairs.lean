module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EuclideanReflectionContraction

/-!
# A concrete origin-oriented reflection exchanging a radial pair

SOURCE_DRAFT (2026-10-17), uncompiled and not imported by production.

Two distinct points determine their perpendicular-bisector reflection. If the
first point has smaller norm, the chosen positive side contains the origin
strictly. All geometric data are explicitly constructed from the two points.
Consequently inequalities against all such reflections imply monotonicity
between points of strictly different radii. Producing those inequalities for
an actual orbit minimizer remains a separate proof obligation.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace RealInnerProductSpace

namespace FaberKrahnDevelopment.EuclideanReflection

/-- Unit normal directed from the second point towards the first. -/
def pairNormal (x y : Plane) (hxy : x ≠ y) : UnitNormal := by
  refine ⟨‖x - y‖⁻¹ • (x - y), ?_⟩
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
    inv_mul_cancel₀ hd]

lemma norm_sub_smul_pairNormal (x y : Plane) (hxy : x ≠ y) :
    ‖x - y‖ • (pairNormal x y hxy : Plane) = x - y := by
  have hd : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  change ‖x - y‖ • (‖x - y‖⁻¹ • (x - y)) = x - y
  rw [smul_smul, mul_inv_cancel₀ hd, one_smul]

/-- The normal coordinate of the midpoint of the two points. -/
def pairOffset (x y : Plane) (hxy : x ≠ y) : ℝ :=
  (⟪(pairNormal x y hxy : Plane), x⟫_ℝ +
    ⟪(pairNormal x y hxy : Plane), y⟫_ℝ) / 2

lemma inner_pairNormal_sub (x y : Plane) (hxy : x ≠ y) :
    ⟪(pairNormal x y hxy : Plane), x⟫_ℝ -
        ⟪(pairNormal x y hxy : Plane), y⟫_ℝ = ‖x - y‖ := by
  calc
    ⟪(pairNormal x y hxy : Plane), x⟫_ℝ -
        ⟪(pairNormal x y hxy : Plane), y⟫_ℝ =
        ⟪(pairNormal x y hxy : Plane), x - y⟫_ℝ := by rw [inner_sub_right]
    _ = ⟪(pairNormal x y hxy : Plane),
        ‖x - y‖ • (pairNormal x y hxy : Plane)⟫_ℝ :=
      congrArg (fun z : Plane => ⟪(pairNormal x y hxy : Plane), z⟫_ℝ)
        (norm_sub_smul_pairNormal x y hxy).symm
    _ = ‖x - y‖ := by rw [real_inner_smul_right, inner_normal_self, mul_one]

lemma pair_reflection_eq (x y : Plane) (hxy : x ≠ y) :
    reflection (pairNormal x y hxy) (pairOffset x y hxy) x = y := by
  have hinner := inner_pairNormal_sub x y hxy
  have hcoeff : 2 * (pairOffset x y hxy -
      ⟪(pairNormal x y hxy : Plane), x⟫_ℝ) = -‖x - y‖ := by
    unfold pairOffset
    linarith
  rw [reflection_eq_add_smul, hcoeff, neg_smul, norm_sub_smul_pairNormal]
  abel

lemma left_mem_pair_halfspace (x y : Plane) (hxy : x ≠ y) :
    x ∈ halfspace (pairNormal x y hxy) (pairOffset x y hxy) := by
  have hinner := inner_pairNormal_sub x y hxy
  have hd := norm_nonneg (x - y)
  change pairOffset x y hxy ≤ ⟪(pairNormal x y hxy : Plane), x⟫_ℝ
  unfold pairOffset
  linarith

/-- The signed offset is strictly negative exactly in the needed orientation
when the first radius is strictly smaller. -/
lemma pairOffset_neg_of_norm_lt (x y : Plane) (hxy : x ≠ y)
    (h : ‖x‖ < ‖y‖) : pairOffset x y hxy < 0 := by
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hnorm : ‖x‖ ^ 2 - ‖y‖ ^ 2 = ⟪x - y, x + y⟫_ℝ := by
    simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y x]
    ring
  have hprod : 2 * ‖x - y‖ * pairOffset x y hxy = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
    calc
      2 * ‖x - y‖ * pairOffset x y hxy =
          ‖x - y‖ * (⟪(pairNormal x y hxy : Plane), x⟫_ℝ +
            ⟪(pairNormal x y hxy : Plane), y⟫_ℝ) := by
        unfold pairOffset
        ring
      _ = ⟪‖x - y‖ • (pairNormal x y hxy : Plane), x + y⟫_ℝ := by
        rw [real_inner_smul_left, inner_add_right]
      _ = ⟪x - y, x + y⟫_ℝ := by rw [norm_sub_smul_pairNormal]
      _ = ‖x‖ ^ 2 - ‖y‖ ^ 2 := hnorm.symm
  have hsq : ‖x‖ ^ 2 - ‖y‖ ^ 2 < 0 := by nlinarith [norm_nonneg x]
  have hnegative : 2 * ‖x - y‖ * pairOffset x y hxy < 0 := by
    rw [hprod]
    exact hsq
  by_contra hn
  have hc : 0 ≤ pairOffset x y hxy := le_of_not_gt hn
  have hnonnegative : 0 ≤ 2 * ‖x - y‖ * pairOffset x y hxy :=
    mul_nonneg (mul_nonneg (by norm_num) hd.le) hc
  linarith

/-- Reflected-order inequalities for every strict origin-containing halfspace
force the expected pointwise order between unequal radii. No rearranged
function is postulated by this lemma. -/
lemma radial_order_of_reflection_order (f : Plane → ℝ)
    (horder : ∀ (ν : UnitNormal) (c : ℝ), c < 0 →
      ∀ x ∈ halfspace ν c, f (reflection ν c x) ≤ f x)
    {x y : Plane} (h : ‖x‖ < ‖y‖) : f y ≤ f x := by
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact (lt_irrefl _ h)
  have hresult := horder (pairNormal x y hxy) (pairOffset x y hxy)
    (pairOffset_neg_of_norm_lt x y hxy h) x (left_mem_pair_halfspace x y hxy)
  rwa [pair_reflection_eq] at hresult

end FaberKrahnDevelopment.EuclideanReflection

end

end
