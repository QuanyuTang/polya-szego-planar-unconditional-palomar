module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import CompactLipOriginalH01

/-!
# Real energies of the actual compact Lipschitz H01 tuple

SOURCE_DRAFT: not registered or native checked. The actual zero-extension
isometry and the already identified representatives relate the unchanged
original energies to real whole-space integrals. The gradient integral is
genuinely finite, as each actual coordinate is in L2. No energy identity or
integrability is an additional hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal RealInnerProductSpace InnerProductSpace

namespace Buckling.CompactLipOriginalH01

lemma norm_fderiv_sq_eq (L : Plane →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = L (EuclideanSpace.single 0 1) ^ 2 + L (EuclideanSpace.single 1 1) ^ 2 := by
  set w := (InnerProductSpace.toDual ℝ Plane).symm L with hw
  have hL : L = InnerProductSpace.toDual ℝ Plane w := by simp [hw]
  have hn : ‖L‖ = ‖w‖ := by rw [hL, LinearIsometryEquiv.norm_map]
  have hi : ∀ i, L (EuclideanSpace.single i 1) = w i := by
    intro i
    rw [hL, InnerProductSpace.toDual_apply_apply]
    simp [EuclideanSpace.inner_single_right]
  rw [hn, hi, hi, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

lemma integrable_gradient_sq {G : Plane → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) (hc : HasCompactSupport G) :
    Integrable (fun x => ‖fderiv ℝ G x‖ ^ 2) (volume : Measure Plane) := by
  have heq : (fun x => ‖fderiv ℝ G x‖ ^ 2) =
      (fun x => coordinate G 0 x ^ 2 + coordinate G 1 x ^ 2) := by
    funext x
    exact norm_fderiv_sq_eq (fderiv ℝ G x)
  rw [heq]
  exact (coordinate_memLp hG hc 0).integrable_sq.add
    (coordinate_memLp hG hc 1).integrable_sq

lemma energy0_tuple {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) :
    energy0 (tuple Ω hG hc) = ∫ x, G x ^ 2 := by
  unfold energy0
  rw [← (lpExtendByZero volume 2 Ω hΩ.measurableSet).norm_map (tuple Ω hG hc).1,
    L2.norm_sq_eq_integral_sq]
  apply integral_congr_ae
  exact (tuple_extend_value_ae hΩ hG hc hs).mono fun x hx => congrArg (fun r : ℝ => r ^ 2) hx

lemma norm_tuple_coordinate_sq {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) (i : Fin 2) :
    ‖(tuple Ω hG hc).2 i‖ ^ 2 = ∫ x, coordinate G i x ^ 2 := by
  rw [← (lpExtendByZero volume 2 Ω hΩ.measurableSet).norm_map ((tuple Ω hG hc).2 i),
    L2.norm_sq_eq_integral_sq]
  apply integral_congr_ae
  exact (tuple_extend_coordinate_ae hΩ hG hc hs i).mono fun x hx => congrArg (fun r : ℝ => r ^ 2) hx

lemma energy1_tuple {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) :
    energy1 (tuple Ω hG hc) = ∫ x, ‖fderiv ℝ G x‖ ^ 2 := by
  simp only [energy1, Fin.sum_univ_two, norm_tuple_coordinate_sq hΩ hG hc hs]
  rw [← integral_add (coordinate_memLp hG hc 0).integrable_sq
    (coordinate_memLp hG hc 1).integrable_sq]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => (norm_fderiv_sq_eq (fderiv ℝ G x)).symm

end Buckling.CompactLipOriginalH01

end

end
