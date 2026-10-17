module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RadialPotentialCenter
public import EuclideanReflectionContraction

/-!
# The actual radial potential kernel under affine reflection

SOURCE_DRAFT: not registered or native checked.
The explicit squared-distance identity gives a strictly positive kernel
gap when both the center and the point are strictly on the chosen side.
The chosen radial potential also transports exactly under reflection.
No polarization branch, center maximality or symmetry is assumed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace RealInnerProductSpace

namespace Buckling.RadialKernelReflection

open FaberKrahnDevelopment.EuclideanReflection RadialPotentialCenter

lemma distance_to_reflection_ge (ν : UnitNormal) (c : ℝ) {p x : Space}
    (hp : c ≤ inner ℝ (ν : Space) p) (hx : c ≤ inner ℝ (ν : Space) x) :
    dist p x ≤ dist p (reflection ν c x) := by
  have hprod : 0 ≤ (c - inner ℝ (ν : Space) p) * (c - inner ℝ (ν : Space) x) :=
    mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hp) (sub_nonpos.mpr hx)
  have he := reflection_cross_dist_sq_sub ν c p x
  nlinarith [show 0 ≤ dist p x from dist_nonneg,
    show 0 ≤ dist p (reflection ν c x) from dist_nonneg]

lemma distance_to_reflection_gt (ν : UnitNormal) (c : ℝ) {p x : Space}
    (hp : c < inner ℝ (ν : Space) p) (hx : c < inner ℝ (ν : Space) x) :
    dist p x < dist p (reflection ν c x) := by
  have hprod : 0 < (c - inner ℝ (ν : Space) p) * (c - inner ℝ (ν : Space) x) :=
    mul_pos_of_neg_of_neg (sub_neg.mpr hp) (sub_neg.mpr hx)
  have he := reflection_cross_dist_sq_sub ν c p x
  nlinarith [show 0 ≤ dist p x from dist_nonneg,
    show 0 ≤ dist p (reflection ν c x) from dist_nonneg]

lemma kernel_reflection_le (ν : UnitNormal) (c : ℝ) {p x : Space}
    (hp : c ≤ inner ℝ (ν : Space) p) (hx : c ≤ inner ℝ (ν : Space) x) :
    kernel (reflection ν c x - p) ≤ kernel (x - p) := by
  have hd : ‖x - p‖ ≤ ‖reflection ν c x - p‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using distance_to_reflection_ge ν c hp hx
  exact one_div_le_one_div_of_le (by positivity : 0 < 1 + ‖x - p‖)
    (add_le_add le_rfl hd)

lemma kernel_reflection_lt (ν : UnitNormal) (c : ℝ) {p x : Space}
    (hp : c < inner ℝ (ν : Space) p) (hx : c < inner ℝ (ν : Space) x) :
    kernel (reflection ν c x - p) < kernel (x - p) := by
  have hd : ‖x - p‖ < ‖reflection ν c x - p‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using distance_to_reflection_gt ν c hp hx
  exact one_div_lt_one_div_of_lt (by positivity : 0 < 1 + ‖x - p‖)
    (add_lt_add_of_le_of_lt le_rfl hd)

def gap (ν : UnitNormal) (c : ℝ) (p x : Space) : ℝ :=
  kernel (x - p) - kernel (reflection ν c x - p)

lemma gap_nonneg (ν : UnitNormal) (c : ℝ) {p x : Space}
    (hp : c ≤ inner ℝ (ν : Space) p) (hx : c ≤ inner ℝ (ν : Space) x) :
    0 ≤ gap ν c p x := sub_nonneg.mpr (kernel_reflection_le ν c hp hx)

lemma gap_pos (ν : UnitNormal) (c : ℝ) {p x : Space}
    (hp : c < inner ℝ (ν : Space) p) (hx : c < inner ℝ (ν : Space) x) :
    0 < gap ν c p x := sub_pos.mpr (kernel_reflection_lt ν c hp hx)

lemma abs_gap_le_one (ν : UnitNormal) (c : ℝ) (p x : Space) :
    |gap ν c p x| ≤ 1 := by
  apply abs_le.mpr
  have h1 := kernel_pos (x - p)
  have h2 := kernel_pos (reflection ν c x - p)
  have h3 := kernel_le_one (x - p)
  have h4 := kernel_le_one (reflection ν c x - p)
  constructor <;> dsimp [gap] <;> linarith

lemma kernel_reflection_swap (ν : UnitNormal) (c : ℝ) (p x : Space) :
    kernel (reflection ν c x - p) = kernel (x - reflection ν c p) := by
  have hd := (reflection_isometry ν c).dist_eq x (reflection ν c p)
  simp only [reflection_reflection, dist_eq_norm] at hd
  exact congrArg (fun a : ℝ => 1 / (1 + a)) hd

lemma kernel_reflection_both (ν : UnitNormal) (c : ℝ) (p x : Space) :
    kernel (reflection ν c x - reflection ν c p) = kernel (x - p) := by
  have hd := (reflection_isometry ν c).dist_eq x p
  simp only [dist_eq_norm] at hd
  exact congrArg (fun a : ℝ => 1 / (1 + a)) hd

/-- The reflected density remains genuinely L1. -/
lemma integrable_reflected {U : Space → ℝ} (hU : Integrable U volume)
    (ν : UnitNormal) (c : ℝ) :
    Integrable (fun x => U (reflection ν c x)) volume :=
  (reflection_measurePreserving ν c).integrable_comp_of_integrable hU

/-- Actual reflection of the density is exactly reflection of the point
in its actual radial potential. This is a true change of variables. -/
theorem potential_reflected_density (ν : UnitNormal) (c : ℝ)
    (U : Space → ℝ) (p : Space) :
    potential (fun x => U (reflection ν c x)) p = potential U (reflection ν c p) := by
  let e : Space ≃ᵐ Space := MeasurableEquiv.ofInvolutive (reflection ν c)
    (reflection_involutive ν c) (reflection_measurable ν c)
  calc
    potential (fun x => U (reflection ν c x)) p =
        ∫ x, U (reflection ν c x) *
          kernel (reflection ν c x - reflection ν c p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change U (reflection ν c x) * kernel (x - p) =
          U (reflection ν c x) * kernel (reflection ν c x - reflection ν c p)
        rw [kernel_reflection_both]
    _ = potential U (reflection ν c p) :=
      (reflection_measurePreserving ν c).integral_comp e.measurableEmbedding
        (fun x => U x * kernel (x - reflection ν c p))

end Buckling.RadialKernelReflection

end

end
