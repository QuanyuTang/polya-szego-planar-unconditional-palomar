module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import BoundedPolarizationOrbit
public import PolarizationMomentTransport
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Actual squared-radius moment decrease and its strict equality consequence

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.
The geometric ordering weight is the GLOBAL squared norm, never its clipped
version. The clipped weight is used only to produce an integrable continuous
moment functional, whose values agree with the global integral on functions
vanishing outside the common ball. Integrability of both weighted products is
derived from that identity and the actual bounded-continuous construction.

For a strict origin-containing halfspace, equality of these actual moments
forces reflection order: paired equality a.e. and a strict scalar sorting
inequality give order in the interior a.e.; the continuous violation set is
open and null, hence empty; the reflecting boundary is fixed pointwise.

No radial limit, Sobolev energy, rearrangement, Faber--Krahn, or equality
rigidity theorem is assumed here. All imported drafts still require actual
Lean elaboration and axiom inspection, as does this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal InnerProductSpace RealInnerProductSpace

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- Compactly supported weight for the continuous global BCF functional.
This weight is NOT used as the ordering weight in the transport theorem. -/
def clippedSquaredWeight (S : ℝ) : Plane → ℝ :=
  (Metric.closedBall (0 : Plane) S).indicator (fun x => ‖x‖ ^ 2)

lemma integrable_clippedSquaredWeight (S : ℝ) :
    Integrable (clippedSquaredWeight S) volume := by
  have hcont : Continuous (fun x : Plane => ‖x‖ ^ 2) := continuous_norm.pow 2
  have hlocal : IntegrableOn (fun x : Plane => ‖x‖ ^ 2)
      (Metric.closedBall (0 : Plane) S) volume :=
    hcont.continuousOn.integrableOn_compact (isCompact_closedBall (0 : Plane) S)
  exact hlocal.integrable_indicator Metric.isClosed_closedBall.measurableSet

/-- A literal continuous moment functional on whole-plane BCFs. -/
def clippedSquaredMoment (S : ℝ) (f : Plane →ᵇ ℝ) : ℝ :=
  weightedMoment volume (clippedSquaredWeight S) f

lemma continuous_clippedSquaredMoment (S : ℝ) :
    Continuous (clippedSquaredMoment S) :=
  continuous_weightedMoment (integrable_clippedSquaredWeight S)

/-- Pointwise agreement of clipped and global weighted products on common support. -/
lemma clippedSquaredWeight_mul_eq {f : Plane →ᵇ ℝ} {S : ℝ}
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (x : Plane) :
    clippedSquaredWeight S x * f x = f x * ‖x‖ ^ 2 := by
  classical
  by_cases hx : x ∈ Metric.closedBall (0 : Plane) S
  · simp only [clippedSquaredWeight, indicator_of_mem hx, mul_comm]
  · have hxR : S < ‖x‖ := by
      simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    simp only [clippedSquaredWeight, indicator_of_notMem hx, hfZ x hxR, zero_mul]

lemma clippedSquaredMoment_eq_integral {f : Plane →ᵇ ℝ} {S : ℝ}
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    clippedSquaredMoment S f = ∫ x, f x * ‖x‖ ^ 2 ∂volume := by
  unfold clippedSquaredMoment weightedMoment
  exact integral_congr_ae (Eventually.of_forall (clippedSquaredWeight_mul_eq hfZ))

/-- Global squared-radius product integrability is produced from the clipped
integrable weight and literal zero values outside the common ball. -/
lemma integrable_mul_norm_sq_of_commonSupport {f : Plane →ᵇ ℝ} {S : ℝ}
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    Integrable (fun x => f x * ‖x‖ ^ 2) volume :=
  (integrable_weight_mul_boundedContinuous (integrable_clippedSquaredWeight S) f).congr
    (Eventually.of_forall (clippedSquaredWeight_mul_eq hfZ))

namespace OriginHalfspace

/-- Concrete ordering of the GLOBAL squared-norm weight. -/
lemma norm_sq_le_reflection (s : OriginHalfspace) (x : Plane)
    (hx : x ∈ halfspace s.normal s.offset) :
    ‖x‖ ^ 2 ≤ ‖reflection s.normal s.offset x‖ ^ 2 :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (norm_le_norm_reflection_of_mem s.normal s.offset s.offset_nonpos hx)

/-- The squared-radius ordering is strict at interior points when `c < 0`. -/
lemma norm_sq_lt_reflection_of_inner_gt (s : OriginHalfspace)
    (hc : s.offset < 0) {x : Plane}
    (hx : s.offset < ⟪(s.normal : Plane), x⟫_ℝ) :
    ‖x‖ ^ 2 < ‖reflection s.normal s.offset x‖ ^ 2 := by
  have hdiff := reflection_norm_sq_sub s.normal s.offset x
  have hpos : 0 < s.offset * (s.offset - ⟪(s.normal : Plane), x⟫_ℝ) :=
    mul_pos_of_neg_of_neg hc (sub_neg.mpr hx)
  nlinarith

lemma boundedStep_zero_outside_ball (s : OriginHalfspace)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    ∀ x, S < ‖x‖ → s.boundedStep f hfL hfR x = 0 := by
  intro x hx
  exact s.step_eq_zero_of_radius_lt (fun z => (hfR z).1) hfZ hx

/-- Actual global moment decrease, with all integrability and geometry produced. -/
lemma integral_norm_sq_step_le (s : OriginHalfspace)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, s.step f x * ‖x‖ ^ 2 ∂volume) ≤ ∫ x, f x * ‖x‖ ^ 2 ∂volume := by
  have hpZ := s.boundedStep_zero_outside_ball hfL hfR hfZ
  have hfI := integrable_mul_norm_sq_of_commonSupport hfZ
  have hpI := integrable_mul_norm_sq_of_commonSupport hpZ
  exact integral_weighted_polarization_le
    (reflection_measurePreserving s.normal s.offset)
    (reflection_involutive s.normal s.offset)
    (reflection_ae_swap s.normal s.offset)
    (s.norm_sq_le_reflection) hfI hpI

/-- The continuous clipped functional agrees with both true moments here. -/
lemma clippedSquaredMoment_boundedStep_le (s : OriginHalfspace)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    clippedSquaredMoment S (s.boundedStep f hfL hfR) ≤ clippedSquaredMoment S f := by
  rw [clippedSquaredMoment_eq_integral (s.boundedStep_zero_outside_ball hfL hfR hfZ),
    clippedSquaredMoment_eq_integral hfZ]
  exact s.integral_norm_sq_step_le hfL hfR hfZ

/-- Equal actual moments force interior reflection order almost everywhere. -/
lemma ae_reflection_order_of_clippedSquaredMoment_eq (s : OriginHalfspace)
    (hc : s.offset < 0) {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0)
    (heq : clippedSquaredMoment S (s.boundedStep f hfL hfR) = clippedSquaredMoment S f) :
    ∀ᵐ x ∂volume, s.offset < ⟪(s.normal : Plane), x⟫_ℝ →
      f (reflection s.normal s.offset x) ≤ f x := by
  have hpZ := s.boundedStep_zero_outside_ball hfL hfR hfZ
  have hfI := integrable_mul_norm_sq_of_commonSupport hfZ
  have hpI := integrable_mul_norm_sq_of_commonSupport hpZ
  have heqI : (∫ x, s.step f x * ‖x‖ ^ 2 ∂volume) =
      ∫ x, f x * ‖x‖ ^ 2 ∂volume := by
    simpa only [clippedSquaredMoment_eq_integral hpZ,
      clippedSquaredMoment_eq_integral hfZ, boundedStep_coe] using! heq
  have hpair := ae_weighted_polarization_pair_eq_of_integral_eq
    (reflection_measurePreserving s.normal s.offset)
    (reflection_involutive s.normal s.offset)
    (reflection_ae_swap s.normal s.offset)
    (s.norm_sq_le_reflection) hfI hpI heqI
  filter_upwards [hpair] with x hxeq
  intro hx
  by_contra hn
  have hvalue : f x < f (reflection s.normal s.offset x) := lt_of_not_ge hn
  have hxH : x ∈ halfspace s.normal s.offset := hx.le
  have hτH : reflection s.normal s.offset x ∉ halfspace s.normal s.offset := by
    rw [reflection_mem_halfspace_iff]
    exact not_le_of_gt hx
  have hstrict := sorted_weighted_pair_lt (f x)
    (f (reflection s.normal s.offset x)) (‖x‖ ^ 2)
    (‖reflection s.normal s.offset x‖ ^ 2) hvalue
    (s.norm_sq_lt_reflection_of_inner_gt hc hx)
  have heqPair :
      max (f x) (f (reflection s.normal s.offset x)) * ‖x‖ ^ 2 +
          min (f x) (f (reflection s.normal s.offset x)) *
            ‖reflection s.normal s.offset x‖ ^ 2 =
        f x * ‖x‖ ^ 2 + f (reflection s.normal s.offset x) *
          ‖reflection s.normal s.offset x‖ ^ 2 := by
    simpa only [twoPointPolarization, if_pos hxH, if_neg hτH,
      reflection_reflection, min_comm] using hxeq
  exact (ne_of_lt hstrict) heqPair

/-- Continuity upgrades the actual a.e. order to all interior points; the
fixed boundary then gives order on the entire closed chosen halfspace. -/
lemma reflection_order_of_clippedSquaredMoment_eq (s : OriginHalfspace)
    (hc : s.offset < 0) {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0)
    (heq : clippedSquaredMoment S (s.boundedStep f hfL hfR) = clippedSquaredMoment S f) :
    ∀ x ∈ halfspace s.normal s.offset, f (reflection s.normal s.offset x) ≤ f x := by
  have hae := s.ae_reflection_order_of_clippedSquaredMoment_eq hc hfL hfR hfZ heq
  let U : Set Plane := {x | s.offset < ⟪(s.normal : Plane), x⟫_ℝ ∧
    f x < f (reflection s.normal s.offset x)}
  have hInner : Continuous (fun x : Plane => ⟪(s.normal : Plane), x⟫_ℝ) :=
    (continuous_const : Continuous (fun _ : Plane => (s.normal : Plane))).inner
      continuous_id
  have hReflected : Continuous (fun x : Plane => f (reflection s.normal s.offset x)) :=
    f.continuous.comp (reflection_isometry s.normal s.offset).continuous
  have hU : IsOpen U := by
    change IsOpen ({x : Plane | s.offset < ⟪(s.normal : Plane), x⟫_ℝ} ∩
      {x : Plane | f x < f (reflection s.normal s.offset x)})
    exact (isOpen_lt
      (continuous_const : Continuous (fun _ : Plane => s.offset)) hInner).inter
        (isOpen_lt f.continuous hReflected)
  have hnull : volume U = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hae] with x hx
    intro hxU
    exact (not_lt_of_ge (hx hxU.1)) hxU.2
  have hempty : U = ∅ := hU.eq_empty_of_measure_zero hnull
  intro x hxH
  change s.offset ≤ ⟪(s.normal : Plane), x⟫_ℝ at hxH
  by_cases hx : s.offset < ⟪(s.normal : Plane), x⟫_ℝ
  · by_contra hn
    have hxU : x ∈ U := ⟨hx, lt_of_not_ge hn⟩
    rw [hempty] at hxU
    exact hxU
  · have hinner : ⟪(s.normal : Plane), x⟫_ℝ = s.offset :=
      le_antisymm (le_of_not_gt hx) hxH
    have hfixed : reflection s.normal s.offset x = x := by
      rw [reflection_eq_add_smul, hinner]
      simp only [sub_self, mul_zero, zero_smul, add_zero]
    simpa only [hfixed] using (le_refl (f x))

end OriginHalfspace

end FaberKrahnDevelopment

end

end
