module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import ReflectionPairs
public import PolarizedOpenDomain
public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Actual Lebesgue good points and reflection comparison of ball averages

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

GoodPoint is a literal closed-ball-average differentiation property of the
given L1 representative. The canonical Lebesgue differentiation theorem
produces it on one full-measure set, independently of any reflection.
For a fixed actual reflection, AE order on its chosen side compares all
averages over balls contained in that side. Actual MP change of variables
and actual isometry identify the partner-ball average. At two good points
the averages tend to the actual values, giving pointwise comparison there.

Two arbitrary good points of different distances from a fixed center then
determine one actual bisector reflection. No uncountable intersection of
AE reflection statements is taken. The last root gives strict radial order
on the one actually produced full-measure good-point set.

The final finite-positive-set-radius/supremum and null-sphere argument is
not asserted here. It remains a separate measure-theoretic consumer of this
actual good-point radial comparison; no a.e. ball is an input or output.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal MeasureTheory InnerProductSpace RealInnerProductSpace

namespace Buckling.ReflectionOrderGoodPoints

open FaberKrahnDevelopment.EuclideanReflection FaberKrahnDevelopment.PolarizedOpenDomain

def GoodPoint (U : Plane → ℝ) (x : Plane) : Prop :=
  Tendsto (fun r : ℝ => ⨍ z in closedBall x r, U z) (𝓝[>] 0) (𝓝 (U x))

/-- One actual full-measure differentiation set, before choosing any of
the uncountably many possible affine reflections. -/
theorem ae_goodPoint {U : Plane → ℝ} (hU : Integrable U volume) :
    ∀ᵐ x ∂volume, GoodPoint U x := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average
    (volume : Measure Plane) hU.locallyIntegrable (0 : ℝ)] with x hx
  exact hx (fun _ : ℝ => x) (fun r : ℝ => r) tendsto_id
    (Eventually.of_forall fun r => by
      simp only [zero_mul]
      exact mem_closedBall_self le_rfl)

lemma reflection_preimage_closedBall (ν : UnitNormal) (c : ℝ) (x : Plane) (r : ℝ) :
    reflection ν c ⁻¹' closedBall (reflection ν c x) r = closedBall x r := by
  ext z
  change dist (reflection ν c z) (reflection ν c x) ≤ r ↔ dist z x ≤ r
  rw [(reflection_isometry ν c).dist_eq]

/-- Actual restricted integral and actual ball measure are both transported;
the two averages therefore have the same normalization. -/
lemma average_reflection_eq (ν : UnitNormal) (c : ℝ) (U : Plane → ℝ)
    (x : Plane) (r : ℝ) :
    (⨍ z in closedBall (reflection ν c x) r, U z) =
      ⨍ z in closedBall x r, U (reflection ν c z) := by
  let e : Plane ≃ᵐ Plane := MeasurableEquiv.ofInvolutive (reflection ν c)
    (reflection_involutive ν c) (reflection_measurable ν c)
  have hPre := reflection_preimage_closedBall ν c x r
  have hIntegral := (reflection_measurePreserving ν c).setIntegral_preimage_emb
    e.measurableEmbedding U (closedBall (reflection ν c x) r)
  rw [hPre] at hIntegral
  have hMeasure := (reflection_measurePreserving ν c).measure_preimage
    (measurableSet_closedBall (x := reflection ν c x) (ε := r)).nullMeasurableSet
  rw [hPre] at hMeasure
  have hReal : volume.real (closedBall (reflection ν c x) r) =
      volume.real (closedBall x r) := congrArg ENNReal.toReal hMeasure.symm
  rw [setAverage_eq, setAverage_eq, hReal, ← hIntegral]

/-- Genuine L1 on both balls and genuine AE reflection order compare their
actual averages; no value at the center is taken from an AE statement. -/
lemma average_reflection_le (ν : UnitNormal) (c : ℝ) {U : Plane → ℝ}
    (hU : Integrable U volume)
    (hOrder : ∀ᵐ z ∂(volume.restrict (halfspace ν c)), U (reflection ν c z) ≤ U z)
    (x : Plane) (r : ℝ) (hBall : closedBall x r ⊆ halfspace ν c) :
    (⨍ z in closedBall (reflection ν c x) r, U z) ≤ ⨍ z in closedBall x r, U z := by
  have hR : Integrable (fun z => U (reflection ν c z)) volume :=
    (reflection_measurePreserving ν c).integrable_comp_of_integrable hU
  have hAll : ∀ᵐ z ∂volume, z ∈ halfspace ν c → U (reflection ν c z) ≤ U z :=
    (ae_restrict_iff' (halfspace_measurableSet ν c)).mp hOrder
  have hAE : ∀ᵐ z ∂(volume.restrict (closedBall x r)), U (reflection ν c z) ≤ U z :=
    (ae_restrict_iff' measurableSet_closedBall).mpr
      (hAll.mono fun z hz hzB => hz (hBall hzB))
  have hIntegral : (∫ z in closedBall x r, U (reflection ν c z)) ≤
      ∫ z in closedBall x r, U z := integral_mono_ae hR.restrict hU.restrict hAE
  rw [average_reflection_eq ν c U x r, setAverage_eq, setAverage_eq,
    smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left hIntegral (inv_nonneg.mpr ENNReal.toReal_nonneg)

/-- A strict-side point has actual sufficiently small closed balls inside
the chosen side; the fixed reflecting boundary is never crossed. -/
lemma eventually_closedBall_subset_halfspace (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : c < inner ℝ (ν : Plane) x) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, closedBall x r ⊆ halfspace ν c := by
  obtain ⟨δ, hδ, hB⟩ := Metric.isOpen_iff.mp (strictSide_isOpen ν c) x hx
  have hr : ∀ᶠ r : ℝ in 𝓝[>] 0, r < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  filter_upwards [hr] with r hr z hz
  have hzB : z ∈ ball x δ := lt_of_le_of_lt hz hr
  exact (show c < inner ℝ (ν : Plane) z from hB hzB).le

/-- The two actual good-point limits turn one fixed AE reflection order
into actual order of these two values. No uncountable AE intersection. -/
theorem order_at_goodPoints (ν : UnitNormal) (c : ℝ) {U : Plane → ℝ}
    (hU : Integrable U volume)
    (hOrder : ∀ᵐ z ∂(volume.restrict (halfspace ν c)), U (reflection ν c z) ≤ U z)
    {x : Plane} (hx : c < inner ℝ (ν : Plane) x)
    (hGood : GoodPoint U x) (hGoodR : GoodPoint U (reflection ν c x)) :
    U (reflection ν c x) ≤ U x := by
  apply le_of_tendsto_of_tendsto hGoodR hGood
  filter_upwards [eventually_closedBall_subset_halfspace ν c hx] with r hr
  exact average_reflection_le ν c hU hOrder x r hr

lemma pairOffset_lt_inner_left (x y : Plane) (hxy : x ≠ y) :
    pairOffset x y hxy < inner ℝ (pairNormal x y hxy : Plane) x := by
  have hinner := inner_pairNormal_sub x y hxy
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  unfold pairOffset
  linarith

/-- The actual perpendicular bisector is oriented strictly towards a center
which is strictly closer to the first point. Its center-side property is
derived from the actual scalar products, not supplied as extra geometry. -/
lemma pairOffset_lt_inner_center (p x y : Plane) (hxy : x ≠ y)
    (hDist : dist p x < dist p y) :
    pairOffset x y hxy < inner ℝ (pairNormal x y hxy : Plane) p := by
  have hNorm : ‖x - p‖ < ‖y - p‖ := by
    simpa only [dist_eq_norm, norm_sub_rev] using hDist
  have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hExpansion : ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 =
      inner ℝ (x - y) ((2 : ℝ) • p - (x + y)) := by
    simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right, inner_add_right,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm y x]
    ring
  have hProduct : 2 * ‖x - y‖ *
      (inner ℝ (pairNormal x y hxy : Plane) p - pairOffset x y hxy) =
        ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 := by
    calc
      2 * ‖x - y‖ * (inner ℝ (pairNormal x y hxy : Plane) p - pairOffset x y hxy) =
          ‖x - y‖ * (2 * inner ℝ (pairNormal x y hxy : Plane) p -
            inner ℝ (pairNormal x y hxy : Plane) x -
            inner ℝ (pairNormal x y hxy : Plane) y) := by
        unfold pairOffset
        ring
      _ = inner ℝ (‖x - y‖ • (pairNormal x y hxy : Plane))
          ((2 : ℝ) • p - (x + y)) := by
        rw [real_inner_smul_left, inner_sub_right, real_inner_smul_right, inner_add_right]
        ring
      _ = inner ℝ (x - y) ((2 : ℝ) • p - (x + y)) := by
        rw [norm_sub_smul_pairNormal]
      _ = ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 := hExpansion.symm
  have hPositive : 0 < ‖y - p‖ ^ 2 - ‖x - p‖ ^ 2 := by
    nlinarith [norm_nonneg (x - p)]
  by_contra h
  have hNonpos : inner ℝ (pairNormal x y hxy : Plane) p - pairOffset x y hxy ≤ 0 :=
    sub_nonpos.mpr (le_of_not_gt h)
  have hp := mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd.le) hNonpos
  linarith

/-- Actual strict radial order on the one full-measure good-point set. Each
pair chooses a single actual reflection and uses its AE order through ball
averages, rather than intersecting the AE orders over all reflections. -/
theorem radial_order_at_goodPoints {U : Plane → ℝ} (hU : Integrable U volume) (p : Plane)
    (hOrder : ∀ (ν : UnitNormal) (c : ℝ), c < inner ℝ (ν : Plane) p →
      ∀ᵐ z ∂(volume.restrict (halfspace ν c)), U (reflection ν c z) ≤ U z)
    {x y : Plane} (hx : GoodPoint U x) (hy : GoodPoint U y)
    (hDist : dist p x < dist p y) : U y ≤ U x := by
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact (lt_irrefl _ hDist)
  let ν := pairNormal x y hxy
  let c := pairOffset x y hxy
  have hc : c < inner ℝ (ν : Plane) p := pairOffset_lt_inner_center p x y hxy hDist
  have hLeft : c < inner ℝ (ν : Plane) x := pairOffset_lt_inner_left x y hxy
  have hRGood : GoodPoint U (reflection ν c x) := by
    simpa only [ν, c, pair_reflection_eq] using hy
  have h := order_at_goodPoints ν c hU (hOrder ν c hc) hLeft hx hRGood
  simpa only [ν, c, pair_reflection_eq] using h

end Buckling.ReflectionOrderGoodPoints

end

end
