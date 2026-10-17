module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import ReflectionPairs
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Topology.Algebra.Support

/-!
# The support radius forced by the positive-set area

SOURCE_DRAFT (2026-10-17), not yet compiled and not imported by production.

Only strict order between different radii is needed: positivity at radius r
forces positivity on the entire open ball of radius r. Its literal Euclidean
area then prevents r from exceeding the equal-area radius. No Sobolev limit,
radial representation, rearrangement, or spectral comparison is assumed.

The intended producers are reflection order from the actual moment minimizer
and the strict-superlevel distribution at zero from uniform orbit closure.
-/

@[expose] public section

open Set MeasureTheory

namespace FaberKrahnDevelopment.EuclideanReflection

lemma volume_ball_toReal (r : ℝ) (hr : 0 ≤ r) :
    (volume (Metric.ball (0 : Plane) r)).toReal = Real.pi * r ^ 2 := by
  rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

/-- Radius comparison is derived from the actual planar area formula. -/
lemma radius_le_of_volume_ball_le {r R : ℝ} (hr : 0 ≤ r) (hR : 0 ≤ R)
    (hvol : volume (Metric.ball (0 : Plane) r) ≤
      volume (Metric.ball (0 : Plane) R)) : r ≤ R := by
  have hv := ENNReal.toReal_mono
    (measure_ball_ne_top (μ := (volume : Measure Plane)) (x := (0 : Plane)) (r := R)) hvol
  rw [volume_ball_toReal r hr, volume_ball_toReal R hR] at hv
  have hs : r ^ 2 ≤ R ^ 2 := le_of_mul_le_mul_left hv Real.pi_pos
  exact le_of_sq_le_sq hs hR

/-- Strict radial order and an actual area bound force the function to vanish
outside the corresponding closed ball. Nonnegativity supplies positivity at
any alleged nonzero value outside it. -/
lemma eq_zero_of_radius_lt_of_superlevel_area_bound {f : Plane → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x, 0 ≤ f x)
    (horder : ∀ {x y : Plane}, ‖x‖ < ‖y‖ → f y ≤ f x)
    (hArea : volume {x | 0 < f x} ≤ volume (Metric.ball (0 : Plane) R))
    {x : Plane} (hx : R < ‖x‖) : f x = 0 := by
  by_contra hzero
  have hpos : 0 < f x := lt_of_le_of_ne (hf x) (Ne.symm hzero)
  have hsub : Metric.ball (0 : Plane) ‖x‖ ⊆ {z | 0 < f z} := by
    intro z hz
    have hzr : ‖z‖ < ‖x‖ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    exact hpos.trans_le (horder hzr)
  have hvol := (measure_mono hsub).trans hArea
  have hr := radius_le_of_volume_ball_le (norm_nonneg x) hR hvol
  exact (not_le.mpr hx) hr

lemma tsupport_subset_closedBall_of_superlevel_area_bound {f : Plane → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x, 0 ≤ f x)
    (horder : ∀ {x y : Plane}, ‖x‖ < ‖y‖ → f y ≤ f x)
    (hArea : volume {x | 0 < f x} ≤ volume (Metric.ball (0 : Plane) R)) :
    tsupport f ⊆ Metric.closedBall (0 : Plane) R := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  change dist x (0 : Plane) ≤ R
  rw [dist_zero_right]
  by_contra hn
  exact hx (eq_zero_of_radius_lt_of_superlevel_area_bound hR hf horder hArea
    (not_le.mp hn))

/-- The same support conclusion using the actual reflected-pair producer of
strict radial order. No choice of an abstract radial function is required. -/
lemma tsupport_subset_closedBall_of_reflection_order {f : Plane → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ x, 0 ≤ f x)
    (horder : ∀ (ν : UnitNormal) (c : ℝ), c < 0 →
      ∀ x ∈ halfspace ν c, f (reflection ν c x) ≤ f x)
    (hArea : volume {x | 0 < f x} ≤ volume (Metric.ball (0 : Plane) R)) :
    tsupport f ⊆ Metric.closedBall (0 : Plane) R :=
  tsupport_subset_closedBall_of_superlevel_area_bound hR hf
    (fun h => radial_order_of_reflection_order f horder h) hArea

end FaberKrahnDevelopment.EuclideanReflection
