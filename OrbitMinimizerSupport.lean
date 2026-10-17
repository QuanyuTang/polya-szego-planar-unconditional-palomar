module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import SquaredMomentPolarization
public import UniformDistributionClosure
public import RadialSupportRadius

/-!
# Actual orbit-closure moment minimizers have the area-controlled support

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.
The initial data are a literal nonnegative bounded Lipschitz function, its
common support ball, and an upper bound for the area of its positive set.
The function produced below is a member of the GLOBAL uniform closure of its
actual finite polarization orbit. It is an actual clipped squared-moment
minimizer, with the original pointwise bounds and support retained.

Closure stability and actual squared-moment decrease force equality for every
strict origin-containing reflection. The strict equality producer then gives
reflection order. The actual finite-orbit distribution and its uniform-closure
producer preserve the positive-set area. Reflected pairs and the planar ball
area formula then force support in the prescribed equal-or-larger-area ball.

No ordered limit, radiality, moment decrease, distribution, Sobolev energy,
or Faber--Krahn theorem is postulated as an input. This support producer does
not establish the still separate sharp spectral/energy or equality-rigidity
steps. Actual compilation and axiom inspection of the entire dependency chain
remain required.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- The distribution of the literal finite orbit passes to its global uniform
closure at every strict threshold, including the positive-set threshold zero. -/
lemma measure_superlevel_of_mem_boundedPolarizationOrbit_closure
    {f v : Plane →ᵇ ℝ} (hv : v ∈ closure (boundedPolarizationOrbit f)) (t : ℝ) :
    volume {x | t < v x} = volume {x | t < f x} := by
  apply strictSuperlevel_measure_eq_of_mem_uniform_closure volume (f : Plane → ℝ) ?_ hv t
  intro g hg u
  exact measure_superlevel_of_mem_finitePolarizationOrbit f.continuous.measurable hg u

/-- A literal minimizer in the actual orbit closure is reflection ordered.
The minimum is consumed here; its existence is produced in the next theorem. -/
lemma reflection_order_of_boundedOrbit_moment_minimizer
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0)
    (hv : v ∈ closure (boundedPolarizationOrbit f))
    (hmin : IsMinOn (clippedSquaredMoment S) (closure (boundedPolarizationOrbit f)) v) :
    ∀ (ν : UnitNormal) (c : ℝ), c < 0 →
      ∀ x ∈ halfspace ν c, v (reflection ν c x) ≤ v x := by
  have hvBounds := closure_boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ hv
  have hvL : LipschitzWith K v := hvBounds.1
  have hvR : ∀ x, v x ∈ Icc 0 M := hvBounds.2.1
  have hvZ : ∀ x, S < ‖x‖ → v x = 0 := by
    intro x hx
    apply hvBounds.2.2 x
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  intro ν c hc
  let s : OriginHalfspace := ⟨ν, c, hc.le⟩
  obtain ⟨p, hp, hpFun⟩ := exists_step_mem_closure_boundedPolarizationOrbit s hfL hfR hfZ hv
  have hpEq : p = s.boundedStep v hvL hvR := by
    apply BoundedContinuousFunction.ext
    intro x
    exact congrFun hpFun x
  have hminLe : clippedSquaredMoment S v ≤ clippedSquaredMoment S p := hmin hp
  have hstepLe : clippedSquaredMoment S p ≤ clippedSquaredMoment S v := by
    rw [hpEq]
    exact s.clippedSquaredMoment_boundedStep_le hvL hvR hvZ
  have heq : clippedSquaredMoment S (s.boundedStep v hvL hvR) =
      clippedSquaredMoment S v := by
    rw [← hpEq]
    exact le_antisymm hstepLe hminLe
  exact s.reflection_order_of_clippedSquaredMoment_eq hc hvL hvR hvZ heq

/-- Construct a genuine moment-minimizing member of the actual global orbit
closure and derive support in the prescribed area-controlled closed ball.
All regularity, bounds, support and distribution conclusions refer to this
same whole-plane bounded continuous function. -/
lemma exists_boundedOrbit_minimizer_with_area_support
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S R : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hR : 0 ≤ R)
    (hArea : volume {x | 0 < f x} ≤ volume (Metric.ball (0 : Plane) R)) :
    ∃ v ∈ closure (boundedPolarizationOrbit f),
      LipschitzWith K v ∧ (∀ x, v x ∈ Icc 0 M) ∧
        (∀ x, x ∉ Metric.closedBall (0 : Plane) S → v x = 0) ∧
        (∀ t : ℝ, volume {x | t < v x} = volume {x | t < f x}) ∧
        IsMinOn (clippedSquaredMoment S) (closure (boundedPolarizationOrbit f)) v ∧
        (∀ (ν : UnitNormal) (c : ℝ), c < 0 →
          ∀ x ∈ halfspace ν c, v (reflection ν c x) ≤ v x) ∧
        tsupport (v : Plane → ℝ) ⊆ Metric.closedBall (0 : Plane) R := by
  obtain ⟨v, hv, hvL, hvR, hvZ, hvMin⟩ :=
    exists_min_weightedMoment_on_boundedPolarizationOrbit hfL hfR hfZ
      (integrable_clippedSquaredWeight S)
  have hvMin' : IsMinOn (clippedSquaredMoment S)
      (closure (boundedPolarizationOrbit f)) v := hvMin
  have hOrder := reflection_order_of_boundedOrbit_moment_minimizer hfL hfR hfZ hv hvMin'
  have hDistribution : ∀ t : ℝ, volume {x | t < v x} = volume {x | t < f x} :=
    measure_superlevel_of_mem_boundedPolarizationOrbit_closure hv
  have hAreaV : volume {x | 0 < v x} ≤ volume (Metric.ball (0 : Plane) R) := by
    rw [hDistribution 0]
    exact hArea
  have hSupport : tsupport (v : Plane → ℝ) ⊆ Metric.closedBall (0 : Plane) R :=
    tsupport_subset_closedBall_of_reflection_order hR (fun x => (hvR x).1) hOrder hAreaV
  exact ⟨v, hv, hvL, hvR, hvZ, hDistribution, hvMin', hOrder, hSupport⟩

end FaberKrahnDevelopment

end

end
