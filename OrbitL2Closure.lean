module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import BoundedPolarizationOrbit
public import FiniteOrbitEnergies
public import UniformSquaredIntegral
public import Mathlib.Topology.Sequences

/-!
# Actual mass of the global uniform orbit closure

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.

Every element of the literal bounded polarization orbit has the initial
real square integral by `FiniteOrbitEnergies`. The integrable indicator of
the common closed ball defines a continuous clipped-square functional on
the global BCF space. Its level set is closed and contains the actual orbit,
so it contains the orbit closure. The proved common-support closure theorem
then identifies the clipped square integral with the whole-plane integral.

Actual integrability and actual approximating sequences are also produced.
The stronger sequence interface consists of explicit finite lists, rather
than a sequence presumed to have good analytic limit properties.

There is no energy assertion for closure members, no radiality assumption,
no layer cake formula, and no Faber--Krahn estimate here.
-/

@[expose] public section

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

lemma integral_sq_of_mem_boundedPolarizationOrbit
    {f g : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hg : g ∈ boundedPolarizationOrbit f) :
    (∫ x, g x ^ 2) = ∫ x, f x ^ 2 :=
  (energies_of_mem_finitePolarizationOrbit hfL (fun x => (hfR x).1) hfZ hg).1

/-- Actual square integrability of every closure member follows from the
retained Lipschitz and common-support bounds, not from a formal integral value. -/
lemma integrable_sq_of_mem_closure_boundedPolarizationOrbit
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0)
    (hv : v ∈ closure (boundedPolarizationOrbit f)) :
    Integrable (fun x => v x ^ 2) volume := by
  have hBounds := closure_boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ hv
  have hvZ : ∀ x, S < ‖x‖ → v x = 0 := by
    intro x hx
    apply hBounds.2.2 x
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact integrable_sq_of_lipschitz_zero_outside_ball hBounds.1 hvZ

/-- The original real square mass is retained by every actual global
uniform orbit-closure member. No distribution or good-limit premise is used. -/
lemma integral_sq_of_mem_closure_boundedPolarizationOrbit
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0)
    (hv : v ∈ closure (boundedPolarizationOrbit f)) :
    (∫ x, v x ^ 2) = ∫ x, f x ^ 2 := by
  let B := Metric.closedBall (0 : Plane) S
  let J := clippedSquaredIntegral volume B
  have hJ : Continuous J := continuous_clippedSquaredIntegral
    Metric.isClosed_closedBall.measurableSet
    ((isCompact_closedBall (0 : Plane) S).measure_lt_top.ne)
  have hLevelClosed : IsClosed {g : Plane →ᵇ ℝ | J g = ∫ x, f x ^ 2} :=
    isClosed_eq hJ continuous_const
  have hOrbitLevel : boundedPolarizationOrbit f ⊆
      {g : Plane →ᵇ ℝ | J g = ∫ x, f x ^ 2} := by
    intro g hg
    have hBounds := boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ hg
    exact (clippedSquaredIntegral_eq_integral hBounds.2.2).trans
      (integral_sq_of_mem_boundedPolarizationOrbit hfL hfR hfZ hg)
  have hClosureLevel := closure_minimal hOrbitLevel hLevelClosed
  have hvBounds := closure_boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ hv
  calc
    (∫ x, v x ^ 2) = J v := (clippedSquaredIntegral_eq_integral hvBounds.2.2).symm
    _ = ∫ x, f x ^ 2 := hClosureLevel hv

/-- A closure member is the uniform limit of a genuine sequence in the
actual orbit; this follows from the metric-space closure theorem. -/
lemma exists_seq_boundedPolarizationOrbit_tendsto {f v : Plane →ᵇ ℝ}
    (hv : v ∈ closure (boundedPolarizationOrbit f)) :
    ∃ g : ℕ → (Plane →ᵇ ℝ), (∀ n, g n ∈ boundedPolarizationOrbit f) ∧
      Tendsto g atTop (𝓝 v) :=
  mem_closure_iff_seq_limit.mp hv

/-- The approximating sequence can be realized by explicit finite lists of
the already defined geometric polarization operations. -/
lemma exists_finite_lists_tendsto_of_mem_closure_boundedPolarizationOrbit
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hv : v ∈ closure (boundedPolarizationOrbit f)) :
    ∃ ss : ℕ → List OriginHalfspace,
      Tendsto (fun n => boundedFinitePolarization (ss n) f hfL hfR) atTop (𝓝 v) := by
  obtain ⟨g, hg, hLimit⟩ := exists_seq_boundedPolarizationOrbit_tendsto hv
  choose ss hss using fun n => (mem_boundedPolarizationOrbit_iff hfL hfR).mp (hg n)
  refine ⟨ss, ?_⟩
  have hEq : (fun n => boundedFinitePolarization (ss n) f hfL hfR) = g := funext hss
  rw [hEq]
  exact hLimit

end FaberKrahnDevelopment
