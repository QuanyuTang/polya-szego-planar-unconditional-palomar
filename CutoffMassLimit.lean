module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import OrbitL2Closure
public import SpectralCutoffGeometry

/-!
# Actual cutoff mass convergence for finite orbit approximations

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.

The actual smooth spectral cutoff is packaged as a whole-plane BCF using
its literal range [0,1]. Continuous BCF multiplication turns uniform
convergence to a function supported in closedBall R into uniform convergence
of the cutoff products to that same function. Every cutoff product vanishes
outside closedBall (R+epsilon), independently of the varying input's support.
The finite-measure-support square-integral theorem therefore gives actual
full-plane mass convergence. For orbit-closure members the limiting mass is
the initial mass by `OrbitL2Closure`.

The final producer supplies explicit finite lists and their true mass
convergence; it assumes neither a preselected good sequence nor a mass-limit
identity. No cutoff energy estimate or spectral inequality is proved here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- The literal spectral cutoff as an actual bounded continuous function. -/
def boundedSpectralCutoff (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨(spectralCutoff R ε hR hε : Plane → ℝ), (spectralCutoff R ε hR hε).continuous⟩ 1
    (fun x y => dist_le_of_mem_Icc_zero
      (spectralCutoff_mem_Icc R ε hR hε x) (spectralCutoff_mem_Icc R ε hR hε y))

@[simp] lemma boundedSpectralCutoff_apply (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (x : Plane) : boundedSpectralCutoff R ε hR hε x = spectralCutoff R ε hR hε x := rfl

lemma boundedSpectralCutoff_mul_eq_self {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {v : Plane →ᵇ ℝ} (hvZ : ∀ x, R < ‖x‖ → v x = 0) :
    boundedSpectralCutoff R ε hR hε * v = v := by
  apply BoundedContinuousFunction.ext
  intro x
  exact spectralCutoff_mul_eq_self hR hε hvZ x

/-- Multiplication by the fixed literal cutoff preserves uniform convergence
to a limit on which that cutoff equals one. -/
lemma tendsto_boundedSpectralCutoff_mul {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {ι : Type*} {l : Filter ι} {F : ι → (Plane →ᵇ ℝ)} {v : Plane →ᵇ ℝ}
    (hvZ : ∀ x, R < ‖x‖ → v x = 0) (hF : Tendsto F l (𝓝 v)) :
    Tendsto (fun i => boundedSpectralCutoff R ε hR hε * F i) l (𝓝 v) := by
  have hMul : Tendsto (fun i => boundedSpectralCutoff R ε hR hε * F i) l
      (𝓝 (boundedSpectralCutoff R ε hR hε * v)) := tendsto_const_nhds.mul hF
  rwa [boundedSpectralCutoff_mul_eq_self hR hε hvZ] at hMul

/-- The cutoff itself produces common compact support for all the products;
no support or amplitude condition on the varying BCF inputs is needed. -/
lemma tendsto_integral_sq_spectralCutoff_mul {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {ι : Type*} {l : Filter ι} {F : ι → (Plane →ᵇ ℝ)} {v : Plane →ᵇ ℝ}
    (hvZ : ∀ x, R < ‖x‖ → v x = 0) (hF : Tendsto F l (𝓝 v)) :
    Tendsto (fun i => ∫ x, (spectralCutoff R ε hR hε x * F i x) ^ 2) l
      (𝓝 (∫ x, v x ^ 2)) := by
  let B := Metric.closedBall (0 : Plane) (R + ε)
  have hCutZero : ∀ x, x ∉ B → boundedSpectralCutoff R ε hR hε x = 0 := by
    intro x hx
    have hxR : R + ε < ‖x‖ := by
      simpa only [B, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    change spectralCutoff R ε hR hε x = 0
    apply (spectralCutoff R ε hR hε).zero_of_le_dist
    change R + ε ≤ dist x (0 : Plane)
    simpa only [dist_zero_right] using hxR.le
  have hProductZero : ∀ i x, x ∉ B →
      (boundedSpectralCutoff R ε hR hε * F i) x = 0 := by
    intro i x hx
    change boundedSpectralCutoff R ε hR hε x * F i x = 0
    rw [hCutZero x hx, zero_mul]
  have hvB : ∀ x, x ∉ B → v x = 0 := by
    intro x hx
    have hxR : R + ε < ‖x‖ := by
      simpa only [B, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    apply hvZ x
    linarith
  have hMass := tendsto_integral_sq_of_uniform_commonSupport (μ := volume)
    Metric.isClosed_closedBall.measurableSet
    ((isCompact_closedBall (0 : Plane) (R + ε)).measure_lt_top.ne)
    (tendsto_boundedSpectralCutoff_mul hR hε hvZ hF) hProductZero hvB
  simpa only [BoundedContinuousFunction.mul_apply, boundedSpectralCutoff_apply] using hMass

/-- Every actual orbit-closure member with the tighter support bound has
explicit finite-list approximations whose cutoff masses tend to the initial
real mass. No preexisting good sequence or mass convergence is assumed. -/
lemma exists_finite_lists_cutoff_mass_tendsto
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} {M S R ε : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0)
    (hv : v ∈ closure (boundedPolarizationOrbit f))
    (hR : 0 ≤ R) (hε : 0 < ε) (hvZ : ∀ x, R < ‖x‖ → v x = 0) :
    ∃ ss : ℕ → List OriginHalfspace,
      Tendsto (fun n => boundedFinitePolarization (ss n) f hfL hfR) atTop (𝓝 v) ∧
      Tendsto (fun n => ∫ x,
        (spectralCutoff R ε hR hε x * finitePolarization (ss n) f x) ^ 2)
        atTop (𝓝 (∫ x, f x ^ 2)) := by
  obtain ⟨ss, hLimit⟩ :=
    exists_finite_lists_tendsto_of_mem_closure_boundedPolarizationOrbit hfL hfR hv
  refine ⟨ss, hLimit, ?_⟩
  have hMass := tendsto_integral_sq_spectralCutoff_mul hR hε hvZ hLimit
  rw [integral_sq_of_mem_closure_boundedPolarizationOrbit hfL hfR hfZ hv] at hMass
  simpa only [boundedFinitePolarization_coe] using hMass

end FaberKrahnDevelopment

end

end
