module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import OrbitMinimizerSupport
public import CutoffMassLimit
public import CutoffRayleighReal
public import Mathlib.Topology.Order.DenselyOrdered

/-!
# Sharp planar inequality for an actual fixed initial Lipschitz function

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.

The inputs below are only the literal initial bounded continuous function,
its global Lipschitz constant, its nonnegative bounded range, its common
support ball, a positive target radius, and the positive-set area bound.
The actual orbit minimizer produces the tighter support. Actual finite-list
approximations produce both uniform convergence and cutoff mass convergence;
their global derivative energies equal the initial derivative energy.

The finite spectral cutoff estimate is passed first through the finite-list
limit, then through delta approaching zero from above, then through epsilon
approaching zero from above. No limit gradient, Sobolev lower semicontinuity,
energy bound, mass identity, good limiting function, radiality, or spectral
inequality is supplied as an input. Zero initial mass is permitted.

This is only the fixed-initial-function inequality node. It does not prove
the full original ExtFaberKrahn interface, equality rigidity, or the project's
unconditional main theorem. Actual compilation and axiom inspection of this
module and the complete dependency chain remain required.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- The sharp real-integral inequality for a literal nonnegative compactly
supported whole-plane bounded Lipschitz function. All limiting data in the
proof are produced from its actual finite polarization orbit. -/
lemma fixedInitial_faberKrahn
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S R : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hR : 0 < R)
    (hArea : volume {x | 0 < f x} ≤ volume (Metric.ball (0 : Plane) R)) :
    Buckling.jq ^ 2 / R ^ 2 * (∫ x, f x ^ 2 ∂volume) ≤
      ∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume := by
  obtain ⟨v, hv, _hvL, _hvR, _hvZS, _hvDistribution, _hvMin, _hvOrder, hvSupport⟩ :=
    exists_boundedOrbit_minimizer_with_area_support hfL hfR hfZ hR.le hArea
  have hvZ : ∀ x, R < ‖x‖ → v x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have hxR : ‖x‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hvSupport hxs
    exact (not_le_of_gt hx) hxR
  have hfN : ∀ x, 0 ≤ f x := fun x => (hfR x).1
  -- Epsilon is fixed until the uniform-orbit and delta limits are complete.
  have hEpsilon : ∀ ε : ℝ, 0 < ε →
      Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 * (∫ x, f x ^ 2 ∂volume) ≤
        ∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume := by
    intro ε hε
    have hDelta : ∀ δ : ℝ, 0 < δ →
        Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 * (∫ x, f x ^ 2 ∂volume) ≤
          (1 + δ) * (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume) := by
      intro δ hδ
      obtain ⟨ss, hLimit, hMass⟩ :=
        exists_finite_lists_cutoff_mass_tendsto hfL hfR hfZ hv hR.le hε hvZ
      let g : ℕ → (Plane →ᵇ ℝ) :=
        fun n => boundedFinitePolarization (ss n) f hfL hfR
      have hDist : Tendsto (fun n => dist (g n) v) atTop (𝓝 (0 : ℝ)) := by
        simpa only [g, dist_self] using hLimit.dist
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => v) atTop (𝓝 v))
      have hFinite (n : ℕ) :
          Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 *
              (∫ x, (spectralCutoff R ε hR.le hε x *
                finitePolarization (ss n) f x) ^ 2 ∂volume) ≤
            (1 + δ) * (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume) +
              (1 + δ⁻¹) * dist (g n) v ^ 2 * spectralCutoffEnergy R ε hR.le hε := by
        have hgL : LipschitzWith K (g n) :=
          lipschitzWith_finitePolarization (ss n) hfL
        have hgZ : ∀ x, S < ‖x‖ → g n x = 0 :=
          finitePolarization_eq_zero_of_radius_lt (ss n) hfN hfZ
        have hgEnergy : (∫ x, ‖fderiv ℝ (g n : Plane → ℝ) x‖ ^ 2 ∂volume) =
            ∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume :=
          integral_derivativeEnergy_finitePolarization (ss n) hfL hfN hfZ
        have h := spectralCutoff_rayleigh_energy_le hR.le hε hδ hgL hgZ hvZ
        rw [hgEnergy] at h
        exact h
      have hLeft : Tendsto (fun n =>
          Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 *
            (∫ x, (spectralCutoff R ε hR.le hε x *
              finitePolarization (ss n) f x) ^ 2 ∂volume)) atTop
          (𝓝 (Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 *
            (∫ x, f x ^ 2 ∂volume))) := tendsto_const_nhds.mul hMass
      have hError : Tendsto (fun n =>
          (1 + δ⁻¹) * dist (g n) v ^ 2 * spectralCutoffEnergy R ε hR.le hε)
          atTop (𝓝 (0 : ℝ)) := by
        simpa using
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 + δ⁻¹)) atTop
            (𝓝 (1 + δ⁻¹))).mul (hDist.pow 2)).mul
              (tendsto_const_nhds : Tendsto
                (fun _ : ℕ => spectralCutoffEnergy R ε hR.le hε) atTop
                (𝓝 (spectralCutoffEnergy R ε hR.le hε)))
      have hRight : Tendsto (fun n =>
          (1 + δ) * (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume) +
            (1 + δ⁻¹) * dist (g n) v ^ 2 * spectralCutoffEnergy R ε hR.le hε)
          atTop (𝓝 ((1 + δ) *
            (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume))) := by
        simpa using
          (tendsto_const_nhds : Tendsto
            (fun _ : ℕ => (1 + δ) *
              (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume)) atTop
            (𝓝 ((1 + δ) *
              (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume)))).add hError
      exact le_of_tendsto_of_tendsto hLeft hRight (Eventually.of_forall hFinite)
    -- Only continuity in delta is used: no sign of the energy is assumed.
    have hId : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hDeltaLimit : Tendsto (fun δ : ℝ =>
        (1 + δ) * (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume))
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume)) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ))
          (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))).add hId).mul
            (tendsto_const_nhds : Tendsto
              (fun _ : ℝ => ∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume)
              (𝓝[>] (0 : ℝ))
              (𝓝 (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume)))
    apply ge_of_tendsto hDeltaLimit
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact hDelta δ hδ
  -- Positivity of R supplies exactly the denominator continuity at epsilon=0.
  have hId : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hDenominator : Tendsto (fun ε : ℝ => (R + 2 * ε) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (R ^ 2)) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => R)
        (𝓝[>] (0 : ℝ)) (𝓝 R)).add
          ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ))
            (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ))).mul hId)).pow 2
  have hEpsilonLimit : Tendsto (fun ε : ℝ =>
      Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 * (∫ x, f x ^ 2 ∂volume))
      (𝓝[>] (0 : ℝ))
      (𝓝 (Buckling.jq ^ 2 / R ^ 2 * (∫ x, f x ^ 2 ∂volume))) :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Buckling.jq ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (Buckling.jq ^ 2))).div
        hDenominator (pow_ne_zero 2 hR.ne')).mul tendsto_const_nhds
  apply le_of_tendsto hEpsilonLimit
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEpsilon ε hε

end FaberKrahnDevelopment

end

end
