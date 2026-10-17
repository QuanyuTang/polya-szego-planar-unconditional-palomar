module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01NonnegativeCompactApproximation
public import AffinePolarizationRealEnergy
public import PolarizationL2Continuity
public import H01WeakLimitAdmissibility

/-!
# An actual original H01 candidate under arbitrary affine polarization

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
Actual nonnegative compact Lipschitz approximants are polarized, then
placed in the unchanged original H01 of the actual open polarized domain
using the canonical compact-Lipschitz tuple. Its actual whole-space value
is identified with the actual L2 polarization, not just by an energy law.

Real affine mass and derivative-energy preservation give convergence of
both original energies. Actual L2 continuity of polarization supplies the
strong value limit. The actual original-H01 weak-limit producer then gives
membership, the exact polarized value, preserved mass, and no larger E1.

No finite-area, bounded-domain, offset-sign, minimizer, SMP, PDE, prechosen
approximation, weak limit, or energy-preservation premise is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.AffinePolarizedH01Candidate

open FaberKrahnDevelopment FaberKrahnDevelopment.EuclideanReflection
open H01NonnegativeCompactApproximation

/-- A nonnegative class in the actual original H01 has an admissible
candidate in the actual polarized open domain, for every affine halfspace. -/
theorem exists_affine_polarized_H01_candidate {Ω : Set Plane} (hΩ : IsOpen Ω)
    (ν : UnitNormal) (c : ℝ) (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (hu0 : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x) :
    ∃ w : L2 (PolarizedOpenDomain.domain ν c Ω) ×
        (Fin 2 → L2 (PolarizedOpenDomain.domain ν c Ω)),
      w ∈ H01 (PolarizedOpenDomain.domain ν c Ω) ∧
      h01GlobalValue (PolarizedOpenDomain.domain ν c Ω)
          (PolarizedOpenDomain.domain_isOpen ν c hΩ).measurableSet w =
        PolarizationL2.polarizationLp (halfspace_measurableSet ν c)
          (reflection_measurePreserving ν c) (h01GlobalValue Ω hΩ.measurableSet u) ∧
      energy0 w = energy0 u ∧ energy1 w ≤ energy1 u := by
  obtain ⟨φ, K, _hgraph, hLip, hdata, hFn, hMass, hEnergy⟩ :=
    exists_nonnegative_compact_lipschitz_approximation hΩ u hu hu0
  let ΩH : Set Plane := PolarizedOpenDomain.domain ν c Ω
  have hΩH : IsOpen ΩH := PolarizedOpenDomain.domain_isOpen ν c hΩ
  let f : ℕ → Plane → ℝ := fun n => absTest (φ n)
  let P : ℕ → Plane → ℝ := fun n =>
    twoPointPolarization (halfspace ν c) (reflection ν c) (f n)
  have hfN : ∀ n x, 0 ≤ f n x := fun n => (hdata n).1
  have hfC : ∀ n, HasCompactSupport (f n) := fun n => (hdata n).2.1
  have hfS : ∀ n, tsupport (f n) ⊆ Ω := fun n => (hdata n).2.2.1
  have hPL : ∀ n, LipschitzWith (K n) (P n) := fun n =>
    AffineRealEnergy.lipschitzWith_polarization ν c (hLip n)
  have hPS : ∀ n, HasCompactSupport (P n) ∧ tsupport (P n) ⊆ ΩH := fun n =>
    PolarizedOpenDomain.polarization_hasCompactSupport_inside ν c (hfN n) (hfC n) (hfS n)
  let v : ℕ → L2 ΩH × (Fin 2 → L2 ΩH) := fun n =>
    CompactLipOriginalH01.tuple ΩH (hPL n) (hPS n).1
  have hv : ∀ n, v n ∈ H01 ΩH := fun n =>
    CompactLipOriginalH01.tuple_mem_H01 hΩH (hPL n) (hPS n).1 (hPS n).2
  let z : Lp ℝ 2 (volume : Measure Plane) :=
    PolarizationL2.polarizationLp (halfspace_measurableSet ν c)
      (reflection_measurePreserving ν c) (h01GlobalValue Ω hΩ.measurableSet u)
  have hValue : ∀ n, h01GlobalValue ΩH hΩH.measurableSet (v n) =
      PolarizationL2.polarizationLp (halfspace_measurableSet ν c)
        (reflection_measurePreserving ν c) (absTestLp (φ n)) := by
    intro n
    apply Lp.ext
    have hJ : (h01GlobalValue ΩH hΩH.measurableSet (v n) : Plane → ℝ) =ᵐ[volume] P n :=
      CompactLipOriginalH01.tuple_extend_value_ae hΩH (hPL n) (hPS n).1 (hPS n).2
    have hPolar : (PolarizationL2.polarizationLp (halfspace_measurableSet ν c)
        (reflection_measurePreserving ν c) (absTestLp (φ n)) : Plane → ℝ) =ᵐ[volume] P n :=
      (PolarizationL2.coeFn_polarizationLp (halfspace_measurableSet ν c)
        (reflection_measurePreserving ν c) (absTestLp (φ n))).trans
        (PolarizationL2.twoPointPolarization_congr_ae (reflection_measurePreserving ν c)
          (coeFn_absTestLp (φ n)))
    exact hJ.trans hPolar.symm
  have hPolarLimit : Tendsto (fun n =>
      PolarizationL2.polarizationLp (halfspace_measurableSet ν c)
        (reflection_measurePreserving ν c) (absTestLp (φ n))) atTop (𝓝 z) :=
    ((PolarizationL2.continuous_polarizationLp (halfspace_measurableSet ν c)
      (reflection_measurePreserving ν c)).tendsto _).comp hFn
  have hz : Tendsto (fun n => h01GlobalValue ΩH hΩH.measurableSet (v n)) atTop (𝓝 z) := by
    simpa only [hValue] using hPolarLimit
  have h0eq : ∀ n, energy0 (v n) = ∫ x, absTest (φ n) x ^ 2 := by
    intro n
    exact (CompactLipOriginalH01.energy0_tuple hΩH (hPL n) (hPS n).1 (hPS n).2).trans
      (AffineRealEnergy.integral_sq_polarization ν c (hLip n) (hfC n) (hfN n))
  have h1eq : ∀ n, energy1 (v n) = ∫ x, ‖fderiv ℝ (absTest (φ n)) x‖ ^ 2 := by
    intro n
    exact (CompactLipOriginalH01.energy1_tuple hΩH (hPL n) (hPS n).1 (hPS n).2).trans
      (AffineRealEnergy.integral_gradient_sq_polarization ν c (hLip n) (hfC n) (hfN n))
  have h0 : Tendsto (fun n => energy0 (v n)) atTop (𝓝 (energy0 u)) := by
    simpa only [h0eq] using hMass
  have h1 : Tendsto (fun n => energy1 (v n)) atTop (𝓝 (energy1 u)) := by
    simpa only [h1eq] using hEnergy
  exact H01WeakLimitAdmissibility.exists_H01_of_strong_globalValue_tendsto
    hΩH.measurableSet v hv z (energy0 u) (energy1 u) hz h0 h1

end Buckling.AffinePolarizedH01Candidate

end

end
