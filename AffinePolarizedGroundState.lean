module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import AffinePolarizedH01Candidate
public import H01NonnegativeMinimizer
public import H01WeakGradientBridge

/-!
# Actual polarized ground states at equality in the FK bound

SOURCE_DRAFT: not compiled or registered. The genuine global FK inequality
is an explicit intermediate input, to be supplied by the existing inequality
proof. Actual polarized admissibility and actual area preservation force
equality in both the original Rayleigh lower bound and the energy estimate.
No polarized eigenfunction, Euler equation or admissibility is assumed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.AffinePolarizedGroundState

open FaberKrahnDevelopment FaberKrahnDevelopment.EuclideanReflection
open H01WeakGradientBridge

theorem exists_polarized_groundState {k : ℝ} (hk : 0 < k)
    (hFK : ∀ U : Set Plane, IsOpen U → 0 < volume U → volume U < ⊤ →
      k ≤ (volume U).toReal * dirichletEig U)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k)
    (ν : UnitNormal) (c : ℝ) (u : L2 Ω × (Fin 2 → L2 Ω))
    (hu : u ∈ H01 Ω) (huMass : energy0 u = 1)
    (huEnergy : energy1 u = dirichletEig Ω)
    (huN : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x) :
    ∃ w : L2 (PolarizedOpenDomain.domain ν c Ω) ×
        (Fin 2 → L2 (PolarizedOpenDomain.domain ν c Ω)),
      w ∈ H01 (PolarizedOpenDomain.domain ν c Ω) ∧ energy0 w = 1 ∧
      energy1 w = dirichletEig Ω ∧
      dirichletEig (PolarizedOpenDomain.domain ν c Ω) = dirichletEig Ω ∧
      ((fullComponent (PolarizedOpenDomain.domain_isOpen ν c hΩ).measurableSet w.1 :
          Plane → ℝ) =ᵐ[volume]
        twoPointPolarization (halfspace ν c) (reflection ν c)
          (fullComponent hΩ.measurableSet u.1)) ∧
      (∀ᵐ x ∂volume,
        0 ≤ fullComponent (PolarizedOpenDomain.domain_isOpen ν c hΩ).measurableSet w.1 x) := by
  let ΩH := PolarizedOpenDomain.domain ν c Ω
  have hΩH : IsOpen ΩH := PolarizedOpenDomain.domain_isOpen ν c hΩ
  have hArea : volume ΩH = volume Ω := PolarizedOpenDomain.volume_domain ν c hΩ.measurableSet
  have hPos : 0 < volume Ω := hΩ.measure_pos volume hne
  have hA : 0 < (volume Ω).toReal := ENNReal.toReal_pos hPos.ne' hfin.ne
  obtain ⟨w, hw, hValue, hwMass, hwEnergy⟩ :=
    AffinePolarizedH01Candidate.exists_affine_polarized_H01_candidate hΩ ν c u hu huN
  have h0 : energy0 w = 1 := hwMass.trans huMass
  have hLower := H01DirichletEuler.dirichletEig_mul_energy0_le w hw
  have hEigenLe : dirichletEig ΩH ≤ dirichletEig Ω := by
    simpa only [h0, mul_one, huEnergy] using hLower.trans hwEnergy
  have hFKH := hFK ΩH hΩH (by rwa [hArea]) (by rwa [hArea])
  have hEigenGe : dirichletEig Ω ≤ dirichletEig ΩH := by
    apply le_of_mul_le_mul_left _ hA
    rw [hArea, ← heq] at hFKH
    exact hFKH
  have hEigen : dirichletEig ΩH = dirichletEig Ω := le_antisymm hEigenLe hEigenGe
  have hEnergy : energy1 w = dirichletEig Ω := by
    apply le_antisymm (hwEnergy.trans_eq huEnergy)
    have hLower' : dirichletEig ΩH ≤ energy1 w := by
      simpa only [h0, mul_one] using hLower
    exact hEigen.symm.trans_le hLower'
  have hRep : (fullComponent hΩH.measurableSet w.1 : Plane → ℝ) =ᵐ[volume]
      twoPointPolarization (halfspace ν c) (reflection ν c)
        (fullComponent hΩ.measurableSet u.1) := by
    have hP := PolarizationL2.coeFn_polarizationLp (halfspace_measurableSet ν c)
      (reflection_measurePreserving ν c) (h01GlobalValue Ω hΩ.measurableSet u)
    rw [← hValue] at hP
    exact hP
  have hUN := H01NonnegativeMinimizer.lpExtendByZero_nonneg_ae hΩ.measurableSet u.1 huN
  have hRN := (reflection_measurePreserving ν c).quasiMeasurePreserving.ae hUN
  refine ⟨w, hw, h0, hEnergy, hEigen, hRep, ?_⟩
  filter_upwards [hRep, hUN, hRN] with x hx hux hrx
  rw [hx]
  by_cases hxH : x ∈ halfspace ν c
  · simpa only [twoPointPolarization, if_pos hxH] using (le_max_of_le_left hux)
  · simpa only [twoPointPolarization, if_neg hxH] using (le_min hux hrx)

end Buckling.AffinePolarizedGroundState
end
end
