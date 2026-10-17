module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import AffinePolarizedGroundState
public import AffineReflectionWeakTransport
public import FaberKrahnEqualityConnected
public import H01GroundStatePositive
public import WeakGradientDifference
public import WeakSMPMinimumBranch
public import PolarizationBranchExtension

/-!
# Actual global polarization branches of an original FK equality ground state

SOURCE_DRAFT: not compiled or registered. The genuine global FK inequality
remains an explicit intermediate input. The original minimizer, polarized
H01 candidate and its Euler equation, both global subsolutions, both weak
gradients, the connected nonempty strict folded domain, and the minimum-zero
identity actually supply the weak SMP branch. No polarization branch, PDE,
classical regularity or finite-component premise is added to the theorem.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.FaberKrahnPolarizationBranch

open FaberKrahnDevelopment FaberKrahnDevelopment.EuclideanReflection
open FaberKrahnDevelopment.PolarizedOpenDomain
open FaberKrahnDevelopment.FoldedDomainConnected
open H01WeakGradientBridge AffineReflectionWeakTransport

lemma min_max_differences (a b : ℝ) : min (max a b - a) (max a b - b) = 0 := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, sub_self, min_eq_right (sub_nonneg.mpr h)]
  · rw [max_eq_left h, sub_self, min_eq_left (sub_nonneg.mpr h)]

theorem global_branch_of_groundState_at_equality {k : ℝ} (hk : 0 < k)
    (hFK : ∀ A : Set Plane, IsOpen A → 0 < volume A → volume A < ⊤ →
      k ≤ (volume A).toReal * dirichletEig A)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (hMass : energy0 u = 1) (hEnergy : energy1 u = dirichletEig Ω)
    (huN : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x)
    (ν : UnitNormal) (c : ℝ) :
    (twoPointPolarization (halfspace ν c) (reflection ν c)
        (fullComponent hΩ.measurableSet u.1) =ᵐ[volume]
      (fullComponent hΩ.measurableSet u.1 : Plane → ℝ)) ∨
    (twoPointPolarization (halfspace ν c) (reflection ν c)
        (fullComponent hΩ.measurableSet u.1) =ᵐ[volume]
      fun x => fullComponent hΩ.measurableSet u.1 (reflection ν c x)) := by
  let U : Plane → ℝ := fullComponent hΩ.measurableSet u.1
  let g : Fin 2 → Plane → ℝ := fun i => fullComponent hΩ.measurableSet (u.2 i)
  have hU2 : MemLp U 2 volume := Lp.memLp _
  have hg2 : ∀ i, MemLp (g i) 2 volume := fun i => Lp.memLp _
  have hUweak := H01_fullLp_hasWeakGradOn hΩ.measurableSet hu
  have heigenvalue := H01NonnegativeMinimizer.dirichletEig_nonneg hΩ hne hfin
  have huEq : energy1 u = dirichletEig Ω * energy0 u := by
    simpa only [hMass, mul_one] using hEnergy
  have hSub : ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, g i x * pderiv i ψ x) ≤ dirichletEig Ω * ∫ x, U x * ψ x := by
    intro ψ hψ hψN
    exact H01ZeroExtensionSubsolution.global_subsolution_of_energy_eq
      hΩ u hu huN huEq heigenvalue hψ hψN
  obtain ⟨hR2, hr2, hRweak, hRSub⟩ :=
    whole_data_reflection ν c (dirichletEig Ω) hU2 hg2 hUweak hSub
  obtain ⟨w, hw, hwMass, hwEnergy, hEigen, hValue, _hwN⟩ :=
    AffinePolarizedGroundState.exists_polarized_groundState hk hFK
      hΩ hne hfin heq ν c u hu hMass hEnergy huN
  let ΩH := domain ν c Ω
  have hΩH : IsOpen ΩH := domain_isOpen ν c hΩ
  let V : Plane → ℝ := fullComponent hΩH.measurableSet w.1
  let h : Fin 2 → Plane → ℝ := fun i => fullComponent hΩH.measurableSet (w.2 i)
  have hV2 : MemLp V 2 volume := Lp.memLp _
  have hh2 : ∀ i, MemLp (h i) 2 volume := fun i => Lp.memLp _
  have hVweak := H01_fullLp_hasWeakGradOn hΩH.measurableSet hw
  let D := foldedDomain ν c Ω
  have hD : IsOpen D := foldedDomain_isOpen ν c hΩ
  have hConnected := FaberKrahnEqualityConnected.isConnected_of_faberKrahn_equality
    hk hFK hΩ hne hfin heq
  have hDconn : IsPreconnected D := isPreconnected_foldedDomain ν c hΩ hConnected.isPreconnected
  have hDne : D.Nonempty := foldedDomain_nonempty ν c hΩ hne
  have hwEq : energy1 w = dirichletEig ΩH * energy0 w := by
    rw [hwEnergy, hwMass, hEigen, mul_one]
  have hEuler : ∀ ψ : Plane → ℝ, IsTestFn D ψ →
      (∑ i, ∫ x, h i x * pderiv i ψ x) = dirichletEig Ω * ∫ x, V x * ψ x := by
    intro ψ hψ
    have hψH : IsTestFn ΩH ψ :=
      ⟨hψ.1, hψ.2.1, hψ.2.2.trans (foldedDomain_subset_domain ν c Ω)⟩
    simpa only [ΩH, V, h, hEigen] using!
      H01FullEuler.full_euler_of_energy_eq hΩH.measurableSet hw hwEq hψH
  have hMax : ∀ᵐ x ∂volume.restrict D,
      V x = max (U x) (U (reflection ν c x)) := by
    filter_upwards [ae_restrict_of_ae hValue, ae_restrict_mem hD.measurableSet] with x hx hxD
    have hxH : x ∈ halfspace ν c :=
      (show c < inner ℝ (ν : Plane) x from hxD.2).le
    simpa only [twoPointPolarization, if_pos hxH] using hx
  have hN1 : ∀ᵐ x ∂volume.restrict D, 0 ≤ V x - U x :=
    hMax.mono fun x hx => sub_nonneg.mpr (hx.symm ▸ le_max_left _ _)
  have hN2 : ∀ᵐ x ∂volume.restrict D, 0 ≤ V x - U (reflection ν c x) :=
    hMax.mono fun x hx => sub_nonneg.mpr (hx.symm ▸ le_max_right _ _)
  have hMin : ∀ᵐ x ∂volume.restrict D,
      min (V x - U x) (V x - U (reflection ν c x)) = 0 := by
    filter_upwards [hMax] with x hx
    rw [hx]
    exact min_max_differences _ _
  have hS1 := WeakGradientDifference.difference_supersolution hD.measurableSet heigenvalue
    hU2 hV2 hg2 hh2 hN1 hEuler hSub
  have hS2 := WeakGradientDifference.difference_supersolution hD.measurableSet heigenvalue
    hR2 hV2 hr2 hh2 hN2 hEuler hRSub
  have hW1 := WeakGradientDifference.weak_gradient_sub hU2 hV2 hg2 hh2 hUweak hVweak
  have hW2 := WeakGradientDifference.weak_gradient_sub hR2 hV2 hr2 hh2 hRweak hVweak
  have hBranch := WeakSMPMinimumBranch.zero_branch hD hDconn hDne
    (hV2.sub hU2) (hV2.sub hR2)
    (fun i => (hh2 i).sub (hg2 i)) (fun i => (hh2 i).sub (hr2 i))
    hW1 hW2 hN1 hN2 hS1 hS2 hMin
  apply PolarizationBranchExtension.ae_global_branch_of_folded_branch ν c hΩ U
    (H01GroundStatePositive.fullComponent_off hΩ.measurableSet u.1)
  rcases hBranch with hz | hz
  · left
    filter_upwards [ae_restrict_of_ae hValue, hz] with x hx hzx
    change V x - U x = 0 at hzx
    exact hx.symm.trans (sub_eq_zero.mp hzx)
  · right
    filter_upwards [ae_restrict_of_ae hValue, hz] with x hx hzx
    change V x - U (reflection ν c x) = 0 at hzx
    exact hx.symm.trans (sub_eq_zero.mp hzx)

end Buckling.FaberKrahnPolarizationBranch
end
end
