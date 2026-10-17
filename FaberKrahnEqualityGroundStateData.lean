module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FaberKrahnPolarizationBranch

/-!
# Natural FK equality inputs produce an actual density with every reflection branch

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The global FK inequality is explicitly an intermediate input, to be supplied
by the actual original inequality development. An original H01 mass-one
nonnegative minimizer is genuinely produced. Its literal full-space zero
extension is L2 and L1, has positive real integral, has positive set equal
almost everywhere to the original domain, and satisfies the global
polarization/reflection alternative for every affine halfspace.

No ground state, positivity, branch, reflected PDE, regularity, boundedness,
or moment premise is added. These are consumers of the actual preceding
producers, not a proof-status claim about the uncompiled equality chain.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Buckling.FaberKrahnEqualityGroundStateData

open FaberKrahnDevelopment FaberKrahnDevelopment.EuclideanReflection
open H01WeakGradientBridge

/-- Natural equality data yield the actual original tuple and all global
properties of its actual full-space zero-extended value. The quantifier
over affine reflections is inside the existence of this single tuple. -/
theorem exists_groundState_with_global_branches {k : ℝ} (hk : 0 < k)
    (hFK : ∀ A : Set Plane, IsOpen A → 0 < volume A → volume A < ⊤ →
      k ≤ (volume A).toReal * dirichletEig A)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k) :
    ∃ u : L2 Ω × (Fin 2 → L2 Ω), u ∈ H01 Ω ∧ energy0 u = 1 ∧
      energy1 u = dirichletEig Ω ∧
      (∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x) ∧
      MemLp (fullComponent hΩ.measurableSet u.1) 2 volume ∧
      Integrable (fullComponent hΩ.measurableSet u.1) volume ∧
      (∀ᵐ x ∂volume, 0 ≤ fullComponent hΩ.measurableSet u.1 x) ∧
      (0 < ∫ x, fullComponent hΩ.measurableSet u.1 x) ∧
      ({x | 0 < fullComponent hΩ.measurableSet u.1 x} =ᵐ[volume] Ω) ∧
      (∀ᵐ x ∂volume, x ∉ Ω → fullComponent hΩ.measurableSet u.1 x = 0) ∧
      ∀ (ν : UnitNormal) (c : ℝ),
        (twoPointPolarization (halfspace ν c) (reflection ν c)
            (fullComponent hΩ.measurableSet u.1) =ᵐ[volume]
          (fullComponent hΩ.measurableSet u.1 : Plane → ℝ)) ∨
        (twoPointPolarization (halfspace ν c) (reflection ν c)
            (fullComponent hΩ.measurableSet u.1) =ᵐ[volume]
          fun x => fullComponent hΩ.measurableSet u.1 (reflection ν c x)) := by
  obtain ⟨u, hu, hMass, hEnergy, huN, hFullN⟩ :=
    exists_H01_nonnegative_dirichletEig_minimizer hΩ hne hfin
  have hN : ∀ᵐ x ∂volume, 0 ≤ fullComponent hΩ.measurableSet u.1 x := hFullN
  have hConnected := FaberKrahnEqualityConnected.isConnected_of_faberKrahn_equality
    hk hFK hΩ hne hfin heq
  have heigenvalue := H01NonnegativeMinimizer.dirichletEig_nonneg hΩ hne hfin
  have hEnergyEq : energy1 u = dirichletEig Ω * energy0 u := by
    simpa only [hMass, mul_one] using hEnergy
  have hPosSet := H01GroundStatePositive.positive_set_ae_eq_domain
    hΩ hConnected.isPreconnected hu hMass hEnergyEq hN heigenvalue
  refine ⟨u, hu, hMass, hEnergy, huN, Lp.memLp _,
    H01GroundStatePositive.fullComponent_integrable hΩ.measurableSet hfin u.1,
    hN, H01GroundStatePositive.integral_full_value_pos hΩ.measurableSet hfin u hMass hN,
    hPosSet, H01GroundStatePositive.fullComponent_off hΩ.measurableSet u.1, ?_⟩
  intro ν c
  exact FaberKrahnPolarizationBranch.global_branch_of_groundState_at_equality
    hk hFK hΩ hne hfin heq u hu hMass hEnergy huN ν c

/-- The same naturally produced function, exposed without the original
tuple so that potential/averaging geometry can consume literal functions.
This does not assume any polarization branch or positive-set identity. -/
theorem exists_density_with_global_branches {k : ℝ} (hk : 0 < k)
    (hFK : ∀ A : Set Plane, IsOpen A → 0 < volume A → volume A < ⊤ →
      k ≤ (volume A).toReal * dirichletEig A)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k) :
    ∃ U : Plane → ℝ, MemLp U 2 volume ∧ Integrable U volume ∧
      (∀ᵐ x ∂volume, 0 ≤ U x) ∧ (0 < ∫ x, U x) ∧
      ({x | 0 < U x} =ᵐ[volume] Ω) ∧
      (∀ᵐ x ∂volume, x ∉ Ω → U x = 0) ∧
      ∀ (ν : UnitNormal) (c : ℝ),
        (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume] U) ∨
        (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume]
          fun x => U (reflection ν c x)) := by
  obtain ⟨u, _hu, _hMass, _hEnergy, _huN, hU2, hI, hN, hIP, hPosSet, hOff, hBranches⟩ :=
    exists_groundState_with_global_branches hk hFK hΩ hne hfin heq
  exact ⟨fullComponent hΩ.measurableSet u.1, hU2, hI, hN, hIP, hPosSet, hOff, hBranches⟩

end Buckling.FaberKrahnEqualityGroundStateData

end

end
