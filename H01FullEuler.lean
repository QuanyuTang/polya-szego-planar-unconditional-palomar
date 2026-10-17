module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01ZeroExtensionSubsolution

/-!
# The actual full-space Euler equation for interior compact tests

SOURCE_DRAFT: not compiled or registered. This transports the original
H01 variational identity to actual zero-extended L2 representatives.
The test belongs to the actual original domain. No weak PDE is assumed.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01FullEuler

open H01WeakGradientBridge H01ZeroExtensionSubsolution

lemma inner_right_test {Ω : Set Plane} (f : L2 Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn Ω ψ) : inner ℝ f hψ.toL2 = ∫ x in Ω, f x * ψ x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hrep := hψ.memLp.coeFn_toLp
  change (hψ.toL2 : Plane → ℝ) =ᵐ[volume.restrict Ω] ψ at hrep
  filter_upwards [hrep] with x hx
  simp only [hx, Real.inner_apply, mul_comm]

theorem full_euler_of_energy_eq {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    {u : L2 Ω × (Fin 2 → L2 Ω)} (hu : u ∈ H01 Ω)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    {ψ : Plane → ℝ} (hψ : IsTestFn Ω ψ) :
    (∑ i, ∫ x, fullComponent hΩm (u.2 i) x * pderiv i ψ x) =
      dirichletEig Ω * ∫ x, fullComponent hΩm u.1 x * ψ x := by
  have hψG : IsTestFn univ ψ := ⟨hψ.1, hψ.2.1, subset_univ _⟩
  have hgraph : graphH1 ⟨ψ, hψ⟩ ∈ H01 Ω :=
    subset_closure (mem_range_self (f := graphH1 (Ω := Ω)) ⟨ψ, hψ⟩)
  have he := H01DirichletEuler.euler_of_energy_eq hu heq
    (graphH1 ⟨ψ, hψ⟩) hgraph
  change (∑ i, inner ℝ (u.2 i) (hψ.pderiv i).toL2) =
    dirichletEig Ω * inner ℝ u.1 hψ.toL2 at he
  simp_rw [inner_right_test] at he
  have hsum : (∑ i, ∫ x, fullComponent hΩm (u.2 i) x * pderiv i ψ x) =
      ∑ i, ∫ x in Ω, u.2 i x * pderiv i ψ x := by
    apply Finset.sum_congr rfl
    intro i _
    exact fullComponent_pairing_eq hΩm (u.2 i) (hψG.pderiv i)
  rw [hsum, fullComponent_pairing_eq hΩm u.1 hψG]
  exact he

end Buckling.H01FullEuler
end
end
