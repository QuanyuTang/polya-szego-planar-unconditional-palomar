module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01GroundStateGlobalTest
public import H01WeakGradientBridge
public import H01NonnegativeMinimizer
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The actual zero extension of an original ground state is a subsolution

SOURCE_DRAFT: not registered or native checked.
The graph gradient is identified coordinate by coordinate with the actual
original tuple. Real restricted test pairings are transported through the
actual indicator representative of lpExtendByZero, not through matching
energies. The whole-space weak gradient is supplied independently by the
original H01 closure bridge. The final existence consumer has only open,
nonempty, finite-area domain inputs.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01ZeroExtensionSubsolution

open EllipticPdes H01AbsoluteValue H01WeakGradientBridge

lemma toGraph_coordinate_ae {Ω : Set Plane}
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω) (i : Fin 2) :
    (u.2 i : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => (H1Graph.gradL (toGraph Ω u hu : GraphData Ω) x) i := by
  have he := congrArg (fun V : H1HilbertAmbient Ω => V i.succ)
    (H01GraphEuler.h1Equiv_toGraph Ω u hu)
  rw [H1Graph.h1Equiv_apply_succ] at he
  change (EuclideanSpace.proj (𝕜 := ℝ) i : Plane →L[ℝ] ℝ).compLp
    (H1Graph.gradL (toGraph Ω u hu : GraphData Ω)) = u.2 i at he
  rw [← he]
  exact (EuclideanSpace.proj (𝕜 := ℝ) i : Plane →L[ℝ] ℝ).coeFn_compLp
    (p := 2) (H1Graph.gradL (toGraph Ω u hu : GraphData Ω))

lemma gradient_test_coordinate (ψ : Plane → ℝ) (x : Plane) (i : Fin 2) :
    (gradient ψ x) i = pderiv i ψ x := by
  simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, pderiv] using!
    EllipticPdes.inner_gradient_right ψ x (EuclideanSpace.single i 1)

/-- Both sides use the actual original derivatives; the vector graph
notation is just an isometric coordinate transport. -/
lemma sum_restricted_pair_eq_graph {Ω : Set Plane}
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) :
    (∑ i, ∫ x in Ω, u.2 i x * pderiv i ψ x) =
      ∫ x in Ω, inner ℝ
        (H1Graph.gradL (toGraph Ω u hu : GraphData Ω) x) (gradient ψ x) := by
  have hi : ∀ i, Integrable (fun x => u.2 i x * pderiv i ψ x) (volume.restrict Ω) :=
    fun i => H01GroundStateGlobalTest.integrable_value_test (u.2 i) (hψ.pderiv i)
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (toGraph_coordinate_ae u hu)] with x hx
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i, gradient_test_coordinate]
  exact (Real.inner_apply _ _).symm

/-- A literal scalar zero-extension pairing equals the original restricted
pairing. The smooth compact test supplies real integrability on both sides. -/
lemma fullComponent_pairing_eq {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (f : L2 Ω) {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) :
    (∫ x, fullComponent hΩm f x * ψ x) = ∫ x in Ω, f x * ψ x := by
  have hfull : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hfullPair : Integrable (fun x => fullComponent hΩm f x * ψ x) volume :=
    (Lp.memLp (fullComponent hΩm f)).integrable_mul hfull
  have hrestrictedPair := H01GroundStateGlobalTest.integrable_value_test f hψ
  calc
    (∫ x, fullComponent hΩm f x * ψ x) =
        ∫ x, Ω.indicator (fun x => f x * ψ x) x := by
      apply integral_congr_ae
      filter_upwards [coeFn_fullComponent hΩm f] with x hx
      rw [hx]
      by_cases hxΩ : x ∈ Ω
      · rw [zeroExtend, Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ]
      · rw [zeroExtend, Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ,
          zero_mul]
    _ = ∫ x in Ω, f x * ψ x := integral_indicator hΩm

/-- The actual whole-space derivatives of a nonnegative original ground
state satisfy the full global compact-test subsolution inequality. -/
theorem global_subsolution_of_energy_eq {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (huN : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    (heigenvalue : 0 ≤ dirichletEig Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) (hψN : ∀ x, 0 ≤ ψ x) :
    (∑ i, ∫ x, fullComponent hΩ.measurableSet (u.2 i) x * pderiv i ψ x) ≤
      dirichletEig Ω * ∫ x, fullComponent hΩ.measurableSet u.1 x * ψ x := by
  have hsum : (∑ i, ∫ x, fullComponent hΩ.measurableSet (u.2 i) x * pderiv i ψ x) =
      ∑ i, ∫ x in Ω, u.2 i x * pderiv i ψ x := by
    apply Finset.sum_congr rfl
    intro i _
    exact fullComponent_pairing_eq hΩ.measurableSet (u.2 i) (hψ.pderiv i)
  rw [hsum, fullComponent_pairing_eq hΩ.measurableSet _ hψ,
    sum_restricted_pair_eq_graph u hu hψ]
  exact H01GroundStateGlobalTest.global_test_le_of_energy_eq hΩ u hu huN heq
    heigenvalue hψ hψN

/-- Natural domain inputs actually produce a nonnegative original
minimizer and its full-space weak-gradient/subsolution data. No PDE or
admissible boundary test is postulated in the conclusion. -/
theorem exists_nonnegative_groundState_with_global_subsolution {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤) :
    ∃ u : L2 Ω × (Fin 2 → L2 Ω), u ∈ H01 Ω ∧ energy0 u = 1 ∧
      energy1 u = dirichletEig Ω ∧
      (∀ᵐ x ∂volume, 0 ≤ fullComponent hΩ.measurableSet u.1 x) ∧
      EllipticPdes.Embedding.HasWeakGradOn univ
        (fullComponent hΩ.measurableSet u.1)
        (fun i => fullComponent hΩ.measurableSet (u.2 i)) ∧
      ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
        (∑ i, ∫ x, fullComponent hΩ.measurableSet (u.2 i) x * pderiv i ψ x) ≤
          dirichletEig Ω * ∫ x, fullComponent hΩ.measurableSet u.1 x * ψ x := by
  obtain ⟨u, hu, h0, h1, huN, hfullN⟩ :=
    exists_H01_nonnegative_dirichletEig_minimizer hΩ hne hfin
  refine ⟨u, hu, h0, h1, hfullN, H01_fullLp_hasWeakGradOn hΩ.measurableSet hu, ?_⟩
  intro ψ hψ hψN
  apply global_subsolution_of_energy_eq hΩ u hu huN
    (by simpa only [h0, mul_one] using h1)
    (H01NonnegativeMinimizer.dirichletEig_nonneg hΩ hne hfin) hψ hψN

end Buckling.H01ZeroExtensionSubsolution

end

end
