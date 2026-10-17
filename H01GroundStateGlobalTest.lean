module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01BoundaryTruncation
public import H01GraphEuler
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Global compact test inequalities inside the actual original domain

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

An actual nonnegative original H01 attaining the original Dirichlet value
can be tested against min(u,epsilon*psi), even when the nonnegative global
test psi meets the boundary. Actual boundary truncation supplies membership,
the actual value, and the actual graph gradient. The original Euler identity
then gives an inequality on the actual high set. All low/high terms and
actual products have genuine integrability producers below.

For epsilon_n=1/(n+1), the high-set integrand converges to the full gradient
pairing. The only zero-layer fact used is the actual graph W12 level-set
theorem. L2 Holder supplies a common integrable bound for dominated
convergence. No finite-area, regularity, zero-extension PDE or subsolution
hypothesis is added. The coefficient nonnegativity is explicit here and
will be supplied by the natural nonnegative-minimizer consumer later.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01GroundStateGlobalTest

open EllipticPdes H01AbsoluteValue

lemma test_value_memLp {Ω : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) : MemLp ψ 2 (volume.restrict Ω) :=
  hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1

lemma test_gradient_memLp {Ω : Set Plane} {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) : MemLp (gradient ψ) 2 (volume.restrict Ω) :=
  (continuous_gradient_of_mem (show ψ ∈ testFunctions univ from hψ)).memLp_of_hasCompactSupport
    (hasCompactSupport_gradient_of_mem (show ψ ∈ testFunctions univ from hψ))

lemma integrable_value_test {Ω : Set Plane} (v : L2 Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) :
    Integrable (fun x => v x * ψ x) (volume.restrict Ω) := by
  let h := test_value_memLp (Ω := Ω) hψ
  refine (MeasureTheory.L2.integrable_mul v (h.toLp ψ)).congr ?_
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx]

lemma integrable_gradient_test {Ω : Set Plane} (U : GraphData Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) :
    Integrable (fun x => inner ℝ (H1Graph.gradL U x) (gradient ψ x))
      (volume.restrict Ω) := by
  let h := test_gradient_memLp (Ω := Ω) hψ
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (H1Graph.gradL U) (h.toLp (gradient ψ))).congr ?_
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx]

lemma integrable_gradient_sq {Ω : Set Plane} (U : GraphData Ω) :
    Integrable (fun x => ‖H1Graph.gradL U x‖ ^ 2) (volume.restrict Ω) := by
  refine (MeasureTheory.L2.integrable_inner (𝕜 := ℝ)
    (H1Graph.gradL U) (H1Graph.gradL U)).congr ?_
  exact ae_of_all _ fun x => real_inner_self_eq_norm_sq _

lemma high_set_nullMeasurable {Ω : Set Plane} (v : L2 Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) (ε : ℝ) :
    NullMeasurableSet {x | ε * ψ x < v x} (volume.restrict Ω) :=
  _root_.nullMeasurableSet_lt
    (hψ.1.continuous.aemeasurable.const_mul ε)
    (Lp.aestronglyMeasurable v).aemeasurable

lemma integrable_high_gradient_test {Ω : Set Plane} (v : L2 Ω) (U : GraphData Ω)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) (ε : ℝ) :
    Integrable (fun x => if ε * ψ x < v x then
      inner ℝ (H1Graph.gradL U x) (gradient ψ x) else 0) (volume.restrict Ω) := by
  simpa only [Set.indicator, Set.mem_setOf_eq] using!
    (integrable_gradient_test U hψ).indicator₀ (high_set_nullMeasurable v hψ ε)

/-- The finite positive-epsilon boundary-minimum estimate. The low-set
gradient-square term is genuinely integrable and is discarded by its sign. -/
theorem high_gradient_test_le_of_energy_eq {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (huN : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ u.1 x)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    (heigenvalue : 0 ≤ dirichletEig Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) (hψN : ∀ x, 0 ≤ ψ x) {ε : ℝ} (hε : 0 < ε) :
    (∫ x in Ω, if ε * ψ x < u.1 x then
      inner ℝ (H1Graph.gradL (toGraph Ω u hu : GraphData Ω) x) (gradient ψ x) else 0) ≤
      dirichletEig Ω * ∫ x in Ω, u.1 x * ψ x := by
  classical
  let μ : Measure Plane := volume.restrict Ω
  let U : GraphData Ω := toGraph Ω u hu
  let g : Plane → Plane := H1Graph.gradL U
  let b : Plane → ℝ := fun x => inner ℝ (g x) (gradient ψ x)
  let A : Set Plane := {x | ε * ψ x < u.1 x}
  let low : Plane → ℝ := Aᶜ.indicator (fun x => ‖g x‖ ^ 2)
  let high : Plane → ℝ := A.indicator b
  have hA : NullMeasurableSet A μ := high_set_nullMeasurable u.1 hψ ε
  have hLow : Integrable low μ := (integrable_gradient_sq U).indicator₀ hA.compl
  have hHigh : Integrable high μ := (integrable_gradient_test U hψ).indicator₀ hA
  have hUψ : Integrable (fun x => u.1 x * ψ x) μ := integrable_value_test u.1 hψ
  let η : Plane → ℝ := ε • ψ
  have hη : IsTestFn univ η :=
    (testFunctions (univ : Set Plane)).smul_mem ε (show ψ ∈ testFunctions univ from hψ)
  have hηN : ∀ x, 0 ≤ η x := fun x => mul_nonneg hε.le (hψN x)
  have hηgrad : gradient η = ε • gradient ψ :=
    gradient_smul_of_mem (show ψ ∈ testFunctions univ from hψ) ε
  obtain ⟨m, hm, hmValue, hmGradient⟩ :=
    H01BoundaryTruncation.exists_min_H01 hΩ u hu hη hηN
  let M : GraphData Ω := toGraph Ω m hm
  have hPair : Integrable (fun x => inner ℝ (g x) (H1Graph.gradL M x)) μ :=
    H01GraphEuler.integrable_graph_gradient_pair U M
  have hUM : Integrable (fun x => u.1 x * m.1 x) μ :=
    MeasureTheory.L2.integrable_mul u.1 m.1
  have hEuler : (∫ x, inner ℝ (g x) (H1Graph.gradL M x) ∂μ) =
      dirichletEig Ω * ∫ x, u.1 x * m.1 x ∂μ := by
    simpa only [M, U, g, μ, toGraph_fnL] using!
      H01GraphEuler.graph_integral_euler_of_energy_eq u hu heq M (toGraph Ω m hm).2
  have hDecomp : (∫ x, inner ℝ (g x) (H1Graph.gradL M x) ∂μ) =
      (∫ x, low x ∂μ) + ε * ∫ x, high x ∂μ := by
    calc
      (∫ x, inner ℝ (g x) (H1Graph.gradL M x) ∂μ) =
          ∫ x, low x + ε * high x ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hmGradient] with x hx
        have hηx : η x = ε * ψ x := rfl
        have hηdx : gradient η x = ε • gradient ψ x := congrFun hηgrad x
        have hmG : H1Graph.gradL M x =
            if ε * ψ x < u.1 x then ε • gradient ψ x else g x := by
          simpa only [hηx, hηdx] using hx
        rw [hmG]
        by_cases hxA : ε * ψ x < u.1 x
        · simp [low, high, A, b, hxA, inner_smul_right]
        · simp [low, high, A, b, hxA, real_inner_self_eq_norm_sq]
      _ = (∫ x, low x ∂μ) + ε * ∫ x, high x ∂μ := by
        rw [integral_add hLow (hHigh.const_mul ε), integral_const_mul]
  have hLowN : 0 ≤ ∫ x, low x ∂μ := by
    apply integral_nonneg
    intro x
    by_cases hx : x ∈ Aᶜ <;> simp [low, hx, sq_nonneg]
  have hMass : (∫ x, u.1 x * m.1 x ∂μ) ≤ ε * ∫ x, u.1 x * ψ x ∂μ := by
    have hPoint : (fun x => u.1 x * m.1 x) ≤ᵐ[μ]
        (fun x => ε * (u.1 x * ψ x)) := by
      filter_upwards [huN, hmValue] with x hux hmx
      have hηx : η x = ε * ψ x := rfl
      rw [hmx, hηx]
      calc
        u.1 x * min (u.1 x) (ε * ψ x) ≤ u.1 x * (ε * ψ x) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hux
        _ = ε * (u.1 x * ψ x) := by ring
    simpa only [integral_const_mul] using
      integral_mono_ae hUM (hUψ.const_mul ε) hPoint
  have hBound : ε * (∫ x, high x ∂μ) ≤
      ε * (dirichletEig Ω * ∫ x, u.1 x * ψ x ∂μ) := by
    calc
      ε * (∫ x, high x ∂μ) ≤ (∫ x, low x ∂μ) + ε * ∫ x, high x ∂μ :=
        le_add_of_nonneg_left hLowN
      _ = dirichletEig Ω * ∫ x, u.1 x * m.1 x ∂μ := hDecomp.symm.trans hEuler
      _ ≤ dirichletEig Ω * (ε * ∫ x, u.1 x * ψ x ∂μ) :=
        mul_le_mul_of_nonneg_left hMass heigenvalue
      _ = ε * (dirichletEig Ω * ∫ x, u.1 x * ψ x ∂μ) := by ring
  have hh := (mul_le_mul_iff_right₀ hε).mp hBound
  simpa only [high, A, Set.indicator, Set.mem_setOf_eq, b] using hh

/-- A nonnegative actual original ground state satisfies the global compact
test inequality inside its original domain. No zero-extension transport is
performed in this theorem. -/
theorem global_test_le_of_energy_eq {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (huN : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ u.1 x)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    (heigenvalue : 0 ≤ dirichletEig Ω) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) (hψN : ∀ x, 0 ≤ ψ x) :
    (∫ x in Ω, inner ℝ
      (H1Graph.gradL (toGraph Ω u hu : GraphData Ω) x) (gradient ψ x)) ≤
      dirichletEig Ω * ∫ x in Ω, u.1 x * ψ x := by
  classical
  let μ : Measure Plane := volume.restrict Ω
  let U : GraphData Ω := toGraph Ω u hu
  let b : Plane → ℝ := fun x => inner ℝ (H1Graph.gradL U x) (gradient ψ x)
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let F : ℕ → Plane → ℝ := fun n x => if ε n * ψ x < u.1 x then b x else 0
  have hε : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  have hεt : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hB : Integrable b μ := integrable_gradient_test U hψ
  have hF : ∀ n, Integrable (F n) μ :=
    fun n => integrable_high_gradient_test u.1 U hψ (ε n)
  have hZero : ∀ᵐ x ∂μ, u.1 x = 0 → H1Graph.gradL U x = 0 := by
    have hz := H1Graph.ae_gradL_eq_zero_of_fnL_eq hΩ
      (H1Graph.H01_le_W12 (toGraph Ω u hu).2) (0 : ℝ)
    simpa only [toGraph_fnL] using hz
  have hBound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ ‖b x‖ := by
    intro n
    exact ae_of_all _ fun x => by
      by_cases hx : ε n * ψ x < u.1 x
      · simp only [F, if_pos hx, le_refl]
      · simpa only [F, if_neg hx, norm_zero] using norm_nonneg (b x)
  have hLimit : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (b x)) := by
    filter_upwards [huN, hZero] with x hux hzx
    by_cases hx : u.1 x = 0
    · have hb : b x = 0 := by simp only [b, hzx hx, inner_zero_left]
      simpa only [F, hb, ite_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · have hup : 0 < u.1 x := lt_of_le_of_ne hux (Ne.symm hx)
      have ht : Tendsto (fun n => ε n * ψ x) atTop (𝓝 0) := by
        simpa only [zero_mul] using hεt.mul_const (ψ x)
      have hHigh : ∀ᶠ n in atTop, ε n * ψ x < u.1 x :=
        ht.eventually_lt tendsto_const_nhds hup
      refine Tendsto.congr' ?_
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => b x) atTop (𝓝 (b x)))
      filter_upwards [hHigh] with n hn
      simp only [F, if_pos hn]
  have hIntegral : Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, b x ∂μ)) :=
    tendsto_integral_of_dominated_convergence (fun x => ‖b x‖)
      (fun n => (hF n).aestronglyMeasurable) hB.norm hBound hLimit
  exact le_of_tendsto' hIntegral fun n =>
    high_gradient_test_le_of_energy_eq hΩ u hu huN heq heigenvalue hψ hψN (hε n)

end Buckling.H01GroundStateGlobalTest

end

end
