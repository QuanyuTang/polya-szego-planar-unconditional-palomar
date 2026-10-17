module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.MainResults
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Lower bounds for the project's actual Dirichlet eigenvalue from test functions

SOURCE_DRAFT (2026-10-17). This isolated file has not yet been compiled.
It is not imported by the production buckling project. The project import
is intended to use the separately verified chunked build artifacts.

The definitions of `Buckling.H01`, `graphH1`, `energy0`, `energy1`, and
`dirichletEig` are the original project definitions, without replacement.
A real smooth bump supported in any nonempty open planar domain produces
a strictly positive mass integral. This supplies nonemptiness of the
Dirichlet admissible class. The original graph-energy identities and
continuity of both energies then extend a test-function quotient bound to
the strong graph closure defining H01, and hence to its quotient infimum.

There is no assumption that the admissible class is nonempty, no new weak
Sobolev definition, and no use of `PaperExternals`, E12, or a mollification
axiom in these proofs. This is a density bridge only, not a proof of a test
function Faber--Krahn estimate or of the equality case.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology

namespace Buckling

/-- A nonempty open planar domain contains an actual smooth compactly
supported test function with strictly positive squared L2 mass. -/
lemma exists_test_energy0_pos {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ φ : {φ // IsTestFn Ω φ}, 0 < ∫ x, φ.1 x ^ 2 := by
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨ε, hε, hBall⟩ := Metric.isOpen_iff.mp hΩ x₀ hx₀
  let b : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hb : IsTestFn Ω b := by
    refine ⟨b.contDiff, b.hasCompactSupport, ?_⟩
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ε / 2 < ε; linarith)).trans hBall
  have hCenter : (b : Plane → ℝ) x₀ = 1 :=
    b.one_of_mem_closedBall (Metric.mem_closedBall_self
      (by show (0 : ℝ) ≤ ε / 4; positivity))
  have hSquareSupport : HasCompactSupport (fun x => (b : Plane → ℝ) x ^ 2) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  refine ⟨⟨b, hb⟩, ?_⟩
  exact (b.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    hSquareSupport (fun x => sq_nonneg _) (x := x₀) (by
      change (b : Plane → ℝ) x₀ ^ 2 ≠ 0
      rw [hCenter]
      norm_num)

/-- In particular the nonzero-denominator test class is inhabited; this is
proved from openness and nonemptiness, rather than assumed. -/
lemma exists_test_energy0_ne {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ φ : {φ // IsTestFn Ω φ}, ∫ x, φ.1 x ^ 2 ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_test_energy0_pos hΩ hne
  exact ⟨φ, hφ.ne'⟩

/-- A lower bound for the Dirichlet quotient of every actual smooth test
function is a lower bound for the original project's `dirichletEig Ω`.
The extension to H01 uses its original strong graph-closure definition. -/
theorem le_dirichletEig_of_test {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (c : ℝ)
    (h : ∀ φ : {φ // IsTestFn Ω φ}, ∫ x, φ.1 x ^ 2 ≠ 0 →
      c ≤ (∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2) / ∫ x, φ.1 x ^ 2) :
    c ≤ dirichletEig Ω := by
  obtain ⟨φ₀, hφ₀⟩ := exists_test_energy0_ne hΩ hne
  haveI : Nonempty {v // v ∈ H01 Ω ∧ energy0 v ≠ 0} :=
    ⟨⟨graphH1 φ₀, subset_closure ⟨φ₀, rfl⟩, by rwa [energy0_graphH1]⟩⟩
  refine le_ciInf fun ⟨v, hv, hv0⟩ => ?_
  have hc0 : Continuous fun w : L2 Ω × (Fin 2 → L2 Ω) => energy0 w := by
    unfold energy0
    fun_prop
  have hc1 : Continuous fun w : L2 Ω × (Fin 2 → L2 Ω) => energy1 w := by
    unfold energy1
    fun_prop
  have hContinuous : ContinuousAt (fun w => energy1 w / energy0 w) v :=
    hc1.continuousAt.div hc0.continuousAt hv0
  obtain ⟨u, hu, hLimit⟩ := mem_closure_iff_seq_limit.mp hv
  have hMassLimit : Tendsto (fun n => energy0 (u n)) atTop (𝓝 (energy0 v)) :=
    (hc0.tendsto v).comp hLimit
  have hEventually : ∀ᶠ n in atTop, energy0 (u n) ≠ 0 :=
    hMassLimit.eventually_ne hv0
  apply ge_of_tendsto (hContinuous.tendsto.comp hLimit)
  filter_upwards [hEventually] with n hn
  obtain ⟨φ, hφ⟩ := hu n
  simp only [Function.comp_apply, ← hφ] at hn ⊢
  rw [energy1_graphH1, energy0_graphH1] at *
  exact h φ hn

end Buckling
