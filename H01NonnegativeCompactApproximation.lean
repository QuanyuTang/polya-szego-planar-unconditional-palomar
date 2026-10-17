module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01UniformTails
public import AbsoluteValueEnergy
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Sequences

/-!
# Actual nonnegative compact Lipschitz approximations to the original H01

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The sequence is obtained from the original graph closure, and its literal
absolute values are used. Their whole-space L2 classes converge strongly
to the actual zero extension of a nonnegative original value coordinate.
Both real energies converge because they equal the original smooth graph
energies term by term, using the actual absolute-value derivative identity.

The Lipschitz constants may depend on the sequence index. No finite-area,
bounded-domain, minimizer, weak-compactness, polarization, or positive
approximation hypothesis is introduced. No full H1 strong continuity of
the absolute-value map is claimed or used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01NonnegativeCompactApproximation

def absTest {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) (x : Plane) : ℝ := |φ.1 x|

lemma absTest_nonneg {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) (x : Plane) :
    0 ≤ absTest φ x := abs_nonneg _

lemma continuous_absTest {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    Continuous (absTest φ) := φ.2.1.continuous.abs

lemma hasCompactSupport_absTest {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    HasCompactSupport (absTest φ) :=
  φ.2.2.1.comp_left (g := fun t : ℝ => |t|) (by simp)

lemma tsupport_absTest_subset {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    tsupport (absTest φ) ⊆ Ω := by
  refine (show tsupport (absTest φ) ⊆ tsupport φ.1 from ?_).trans φ.2.2.2
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hφ
  exact hx (by simp only [absTest, hφ, abs_zero])

lemma memLp_absTest {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    MemLp (absTest φ) 2 volume :=
  (continuous_absTest φ).memLp_of_hasCompactSupport (hasCompactSupport_absTest φ)

/-- The actual whole-space L2 class, with its produced MemLp certificate. -/
def absTestLp {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) : Lp ℝ 2 (volume : Measure Plane) :=
  (memLp_absTest φ).toLp (absTest φ)

lemma coeFn_absTestLp {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    (absTestLp φ : Plane → ℝ) =ᵐ[volume] absTest φ :=
  (memLp_absTest φ).coeFn_toLp

lemma lipschitzWith_absTest {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ})
    {K : ℝ≥0} (hK : LipschitzWith K φ.1) : LipschitzWith K (absTest φ) :=
  FaberKrahnDevelopment.lipschitzWith_absoluteValue hK

lemma integrable_absTest_sq {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    Integrable (fun x => absTest φ x ^ 2) volume := (memLp_absTest φ).integrable_sq

/-- The derivative-energy density really is integrable. Its absolute-value
identity is not used only under the Bochner integral's zero convention. -/
lemma integrable_absTest_gradient_sq {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ})
    {K : ℝ≥0} (hK : LipschitzWith K φ.1) :
    Integrable (fun x => ‖fderiv ℝ (absTest φ) x‖ ^ 2) volume := by
  have hc : Continuous (fun x => ‖fderiv ℝ φ.1 x‖ ^ 2) :=
    (φ.2.1.continuous_fderiv (by simp)).norm.fun_pow 2
  have hs : HasCompactSupport (fun x => ‖fderiv ℝ φ.1 x‖ ^ 2) :=
    (φ.2.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L => ‖L‖ ^ 2) (by simp)
  have hOrig : Integrable (fun x => ‖fderiv ℝ φ.1 x‖ ^ 2) (volume : Measure Plane) :=
    hc.integrable_of_hasCompactSupport hs
  apply hOrig.congr
  exact (FaberKrahnDevelopment.ae_norm_fderiv_absoluteValue (μ := volume) hK).mono
    fun x hx => (congrArg (fun t : ℝ => t ^ 2) hx).symm

lemma integral_absTest_sq_eq_energy0 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    (∫ x, absTest φ x ^ 2) = energy0 (graphH1 φ) := by
  change (∫ x, |φ.1 x| ^ 2) = ‖φ.2.toL2‖ ^ 2
  rw [FaberKrahnDevelopment.integral_absoluteValue_sq volume φ.1]
  exact (FiniteAreaCore1.integral_sq φ.2).symm

lemma integral_absTest_gradient_sq_eq_energy1 {Ω : Set Plane}
    (φ : {φ // IsTestFn Ω φ}) {K : ℝ≥0} (hK : LipschitzWith K φ.1) :
    (∫ x, ‖fderiv ℝ (absTest φ) x‖ ^ 2) = energy1 (graphH1 φ) :=
  (FaberKrahnDevelopment.integral_norm_fderiv_absoluteValue_sq (μ := volume) hK).trans
    (FiniteAreaCore1.energy1_graphH1 φ).symm

/-- The actual zero extension of a genuine original test is represented
by the original whole-space smooth function almost everywhere. -/
lemma h01GlobalValue_graph_ae {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (φ : {φ // IsTestFn Ω φ}) :
    (h01GlobalValue Ω hΩm (graphH1 φ) : Plane → ℝ) =ᵐ[volume] φ.1 := by
  have hφ := (ae_restrict_iff' hΩm).mp φ.2.memLp.coeFn_toLp
  have hJ := coeFn_lpExtendByZero hΩm φ.2.toL2
  change (lpExtendByZero volume 2 Ω hΩm φ.2.toL2 : Plane → ℝ) =ᵐ[volume] φ.1
  filter_upwards [hJ, hφ] with x hx hφx
  change x ∈ Ω → (φ.2.toL2 : Plane → ℝ) x = φ.1 x at hφx
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, hφx hxΩ]
  · rw [Set.indicator_of_notMem hxΩ, FiniteAreaCore1.eq_zero_of_notMem φ.2 hxΩ]

lemma h01GlobalValue_nonneg_ae {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu0 : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x) :
    ∀ᵐ x ∂volume, 0 ≤ h01GlobalValue Ω hΩm u x := by
  have hcond := (ae_restrict_iff' hΩm).mp hu0
  have hJ := coeFn_lpExtendByZero hΩm u.1
  change ∀ᵐ x ∂volume, 0 ≤ (lpExtendByZero volume 2 Ω hΩm u.1 : Plane → ℝ) x
  filter_upwards [hJ, hcond] with x hx hu
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ]
    exact hu hxΩ
  · simp only [Set.indicator_of_notMem hxΩ, le_refl]

/-- Actual representative control gives a contraction estimate against
a nonnegative target. No new abstract absolute-value L2 map is postulated. -/
lemma norm_absTestLp_sub_globalValue_le {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (φ : {φ // IsTestFn Ω φ}) (u : L2 Ω × (Fin 2 → L2 Ω))
    (hu0 : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x) :
    ‖absTestLp φ - h01GlobalValue Ω hΩm u‖ ≤
      ‖h01GlobalValue Ω hΩm (graphH1 φ) - h01GlobalValue Ω hΩm u‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (absTestLp φ) (h01GlobalValue Ω hΩm u),
    Lp.coeFn_sub (h01GlobalValue Ω hΩm (graphH1 φ)) (h01GlobalValue Ω hΩm u),
    coeFn_absTestLp φ, h01GlobalValue_graph_ae hΩm φ, h01GlobalValue_nonneg_ae hΩm u hu0]
      with x hsubAbs hsubOrig hAbs hOrig hu
  calc
    ‖(absTestLp φ - h01GlobalValue Ω hΩm u) x‖ =
        ‖|φ.1 x| - h01GlobalValue Ω hΩm u x‖ := by
      simp only [hsubAbs, Pi.sub_apply, hAbs, absTest]
    _ ≤ ‖φ.1 x - h01GlobalValue Ω hΩm u x‖ := by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hu] using
        abs_abs_sub_abs_le_abs_sub (φ.1 x) (h01GlobalValue Ω hΩm u x)
    _ = ‖(h01GlobalValue Ω hΩm (graphH1 φ) - h01GlobalValue Ω hΩm u) x‖ := by
      rw [hsubOrig, Pi.sub_apply, hOrig]

/-- The original defining graph closure supplies the actual smooth tests.
Their absolute values have all the stated geometric and analytic data;
no nonnegative approximation or absolute-value H1 continuity is assumed. -/
theorem exists_nonnegative_compact_lipschitz_approximation {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (hu0 : ∀ᵐ x ∂volume.restrict Ω, 0 ≤ u.1 x) :
    ∃ (φ : ℕ → {φ // IsTestFn Ω φ}) (K : ℕ → ℝ≥0),
      Tendsto (fun n => graphH1 (φ n)) atTop (𝓝 u) ∧
      (∀ n, LipschitzWith (K n) (absTest (φ n))) ∧
      (∀ n, (∀ x, 0 ≤ absTest (φ n) x) ∧ HasCompactSupport (absTest (φ n)) ∧
        tsupport (absTest (φ n)) ⊆ Ω ∧
        Integrable (fun x => absTest (φ n) x ^ 2) volume ∧
        Integrable (fun x => ‖fderiv ℝ (absTest (φ n)) x‖ ^ 2) volume) ∧
      Tendsto (fun n => absTestLp (φ n)) atTop (𝓝 (h01GlobalValue Ω hΩ.measurableSet u)) ∧
      Tendsto (fun n => ∫ x, absTest (φ n) x ^ 2) atTop (𝓝 (energy0 u)) ∧
      Tendsto (fun n => ∫ x, ‖fderiv ℝ (absTest (φ n)) x‖ ^ 2)
        atTop (𝓝 (energy1 u)) := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp hu
  choose φ hφ using hv
  have hgraph : Tendsto (fun n => graphH1 (φ n)) atTop (𝓝 u) := by
    simpa only [hφ] using hlim
  have hLip : ∀ n, ∃ K : ℝ≥0, LipschitzWith K (φ n).1 := fun n =>
    ContDiff.lipschitzWith_of_hasCompactSupport (φ n).2.2.1 (φ n).2.1 (by simp)
  choose K hK using hLip
  have hJ : Tendsto (fun n => h01GlobalValue Ω hΩ.measurableSet (graphH1 (φ n)))
      atTop (𝓝 (h01GlobalValue Ω hΩ.measurableSet u)) :=
    ((h01GlobalValue Ω hΩ.measurableSet).continuous.tendsto u).comp hgraph
  have hJn := tendsto_iff_norm_sub_tendsto_zero.mp hJ
  have hFn : Tendsto (fun n => absTestLp (φ n))
      atTop (𝓝 (h01GlobalValue Ω hΩ.measurableSet u)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun n => norm_absTestLp_sub_globalValue_le hΩ.measurableSet (φ n) u hu0) hJn
  have hE0 : Continuous (fun v : L2 Ω × (Fin 2 → L2 Ω) => energy0 v) := by
    unfold energy0
    fun_prop
  have hE1 : Continuous (fun v : L2 Ω × (Fin 2 → L2 Ω) => energy1 v) := by
    unfold energy1
    fun_prop
  have hMass : Tendsto (fun n => ∫ x, absTest (φ n) x ^ 2) atTop (𝓝 (energy0 u)) := by
    simpa only [Function.comp_def, integral_absTest_sq_eq_energy0] using
      (hE0.tendsto u).comp hgraph
  have hEnergy : Tendsto (fun n => ∫ x, ‖fderiv ℝ (absTest (φ n)) x‖ ^ 2)
      atTop (𝓝 (energy1 u)) := by
    have heq : (fun n => ∫ x, ‖fderiv ℝ (absTest (φ n)) x‖ ^ 2) =
        (fun n => energy1 (graphH1 (φ n))) :=
      funext fun n => integral_absTest_gradient_sq_eq_energy1 (φ n) (hK n)
    rw [heq]
    exact (hE1.tendsto u).comp hgraph
  refine ⟨φ, K, hgraph, (fun n => lipschitzWith_absTest (φ n) (hK n)), ?_, hFn, hMass, hEnergy⟩
  intro n
  exact ⟨absTest_nonneg (φ n), hasCompactSupport_absTest (φ n), tsupport_absTest_subset (φ n),
    integrable_absTest_sq (φ n), integrable_absTest_gradient_sq (φ n) (hK n)⟩

end Buckling.H01NonnegativeCompactApproximation

end

end
