module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PositiveCompactWeakApproximation
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Extending a nonnegative smooth-test inequality by actual L2 approximation

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The actual nonnegative mollifications from PositiveCompactWeakApproximation
are used. Full-space L2 convergence of every gradient coordinate makes its
pairing with the supplied full-space L2 vector field converge. Passing the
finite sum inequality to that limit gives the compact weak-test inequality.

No Lipschitz condition, nonnegative approximating sequence, or weak-test
inequality is assumed for the target function. The general input consists
of its actual L2 weak-gradient data and the original smooth-test inequality.
No reciprocal/logarithm admissibility, Caccioppoli estimate or SMP is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.PositiveCompactWeakTesting

/-- These products are genuinely integrable by L2 Holder, rather than
uncontrolled expressions using the zero convention of a Bochner integral. -/
lemma integrable_mul_of_memLp2 {g h : Plane → ℝ}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    Integrable (fun x => g x * h x) volume :=
  hg.integrable_mul hh

lemma inner_toLp_toLp {g h : Plane → ℝ}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    inner ℝ (hg.toLp g) (hh.toLp h) = ∫ x, g x * h x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/-- Actual L2 class convergence and continuity of its Hilbert pairing
transport representative seminorm convergence to the real integral. -/
lemma tendsto_integral_mul_of_eLpNorm_sub {g h : Plane → ℝ}
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume)
    {f : ℕ → Plane → ℝ} (hf : ∀ n, MemLp (f n) 2 volume)
    (hlim : Tendsto (fun n => eLpNorm (f n - h) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, g x * f n x) atTop (𝓝 (∫ x, g x * h x)) := by
  have hLp : Tendsto (fun n => (hf n).toLp (f n)) atTop (𝓝 (hh.toLp h)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf h hh).mpr hlim
  have hcont : Continuous (fun w : Lp ℝ 2 (volume : Measure Plane) =>
      inner ℝ (hg.toLp g) w) :=
    continuous_const.inner continuous_id
  simpa only [Function.comp_def, inner_toLp_toLp] using (hcont.tendsto _).comp hLp

/-- A supersolution inequality against the actual original nonnegative
smooth tests extends to any literal nonnegative compact weak-H1 function
whose support lies in the same open set. All integrals are full-space. -/
theorem extend_nonnegative_compact_weak_test {D : Set Plane} (hD : IsOpen D)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x)
    {φ : Plane → ℝ} {h : Fin 2 → Plane → ℝ} (hφnonneg : ∀ x, 0 ≤ φ x)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ D)
    (hφ : MemLp φ 2 volume) (hh : ∀ i, MemLp (h i) 2 volume)
    (hweak : EllipticPdes.Embedding.HasWeakGradOn univ φ h) :
    0 ≤ ∑ i, ∫ x, g i x * h i x := by
  obtain ⟨ψ, hψ, hψnonneg, _hvalue, hgrad⟩ :=
    PositiveCompactWeakApproximation.exists_nonnegative_test_approximation
      hD hφnonneg hc hs hφ hh hweak
  have hderivLp : ∀ n i, MemLp (pderiv i (ψ n)) 2 volume := fun n i =>
    ((hψ n).pderiv i).1.continuous.memLp_of_hasCompactSupport ((hψ n).pderiv i).2.1
  have hpair : ∀ i, Tendsto (fun n => ∫ x, g i x * pderiv i (ψ n) x)
      atTop (𝓝 (∫ x, g i x * h i x)) := fun i =>
    tendsto_integral_mul_of_eLpNorm_sub (hg i) (hh i) (fun n => hderivLp n i) (hgrad i)
  have hsum : Tendsto (fun n => ∑ i, ∫ x, g i x * pderiv i (ψ n) x)
      atTop (𝓝 (∑ i, ∫ x, g i x * h i x)) :=
    tendsto_finsetSum Finset.univ (fun i _ => hpair i)
  exact ge_of_tendsto hsum (Eventually.of_forall fun n => hsuper (ψ n) (hψ n) (hψnonneg n))

end Buckling.PositiveCompactWeakTesting

end

end
