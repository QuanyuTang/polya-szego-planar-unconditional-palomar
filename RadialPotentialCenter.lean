module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# An actual positive radial-potential maximum for an L1 density

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The space below is literally EuclideanSpace R (Fin 2), so it is definitionally
the original plane without importing the original broad Core1 module.
The actual kernel is K(z)=1/(1+norm z), and the actual potential is its
integral against U(x) at x-p. Integrability, continuity and decay at infinity
are produced for every integrable U, with no sign restriction. Nonnegative
U with positive integral then gives a strictly positive potential at every
point, and the canonical extreme-value theorem produces a global maximum.

The same genuine bound norm U supports both applications of filter dominated
convergence. For decay, fixed-x distance tends to infinity along cocompact;
the countable-generation obligation for this filter is proved by its actual
distance-comap description. No first moment, bounded support, centroid,
decay, maximizing point, PDE or rearrangement result is an input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Buckling.RadialPotentialCenter

abbrev Space := EuclideanSpace ℝ (Fin 2)

def kernel (z : Space) : ℝ := 1 / (1 + ‖z‖)

def potential (U : Space → ℝ) (p : Space) : ℝ :=
  ∫ x, U x * kernel (x - p)

lemma kernel_pos (z : Space) : 0 < kernel z := by
  dsimp [kernel]
  positivity

lemma kernel_le_one (z : Space) : kernel z ≤ 1 := by
  have hd : 0 < 1 + ‖z‖ := by positivity
  exact (div_le_one hd).mpr (by linarith [norm_nonneg z])

lemma norm_kernel_le_one (z : Space) : ‖kernel z‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (kernel_pos z)]
  exact kernel_le_one z

lemma kernel_neg (z : Space) : kernel (-z) = kernel z := by
  simp only [kernel, norm_neg]

lemma continuous_kernel : Continuous kernel := by
  have hd : Continuous (fun z : Space => (1 : ℝ) + ‖z‖) :=
    continuous_const.fun_add continuous_norm
  exact continuous_const.div₀ hd (fun z => by positivity)

lemma continuous_kernel_sub_right (p : Space) :
    Continuous (fun x : Space => kernel (x - p)) :=
  continuous_kernel.comp (continuous_id.fun_sub continuous_const)

lemma continuous_kernel_sub_left (x : Space) :
    Continuous (fun p : Space => kernel (x - p)) :=
  continuous_kernel.comp (continuous_const.fun_sub continuous_id)

lemma norm_integrand_le (U : Space → ℝ) (x p : Space) :
    ‖U x * kernel (x - p)‖ ≤ ‖U x‖ := by
  rw [norm_mul]
  calc
    ‖U x‖ * ‖kernel (x - p)‖ ≤ ‖U x‖ * 1 :=
      mul_le_mul_of_nonneg_left (norm_kernel_le_one _) (norm_nonneg _)
    _ = ‖U x‖ := mul_one _

/-- Every actual defining integrand is integrable, including for signed U. -/
lemma integrable_integrand {U : Space → ℝ} (hU : Integrable U volume) (p : Space) :
    Integrable (fun x => U x * kernel (x - p)) volume :=
  hU.mul_bdd (continuous_kernel_sub_right p).aestronglyMeasurable
    (ae_of_all _ fun x => norm_kernel_le_one _)

/-- Continuity is a genuine parameter-integral theorem with a fixed L1 bound. -/
theorem continuous_potential {U : Space → ℝ} (hU : Integrable U volume) :
    Continuous (potential U) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q => ∫ x, U x * kernel (x - q)) (𝓝 p)
    (𝓝 (∫ x, U x * kernel (x - p)))
  exact tendsto_integral_filter_of_dominated_convergence (fun x => ‖U x‖)
    (Eventually.of_forall fun q => (integrable_integrand hU q).aestronglyMeasurable)
    (Eventually.of_forall fun q => ae_of_all _ fun x => norm_integrand_le U x q)
    hU.norm (ae_of_all _ fun x =>
      ((continuous_kernel_sub_left x).continuousAt.tendsto).const_mul (U x))

lemma kernel_sub_tendsto_zero (x : Space) :
    Tendsto (fun p : Space => kernel (x - p)) (cocompact Space) (𝓝 0) := by
  have hn : Tendsto (fun p : Space => ‖x - p‖) (cocompact Space) atTop := by
    simpa only [dist_eq_norm] using! _root_.tendsto_dist_left_cocompact_atTop x
  have hd : Tendsto (fun p : Space => (1 : ℝ) + ‖x - p‖)
      (cocompact Space) atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hn.eventually_ge_atTop b] with p hp
    linarith
  exact (tendsto_const_nhds : Tendsto (fun _ : Space => (1 : ℝ))
    (cocompact Space) (𝓝 1)).div_atTop hd

/-- No countable-generation assumption on infinity is inserted as an input. -/
lemma cocompact_countablyGenerated : (cocompact Space).IsCountablyGenerated := by
  rw [← _root_.comap_dist_left_atTop_eq_cocompact (0 : Space)]
  infer_instance

/-- The actual potential vanishes along the actual cocompact filter. -/
theorem potential_tendsto_zero {U : Space → ℝ} (hU : Integrable U volume) :
    Tendsto (potential U) (cocompact Space) (𝓝 0) := by
  letI : (cocompact Space).IsCountablyGenerated := cocompact_countablyGenerated
  have h : Tendsto (fun p : Space => ∫ x, U x * kernel (x - p))
      (cocompact Space) (𝓝 (∫ _ : Space, (0 : ℝ))) :=
    tendsto_integral_filter_of_dominated_convergence (fun x => ‖U x‖)
      (Eventually.of_forall fun p => (integrable_integrand hU p).aestronglyMeasurable)
      (Eventually.of_forall fun p => ae_of_all _ fun x => norm_integrand_le U x p)
      hU.norm (ae_of_all _ fun x => by
        simpa only [mul_zero] using (kernel_sub_tendsto_zero x).const_mul (U x))
  simpa only [potential, integral_zero] using! h

lemma potential_nonneg {U : Space → ℝ}
    (hUN : ∀ᵐ x ∂volume, 0 ≤ U x) (p : Space) : 0 ≤ potential U p := by
  apply integral_nonneg_of_ae
  filter_upwards [hUN] with x hx
  exact mul_nonneg hx (kernel_pos _).le

/-- Strict positivity comes from positive actual mass and the everywhere
strictly positive actual kernel, without any lower bound on its far tail. -/
theorem potential_pos {U : Space → ℝ} (hU : Integrable U volume)
    (hUN : ∀ᵐ x ∂volume, 0 ≤ U x) (hMass : 0 < ∫ x, U x) (p : Space) :
    0 < potential U p := by
  by_contra h
  have hEq : potential U p = 0 := le_antisymm (le_of_not_gt h) (potential_nonneg hUN p)
  have hProdN : ∀ᵐ x ∂volume, 0 ≤ U x * kernel (x - p) := by
    filter_upwards [hUN] with x hx
    exact mul_nonneg hx (kernel_pos _).le
  have hProdZero : (fun x => U x * kernel (x - p)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hProdN (integrable_integrand hU p)).mp hEq
  have hUZero : U =ᵐ[volume] 0 := by
    filter_upwards [hProdZero] with x hx
    change U x * kernel (x - p) = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_right (ne_of_gt (kernel_pos _))
  have hMassZero : (∫ x, U x) = 0 := by
    simpa only [Pi.zero_apply, integral_zero] using! integral_congr_ae hUZero
  exact hMass.ne' hMassZero

/-- An actual positive global maximizing point, produced solely from L1,
nonnegativity and positive actual mass. -/
theorem exists_positive_global_maximum {U : Space → ℝ} (hU : Integrable U volume)
    (hUN : ∀ᵐ x ∂volume, 0 ≤ U x) (hMass : 0 < ∫ x, U x) :
    ∃ p : Space, 0 < potential U p ∧ ∀ q : Space, potential U q ≤ potential U p := by
  have h0 : 0 < potential U 0 := potential_pos hU hUN hMass 0
  have hSmall : ∀ᶠ p in cocompact Space, potential U p ≤ potential U 0 :=
    ((potential_tendsto_zero hU).eventually_lt tendsto_const_nhds h0).mono
      fun p hp => hp.le
  obtain ⟨p, hp⟩ := (continuous_potential hU).exists_forall_ge' (0 : Space) hSmall
  exact ⟨p, potential_pos hU hUN hMass p, hp⟩

end Buckling.RadialPotentialCenter

end

end
