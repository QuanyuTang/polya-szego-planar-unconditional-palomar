module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RadialKernelReflection
public import PolarizationMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Order.Lattice
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Actual radial-potential gain of literal affine polarization

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The input is any actual integrable real density U, including signed ones.
Its literal two-point polarization is genuinely L1. The actual positive
part of the reflected difference is L1, and multiplication by the actual
bounded continuous kernel gap gives a genuinely integrable gain density.
The gain identity uses the actual affine reflection, its actual AE side
swapping, and finite real integral pair transport. A real factor 2 is
cancelled only after the actual integrability producers have been applied.

For a center on the chosen side the gain is nonnegative. For a strict-side
center, zero gain forces actual AE reflection order on the closed side;
the fixed boundary is handled directly, without a new null-boundary input.
The last consumer explicitly takes one of the two actual AE polarization
branches and actual potential maximality. These branches remain obligations
for the subsequent SMP argument; no final symmetry or rigidity is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.RadialPotentialPolarization

open FaberKrahnDevelopment FaberKrahnDevelopment.EuclideanReflection
open RadialPotentialCenter RadialKernelReflection

lemma abs_sorted_pair_le (a b : ℝ) :
    |max a b| ≤ |a| + |b| ∧ |min a b| ≤ |a| + |b| := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h]
    exact ⟨le_add_of_nonneg_left (abs_nonneg a), le_add_of_nonneg_right (abs_nonneg b)⟩
  · rw [max_eq_left h, min_eq_right h]
    exact ⟨le_add_of_nonneg_right (abs_nonneg b), le_add_of_nonneg_left (abs_nonneg a)⟩

lemma norm_positive_part_sub_le (a b : ℝ) :
    ‖max (a - b) 0‖ ≤ ‖a‖ + ‖b‖ := by
  by_cases h : b ≤ a
  · rw [max_eq_left (sub_nonneg.mpr h)]
    exact norm_sub_le a b
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge h)), norm_zero]
    exact add_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The actual L1 producer does not demand an everywhere measurable
representative: actual AE max/min and measurable-side piecewise suffice. -/
lemma integrable_twoPointPolarization (ν : UnitNormal) (c : ℝ)
    {U : Space → ℝ} (hU : Integrable U volume) :
    Integrable (twoPointPolarization (halfspace ν c) (reflection ν c) U) volume := by
  classical
  have hR := integrable_reflected hU ν c
  have hMax : AEStronglyMeasurable
      (fun x => max (U x) (U (reflection ν c x))) volume :=
    hU.aestronglyMeasurable.fun_sup hR.aestronglyMeasurable
  have hMin : AEStronglyMeasurable
      (fun x => min (U x) (U (reflection ν c x))) volume :=
    hU.aestronglyMeasurable.fun_inf hR.aestronglyMeasurable
  have hP : AEStronglyMeasurable
      (twoPointPolarization (halfspace ν c) (reflection ν c) U) volume := by
    simpa only [twoPointPolarization, Set.piecewise] using!
      AEStronglyMeasurable.piecewise (halfspace_measurableSet ν c) hMax.restrict hMin.restrict
  apply (hU.norm.fun_add hR.norm).mono' hP
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ halfspace ν c
    · simpa only [twoPointPolarization, if_pos hx, Real.norm_eq_abs] using
        (abs_sorted_pair_le (U x) (U (reflection ν c x))).1
    · simpa only [twoPointPolarization, if_neg hx, Real.norm_eq_abs] using
        (abs_sorted_pair_le (U x) (U (reflection ν c x))).2

lemma integrable_positive_part_reflected (ν : UnitNormal) (c : ℝ)
    {U : Space → ℝ} (hU : Integrable U volume) :
    Integrable (fun x => max (U (reflection ν c x) - U x) 0) volume := by
  have hR := integrable_reflected hU ν c
  have hD : Integrable (fun x => U (reflection ν c x) - U x) volume := hR.sub' hU
  have hM : AEStronglyMeasurable
      (fun x => max (U (reflection ν c x) - U x) 0) volume :=
    hD.aestronglyMeasurable.fun_sup aestronglyMeasurable_const
  exact (hR.norm.fun_add hU.norm).mono' hM
    (ae_of_all _ fun x => norm_positive_part_sub_le _ _)

def gainDensity (ν : UnitNormal) (c : ℝ) (U : Space → ℝ) (p x : Space) : ℝ :=
  max (U (reflection ν c x) - U x) 0 * gap ν c p x

lemma continuous_gap (ν : UnitNormal) (c : ℝ) (p : Space) : Continuous (gap ν c p) := by
  have hσ : Continuous (fun x : Space => reflection ν c x - p) :=
    (reflection_isometry ν c).continuous.fun_sub continuous_const
  exact (continuous_kernel_sub_right p).fun_sub (continuous_kernel.comp hσ)

lemma integrable_gainDensity (ν : UnitNormal) (c : ℝ) {U : Space → ℝ}
    (hU : Integrable U volume) (p : Space) : Integrable (gainDensity ν c U p) volume :=
  (integrable_positive_part_reflected ν c hU).mul_bdd
    (continuous_gap ν c p).aestronglyMeasurable (ae_of_all _ fun x => by
      simpa only [Real.norm_eq_abs] using abs_gap_le_one ν c p x)

lemma sorted_weighted_pair_gain (a b A B : ℝ) :
    max a b * A + min a b * B - (a * A + b * B) = max (b - a) 0 * (A - B) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, min_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    ring
  · rw [max_eq_left h, min_eq_right h, max_eq_right (sub_nonpos.mpr h)]
    ring

/-- Literal scalar pair algebra, applied away from the already-produced
AE side-swapping exception of the actual reflection. -/
lemma paired_density_gain (ν : UnitNormal) (c : ℝ) (U : Space → ℝ) (p : Space)
    {x : Space} (hSwap : reflection ν c x ∈ halfspace ν c ↔ x ∉ halfspace ν c) :
    (twoPointPolarization (halfspace ν c) (reflection ν c) U x * kernel (x - p) -
        U x * kernel (x - p)) +
      (twoPointPolarization (halfspace ν c) (reflection ν c) U (reflection ν c x) *
          kernel (reflection ν c x - p) - U (reflection ν c x) * kernel (reflection ν c x - p)) =
    (halfspace ν c).indicator (gainDensity ν c U p) x +
      (halfspace ν c).indicator (gainDensity ν c U p) (reflection ν c x) := by
  classical
  by_cases hx : x ∈ halfspace ν c
  · have hσ : reflection ν c x ∉ halfspace ν c := fun h => (hSwap.mp h) hx
    simp only [twoPointPolarization, if_pos hx, if_neg hσ, reflection_reflection,
      Set.indicator_of_mem hx, Set.indicator_of_notMem hσ, add_zero, gainDensity, gap]
    rw [min_comm (U (reflection ν c x)) (U x)]
    nlinarith only [sorted_weighted_pair_gain (U x) (U (reflection ν c x))
      (kernel (x - p)) (kernel (reflection ν c x - p))]
  · have hσ : reflection ν c x ∈ halfspace ν c := hSwap.mpr hx
    simp only [twoPointPolarization, if_neg hx, if_pos hσ, reflection_reflection,
      Set.indicator_of_notMem hx, Set.indicator_of_mem hσ, zero_add, gainDensity, gap]
    rw [min_comm (U x) (U (reflection ν c x))]
    nlinarith only [sorted_weighted_pair_gain (U (reflection ν c x)) (U x)
      (kernel (reflection ν c x - p)) (kernel (x - p))]

/-- Finite real pair transport. All its integrability inputs are produced
from the literal L1 density in the application below. -/
lemma integral_eq_of_ae_pair_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {τ : α → α} (hτ : MeasurePreserving τ μ μ) (hInv : Function.Involutive τ)
    {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hPair : ∀ᵐ x ∂μ, f x + f (τ x) = g x + g (τ x)) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ := by
  let e : α ≃ᵐ α := MeasurableEquiv.ofInvolutive τ hInv hτ.measurable
  have hfτ : Integrable (fun x => f (τ x)) μ := hτ.integrable_comp_of_integrable hf
  have hgτ : Integrable (fun x => g (τ x)) μ := hτ.integrable_comp_of_integrable hg
  have hif : (∫ x, f (τ x) ∂μ) = ∫ x, f x ∂μ := hτ.integral_comp e.measurableEmbedding f
  have hig : (∫ x, g (τ x) ∂μ) = ∫ x, g x ∂μ := hτ.integral_comp e.measurableEmbedding g
  have hh := integral_congr_ae hPair
  rw [integral_add hf hfτ, integral_add hg hgτ, hif, hig] at hh
  linarith

/-- The actual potential gain equals the actual integrable halfspace gain.
No sign restriction on U or position of p is needed for this identity. -/
theorem potential_gain_identity (ν : UnitNormal) (c : ℝ) {U : Space → ℝ}
    (hU : Integrable U volume) (p : Space) :
    potential (twoPointPolarization (halfspace ν c) (reflection ν c) U) p - potential U p =
      ∫ x in halfspace ν c, gainDensity ν c U p x := by
  let P := twoPointPolarization (halfspace ν c) (reflection ν c) U
  let D : Space → ℝ := fun x => P x * kernel (x - p) - U x * kernel (x - p)
  let G : Space → ℝ := (halfspace ν c).indicator (gainDensity ν c U p)
  have hP : Integrable P volume := integrable_twoPointPolarization ν c hU
  have hPW := integrable_integrand hP p
  have hUW := integrable_integrand hU p
  have hD : Integrable D volume := hPW.sub' hUW
  have hG : Integrable G volume :=
    (integrable_gainDensity ν c hU p).indicator (halfspace_measurableSet ν c)
  have hPair : ∀ᵐ x ∂volume, D x + D (reflection ν c x) = G x + G (reflection ν c x) :=
    (reflection_ae_swap ν c).mono fun x hx => paired_density_gain ν c U p hx
  calc
    potential P p - potential U p = ∫ x, D x := (integral_sub hPW hUW).symm
    _ = ∫ x, G x := integral_eq_of_ae_pair_eq (reflection_measurePreserving ν c)
      (reflection_involutive ν c) hD hG hPair
    _ = ∫ x in halfspace ν c, gainDensity ν c U p x :=
      integral_indicator (halfspace_measurableSet ν c)

lemma gainDensity_nonneg (ν : UnitNormal) (c : ℝ) (U : Space → ℝ) {p x : Space}
    (hp : c ≤ inner ℝ (ν : Space) p) (hx : x ∈ halfspace ν c) :
    0 ≤ gainDensity ν c U p x :=
  mul_nonneg (le_max_right _ _) (gap_nonneg ν c hp hx)

theorem potential_gain_nonneg (ν : UnitNormal) (c : ℝ) {U : Space → ℝ}
    (hU : Integrable U volume) {p : Space} (hp : c ≤ inner ℝ (ν : Space) p) :
    0 ≤ potential (twoPointPolarization (halfspace ν c) (reflection ν c) U) p -
      potential U p := by
  rw [potential_gain_identity ν c hU p]
  apply integral_nonneg_of_ae
  apply (ae_restrict_iff' (halfspace_measurableSet ν c)).mpr
  exact ae_of_all _ fun x hx => gainDensity_nonneg ν c U hp hx

/-- Strict-side zero gain forces actual AE order on the entire closed side.
On the fixed boundary order follows pointwise from the actual reflection. -/
theorem ae_reflection_order_of_gain_eq_zero (ν : UnitNormal) (c : ℝ)
    {U : Space → ℝ} (hU : Integrable U volume) {p : Space}
    (hp : c < inner ℝ (ν : Space) p)
    (hGain : potential (twoPointPolarization (halfspace ν c) (reflection ν c) U) p -
      potential U p = 0) :
    ∀ᵐ x ∂(volume.restrict (halfspace ν c)), U (reflection ν c x) ≤ U x := by
  have hH := halfspace_measurableSet ν c
  have hN : 0 ≤ᵐ[volume.restrict (halfspace ν c)] gainDensity ν c U p :=
    (ae_restrict_iff' hH).mpr (ae_of_all _ fun x hx => gainDensity_nonneg ν c U hp.le hx)
  have hInt : Integrable (gainDensity ν c U p) (volume.restrict (halfspace ν c)) :=
    (integrable_gainDensity ν c hU p).restrict
  have hZero : (∫ x in halfspace ν c, gainDensity ν c U p x) = 0 :=
    (potential_gain_identity ν c hU p).symm.trans hGain
  have hAE := (integral_eq_zero_iff_of_nonneg_ae hN hInt).mp hZero
  filter_upwards [hAE, ae_restrict_mem hH] with x hx hxH
  change max (U (reflection ν c x) - U x) 0 * gap ν c p x = 0 at hx
  by_cases hs : c < inner ℝ (ν : Space) x
  · have hGap := gap_pos ν c hp hs
    have hMax : max (U (reflection ν c x) - U x) 0 = 0 :=
      (mul_eq_zero.mp hx).resolve_right (ne_of_gt hGap)
    exact sub_nonpos.mp ((le_max_left _ _).trans hMax.le)
  · have hb : inner ℝ (ν : Space) x = c :=
      le_antisymm (not_lt.mp hs) hxH
    have hFix : reflection ν c x = x := by
      rw [reflection_eq_add_smul, hb]
      simp only [sub_self, mul_zero, zero_smul, add_zero]
    simpa only [hFix] using le_refl (U x)

lemma potential_congr_ae {U V : Space → ℝ} (hUV : U =ᵐ[volume] V) (p : Space) :
    potential U p = potential V p := by
  apply integral_congr_ae
  exact hUV.mono fun x hx => congrArg (fun t : ℝ => t * kernel (x - p)) hx

/-- Explicit branch consumer for a subsequent actual SMP producer. The
branch input is not a new symmetry theorem and is not discharged here. -/
theorem ae_reflection_order_of_global_maximum_and_branch (ν : UnitNormal) (c : ℝ)
    {U : Space → ℝ} (hU : Integrable U volume) {p : Space}
    (hp : c < inner ℝ (ν : Space) p)
    (hMax : ∀ q : Space, potential U q ≤ potential U p)
    (hBranch : (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume] U) ∨
      (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume]
        fun x => U (reflection ν c x))) :
    ∀ᵐ x ∂(volume.restrict (halfspace ν c)), U (reflection ν c x) ≤ U x := by
  have hUpper : potential (twoPointPolarization (halfspace ν c) (reflection ν c) U) p ≤
      potential U p := by
    rcases hBranch with h | h
    · exact (potential_congr_ae h p).le
    · calc
        potential (twoPointPolarization (halfspace ν c) (reflection ν c) U) p =
            potential (fun x => U (reflection ν c x)) p := potential_congr_ae h p
        _ = potential U (reflection ν c p) := potential_reflected_density ν c U p
        _ ≤ potential U p := hMax _
  have hZero : potential (twoPointPolarization (halfspace ν c) (reflection ν c) U) p -
      potential U p = 0 :=
    le_antisymm (sub_nonpos.mpr hUpper) (potential_gain_nonneg ν c hU hp.le)
  exact ae_reflection_order_of_gain_eq_zero ν c hU hp hZero

end Buckling.RadialPotentialPolarization

end

end
