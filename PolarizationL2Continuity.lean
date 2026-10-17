module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationMeasure
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Tactic.Ring

/-!
# Actual two-point polarization on L2

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

For an arbitrary measurable space and measure, a measurable set H and a
measure-preserving map tau define actual two-point polarization on Lp R 2.
No involution, side swapping, geometric reflection, finite measure, sign,
boundedness, or support assumption is used. The actual function is in L2,
its quotient representative is identified almost everywhere, and its L2
Lipschitz constant is at most 2.

The pointwise max/min estimate is the same elementary scalar estimate used
in PolarizationBounds. Only PolarizationMeasure is imported: no uniform
convergence or bounded-continuous-function topology enters the argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace FaberKrahnDevelopment.PolarizationL2

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Sorting two real pairs is bounded by the sum of the two coordinate errors. -/
lemma abs_twoPointPolarization_sub_le {H : Set α} {τ : α → α}
    (f g : α → ℝ) (x : α) :
    |twoPointPolarization H τ f x - twoPointPolarization H τ g x| ≤
      |f x - g x| + |f (τ x) - g (τ x)| := by
  classical
  have hmax : max |f x - g x| |f (τ x) - g (τ x)| ≤
      |f x - g x| + |f (τ x) - g (τ x)| := by
    exact max_le (le_add_of_nonneg_right (abs_nonneg _))
      (le_add_of_nonneg_left (abs_nonneg _))
  by_cases hx : x ∈ H
  · simp only [twoPointPolarization, if_pos hx]
    exact (abs_max_sub_max_le_max _ _ _ _).trans hmax
  · simp only [twoPointPolarization, if_neg hx]
    exact (abs_min_sub_min_le_max _ _ _ _).trans hmax

lemma norm_twoPointPolarization_sub_le {H : Set α} {τ : α → α}
    (f g : α → ℝ) (x : α) :
    ‖twoPointPolarization H τ f x - twoPointPolarization H τ g x‖ ≤
      ‖f x - g x‖ + ‖f (τ x) - g (τ x)‖ := by
  simpa only [Real.norm_eq_abs] using abs_twoPointPolarization_sub_le (H := H) (τ := τ) f g x

@[simp] lemma twoPointPolarization_zero (H : Set α) (τ : α → α) (x : α) :
    twoPointPolarization H τ (fun _ => (0 : ℝ)) x = 0 := by
  classical
  simp [twoPointPolarization]

lemma norm_twoPointPolarization_le {H : Set α} {τ : α → α}
    (f : α → ℝ) (x : α) :
    ‖twoPointPolarization H τ f x‖ ≤ ‖f x‖ + ‖f (τ x)‖ := by
  simpa only [twoPointPolarization_zero, sub_zero] using
    norm_twoPointPolarization_sub_le (H := H) (τ := τ) f (fun _ => 0) x

/-- The measure-preserving map transports AE equality to the partner point.
This makes polarization independent of the chosen L2 representative. -/
lemma twoPointPolarization_congr_ae {H : Set α} {τ : α → α}
    (hτ : MeasurePreserving τ μ μ) {f g : α → ℝ} (hfg : f =ᵐ[μ] g) :
    twoPointPolarization H τ f =ᵐ[μ] twoPointPolarization H τ g := by
  classical
  have hfgτ : ∀ᵐ x ∂μ, f (τ x) = g (τ x) :=
    hτ.quasiMeasurePreserving.tendsto_ae.eventually hfg
  filter_upwards [hfg, hfgτ] with x hx hτx
  simp only [twoPointPolarization, hx, hτx]

/-- A genuinely AEStronglyMeasurable input suffices; a measurable input
representative is constructed rather than assumed. -/
lemma aestronglyMeasurable_twoPointPolarization {H : Set α} {τ : α → α}
    (hH : MeasurableSet H) (hτ : MeasurePreserving τ μ μ) {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (twoPointPolarization H τ f) μ := by
  have hfm : Measurable (hf.mk f) := hf.stronglyMeasurable_mk.measurable
  have hm : AEStronglyMeasurable (twoPointPolarization H τ (hf.mk f)) μ :=
    (measurable_twoPointPolarization hH hτ.measurable hfm).aestronglyMeasurable
  exact hm.congr (twoPointPolarization_congr_ae hτ hf.ae_eq_mk).symm

/-- Actual L2 membership follows from the sum of the two L2 norms. -/
lemma memLp_twoPointPolarization {H : Set α} {τ : α → α}
    (hH : MeasurableSet H) (hτ : MeasurePreserving τ μ μ) {f : α → ℝ}
    (hf : MemLp f 2 μ) : MemLp (twoPointPolarization H τ f) 2 μ := by
  have hsum : MemLp (fun x => ‖f x‖ + ‖f (τ x)‖) 2 μ := by
    simpa only [Pi.add_def, Function.comp_apply] using
      hf.norm.add (hf.comp_measurePreserving hτ).norm
  exact hsum.mono' (aestronglyMeasurable_twoPointPolarization hH hτ hf.aestronglyMeasurable)
    (ae_of_all _ (norm_twoPointPolarization_le f))

/-- The actual L2 polarization class of the canonical representative. -/
def polarizationLp {H : Set α} {τ : α → α} (hH : MeasurableSet H)
    (hτ : MeasurePreserving τ μ μ) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (memLp_twoPointPolarization hH hτ (Lp.memLp f)).toLp (twoPointPolarization H τ f)

lemma coeFn_polarizationLp {H : Set α} {τ : α → α} (hH : MeasurableSet H)
    (hτ : MeasurePreserving τ μ μ) (f : Lp ℝ 2 μ) :
    (polarizationLp hH hτ f : α → ℝ) =ᵐ[μ] twoPointPolarization H τ f :=
  (memLp_twoPointPolarization hH hτ (Lp.memLp f)).coeFn_toLp

/-- It also recovers the polarization of any actual MemLp representative. -/
lemma coeFn_polarizationLp_toLp {H : Set α} {τ : α → α} (hH : MeasurableSet H)
    (hτ : MeasurePreserving τ μ μ) {f : α → ℝ} (hf : MemLp f 2 μ) :
    (polarizationLp hH hτ (hf.toLp f) : α → ℝ) =ᵐ[μ] twoPointPolarization H τ f :=
  (coeFn_polarizationLp hH hτ (hf.toLp f)).trans
    (twoPointPolarization_congr_ae hτ hf.coeFn_toLp)

/-- The L2 class of the pointwise absolute value has the same norm. -/
lemma norm_toLp_norm (f : Lp ℝ 2 μ) :
    ‖((Lp.memLp f).norm).toLp (fun x => ‖f x‖)‖ = ‖f‖ := by
  simp only [Lp.norm_def]
  exact congrArg ENNReal.toReal
    ((eLpNorm_congr_ae (Lp.memLp f).norm.coeFn_toLp).trans
      (eLpNorm_norm _ (Lp.aestronglyMeasurable f)))

/-- A genuine L2 estimate. Both comparison summands are actual L2 classes;
the second has exactly the same norm by measure preservation. -/
theorem norm_polarizationLp_sub_le {H : Set α} {τ : α → α} (hH : MeasurableSet H)
    (hτ : MeasurePreserving τ μ μ) (f g : Lp ℝ 2 μ) :
    ‖polarizationLp hH hτ f - polarizationLp hH hτ g‖ ≤ 2 * ‖f - g‖ := by
  let d : Lp ℝ 2 μ := f - g
  let A : Lp ℝ 2 μ := ((Lp.memLp d).norm).toLp (fun x => ‖d x‖)
  let B : Lp ℝ 2 μ := Lp.compMeasurePreserving τ hτ A
  have hA : (A : α → ℝ) =ᵐ[μ] fun x => ‖d x‖ := (Lp.memLp d).norm.coeFn_toLp
  have hAτ : ∀ᵐ x ∂μ, A (τ x) = ‖d (τ x)‖ :=
    hτ.quasiMeasurePreserving.tendsto_ae.eventually hA
  have hd : ∀ᵐ x ∂μ, d x = f x - g x := Lp.coeFn_sub f g
  have hdτ : ∀ᵐ x ∂μ, d (τ x) = f (τ x) - g (τ x) :=
    hτ.quasiMeasurePreserving.tendsto_ae.eventually hd
  have hdom : ‖polarizationLp hH hτ f - polarizationLp hH hτ g‖ ≤ ‖A + B‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (polarizationLp hH hτ f) (polarizationLp hH hτ g),
      coeFn_polarizationLp hH hτ f, coeFn_polarizationLp hH hτ g,
      Lp.coeFn_add A B, hA, Lp.coeFn_compMeasurePreserving A hτ, hAτ, hd, hdτ]
      with x hsub hPf hPg hadd hAx hBx hAτx hdx hdτx
    simp only [Pi.sub_apply] at hsub
    simp only [Pi.add_apply] at hadd
    simp only [Function.comp_apply] at hBx
    calc
      ‖(polarizationLp hH hτ f - polarizationLp hH hτ g) x‖ =
          ‖twoPointPolarization H τ f x - twoPointPolarization H τ g x‖ := by
            rw [hsub, hPf, hPg]
      _ ≤ ‖f x - g x‖ + ‖f (τ x) - g (τ x)‖ := norm_twoPointPolarization_sub_le f g x
      _ = ‖(A + B) x‖ := by
        rw [hadd, hAx, hBx, hAτx, hdx, hdτx]
        exact (Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))).symm
  calc
    ‖polarizationLp hH hτ f - polarizationLp hH hτ g‖ ≤ ‖A + B‖ := hdom
    _ ≤ ‖A‖ + ‖B‖ := norm_add_le A B
    _ = 2 * ‖f - g‖ := by
      change ‖A‖ + ‖Lp.compMeasurePreserving τ hτ A‖ = _
      rw [Lp.norm_compMeasurePreserving A hτ]
      have hAnorm : ‖A‖ = ‖f - g‖ := norm_toLp_norm d
      rw [hAnorm]
      ring

theorem lipschitzWith_polarizationLp {H : Set α} {τ : α → α} (hH : MeasurableSet H)
    (hτ : MeasurePreserving τ μ μ) : LipschitzWith 2 (polarizationLp hH hτ) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  change dist (polarizationLp hH hτ f) (polarizationLp hH hτ g) ≤ (2 : ℝ) * dist f g
  simpa only [dist_eq_norm] using norm_polarizationLp_sub_le hH hτ f g

theorem continuous_polarizationLp {H : Set α} {τ : α → α} (hH : MeasurableSet H)
    (hτ : MeasurePreserving τ μ μ) : Continuous (polarizationLp hH hτ) :=
  (lipschitzWith_polarizationLp hH hτ).continuous

end FaberKrahnDevelopment.PolarizationL2

end

end
