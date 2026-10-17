module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPRegularizers
public import AnchoredL2Estimate
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Uniform real logarithm-square bounds rule out positive levels

SOURCE_DRAFT: not registered or native checked.
This is a finite-measure consequence of the actual arsinh regularizer,
with no PDE, Poincare, maximum principle or level-set decay assumption.
The function need only be almost everywhere strongly measurable. Its
superlevel sets are handled as null-measurable sets, not assumed Borel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace Buckling.WeakSMPLogBoundDecay

open WeakSMPRegularizers

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma logarithm_mono {δ : ℝ} (hδ : 0 < δ) : Monotone (logarithm δ) := by
  intro a b hab
  apply Real.arsinh_le_arsinh.mpr
  exact div_le_div_of_nonneg_right hab hδ.le

/-- Actual uniform finite real integral bounds force every positive
superlevel set to have measure zero. No measurability of a chosen
pointwise representative beyond AE strong measurability is required. -/
theorem measure_superlevel_eq_zero_of_uniform_log_bound {w : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (C : ℝ)
    (hLp : ∀ δ : ℝ, 0 < δ → MemLp (fun x => logarithm δ (w x)) 2 μ)
    (hBound : ∀ δ : ℝ, 0 < δ → (∫ x, logarithm δ (w x) ^ 2 ∂μ) ≤ C)
    {t : ℝ} (ht : 0 < t) : μ {x | t ≤ w x} = 0 := by
  by_contra hE
  let E : Set α := {x | t ≤ w x}
  have hEm : NullMeasurableSet E μ :=
    hw.aemeasurable.nullMeasurableSet_preimage measurableSet_Ici
  have hm : 0 < μ.real E :=
    AnchoredL2Estimate.real_anchor_measure_pos (pos_iff_ne_zero.mpr hE)
  let N : ℝ := Real.sqrt ((|C| + 1) / μ.real E)
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have hN2 : N ^ 2 * μ.real E = |C| + 1 := by
    dsimp [N]
    rw [Real.sq_sqrt (by positivity : 0 ≤ (|C| + 1) / μ.real E)]
    exact div_mul_cancel₀ _ hm.ne'
  have hlarge : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), N ≤ logarithm δ t :=
    (logarithm_tendsto_atTop_delta_zero ht).eventually (eventually_ge_atTop N)
  obtain ⟨δ, hδ, hδN⟩ := Filter.Eventually.exists (Filter.Eventually.and
    (self_mem_nhdsWithin : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ) hlarge)
  have hδp : 0 < δ := hδ
  have hlower : N ^ 2 * μ.real E ≤ ∫ x in E, logarithm δ (w x) ^ 2 ∂μ := by
    have hc : Integrable (fun _ : α => N ^ 2) (μ.restrict E) := integrable_const _
    have hmLp := (hLp δ hδp).mono_measure (Measure.restrict_le_self (s := E))
    have hpoint : (fun _ : α => N ^ 2) ≤ᵐ[μ.restrict E]
        (fun x => logarithm δ (w x) ^ 2) := by
      filter_upwards [ae_restrict_mem₀ hEm] with x hx
      exact pow_le_pow_left₀ hN (hδN.trans (logarithm_mono hδp hx)) 2
    have h := integral_mono_ae hc hmLp.integrable_sq hpoint
    simpa only [setIntegral_const, smul_eq_mul, mul_comm] using h
  have hwhole : (∫ x in E, logarithm δ (w x) ^ 2 ∂μ) ≤
      ∫ x, logarithm δ (w x) ^ 2 ∂μ :=
    integral_mono_measure Measure.restrict_le_self
      (Eventually.of_forall fun x => sq_nonneg _) (hLp δ hδp).integrable_sq
  have hC := hlower.trans (hwhole.trans (hBound δ hδp))
  rw [hN2] at hC
  linarith [le_abs_self C]

/-- A nonnegative measurable function with a uniform logarithm-square
bound on a finite measure space is zero almost everywhere. -/
theorem ae_eq_zero_of_uniform_log_bound {w : α → ℝ}
    (hw : AEStronglyMeasurable w μ) (hn : ∀ᵐ x ∂μ, 0 ≤ w x) (C : ℝ)
    (hLp : ∀ δ : ℝ, 0 < δ → MemLp (fun x => logarithm δ (w x)) 2 μ)
    (hBound : ∀ δ : ℝ, 0 < δ → (∫ x, logarithm δ (w x) ^ 2 ∂μ) ≤ C) :
    w =ᵐ[μ] 0 := by
  have hlevels : ∀ n : ℕ, ∀ᵐ x ∂μ, ¬ 1 / (n + 1 : ℝ) ≤ w x := by
    intro n
    apply ae_iff.mpr
    simpa only [not_not] using
      measure_superlevel_eq_zero_of_uniform_log_bound hw C hLp hBound
        (t := 1 / (n + 1 : ℝ)) (by positivity)
  filter_upwards [hn, ae_all_iff.mpr hlevels] with x hx hxl
  apply le_antisymm _ hx
  by_contra hpos
  have hwp : 0 < w x := lt_of_not_ge hpos
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hwp
  exact hxl n hn.le

end Buckling.WeakSMPLogBoundDecay

end

end
