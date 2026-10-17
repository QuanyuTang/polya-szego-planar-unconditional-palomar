module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# A finite-measure L2 estimate anchored on an actual positive-measure zero set

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
This is a pure measure-theoretic producer, independent of PDE and H01.
The anchor set need not be measurable: restriction and integral monotonicity
are used through their actual Mathlib APIs. All square densities are proved
integrable. Positivity of the real anchor measure uses actual finiteness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Buckling.AnchoredL2Estimate

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

lemma real_anchor_measure_pos {E : Set α} (hE : 0 < μ E) : 0 < μ.real E := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos hE.ne' (measure_ne_top μ E)

/-- The constant part is controlled by the actual integral over the zero
set, then by monotonicity of the nonnegative square density. -/
lemma anchor_constant_sq_le {E : Set α} {f : α → ℝ}
    (hf : MemLp f 2 μ) (hzero : ∀ᵐ x ∂μ.restrict E, f x = 0) (c : ℝ) :
    μ.real E * c ^ 2 ≤ ∫ x, (f x - c) ^ 2 ∂μ := by
  have hfc : MemLp (fun x => f x - c) 2 μ := hf.sub (memLp_const c)
  have hEeq : (∫ x in E, (f x - c) ^ 2 ∂μ) = μ.real E * c ^ 2 := by
    calc
      (∫ x in E, (f x - c) ^ 2 ∂μ) = ∫ _ in E, c ^ 2 ∂μ := by
        apply integral_congr_ae
        exact hzero.mono fun x hx => by
          change (f x - c) ^ 2 = c ^ 2
          rw [hx, zero_sub, neg_sq]
      _ = μ.real E * c ^ 2 := by rw [setIntegral_const, smul_eq_mul]
  rw [← hEeq]
  exact integral_mono_measure Measure.restrict_le_self
    (ae_of_all _ fun x => sq_nonneg (f x - c)) hfc.integrable_sq

/-- A literal positive-measure zero set gives the anchored L2 estimate.
No Poincare estimate or Sobolev fact is an additional input. -/
theorem integral_sq_le_anchored {E : Set α} (hE : 0 < μ E) {f : α → ℝ}
    (hf : MemLp f 2 μ) (hzero : ∀ᵐ x ∂μ.restrict E, f x = 0) (c : ℝ) :
    (∫ x, f x ^ 2 ∂μ) ≤
      2 * (1 + μ.real univ / μ.real E) * (∫ x, (f x - c) ^ 2 ∂μ) := by
  have hfc : MemLp (fun x => f x - c) 2 μ := hf.sub (memLp_const c)
  have hm : 0 < μ.real E := real_anchor_measure_pos hE
  have hb : 0 ≤ μ.real univ := measureReal_nonneg
  have hconst : c ^ 2 ≤ (∫ x, (f x - c) ^ 2 ∂μ) / μ.real E := by
    apply (le_div_iff₀ hm).mpr
    simpa only [mul_comm] using anchor_constant_sq_le hf hzero c
  have hupperint : Integrable (fun x => 2 * (f x - c) ^ 2 + 2 * c ^ 2) μ :=
    (hfc.integrable_sq.const_mul 2).add (integrable_const (2 * c ^ 2))
  have hpoint : (∫ x, f x ^ 2 ∂μ) ≤ ∫ x, 2 * (f x - c) ^ 2 + 2 * c ^ 2 ∂μ := by
    apply integral_mono hf.integrable_sq hupperint
    intro x
    nlinarith [sq_nonneg (f x - 2 * c)]
  have hupper : (∫ x, 2 * (f x - c) ^ 2 + 2 * c ^ 2 ∂μ) =
      2 * (∫ x, (f x - c) ^ 2 ∂μ) + 2 * c ^ 2 * μ.real univ := by
    rw [integral_add (hfc.integrable_sq.const_mul 2) (integrable_const (2 * c ^ 2)),
      integral_const_mul, integral_const, smul_eq_mul]
    ring
  rw [hupper] at hpoint
  have hscaled := mul_le_mul_of_nonneg_right hconst hb
  calc
    (∫ x, f x ^ 2 ∂μ) ≤ 2 * (∫ x, (f x - c) ^ 2 ∂μ) + 2 * c ^ 2 * μ.real univ := hpoint
    _ ≤ 2 * (∫ x, (f x - c) ^ 2 ∂μ) +
        2 * ((∫ x, (f x - c) ^ 2 ∂μ) / μ.real E) * μ.real univ := by
      nlinarith [hscaled]
    _ = 2 * (1 + μ.real univ / μ.real E) * (∫ x, (f x - c) ^ 2 ∂μ) := by ring

end Buckling.AnchoredL2Estimate

end

end
