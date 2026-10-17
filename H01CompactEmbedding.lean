module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01TranslationModulus
public import H01UniformTails
public import FrechetKolmogorovTail
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Finite-area compactness for the original H01 value map

SOURCE_DRAFT, Lean 4.35-rc3 only; NOT compiled.
All analytic hypotheses of the finite-grid criterion are produced for the
actual original H01 unit ball. The domain is measurable with finite area;
it need not be bounded. This file does not assume compactness or a minimizer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Topology

namespace Buckling

/-- Both independently described maps are literally the zero extension of
the original value coordinate after the same Hilbert coordinate change. -/
lemma h01HilbertGlobalValue_eq_fullValue (Ω : Set Plane) (hΩm : MeasurableSet Ω) :
    h01HilbertGlobalValue Ω hΩm = h01HilbertFullValue Ω hΩm := rfl

/-- The full-space values of the original H01 unit ball are totally bounded.
Finite area supplies the uniform tail; H01 supplies the translation modulus. -/
theorem h01HilbertUnitValueSet_totallyBounded {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (hfin : volume Ω < ⊤) :
    TotallyBounded (h01HilbertUnitValueSet Ω hΩm) := by
  refine FaberKrahnDevelopment.FrechetKolmogorovTail.totallyBounded_of_lipschitz_translation_uniform_tails
      (h01HilbertUnitValueSet Ω hΩm) (M := 1) (Λ := 1) ?_ ?_
      (h01HilbertUnitValueSet_uniform_tails hΩm hfin)
  · rintro g ⟨u, hu, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    rw [h01HilbertGlobalValue_eq_fullValue]
    exact (h01HilbertFullValue_norm_le hΩm u).trans hu
  · rintro g ⟨u, hu, rfl⟩ h
    rw [Metric.mem_closedBall, dist_zero_right] at hu
    rw [h01HilbertGlobalValue_eq_fullValue, one_mul]
    exact h01HilbertFullValue_unit_translation hΩm u hu h

/-- The actual full-space value map of the original H01 is compact on any
measurable finite-area domain, including unbounded domains. -/
theorem h01HilbertGlobalValue_isCompact {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (hfin : volume Ω < ⊤) :
    IsCompactOperator (h01HilbertGlobalValue Ω hΩm).toLinearMap := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (h01HilbertGlobalValue Ω hΩm).toLinearMap one_pos).mpr
  exact (h01HilbertUnitValueSet_totallyBounded hΩm hfin).closure.isCompact_of_isClosed
    isClosed_closure

end Buckling

end

end
