module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01AbsoluteValue
public import H01DirichletEuler
public import EllipticPdes.Analysis.LpExtendByZero

/-!
# A nonnegative minimizer of the original Dirichlet infimum

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The actual original minimizer is replaced by the actual H01 absolute-value
class. Its mass remains one, and its gradient energy cannot increase. The
original denominator-free Rayleigh lower bound gives the reverse inequality,
so the absolute-value class still attains the same original dirichletEig.
Its original restricted value and its actual full-space lpExtendByZero value
are almost everywhere nonnegative. The actual variational Euler identity
is then inherited from equality in the original energy lower bound.

The only domain inputs are open, nonempty, finite volume. No connectedness,
boundedness, positivity, minimizer, weak PDE or maximum principle is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling
namespace H01NonnegativeMinimizer

/-- The actual zero extension of a nonnegative restricted L2 value is
nonnegative in full volume; outside the domain its indicator is zero. -/
lemma lpExtendByZero_nonneg_ae {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (f : L2 Ω) (hf : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ f x) :
    ∀ᵐ x ∂volume, 0 ≤ (lpExtendByZero volume 2 Ω hΩm f : Plane → ℝ) x := by
  have hfin : ∀ᵐ x ∂volume, x ∈ Ω → 0 ≤ f x := (ae_restrict_iff' hΩm).mp hf
  filter_upwards [coeFn_lpExtendByZero hΩm f, hfin] with x hx hfx
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · simpa only [Set.indicator_of_mem hxΩ] using hfx hxΩ
  · rw [Set.indicator_of_notMem hxΩ]

/-- Nonnegativity of the original eigenvalue follows from an actual
attaining class and the unchanged sum-of-squared-norms energy. -/
theorem dirichletEig_nonneg {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) (hfin : volume Ω < ⊤) : 0 ≤ dirichletEig Ω := by
  obtain ⟨u, _, _, h1⟩ := exists_H01_dirichletEig_minimizer hΩ hne hfin
  rw [← h1]
  exact Finset.sum_nonneg fun i _ => sq_nonneg ‖u.2 i‖

end H01NonnegativeMinimizer

/-- An actual mass-one nonnegative minimizer of the actual original
Dirichlet ciInf, with nonnegative actual full-space zero extension. -/
theorem exists_H01_nonnegative_dirichletEig_minimizer {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤) :
    ∃ w : L2 Ω × (Fin 2 → L2 Ω), w ∈ H01 Ω ∧ energy0 w = 1 ∧
      energy1 w = dirichletEig Ω ∧
      (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ w.1 x) ∧
      (∀ᵐ x ∂volume,
        0 ≤ (lpExtendByZero volume 2 Ω hΩ.measurableSet w.1 : Plane → ℝ) x) := by
  obtain ⟨u, hu, hu0, hu1⟩ := exists_H01_dirichletEig_minimizer hΩ hne hfin
  obtain ⟨w, hw, hwAbs, hw0, hw1⟩ := H01AbsoluteValue.exists_abs_H01 hΩ u hu
  have h0 : energy0 w = 1 := hw0.trans hu0
  have hLower := H01DirichletEuler.dirichletEig_mul_energy0_le w hw
  have h1 : energy1 w = dirichletEig Ω := by
    apply le_antisymm
    · simpa only [hu1] using hw1
    · simpa only [h0, mul_one] using hLower
  have hn : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ w.1 x := by
    filter_upwards [hwAbs] with x hx
    rw [hx]
    exact abs_nonneg _
  exact ⟨w, hw, h0, h1, hn,
    H01NonnegativeMinimizer.lpExtendByZero_nonneg_ae hΩ.measurableSet w.1 hn⟩

/-- The nonnegative original minimizer also satisfies the actual original
Euler identity against every original H01 variation. -/
theorem exists_H01_nonnegative_dirichletEig_minimizer_with_euler {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤) :
    ∃ w : L2 Ω × (Fin 2 → L2 Ω), w ∈ H01 Ω ∧ energy0 w = 1 ∧
      energy1 w = dirichletEig Ω ∧
      (∀ᵐ x ∂(volume.restrict Ω), 0 ≤ w.1 x) ∧
      (∀ᵐ x ∂volume,
        0 ≤ (lpExtendByZero volume 2 Ω hΩ.measurableSet w.1 : Plane → ℝ) x) ∧
      ∀ v : L2 Ω × (Fin 2 → L2 Ω), v ∈ H01 Ω →
        (∑ i, inner ℝ (w.2 i) (v.2 i)) = dirichletEig Ω * inner ℝ w.1 v.1 := by
  obtain ⟨w, hw, h0, h1, hn, hext⟩ :=
    exists_H01_nonnegative_dirichletEig_minimizer hΩ hne hfin
  refine ⟨w, hw, h0, h1, hn, hext, ?_⟩
  intro v hv
  exact H01DirichletEuler.euler_of_energy_eq hw
    (by simpa only [h0, mul_one] using h1) v hv

end Buckling

end

end
