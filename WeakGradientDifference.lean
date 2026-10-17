module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01WeakGradientBridge
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Actual weak-gradient differences and their supersolution inequality

SOURCE_DRAFT: not compiled or registered. This generic algebraic consumer
takes the actual Euler equation and actual zero-extension subsolution
inequality supplied by separate producers. The sign of the difference is
needed only on the test domain. All products and subtractions are genuinely
integrable by L2 Holder; no zero convention of an undefined integral is used.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Buckling.WeakGradientDifference

open EllipticPdes.Embedding

theorem weak_gradient_sub {U V : Plane → ℝ} {g h : Fin 2 → Plane → ℝ}
    (hU2 : MemLp U 2 volume) (hV2 : MemLp V 2 volume)
    (hg2 : ∀ i, MemLp (g i) 2 volume) (hh2 : ∀ i, MemLp (h i) 2 volume)
    (hU : HasWeakGradOn univ U g) (hV : HasWeakGradOn univ V h) :
    HasWeakGradOn univ (fun x => V x - U x) (fun i x => h i x - g i x) := by
  intro φ hφc hφs hφU i
  have hφ : IsTestFn univ φ := ⟨hφc, hφs, hφU⟩
  have hm : MemLp φ 2 volume := hφc.continuous.memLp_of_hasCompactSupport hφs
  have hdm : MemLp (pderiv i φ) 2 volume :=
    (hφ.pderiv i).1.continuous.memLp_of_hasCompactSupport (hφ.pderiv i).2.1
  have eU : (∫ x, U x * pderiv i φ x) = -(∫ x, g i x * φ x) := by
    simpa only [Measure.restrict_univ, pderiv, EllipticPdes.Sobolev.partialD] using!
      hU φ hφc hφs hφU i
  have eV : (∫ x, V x * pderiv i φ x) = -(∫ x, h i x * φ x) := by
    simpa only [Measure.restrict_univ, pderiv, EllipticPdes.Sobolev.partialD] using!
      hV φ hφc hφs hφU i
  simp only [Measure.restrict_univ]
  change (∫ x, (V x - U x) * pderiv i φ x) = -(∫ x, (h i x - g i x) * φ x)
  simp_rw [sub_mul]
  have hVd : Integrable (fun x => V x * pderiv i φ x) volume := hV2.integrable_mul hdm
  have hUd : Integrable (fun x => U x * pderiv i φ x) volume := hU2.integrable_mul hdm
  have hhm : Integrable (fun x => h i x * φ x) volume := (hh2 i).integrable_mul hm
  have hgm : Integrable (fun x => g i x * φ x) volume := (hg2 i).integrable_mul hm
  rw [integral_sub hVd hUd, integral_sub hhm hgm, eU, eV]
  ring

theorem difference_supersolution {D : Set Plane} (hD : MeasurableSet D)
    {eigenvalue : ℝ} (heigenvalue : 0 ≤ eigenvalue) {U V : Plane → ℝ}
    (hU : MemLp U 2 volume) (hV : MemLp V 2 volume)
    {g h : Fin 2 → Plane → ℝ}
    (hg : ∀ i, MemLp (g i) 2 volume) (hh : ∀ i, MemLp (h i) 2 volume)
    (hNonneg : ∀ᵐ x ∂volume.restrict D, 0 ≤ V x - U x)
    (hEuler : ∀ ψ : Plane → ℝ, IsTestFn D ψ →
      (∑ i, ∫ x, h i x * pderiv i ψ x) = eigenvalue * ∫ x, V x * ψ x)
    (hSub : ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, g i x * pderiv i ψ x) ≤ eigenvalue * ∫ x, U x * ψ x) :
    ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, (h i x - g i x) * pderiv i ψ x := by
  intro ψ hψ hψN
  have hψG : IsTestFn univ ψ := ⟨hψ.1, hψ.2.1, subset_univ _⟩
  have hm : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1
  have hdm : ∀ i, MemLp (pderiv i ψ) 2 volume :=
    fun i => (hψ.pderiv i).1.continuous.memLp_of_hasCompactSupport (hψ.pderiv i).2.1
  have hVψ := hV.integrable_mul hm
  have hUψ := hU.integrable_mul hm
  have hDψ : Integrable (fun x => (V x - U x) * ψ x) volume :=
    (hV.sub hU).integrable_mul hm
  have hPoint : ∀ᵐ x ∂volume, 0 ≤ (V x - U x) * ψ x := by
    have hN := (ae_restrict_iff' hD).mp hNonneg
    filter_upwards [hN] with x hx
    by_cases hxD : x ∈ D
    · exact mul_nonneg (hx hxD) (hψN x)
    · rw [H01WeakGradientBridge.test_eq_zero_of_notMem hψ hxD, mul_zero]
  have hIntN : 0 ≤ ∫ x, (V x - U x) * ψ x := integral_nonneg_of_ae hPoint
  have hIntEq : (∫ x, (V x - U x) * ψ x) =
      (∫ x, V x * ψ x) - ∫ x, U x * ψ x := by
    simp_rw [sub_mul]
    exact integral_sub hVψ hUψ
  have hSum : (∑ i, ∫ x, (h i x - g i x) * pderiv i ψ x) =
      (∑ i, ∫ x, h i x * pderiv i ψ x) -
        ∑ i, ∫ x, g i x * pderiv i ψ x := by
    simp_rw [sub_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_sub ((hh i).integrable_mul (hdm i)) ((hg i).integrable_mul (hdm i))
  rw [hSum, hEuler ψ hψ]
  have hS := hSub ψ hψG hψN
  have hN := mul_nonneg heigenvalue hIntN
  rw [hIntEq] at hN
  nlinarith only [hS, hN]

end Buckling.WeakGradientDifference
end
end
