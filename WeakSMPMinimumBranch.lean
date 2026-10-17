module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPConnected
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# A minimum-zero pair of actual weak supersolutions has a zero branch

SOURCE_DRAFT: not compiled or registered. This is a consumer of the actual
weak SMP producer. Weak-gradient and supersolution data are explicit at
this generic interface; the polarization assembly must produce them.
No assumption of pointwise positivity or classical regularity is made.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Buckling.WeakSMPMinimumBranch

open EllipticPdes.Embedding

theorem zero_branch {D : Set Plane} (hD : IsOpen D) (hconn : IsPreconnected D)
    (hne : D.Nonempty) {w z : Plane → ℝ}
    (hw : MemLp w 2 volume) (hz : MemLp z 2 volume)
    {g h : Fin 2 → Plane → ℝ}
    (hg : ∀ i, MemLp (g i) 2 volume) (hh : ∀ i, MemLp (h i) 2 volume)
    (hwg : HasWeakGradOn univ w g) (hzh : HasWeakGradOn univ z h)
    (hwN : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hzN : ∀ᵐ x ∂volume.restrict D, 0 ≤ z x)
    (hwS : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x)
    (hzS : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, h i x * pderiv i ψ x)
    (hmin : ∀ᵐ x ∂volume.restrict D, min (w x) (z x) = 0) :
    (w =ᵐ[volume.restrict D] 0) ∨ (z =ᵐ[volume.restrict D] 0) := by
  rcases WeakSMPConnected.zero_or_pos_ae hD hconn hw hg hwg hwN hwS with hw0 | hwP
  · exact Or.inl hw0
  rcases WeakSMPConnected.zero_or_pos_ae hD hconn hz hh hzh hzN hzS with hz0 | hzP
  · exact Or.inr hz0
  have hnull : ∀ᵐ x ∂volume, x ∉ D := by
    have hwP' := (ae_restrict_iff' hD.measurableSet).mp hwP
    have hzP' := (ae_restrict_iff' hD.measurableSet).mp hzP
    have hmin' := (ae_restrict_iff' hD.measurableSet).mp hmin
    filter_upwards [hwP', hzP', hmin'] with x hwx hzx hmx hxD
    have hp : 0 < min (w x) (z x) := lt_min (hwx hxD) (hzx hxD)
    rw [hmx hxD] at hp
    exact lt_irrefl (0 : ℝ) hp
  have hzero : volume D = 0 := by
    exact measure_eq_zero_iff_ae_notMem.mpr hnull
  exact ((hD.measure_pos volume hne).ne' hzero).elim

end Buckling.WeakSMPMinimumBranch
end
end
