module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01ComponentProjection
public import EllipticPdes.Sobolev.Basic
public import Mathlib.Topology.Sequences

/-!
# Restriction of the original H01 to a relatively closed open piece

SOURCE_DRAFT: not registered or native checked. This file keeps the actual
target measure `volume.restrict C`. It constructs restriction by extending
from the original domain to the plane and then restricting to C, proves
original H01(C) membership by test graphs and closure, and identifies both
energies with the projection inside H01(Omega). No a.e. identification of
Sobolev spaces on different domains is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Buckling
namespace ComponentCutoff

def l2Restriction (Ω C : Set Plane) (hΩm : MeasurableSet Ω) :
    L2 Ω →L[ℝ] L2 C :=
  (LpToLpRestrictCLM Plane ℝ ℝ volume 2 C).comp
    (lpExtendByZero volume 2 Ω hΩm).toContinuousLinearMap

lemma coeFn_l2Restriction (Ω C : Set Plane) (hΩm : MeasurableSet Ω)
    (hC : MeasurableSet C) (hCΩ : C ⊆ Ω) (f : L2 Ω) :
    (l2Restriction Ω C hΩm f : Plane → ℝ) =ᵐ[volume.restrict C]
      (f : Plane → ℝ) := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℝ C
    (lpExtendByZero volume 2 Ω hΩm f),
    ae_restrict_of_ae (coeFn_lpExtendByZero hΩm f), ae_restrict_mem hC] with x hr he hxC
  change (l2Restriction Ω C hΩm f : Plane → ℝ) x = f x
  change (LpToLpRestrictCLM Plane ℝ ℝ volume 2 C
    (lpExtendByZero volume 2 Ω hΩm f) : Plane → ℝ) x = f x
  rw [hr, he, Set.indicator_of_mem (hCΩ hxC)]

def dataRestriction (Ω C : Set Plane) (hΩm : MeasurableSet Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) : L2 C × (Fin 2 → L2 C) :=
  (l2Restriction Ω C hΩm v.1, fun i => l2Restriction Ω C hΩm (v.2 i))

lemma continuous_dataRestriction (Ω C : Set Plane) (hΩm : MeasurableSet Ω) :
    Continuous (dataRestriction Ω C hΩm) :=
  ((l2Restriction Ω C hΩm).continuous.comp continuous_fst).prodMk
    (continuous_pi fun i => (l2Restriction Ω C hΩm).continuous.comp
      ((continuous_apply i).comp continuous_snd))

lemma l2Restriction_toL2 {Ω C : Set Plane} {φ : Plane → ℝ}
    (hΩm : MeasurableSet Ω) (hC : IsOpen C)
    (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω) (hφ : IsTestFn Ω φ) :
    l2Restriction Ω C hΩm hφ.toL2 = (isTestFn_indicator hC hrel hφ).toL2 := by
  apply Lp.ext
  filter_upwards [coeFn_l2Restriction Ω C hΩm hC.measurableSet hCΩ hφ.toL2,
    ae_restrict_of_ae_restrict_of_subset hCΩ hφ.memLp.coeFn_toLp,
    (isTestFn_indicator hC hrel hφ).memLp.coeFn_toLp,
    ae_restrict_mem hC.measurableSet] with x hr hf hg hxC
  change (hφ.toL2 : Plane → ℝ) x = φ x at hf
  change ((isTestFn_indicator hC hrel hφ).toL2 : Plane → ℝ) x =
    C.indicator φ x at hg
  rw [hr, hf, hg, Set.indicator_of_mem hxC]

lemma dataRestriction_graphH1 {Ω C : Set Plane}
    (hΩm : MeasurableSet Ω) (hC : IsOpen C)
    (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    (φ : {φ // IsTestFn Ω φ}) :
    dataRestriction Ω C hΩm (graphH1 φ) =
      graphH1 ⟨C.indicator φ.1, isTestFn_indicator hC hrel φ.2⟩ := by
  apply Prod.ext
  · exact l2Restriction_toL2 hΩm hC hrel hCΩ φ.2
  · funext i
    change l2Restriction Ω C hΩm (φ.2.pderiv i).toL2 =
      ((isTestFn_indicator hC hrel φ.2).pderiv i).toL2
    rw [l2Restriction_toL2 hΩm hC hrel hCΩ (φ.2.pderiv i)]
    apply MemLp.toLp_congr
    exact Eventually.of_forall
      (fun x => (congrFun (pderiv_indicator hC hrel φ.2 i) x).symm)

lemma dataRestriction_mem_H01 {Ω C : Set Plane}
    (hΩm : MeasurableSet Ω) (hC : IsOpen C)
    (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    dataRestriction Ω C hΩm v ∈ H01 C := by
  change v ∈ closure (Set.range (graphH1 (Ω := Ω))) at hv
  obtain ⟨s, hs, hst⟩ := mem_closure_iff_seq_limit.mp hv
  have hmem : ∀ n, dataRestriction Ω C hΩm (s n) ∈ H01 C := by
    intro n
    obtain ⟨φ, hφ⟩ := hs n
    rw [← hφ, dataRestriction_graphH1 hΩm hC hrel hCΩ φ]
    exact subset_closure ⟨_, rfl⟩
  have hlim : Tendsto (fun n => dataRestriction Ω C hΩm (s n)) atTop
      (𝓝 (dataRestriction Ω C hΩm v)) :=
    ((continuous_dataRestriction Ω C hΩm).tendsto v).comp hst
  exact (isClosed_H01 C).mem_of_tendsto hlim (Eventually.of_forall hmem)

lemma norm_sq_l2Restriction_eq_projection (Ω C : Set Plane)
    (hΩm : MeasurableSet Ω) (hC : MeasurableSet C) (hCΩ : C ⊆ Ω) (f : L2 Ω) :
    ‖l2Restriction Ω C hΩm f‖ ^ 2 = ‖l2Projection Ω C hC f‖ ^ 2 := by
  rw [MeasureTheory.L2.norm_sq_eq_integral_sq, MeasureTheory.L2.norm_sq_eq_integral_sq]
  calc
    (∫ x, (l2Restriction Ω C hΩm f x) ^ 2 ∂(volume.restrict C)) =
        ∫ x, (f x) ^ 2 ∂(volume.restrict C) := by
      apply integral_congr_ae
      exact (coeFn_l2Restriction Ω C hΩm hC hCΩ f).mono
        fun x hx => congrArg (fun r : ℝ => r ^ 2) hx
    _ = ∫ x, C.indicator (fun y => (f y) ^ 2) x ∂(volume.restrict Ω) := by
      rw [integral_indicator hC, Measure.restrict_restrict_of_subset hCΩ]
    _ = ∫ x, (l2Projection Ω C hC f x) ^ 2 ∂(volume.restrict Ω) := by
      apply integral_congr_ae
      filter_upwards [coeFn_l2Projection Ω C hC f] with x hx
      rw [hx]
      by_cases hxc : x ∈ C
      · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxc]
      · simp only [Set.indicator_of_notMem hxc, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]

lemma energy0_dataRestriction_eq_projection (Ω C : Set Plane)
    (hΩm : MeasurableSet Ω) (hC : MeasurableSet C) (hCΩ : C ⊆ Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) :
    energy0 (dataRestriction Ω C hΩm v) = energy0 (dataProjection Ω C hC v) :=
  norm_sq_l2Restriction_eq_projection Ω C hΩm hC hCΩ v.1

lemma energy1_dataRestriction_eq_projection (Ω C : Set Plane)
    (hΩm : MeasurableSet Ω) (hC : MeasurableSet C) (hCΩ : C ⊆ Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) :
    energy1 (dataRestriction Ω C hΩm v) = energy1 (dataProjection Ω C hC v) := by
  apply Finset.sum_congr rfl
  intro i _
  exact norm_sq_l2Restriction_eq_projection Ω C hΩm hC hCΩ (v.2 i)

end ComponentCutoff
end Buckling

end

end
