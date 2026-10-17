/-
The approximation and level-set convergence argument is adapted from
EllipticPdes/Sobolev/GraphLattice.lean, pinned at
ec784093f30308ef770ff855ce624725adf6f870.
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in that project's LICENSE.
Authors of the original argument: Alejandro Soto Franco
-/

module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EllipticPdes.Sobolev.GraphLattice
public import Mathlib.Tactic.Linarith

/-!
# Positive part above a smooth nonnegative global obstacle

SOURCE_DRAFT: not registered or native checked.
The obstacle is an actual global smooth compact function, and is not
assumed to lie in H01 of the domain. Nonnegativity of the obstacle makes
every positive-part approximant compactly supported inside the domain.
The actual level-set theorem supplies equality of the two gradients on
their equality layer, so the truncations converge in the true H1 norm.
No weak limit, boundary regularity or order-ideal principle is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace Buckling.GraphH01ShiftedTruncation

open EllipticPdes

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Set E}

lemma memLp_positive_difference {ν : Measure E} {v η : E → ℝ}
    (hv : MemLp v 2 ν) (hη : MemLp η 2 ν) (hηn : ∀ x, 0 ≤ η x) :
    MemLp (fun x => max (v x - η x) 0) 2 ν := by
  refine hv.of_le (((continuous_id.max continuous_const).comp_aestronglyMeasurable
    (hv.aestronglyMeasurable.sub hη.aestronglyMeasurable)))
    (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [le_abs_self (v x), hηn x]) (abs_nonneg _)

lemma compact_support_positive_difference {φ η : E → ℝ}
    (hφ : φ ∈ testFunctions Ω) (hη : ∀ x, 0 ≤ η x) :
    HasCompactSupport (fun x => max (φ x - η x) 0) ∧
      tsupport (fun x => max (φ x - η x) 0) ⊆ Ω := by
  have hs : tsupport (fun x => max (φ x - η x) 0) ⊆ tsupport φ :=
    closure_minimal (fun x hx => subset_tsupport _ fun h0 =>
      Function.mem_support.mp hx (by
        rw [h0, zero_sub, max_eq_right (neg_nonpos.mpr (hη x))]))
      (isClosed_tsupport _)
  exact ⟨hφ.2.1.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hφ.2.2⟩

/-- The true graph H01 is closed under `(v-eta)^+` for every smooth
nonnegative compact global obstacle eta, even if eta is not in H01(Omega). -/
theorem exists_mem_H01_positive_difference (hΩ : IsOpen Ω)
    {V : H1Graph μ Ω} (hV : V ∈ H1Graph.H01 μ Ω)
    {η : E → ℝ} (hη : η ∈ testFunctions (univ : Set E))
    (hηn : ∀ x, 0 ≤ η x) :
    ∃ W : H1Graph μ Ω, W ∈ H1Graph.H01 μ Ω ∧
      ((H1Graph.fnL W : E → ℝ) =ᵐ[μ.restrict Ω]
        fun x => max (H1Graph.fnL V x - η x) 0) ∧
      ((H1Graph.gradL W : E → E) =ᵐ[μ.restrict Ω]
        fun x => if η x < H1Graph.fnL V x then
          H1Graph.gradL V x - gradient η x else 0) := by
  classical
  obtain ⟨φ, hφ⟩ := H1Graph.exists_seq_testGraphₗ_tendsto hV
  obtain ⟨hX0, hXg⟩ := H1Graph.tendsto_iff.1 hφ
  let v : E → ℝ := H1Graph.fnL V
  let g : E → E := H1Graph.gradL V
  let ψ : ℕ → E → ℝ := fun n => φ n
  have hψ : ∀ n, ψ n ∈ testFunctions Ω := fun n => (φ n).2
  have hψc : ∀ n, Continuous (ψ n) := fun n => (hψ n).1.continuous
  have hvm : MemLp v 2 (μ.restrict Ω) := Lp.memLp _
  have hgm : MemLp g 2 (μ.restrict Ω) := Lp.memLp _
  have hηm : MemLp η 2 μ := hη.1.continuous.memLp_of_hasCompactSupport hη.2.1
  have hdηm : MemLp (gradient η) 2 μ :=
    (continuous_gradient_of_mem hη).memLp_of_hasCompactSupport
      (hasCompactSupport_gradient_of_mem hη)
  have hηr := hηm.mono_measure (Measure.restrict_le_self (s := Ω))
  have hdηr := hdηm.mono_measure (Measure.restrict_le_self (s := Ω))
  have hX0' : Tendsto (fun n => eLpNorm (ψ n - v) 2 (μ.restrict Ω))
      atTop (𝓝 0) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hX0).congr fun n =>
      eLpNorm_congr_ae ((H1Graph.coeFn_fnL_testGraphₗ (φ n)).sub EventuallyEq.rfl)
  have hXg' : Tendsto (fun n => eLpNorm (gradient (ψ n) - g) 2 (μ.restrict Ω))
      atTop (𝓝 0) :=
    ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hXg).congr fun n =>
      eLpNorm_congr_ae ((H1Graph.coeFn_gradL_testGraphₗ (φ n)).sub EventuallyEq.rfl)
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hX0').exists_seq_tendsto_ae
  have hwv := (H1Graph.mem_W12_iff_hasWeakFDerivOn hΩ V).1
    (H1Graph.H01_le_W12 hV)
  have hwη : HasWeakFDerivOn (⟨Ω, hΩ⟩ : Opens E) η (fderiv ℝ η) μ :=
    hasWeakFDerivOn_fderiv ((hη.1.of_le (by exact_mod_cast le_top)).contDiffOn)
  have hw : HasWeakFDerivOn (⟨Ω, hΩ⟩ : Opens E) (v - η)
      (fun x => innerSL ℝ (g x - gradient η x)) μ := by
    apply (hwv.sub hwη).congr_ae EventuallyEq.rfl
    exact Eventually.of_forall fun x => by
      simp only [Pi.sub_apply, map_sub, gradient]
      change innerSL ℝ (g x) - fderiv ℝ η x =
        innerSL ℝ (g x) - (InnerProductSpace.toDual ℝ E)
          ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x))
      rw [(InnerProductSpace.toDual ℝ E).apply_symm_apply]
  have hlev : ∀ᵐ x ∂(μ.restrict Ω), (v - η) x = 0 →
      (g - gradient η) x = 0 := by
    filter_upwards [hw.ae_eq_zero_of_eq_const 0] with x hx hxeq
    change g x - gradient η x = 0
    apply norm_eq_zero.mp
    rw [← innerSL_apply_norm ℝ, hx hxeq, norm_zero]
  let T : ℕ → E → ℝ := fun i x => max (ψ (ns i) x - η x) 0
  let D : ℕ → E → E := fun i x =>
    if 0 < ψ (ns i) x - η x then gradient (ψ (ns i)) x - gradient η x else 0
  have hTm : ∀ i, MemLp (T i) 2 μ := fun i =>
    memLp_positive_difference ((hψc _).memLp_of_hasCompactSupport (hψ _).2.1) hηm hηn
  have hDm : ∀ i, MemLp (D i) 2 μ := fun i =>
    memLp_ite_lt_vec
      (((hψc _).memLp_of_hasCompactSupport (hψ _).2.1).sub hηm)
      (((continuous_gradient_of_mem (hψ _)).memLp_of_hasCompactSupport
        (hasCompactSupport_gradient_of_mem (hψ _))).sub hdηm) 0
  have hTwg : ∀ i, HasWeakFDerivOn ⊤ (T i)
      (fun x => innerSL ℝ (D i x)) μ := fun i => by
    have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (ψ (ns i) - η) := (hψ _).1.sub hη.1
    have ht := (hasWeakFDerivOn_fderiv (Ω := (⊤ : Opens E)) (μ := μ)
      ((hsmooth.of_le (by exact_mod_cast le_top)).contDiffOn)).posPart
    apply ht.congr_ae EventuallyEq.rfl
    exact Eventually.of_forall fun x => by
      dsimp [D]
      split_ifs
      · rw [fderiv_sub ((hψ _).1.differentiable (by simp) x)
          (hη.1.differentiable (by simp) x)]
        simp only [gradient, map_sub]
        change fderiv ℝ (ψ (ns i)) x - fderiv ℝ η x =
          (InnerProductSpace.toDual ℝ E)
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (ψ (ns i)) x)) -
          (InnerProductSpace.toDual ℝ E)
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ η x))
        simp only [(InnerProductSpace.toDual ℝ E).apply_symm_apply]
      · simp
  have hWmem : ∀ i, H1Graph.mk
      ((hTm i).mono_measure Measure.restrict_le_self |>.toLp (T i))
      ((hDm i).mono_measure Measure.restrict_le_self |>.toLp (D i)) ∈
      H1Graph.H01 μ Ω := fun i =>
    H1Graph.mem_H01_of_hasCompactSupport hΩ (hTwg i) (hTm i) (hDm i)
      (compact_support_positive_difference (hψ _) hηn).1
      (compact_support_positive_difference (hψ _) hηn).2
  have hwlim := memLp_positive_difference hvm hηr hηn
  have hhlim := memLp_ite_lt_vec (hvm.sub hηr) (hgm.sub hdηr) 0
  have hWlim : H1Graph.mk (hwlim.toLp _) (hhlim.toLp _) ∈ H1Graph.H01 μ Ω := by
    refine H1Graph.isClosed_H01.mem_of_tendsto (b := atTop) ?_
      (Eventually.of_forall hWmem)
    refine H1Graph.tendsto_mk_of_tendsto_eLpNorm hwlim hhlim
      (f := T) (g := D) (fun i => ?_) (fun i => ?_) ?_ ?_
    · rw [H1Graph.fnL_mk]
      exact ((hTm i).mono_measure Measure.restrict_le_self).coeFn_toLp
    · rw [H1Graph.gradL_mk]
      exact ((hDm i).mono_measure Measure.restrict_le_self).coeFn_toLp
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (hX0'.comp hns.tendsto_atTop) (fun _ => zero_le) fun i => ?_
      apply eLpNorm_mono_ae
        ((((hψc _).sub hη.1.continuous).max continuous_const).aestronglyMeasurable.sub
          hwlim.aestronglyMeasurable)
      exact Eventually.of_forall fun x => by
        simp only [Pi.sub_apply, Real.norm_eq_abs, T]
        exact abs_max_sub_le _ _ _
    · have hshift : Tendsto
          (fun i => eLpNorm ((gradient (ψ (ns i)) - gradient η) -
            (g - gradient η)) 2 (μ.restrict Ω)) atTop (𝓝 0) := by
        simpa only [Function.comp_apply, sub_sub_sub_cancel_right] using! hXg'.comp hns.tendsto_atTop
      exact tendsto_eLpNorm_ite_lt_sub
        (fun i => ((hψc _).sub hη.1.continuous).aestronglyMeasurable)
        (fun i => ((continuous_gradient_of_mem (hψ _)).sub
          (continuous_gradient_of_mem hη)).aestronglyMeasurable)
        (hvm.sub hηr).aestronglyMeasurable (hgm.sub hdηr) hshift
        (hae.mono fun x hx => hx.sub tendsto_const_nhds) hlev
  refine ⟨H1Graph.mk (hwlim.toLp _) (hhlim.toLp _), hWlim, ?_, ?_⟩
  · simpa only [H1Graph.fnL_mk] using hwlim.coeFn_toLp
  · simpa only [H1Graph.gradL_mk, Pi.sub_apply, sub_pos] using hhlim.coeFn_toLp

end Buckling.GraphH01ShiftedTruncation

end

end
