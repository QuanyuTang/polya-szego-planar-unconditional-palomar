module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01HilbertModel
public import H01UniformTails
public import EllipticPdes.Analysis.WeakCompactness
public import EllipticPdes.Analysis.DirectMethodForm
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Tactic.Linarith

/-!
# Weak-limit admissibility in the actual original H01

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The inputs are actual original H01 classes v_n, strong L2 convergence of
their actual whole-space zero extensions, and convergence of their two
original real energies. Boundedness is produced from the Hilbert norm
identity E0+E1. The actual closed H01 Hilbert submodule is complete, so the
pinned weak sequential compactness theorem produces a subsequence and a
limit in that same submodule. Bounded linearity of the actual value map
identifies its strong value limit with the value of the weak H01 limit.
Weak lower semicontinuity of the Hilbert norm, minus the preserved mass,
then gives the original gradient-energy inequality.

Only measurability of the domain is needed. No finite area, boundedness,
compact embedding, minimizer, PDE or preselected weak limit is an input.
H01UniformTails is imported for its actual J definitions; its finite-area
tail or compactness consequences are never applied.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01WeakLimitAdmissibility

/-- Actual inclusion in the complete Hilbert model of the original H01. -/
def lift (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    h01HilbertSubmodule Ω :=
  ⟨h1DataToHilbert Ω v, (h1DataToHilbert_mem_iff Ω v).mpr hv⟩

lemma lift_norm_sq (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    ‖lift Ω v hv‖ ^ 2 = energy0 v + energy1 v :=
  norm_h1DataToHilbert_sq Ω v

lemma lift_globalValue (Ω : Set Plane) (hΩm : MeasurableSet Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    h01HilbertGlobalValue Ω hΩm (lift Ω v hv) = h01GlobalValue Ω hΩm v := by
  change h01GlobalValue Ω hΩm ((h1DataToHilbert Ω).symm (h1DataToHilbert Ω v)) = _
  rw [(h1DataToHilbert Ω).symm_apply_apply]

/-- Actual return from the same closed Hilbert model to the original tuple. -/
def lower (Ω : Set Plane) (W : h01HilbertSubmodule Ω) : L2 Ω × (Fin 2 → L2 Ω) :=
  (h1DataToHilbert Ω).symm W.1

lemma lower_mem_H01 (Ω : Set Plane) (W : h01HilbertSubmodule Ω) :
    lower Ω W ∈ H01 Ω := by
  apply (h1DataToHilbert_mem_iff Ω (lower Ω W)).mp
  simpa [lower] using W.2

lemma lower_norm_sq (Ω : Set Plane) (W : h01HilbertSubmodule Ω) :
    ‖W‖ ^ 2 = energy0 (lower Ω W) + energy1 (lower Ω W) := by
  simpa [lower] using norm_h1DataToHilbert_sq Ω (lower Ω W)

lemma lower_globalValue (Ω : Set Plane) (hΩm : MeasurableSet Ω)
    (W : h01HilbertSubmodule Ω) :
    h01GlobalValue Ω hΩm (lower Ω W) = h01HilbertGlobalValue Ω hΩm W := rfl

lemma globalValue_norm_sq (Ω : Set Plane) (hΩm : MeasurableSet Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) :
    ‖h01GlobalValue Ω hΩm v‖ ^ 2 = energy0 v := by
  have hn : ‖h01GlobalValue Ω hΩm v‖ = ‖v.1‖ :=
    (lpExtendByZero volume 2 Ω hΩm).norm_map v.1
  simpa only [energy0] using congrArg (fun a : ℝ => a ^ 2) hn

/-- Strong actual zero-extended values and convergent original energies
produce a genuine original H01 limit with the same mass and no larger E1. -/
theorem exists_H01_of_strong_globalValue_tendsto {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (v : ℕ → L2 Ω × (Fin 2 → L2 Ω))
    (hv : ∀ n, v n ∈ H01 Ω) (z : Lp ℝ 2 (volume : Measure Plane)) (m e : ℝ)
    (hz : Tendsto (fun n => h01GlobalValue Ω hΩm (v n)) atTop (𝓝 z))
    (h0 : Tendsto (fun n => energy0 (v n)) atTop (𝓝 m))
    (h1 : Tendsto (fun n => energy1 (v n)) atTop (𝓝 e)) :
    ∃ w : L2 Ω × (Fin 2 → L2 Ω), w ∈ H01 Ω ∧
      h01GlobalValue Ω hΩm w = z ∧ energy0 w = m ∧ energy1 w ≤ e := by
  let U : ℕ → h01HilbertSubmodule Ω := fun n => lift Ω (v n) (hv n)
  have hU : ∀ n, ‖U n‖ ^ 2 = energy0 (v n) + energy1 (v n) :=
    fun n => lift_norm_sq Ω (v n) (hv n)
  have hTotal : Tendsto (fun n => energy0 (v n) + energy1 (v n)) atTop (𝓝 (m + e)) :=
    h0.add h1
  obtain ⟨C, hC⟩ := hTotal.bddAbove_range
  have hBound : ∀ n, ‖U n‖ ≤ Real.sqrt C := by
    intro n
    calc
      ‖U n‖ = Real.sqrt (‖U n‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt C := Real.sqrt_le_sqrt (by rw [hU n]; exact hC ⟨n, rfl⟩)
  obtain ⟨W, φ, hφ, hWeak⟩ := EllipticPdes.Analysis.exists_weakLimit hBound
  have hStrong : Tendsto (fun n => h01HilbertGlobalValue Ω hΩm (U (φ n)))
      atTop (𝓝 z) := by
    simpa only [U, lift_globalValue, Function.comp_def] using hz.comp hφ.tendsto_atTop
  have hIdentify : z = h01HilbertGlobalValue Ω hΩm W :=
    EllipticPdes.Analysis.eq_of_tendsto_of_weakLimit hWeak hStrong
  have hNormEq : (fun n => ‖U n‖) =
      (fun n => Real.sqrt (energy0 (v n) + energy1 (v n))) := by
    funext n
    rw [← hU n, Real.sqrt_sq (norm_nonneg _)]
  have hNorm : Tendsto (fun n => ‖U n‖) atTop (𝓝 (Real.sqrt (m + e))) := by
    rw [hNormEq]
    exact (Real.continuous_sqrt.tendsto (m + e)).comp hTotal
  have hWeakBound : ‖W‖ ≤ Real.sqrt (m + e) :=
    EllipticPdes.Analysis.norm_weakLimit_le_of_tendsto
      (hNorm.comp hφ.tendsto_atTop) hWeak
  have hTotalNonneg : 0 ≤ m + e := by
    apply ge_of_tendsto hTotal
    exact Eventually.of_forall fun n => by rw [← hU n]; exact sq_nonneg _
  have hWeakSq : ‖W‖ ^ 2 ≤ m + e := by
    calc
      ‖W‖ ^ 2 ≤ Real.sqrt (m + e) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hWeakBound 2
      _ = m + e := Real.sq_sqrt hTotalNonneg
  have hMassValue : Tendsto (fun n => energy0 (v n)) atTop (𝓝 (‖z‖ ^ 2)) := by
    simpa only [globalValue_norm_sq] using hz.norm.pow 2
  have hMassLimit : m = ‖z‖ ^ 2 := tendsto_nhds_unique h0 hMassValue
  have hValue : h01GlobalValue Ω hΩm (lower Ω W) = z := by
    rw [lower_globalValue]
    exact hIdentify.symm
  have hMass : energy0 (lower Ω W) = m := by
    rw [← globalValue_norm_sq Ω hΩm (lower Ω W), hValue, hMassLimit]
  refine ⟨lower Ω W, lower_mem_H01 Ω W, hValue, hMass, ?_⟩
  rw [lower_norm_sq, hMass] at hWeakSq
  linarith

/-- The common preservation consumer: if actual approximants approach a
candidate full-space value while their original energies approach those
of a specified original H01 class, that candidate is admissible with the
same original mass and no larger original gradient energy. -/
theorem exists_H01_of_strong_globalValue_tendsto_same_energies {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (u : {u : L2 Ω × (Fin 2 → L2 Ω) // u ∈ H01 Ω})
    (v : ℕ → L2 Ω × (Fin 2 → L2 Ω)) (hv : ∀ n, v n ∈ H01 Ω)
    (z : Lp ℝ 2 (volume : Measure Plane))
    (hz : Tendsto (fun n => h01GlobalValue Ω hΩm (v n)) atTop (𝓝 z))
    (h0 : Tendsto (fun n => energy0 (v n)) atTop (𝓝 (energy0 u.1)))
    (h1 : Tendsto (fun n => energy1 (v n)) atTop (𝓝 (energy1 u.1))) :
    ∃ w : L2 Ω × (Fin 2 → L2 Ω), w ∈ H01 Ω ∧
      h01GlobalValue Ω hΩm w = z ∧ energy0 w = energy0 u.1 ∧ energy1 w ≤ energy1 u.1 :=
  exists_H01_of_strong_globalValue_tendsto hΩm v hv z (energy0 u.1) (energy1 u.1) hz h0 h1

end Buckling.H01WeakLimitAdmissibility

end

end
