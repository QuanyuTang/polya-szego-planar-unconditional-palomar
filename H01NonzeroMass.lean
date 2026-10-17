module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01UniformTails
public import FiniteAreaTestLpBounds
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Nonzero mass in the original H01 on a nonempty open domain

SOURCE_DRAFT, Lean 4.35.0-rc3 only; NOT compiled or registered.
A genuine smooth bump in a ball contained in the domain produces an
original test function with positive square integral. Its actual graphH1
belongs to the original H01 by the defining closure. After the existing
Hilbert coordinate change and the actual isometric extension by zero, its
value component still has positive norm. Real scalar rescaling then gives
unit mass. No nonzero test, finite-area assumption, compact embedding,
eigenfunction or minimizer is supplied as an additional hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Topology

namespace Buckling

/-- A real compactly supported smooth test with positive L2 mass is produced
from the domain's actual openness and nonemptiness. -/
lemma exists_test_sq_integral_pos {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ φ : {φ // IsTestFn Ω φ}, 0 < ∫ x, φ.1 x ^ 2 := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ a ha
  let b : ContDiffBump a := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hb : IsTestFn Ω b := by
    refine ⟨b.contDiff, b.hasCompactSupport, ?_⟩
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball
      (by show ε / 2 < ε; linarith)).trans hball
  have hb_one : (b : Plane → ℝ) a = 1 :=
    b.one_of_mem_closedBall (Metric.mem_closedBall_self
      (by show (0 : ℝ) ≤ ε / 4; positivity))
  have hc : Continuous (fun x => (b : Plane → ℝ) x ^ 2) :=
    b.continuous.fun_pow 2
  have hs : HasCompactSupport (fun x => (b : Plane → ℝ) x ^ 2) :=
    b.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  refine ⟨⟨b, hb⟩, ?_⟩
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hs
    (fun x => sq_nonneg ((b : Plane → ℝ) x)) (x := a) (by
      change (b : Plane → ℝ) a ^ 2 ≠ 0
      rw [hb_one]
      norm_num)

/-- The original H01 Hilbert model genuinely contains a class whose actual
full-space value has norm one; no witness is assumed from outside. -/
theorem exists_h01HilbertGlobalValue_norm_eq_one {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ W : h01HilbertSubmodule Ω,
      ‖h01HilbertGlobalValue Ω hΩ.measurableSet W‖ = 1 := by
  obtain ⟨φ, hmass⟩ := exists_test_sq_integral_pos hΩ hne
  have hmem : graphH1 φ ∈ H01 Ω := by
    exact subset_closure
      (show graphH1 φ ∈ Set.range (graphH1 (Ω := Ω)) from ⟨φ, rfl⟩)
  let W₀ : h01HilbertSubmodule Ω :=
    ⟨h1DataToHilbert Ω (graphH1 φ),
      (h1DataToHilbert_mem_iff Ω (graphH1 φ)).mpr hmem⟩
  have hvalue : h01HilbertGlobalValue Ω hΩ.measurableSet W₀ =
      lpExtendByZero volume 2 Ω hΩ.measurableSet φ.2.toL2 := by
    change lpExtendByZero volume 2 Ω hΩ.measurableSet
      (((h1DataToHilbert Ω).symm (h1DataToHilbert Ω (graphH1 φ))).1) =
        lpExtendByZero volume 2 Ω hΩ.measurableSet φ.2.toL2
    simp only [ContinuousLinearEquiv.symm_apply_apply, graphH1]
  have hmass_eq : ‖h01HilbertGlobalValue Ω hΩ.measurableSet W₀‖ ^ 2 =
      ∫ x, φ.1 x ^ 2 := by
    rw [hvalue, (lpExtendByZero volume 2 Ω hΩ.measurableSet).norm_map φ.2.toL2]
    exact FiniteAreaCore1.integral_sq φ.2
  have hpos : 0 < ‖h01HilbertGlobalValue Ω hΩ.measurableSet W₀‖ := by
    nlinarith [norm_nonneg (h01HilbertGlobalValue Ω hΩ.measurableSet W₀)]
  refine ⟨‖h01HilbertGlobalValue Ω hΩ.measurableSet W₀‖⁻¹ • W₀, ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

end Buckling

end

end
