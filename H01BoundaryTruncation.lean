module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import GraphH01ShiftedTruncation
public import H01AbsoluteValue
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Actual boundary truncation in the original H01

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

For an actual original u in H01(Omega), and any nonnegative global smooth
compact obstacle eta, the actual graph lattice producer gives (u-eta)^+ in
graph H01. Subtracting it from the actual graph of u gives min(u,eta).
The true graph/original coordinate changes are proved inverse below, so
the returned original class has both the stated value and the stated
actual graph gradient, rather than just matching energies.

The obstacle need not belong to H01(Omega), and u need not be nonnegative.
The domain is only assumed open; no finite area or boundedness is needed.
No Euler, PDE, weak limit, ideal principle or comparison result is an input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01BoundaryTruncation

open EllipticPdes H01AbsoluteValue

/-- The actual original-to-graph map, followed by its actual inverse,
returns the original tuple itself. -/
lemma fromGraph_toGraph (Ω : Set Plane) (u : L2 Ω × (Fin 2 → L2 Ω))
    (hu : u ∈ H01 Ω) : fromGraph Ω (toGraph Ω u hu : GraphData Ω) = u := by
  simpa only [fromGraph, toGraph, H1Graph.h1Equiv_h01Equiv, toCoordinate] using
    (h1DataToHilbert Ω).symm_apply_apply u

/-- The inverse transport of a genuine graph H01 class returns that same
graph class, including its actual gradient component. -/
lemma toGraph_fromGraph (Ω : Set Plane) (M : GraphData Ω)
    (hM : M ∈ H1Graph.H01 (volume : Measure Plane) Ω) :
    (toGraph Ω (fromGraph Ω M) (fromGraph_mem_H01 Ω hM) : GraphData Ω) = M := by
  apply (H1Graph.h1Equiv Ω).injective
  change H1Graph.h1Equiv Ω
    (H1Graph.h01Equiv Ω
      (toCoordinate Ω (fromGraph Ω M) (fromGraph_mem_H01 Ω hM)) : GraphData Ω) = _
  simpa only [H1Graph.h1Equiv_h01Equiv, toCoordinate, fromGraph] using
    (h1DataToHilbert Ω).apply_symm_apply (H1Graph.h1Equiv Ω M)

lemma sub_positive_part_eq_min (a b : ℝ) : a - max (a - b) 0 = min a b := by
  by_cases h : b ≤ a
  · rw [max_eq_left (sub_nonneg.mpr h), min_eq_right h]
    ring
  · have hab : a ≤ b := le_of_lt (lt_of_not_ge h)
    rw [max_eq_right (sub_nonpos.mpr hab), sub_zero, min_eq_left hab]

/-- The actual original H01 class for min(u,eta), with its actual value
and graph gradient. The latter uses the actual original-to-graph map. -/
theorem exists_min_H01 {Ω : Set Plane} (hΩ : IsOpen Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    {η : Plane → ℝ} (hη : IsTestFn univ η) (hηn : ∀ x, 0 ≤ η x) :
    ∃ m : L2 Ω × (Fin 2 → L2 Ω), ∃ hm : m ∈ H01 Ω,
      ((m.1 : Plane → ℝ) =ᵐ[volume.restrict Ω] fun x => min (u.1 x) (η x)) ∧
      ((H1Graph.gradL (toGraph Ω m hm : GraphData Ω) : Plane → Plane)
        =ᵐ[volume.restrict Ω] fun x =>
          if η x < u.1 x then gradient η x else
            H1Graph.gradL (toGraph Ω u hu : GraphData Ω) x) := by
  let V : GraphData Ω := toGraph Ω u hu
  have hV : V ∈ H1Graph.H01 (volume : Measure Plane) Ω := (toGraph Ω u hu).2
  have hVvalue : H1Graph.fnL V = u.1 := toGraph_fnL Ω u hu
  have hηGraph : η ∈ testFunctions (univ : Set Plane) := hη
  obtain ⟨W, hW, hWvalue, hWgradient⟩ :=
    GraphH01ShiftedTruncation.exists_mem_H01_positive_difference hΩ hV hηGraph hηn
  let M : GraphData Ω := V - W
  have hM : M ∈ H1Graph.H01 (volume : Measure Plane) Ω :=
    (H1Graph.H01 (volume : Measure Plane) Ω).sub_mem hV hW
  have hSubValue : (H1Graph.fnL M : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => H1Graph.fnL V x - H1Graph.fnL W x := by
    simpa only [M, map_sub, Pi.sub_apply] using!
      Lp.coeFn_sub (H1Graph.fnL V) (H1Graph.fnL W)
  have hSubGradient : (H1Graph.gradL M : Plane → Plane) =ᵐ[volume.restrict Ω]
      fun x => H1Graph.gradL V x - H1Graph.gradL W x := by
    simpa only [M, map_sub, Pi.sub_apply] using!
      Lp.coeFn_sub (H1Graph.gradL V) (H1Graph.gradL W)
  have hValue : (H1Graph.fnL M : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => min (u.1 x) (η x) := by
    filter_upwards [hSubValue, hWvalue] with x hx hwx
    rw [hx, hwx, hVvalue]
    exact sub_positive_part_eq_min (u.1 x) (η x)
  have hGradient : (H1Graph.gradL M : Plane → Plane) =ᵐ[volume.restrict Ω]
      fun x => if η x < u.1 x then gradient η x else H1Graph.gradL V x := by
    filter_upwards [hSubGradient, hWgradient] with x hx hwx
    rw [hx, hwx, hVvalue]
    by_cases h : η x < u.1 x
    · simp only [if_pos h]
      abel
    · simp only [if_neg h, sub_zero]
  let m : L2 Ω × (Fin 2 → L2 Ω) := fromGraph Ω M
  have hm : m ∈ H01 Ω := fromGraph_mem_H01 Ω hM
  have hBack : (toGraph Ω m hm : GraphData Ω) = M := toGraph_fromGraph Ω M hM
  refine ⟨m, hm, ?_, ?_⟩
  · simpa only [m, fromGraph_fnL] using hValue
  · simpa only [hBack] using hGradient

/-- If the original input is nonnegative almost everywhere, the actual
truncated value is nonnegative almost everywhere as well. -/
lemma min_value_nonneg_ae {Ω : Set Plane} {u m : L2 Ω × (Fin 2 → L2 Ω)}
    {η : Plane → ℝ} (hηn : ∀ x, 0 ≤ η x)
    (huN : ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ u.1 x)
    (hmValue : (m.1 : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => min (u.1 x) (η x)) :
    ∀ᵐ x ∂(volume.restrict Ω), 0 ≤ m.1 x := by
  filter_upwards [huN, hmValue] with x hu hm
  rw [hm]
  exact le_min hu (hηn x)

end Buckling.H01BoundaryTruncation

end

end
