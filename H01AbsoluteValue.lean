module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EllipticH01Bridge
public import EllipticPdes.Sobolev.GraphEuclidean
public import EllipticPdes.Sobolev.GraphLattice
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith

/-!
# Absolute value in the actual original H01

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The actual graph-space H01 lattice theorem is used twice, on V and -V at
level zero. Their positive parts are added. The resulting value is |v|;
its vector gradient is g on the positive layer, -g on the negative layer,
and zero on the zero layer. Hence its gradient norm is at most the original
one, without needing to prove that the original gradient vanishes there.

The actual GraphEuclidean isometries and the verified original-coordinate
bridge transport this concrete class back to the unchanged original H01.
The value representative is identified almost everywhere, and original E0
and E1 are compared using their actual L2 norms. No finite-area, bounded
domain, minimizer, weak-gradient, or lattice assumption is added.

Only the narrow GraphEuclidean and GraphLattice sources from pinned
EllipticPDE ec784093f30308ef770ff855ce624725adf6f870 are used. The complete
H01Lattice and DivFormEuclidean modules are not imported; no proof body
from either is copied. All transports below are explicit new wrappers.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01AbsoluteValue

open EllipticPdes

abbrev GraphData (Ω : Set Plane) := H1Graph (volume : Measure Plane) Ω

/-- The original class as the actual coordinate H01 subtype. -/
def toCoordinate (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    EllipticPdes.Sobolev.H01 Ω :=
  ⟨h1DataToHilbert Ω v, by
    rw [← h01HilbertSubmodule_eq_elliptic]
    exact (h1DataToHilbert_mem_iff Ω v).mpr hv⟩

/-- The actual original class in the actual graph H01, with no new hypothesis. -/
def toGraph (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    H1Graph.H01 (volume : Measure Plane) Ω :=
  H1Graph.h01Equiv Ω (toCoordinate Ω v hv)

lemma toGraph_fnL (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    H1Graph.fnL (toGraph Ω v hv : GraphData Ω) = v.1 :=
  H1Graph.fnL_h01Equiv Ω (toCoordinate Ω v hv)

lemma toGraph_gradient_sq (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω))
    (hv : v ∈ H01 Ω) :
    ‖H1Graph.gradL (toGraph Ω v hv : GraphData Ω)‖ ^ 2 = energy1 v :=
  H1Graph.norm_gradL_h01Equiv_sq Ω (toCoordinate Ω v hv)

/-- Return an actual graph class to the unchanged original product. -/
def fromGraph (Ω : Set Plane) (W : GraphData Ω) : L2 Ω × (Fin 2 → L2 Ω) :=
  (h1DataToHilbert Ω).symm (H1Graph.h1Equiv Ω W)

lemma fromGraph_mem_H01 (Ω : Set Plane) {W : GraphData Ω}
    (hW : W ∈ H1Graph.H01 (volume : Measure Plane) Ω) : fromGraph Ω W ∈ H01 Ω := by
  apply (h1DataToHilbert_mem_iff Ω (fromGraph Ω W)).mp
  rw [h01HilbertSubmodule_eq_elliptic]
  have hmem := Submodule.mem_map_of_mem
    (f := (H1Graph.h1Equiv Ω).toLinearEquiv.toLinearMap) hW
  rw [H1Graph.map_h1Equiv_H01] at hmem
  simpa [fromGraph] using hmem

lemma fromGraph_fnL (Ω : Set Plane) (W : GraphData Ω) :
    (fromGraph Ω W).1 = H1Graph.fnL W := by
  have h := congrArg (fun U : H1HilbertAmbient Ω => U 0)
    ((h1DataToHilbert Ω).apply_symm_apply (H1Graph.h1Equiv Ω W))
  change (fromGraph Ω W).1 = H1Graph.fnL W at h
  exact h

lemma fromGraph_coordinate (Ω : Set Plane) (W : GraphData Ω) (i : Fin 2) :
    (fromGraph Ω W).2 i = (H1Graph.h1Equiv Ω W) i.succ := by
  have h := congrArg (fun U : H1HilbertAmbient Ω => U i.succ)
    ((h1DataToHilbert Ω).apply_symm_apply (H1Graph.h1Equiv Ω W))
  change (fromGraph Ω W).2 i = (H1Graph.h1Equiv Ω W) i.succ at h
  exact h

lemma fromGraph_energy0 (Ω : Set Plane) (W : GraphData Ω) :
    energy0 (fromGraph Ω W) = ‖H1Graph.fnL W‖ ^ 2 := by
  rw [energy0, fromGraph_fnL]

lemma fromGraph_energy1 (Ω : Set Plane) (W : GraphData Ω) :
    energy1 (fromGraph Ω W) = ‖H1Graph.gradL W‖ ^ 2 := by
  rw [energy1, H1Graph.norm_gradL_sq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fromGraph_coordinate]

/-- The true lattice construction in graph H01. Its gradient formula is
literal, and vanishes on the zero layer regardless of the original gradient. -/
theorem exists_graph_abs {Ω : Set Plane} (hΩ : IsOpen Ω) {V : GraphData Ω}
    (hV : V ∈ H1Graph.H01 (volume : Measure Plane) Ω) :
    ∃ W : GraphData Ω, W ∈ H1Graph.H01 (volume : Measure Plane) Ω ∧
      ((H1Graph.fnL W : Plane → ℝ) =ᵐ[volume.restrict Ω]
        fun x => |H1Graph.fnL V x|) ∧
      ((H1Graph.gradL W : Plane → Plane) =ᵐ[volume.restrict Ω] fun x =>
        (if 0 < H1Graph.fnL V x then H1Graph.gradL V x else 0) +
          (if 0 < -H1Graph.fnL V x then -H1Graph.gradL V x else 0)) ∧
      ‖H1Graph.gradL W‖ ≤ ‖H1Graph.gradL V‖ := by
  obtain ⟨P, hP, hPv, hPg⟩ :=
    H1Graph.exists_mem_H01_posPart_sub_const hΩ hV (k := 0) le_rfl
  obtain ⟨N, hN, hNv, hNg⟩ :=
    H1Graph.exists_mem_H01_posPart_sub_const hΩ
      ((H1Graph.H01 (volume : Measure Plane) Ω).neg_mem hV) (k := 0) le_rfl
  have hvNeg : (H1Graph.fnL (-V) : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => -H1Graph.fnL V x := by
    rw [map_neg]
    filter_upwards [Lp.coeFn_neg (H1Graph.fnL V)] with x hx
    simpa only [Pi.neg_apply] using hx
  have hgNeg : (H1Graph.gradL (-V) : Plane → Plane) =ᵐ[volume.restrict Ω]
      fun x => -H1Graph.gradL V x := by
    rw [map_neg]
    filter_upwards [Lp.coeFn_neg (H1Graph.gradL V)] with x hx
    simpa only [Pi.neg_apply] using hx
  have hAddValue : (H1Graph.fnL (P + N) : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => H1Graph.fnL P x + H1Graph.fnL N x := by
    rw [H1Graph.fnL_add]
    filter_upwards [Lp.coeFn_add (H1Graph.fnL P) (H1Graph.fnL N)] with x hx
    simpa only [Pi.add_apply] using hx
  have hAddGradient : (H1Graph.gradL (P + N) : Plane → Plane) =ᵐ[volume.restrict Ω]
      fun x => H1Graph.gradL P x + H1Graph.gradL N x := by
    rw [H1Graph.gradL_add]
    filter_upwards [Lp.coeFn_add (H1Graph.gradL P) (H1Graph.gradL N)] with x hx
    simpa only [Pi.add_apply] using hx
  have hAbs : (H1Graph.fnL (P + N) : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => |H1Graph.fnL V x| := by
    filter_upwards [hAddValue, hPv, hNv, hvNeg] with x ha hp hn hneg
    rw [ha, hp, hn, hneg]
    simp only [sub_zero]
    by_cases hx : 0 ≤ H1Graph.fnL V x
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero, abs_of_nonneg hx]
    · have hx' : H1Graph.fnL V x ≤ 0 := le_of_lt (lt_of_not_ge hx)
      rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx'), zero_add, abs_of_nonpos hx']
  have hGrad : (H1Graph.gradL (P + N) : Plane → Plane) =ᵐ[volume.restrict Ω] fun x =>
      (if 0 < H1Graph.fnL V x then H1Graph.gradL V x else 0) +
        (if 0 < -H1Graph.fnL V x then -H1Graph.gradL V x else 0) := by
    filter_upwards [hAddGradient, hPg, hNg, hvNeg, hgNeg] with x ha hp hn hv hg
    have hn' : H1Graph.gradL N x =
        if 0 < -H1Graph.fnL V x then -H1Graph.gradL V x else 0 := by
      simpa only [hv, hg] using hn
    exact ha.trans (congrArg₂ (fun a b : Plane => a + b) hp hn')
  refine ⟨P + N, (H1Graph.H01 (volume : Measure Plane) Ω).add_mem hP hN, hAbs, hGrad, ?_⟩
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hGrad] with x hx
  rw [hx]
  by_cases hp : 0 < H1Graph.fnL V x
  · have hn : ¬ 0 < -H1Graph.fnL V x := not_lt_of_ge (neg_nonpos.mpr hp.le)
    simp only [if_pos hp, if_neg hn, add_zero, le_refl]
  · by_cases hn : 0 < -H1Graph.fnL V x
    · simp only [if_neg hp, if_pos hn, zero_add, norm_neg, le_refl]
    · simp only [if_neg hp, if_neg hn, zero_add, norm_zero]
      exact norm_nonneg _

/-- Absolute value preserves the actual original mass and does not increase
the actual original derivative energy on every open domain. -/
theorem exists_abs_H01 {Ω : Set Plane} (hΩ : IsOpen Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    ∃ w : L2 Ω × (Fin 2 → L2 Ω), w ∈ H01 Ω ∧
      ((w.1 : Plane → ℝ) =ᵐ[volume.restrict Ω] fun x => |v.1 x|) ∧
      energy0 w = energy0 v ∧ energy1 w ≤ energy1 v := by
  let V : GraphData Ω := toGraph Ω v hv
  have hV : V ∈ H1Graph.H01 (volume : Measure Plane) Ω := (toGraph Ω v hv).2
  have hVvalue : H1Graph.fnL V = v.1 := toGraph_fnL Ω v hv
  have hVenergy : ‖H1Graph.gradL V‖ ^ 2 = energy1 v := toGraph_gradient_sq Ω v hv
  obtain ⟨W, hW, hAbs, _, hGrad⟩ := exists_graph_abs hΩ hV
  refine ⟨fromGraph Ω W, fromGraph_mem_H01 Ω hW, ?_, ?_, ?_⟩
  · simpa only [fromGraph_fnL, hVvalue] using hAbs
  · calc
      energy0 (fromGraph Ω W) = ‖H1Graph.fnL W‖ ^ 2 := fromGraph_energy0 Ω W
      _ = ‖H1Graph.fnL V‖ ^ 2 := by
        rw [L2.norm_sq_eq_integral_sq, L2.norm_sq_eq_integral_sq]
        apply integral_congr_ae
        filter_upwards [hAbs] with x hx
        rw [hx, sq_abs]
      _ = energy0 v := by simpa only [energy0, hVvalue]
  · calc
      energy1 (fromGraph Ω W) = ‖H1Graph.gradL W‖ ^ 2 := fromGraph_energy1 Ω W
      _ ≤ ‖H1Graph.gradL V‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hGrad
      _ = energy1 v := hVenergy

end Buckling.H01AbsoluteValue

end

end
