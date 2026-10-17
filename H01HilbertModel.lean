module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.Core1
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# A Hilbert model of the original H01 graph closure

SOURCE_DRAFT (2026-10-17): isolated; native verification is recorded separately.
The definitions H01, graphH1, energy0, and energy1 are the original ones.
This file proves that the actual graph range is a linear subspace and hence
that its actual closure is a closed subspace. A continuous linear change of
coordinates identifies the product with three L2 components equipped with
their Hilbert norm. No domain regularity, boundedness, finite-area assumption,
compact embedding, eigenfunction, or rigidity hypothesis is introduced.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology

namespace Buckling

lemma IsTestFn.add {Ω : Set Plane} {φ ψ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) (hψ : IsTestFn Ω ψ) : IsTestFn Ω (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, ?_⟩
  exact (tsupport_add φ ψ).trans (union_subset hφ.2.2 hψ.2.2)

lemma IsTestFn.const_smul {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) (c : ℝ) : IsTestFn Ω (c • φ) := by
  refine ⟨hφ.1.const_smul c, ?_, ?_⟩
  · exact hφ.2.1.comp_left (g := fun t : ℝ => c • t) (by simp)
  · exact (tsupport_smul_subset_right (fun _ : Plane => c) φ).trans hφ.2.2

lemma IsTestFn.zero (Ω : Set Plane) : IsTestFn Ω (0 : Plane → ℝ) := by
  refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
  simp

lemma pderiv_add_test {Ω : Set Plane} {φ ψ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) (hψ : IsTestFn Ω ψ) (i : Fin 2) :
    pderiv i (φ + ψ) = pderiv i φ + pderiv i ψ := by
  funext x
  simp only [pderiv, fderiv_add (hφ.1.differentiable (by simp) x)
    (hψ.1.differentiable (by simp) x), ContinuousLinearMap.add_apply, Pi.add_apply]

lemma pderiv_const_smul_test {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) (c : ℝ) (i : Fin 2) :
    pderiv i (c • φ) = c • pderiv i φ := by
  funext x
  simp only [pderiv, fderiv_const_smul (hφ.1.differentiable (by simp) x) c,
    ContinuousLinearMap.smul_apply, Pi.smul_apply]

lemma graphH1_add {Ω : Set Plane} (φ ψ : {φ // IsTestFn Ω φ}) :
    graphH1 ⟨φ.1 + ψ.1, φ.2.add ψ.2⟩ = graphH1 φ + graphH1 ψ := by
  apply Prod.ext
  · exact MemLp.toLp_add φ.2.memLp ψ.2.memLp
  · funext i
    change ((φ.2.add ψ.2).pderiv i).memLp.toLp _ =
      (φ.2.pderiv i).memLp.toLp _ + (ψ.2.pderiv i).memLp.toLp _
    rw [← MemLp.toLp_add (φ.2.pderiv i).memLp (ψ.2.pderiv i).memLp]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (pderiv_add_test φ.2 ψ.2 i))

lemma graphH1_const_smul {Ω : Set Plane} (c : ℝ) (φ : {φ // IsTestFn Ω φ}) :
    graphH1 ⟨c • φ.1, φ.2.const_smul c⟩ = c • graphH1 φ := by
  apply Prod.ext
  · exact MemLp.toLp_const_smul c φ.2.memLp
  · funext i
    change ((φ.2.const_smul c).pderiv i).memLp.toLp _ =
      c • (φ.2.pderiv i).memLp.toLp _
    rw [← MemLp.toLp_const_smul c (φ.2.pderiv i).memLp]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (congrFun (pderiv_const_smul_test φ.2 c i))

/-- The range is exactly the original test-function graph, without a span. -/
def h01GraphSubmodule (Ω : Set Plane) : Submodule ℝ (L2 Ω × (Fin 2 → L2 Ω)) where
  carrier := Set.range (graphH1 (Ω := Ω))
  zero_mem' := by
    refine ⟨⟨0 • (0 : Plane → ℝ), (IsTestFn.zero Ω).const_smul 0⟩, ?_⟩
    exact (graphH1_const_smul (Ω := Ω) 0 ⟨0, IsTestFn.zero Ω⟩).trans (zero_smul ℝ _)
  add_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨ψ, rfl⟩
    exact ⟨⟨φ.1 + ψ.1, φ.2.add ψ.2⟩, graphH1_add φ ψ⟩
  smul_mem' := by
    rintro c _ ⟨φ, rfl⟩
    exact ⟨⟨c • φ.1, φ.2.const_smul c⟩, graphH1_const_smul c φ⟩

def h01ClosedSubmodule (Ω : Set Plane) : Submodule ℝ (L2 Ω × (Fin 2 → L2 Ω)) :=
  (h01GraphSubmodule Ω).topologicalClosure

@[simp] lemma coe_h01ClosedSubmodule (Ω : Set Plane) :
    (h01ClosedSubmodule Ω : Set (L2 Ω × (Fin 2 → L2 Ω))) = H01 Ω := rfl

lemma isClosed_H01 (Ω : Set Plane) : IsClosed (H01 Ω) := isClosed_closure

lemma convex_H01 (Ω : Set Plane) : Convex ℝ (H01 Ω) :=
  (h01ClosedSubmodule Ω).convex

/-- The Hilbert norm uses the sum of the squares of all three L2 norms. -/
abbrev H1HilbertAmbient (Ω : Set Plane) := PiLp 2 (fun _ : Fin 3 => L2 Ω)

/-- Only the finite-product norm changes; all three actual L2 data are retained. -/
def h1DataToHilbert (Ω : Set Plane) :
    (L2 Ω × (Fin 2 → L2 Ω)) ≃L[ℝ] H1HilbertAmbient Ω :=
  (Fin.consEquivL ℝ (fun _ : Fin 3 => L2 Ω)).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => L2 Ω)).symm

@[simp] lemma h1DataToHilbert_apply (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) :
    h1DataToHilbert Ω v = WithLp.toLp 2 (Fin.cons v.1 v.2) := rfl

lemma norm_h1DataToHilbert_sq (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) :
    ‖h1DataToHilbert Ω v‖ ^ 2 = energy0 v + energy1 v := by
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Fin 3, ‖(Fin.cons v.1 v.2 : Fin 3 → L2 Ω) i‖ ^ 2) =
    energy0 v + energy1 v
  rw [Fin.sum_univ_succ]
  rfl

/-- The image of the actual H01, not a separately postulated Sobolev space. -/
def h01HilbertSubmodule (Ω : Set Plane) : Submodule ℝ (H1HilbertAmbient Ω) :=
  (h01ClosedSubmodule Ω).map (h1DataToHilbert Ω).toLinearMap

lemma coe_h01HilbertSubmodule (Ω : Set Plane) :
    (h01HilbertSubmodule Ω : Set (H1HilbertAmbient Ω)) = h1DataToHilbert Ω '' H01 Ω := rfl

lemma isClosed_h01HilbertSubmodule (Ω : Set Plane) :
    IsClosed (h01HilbertSubmodule Ω : Set (H1HilbertAmbient Ω)) := by
  rw [coe_h01HilbertSubmodule, (h1DataToHilbert Ω).isClosed_image]
  exact isClosed_H01 Ω

instance (Ω : Set Plane) : CompleteSpace (h01HilbertSubmodule Ω) :=
  (isClosed_h01HilbertSubmodule Ω).completeSpace_coe

@[simp] lemma h1DataToHilbert_mem_iff (Ω : Set Plane) (v : L2 Ω × (Fin 2 → L2 Ω)) :
    h1DataToHilbert Ω v ∈ h01HilbertSubmodule Ω ↔ v ∈ H01 Ω := by
  change h1DataToHilbert Ω v ∈ h1DataToHilbert Ω '' H01 Ω ↔ _
  exact (h1DataToHilbert Ω).injective.mem_set_image

end Buckling

end

end
