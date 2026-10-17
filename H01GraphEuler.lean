module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01AbsoluteValue
public import H01DirichletEuler
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Tactic.Linarith

/-!
# Actual graph transport of the original variational Euler identity

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The original two derivative-coordinate pairings equal the actual vector
gradient pairing after the genuine original-to-graph coordinate map. This
follows from GraphEuclidean inner-product isometry, the three-coordinate
L2 inner product, and cancellation of the actual value pairing. The inverse
map returns every actual graph H01 variation to the original H01.

The original energy equality gives the original Euler identity; the roots
below only transport that theorem, including the actual restricted-L2
representative integrals. All products are genuinely integrable by L2
Holder. No PDE, regularity, compactness or new Euler hypothesis is added.
The transport itself works for every domain; the intended open-domain case
therefore needs no extra premise here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.H01GraphEuler

open EllipticPdes H01AbsoluteValue

lemma h1Equiv_toGraph (Ω : Set Plane) (u : L2 Ω × (Fin 2 → L2 Ω))
    (hu : u ∈ H01 Ω) :
    H1Graph.h1Equiv Ω (toGraph Ω u hu : GraphData Ω) = h1DataToHilbert Ω u :=
  H1Graph.h1Equiv_h01Equiv Ω (toCoordinate Ω u hu)

/-- The actual inverse coordinate map returns the same graph variation. -/
lemma toGraph_fromGraph (Ω : Set Plane) (T : GraphData Ω)
    (hT : T ∈ H1Graph.H01 (volume : Measure Plane) Ω) :
    (toGraph Ω (fromGraph Ω T) (fromGraph_mem_H01 Ω hT) : GraphData Ω) = T := by
  apply (H1Graph.h1Equiv Ω).injective
  rw [h1Equiv_toGraph]
  exact (h1DataToHilbert Ω).apply_symm_apply (H1Graph.h1Equiv Ω T)

/-- The actual original value pairing is precisely the graph value pairing. -/
lemma original_value_inner_eq_graph (Ω : Set Plane)
    (u v : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω) (hv : v ∈ H01 Ω) :
    inner ℝ u.1 v.1 = inner ℝ
      (H1Graph.fnL (toGraph Ω u hu : GraphData Ω))
      (H1Graph.fnL (toGraph Ω v hv : GraphData Ω)) := by
  rw [toGraph_fnL, toGraph_fnL]

/-- The actual original gradient-coordinate pairing equals the actual
vector-gradient pairing; no energy-equivalent replacement is used. -/
lemma original_gradient_inner_eq_graph (Ω : Set Plane)
    (u v : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω) (hv : v ∈ H01 Ω) :
    (∑ i, inner ℝ (u.2 i) (v.2 i)) = inner ℝ
      (H1Graph.gradL (toGraph Ω u hu : GraphData Ω))
      (H1Graph.gradL (toGraph Ω v hv : GraphData Ω)) := by
  have h := (H1Graph.h1Equiv Ω).inner_map_map
    (toGraph Ω u hu : GraphData Ω) (toGraph Ω v hv : GraphData Ω)
  rw [h1Equiv_toGraph, h1Equiv_toGraph, H1Graph.inner_eq] at h
  simp only [h1DataToHilbert_apply, PiLp.inner_apply] at h
  change (∑ j : Fin 3, inner ℝ ((Fin.cons u.1 u.2 : Fin 3 → L2 Ω) j)
    ((Fin.cons v.1 v.2 : Fin 3 → L2 Ω) j)) = _ at h
  rw [Fin.sum_univ_succ] at h
  simp only [Fin.cons_zero, Fin.cons_succ, toGraph_fnL] at h
  linarith

lemma integrable_graph_gradient_pair {Ω : Set Plane} (U T : GraphData Ω) :
    Integrable (fun x => inner ℝ (H1Graph.gradL U x) (H1Graph.gradL T x))
      (volume.restrict Ω) :=
  MeasureTheory.L2.integrable_inner (𝕜 := ℝ) (H1Graph.gradL U) (H1Graph.gradL T)

lemma integrable_graph_value_product {Ω : Set Plane} (U T : GraphData Ω) :
    Integrable (fun x => H1Graph.fnL U x * H1Graph.fnL T x) (volume.restrict Ω) :=
  MeasureTheory.L2.integrable_mul (H1Graph.fnL U) (H1Graph.fnL T)

lemma graph_gradient_inner_eq_integral {Ω : Set Plane} (U T : GraphData Ω) :
    inner ℝ (H1Graph.gradL U) (H1Graph.gradL T) =
      ∫ x in Ω, inner ℝ (H1Graph.gradL U x) (H1Graph.gradL T x) := by
  rw [MeasureTheory.L2.inner_def]

lemma graph_value_inner_eq_integral {Ω : Set Plane} (U T : GraphData Ω) :
    inner ℝ (H1Graph.fnL U) (H1Graph.fnL T) =
      ∫ x in Ω, H1Graph.fnL U x * H1Graph.fnL T x :=
  MeasureTheory.L2.real_inner_eq_integral (H1Graph.fnL U) (H1Graph.fnL T)

/-- The original equality case of the Rayleigh lower bound gives the
actual graph Euler identity against every actual graph H01 variation. -/
theorem graph_inner_euler_of_energy_eq {Ω : Set Plane}
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    (T : GraphData Ω) (hT : T ∈ H1Graph.H01 (volume : Measure Plane) Ω) :
    inner ℝ (H1Graph.gradL (toGraph Ω u hu : GraphData Ω)) (H1Graph.gradL T) =
      dirichletEig Ω * inner ℝ
        (H1Graph.fnL (toGraph Ω u hu : GraphData Ω)) (H1Graph.fnL T) := by
  let t : L2 Ω × (Fin 2 → L2 Ω) := fromGraph Ω T
  have ht : t ∈ H01 Ω := fromGraph_mem_H01 Ω hT
  have hBack : (toGraph Ω t ht : GraphData Ω) = T := toGraph_fromGraph Ω T hT
  have hEuler := H01DirichletEuler.euler_of_energy_eq hu heq t ht
  have hGraph :
      inner ℝ (H1Graph.gradL (toGraph Ω u hu : GraphData Ω))
          (H1Graph.gradL (toGraph Ω t ht : GraphData Ω)) =
        dirichletEig Ω * inner ℝ
          (H1Graph.fnL (toGraph Ω u hu : GraphData Ω))
          (H1Graph.fnL (toGraph Ω t ht : GraphData Ω)) := by
    rw [← original_gradient_inner_eq_graph, toGraph_fnL, toGraph_fnL]
    exact hEuler
  simpa only [hBack] using hGraph

/-- The actual restricted representative integrals of the original Euler
identity. Both integrability obligations have independent producers above. -/
theorem graph_integral_euler_of_energy_eq {Ω : Set Plane}
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hu : u ∈ H01 Ω)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    (T : GraphData Ω) (hT : T ∈ H1Graph.H01 (volume : Measure Plane) Ω) :
    (∫ x in Ω, inner ℝ
      (H1Graph.gradL (toGraph Ω u hu : GraphData Ω) x) (H1Graph.gradL T x)) =
      dirichletEig Ω *
        ∫ x in Ω, H1Graph.fnL (toGraph Ω u hu : GraphData Ω) x * H1Graph.fnL T x := by
  simpa only [graph_gradient_inner_eq_integral, graph_value_inner_eq_integral] using
    graph_inner_euler_of_energy_eq u hu heq T hT

end Buckling.H01GraphEuler

end

end
