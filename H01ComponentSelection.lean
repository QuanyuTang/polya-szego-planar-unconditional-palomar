module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01ComponentRestriction
public import Mathlib.Topology.Bases

/-!
# A nonzero mass lies in some open connected component

SOURCE_DRAFT: not registered or native checked. A countable subcover of the
actual open connected components suffices; no quotient or finite-component
assumption is used. The selected restriction has the actual original H01
membership and inherits sharp global energy equality by orthogonal splitting.
This file does not assert Faber-Krahn equality rigidity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Buckling
namespace ComponentCutoff

lemma iUnion_connectedComponents (Ω : Set Plane) :
    (⋃ x : Ω, connectedComponentIn Ω x.1) = Ω := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
    exact connectedComponentIn_subset Ω x.1 hx
  · intro hy
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, mem_connectedComponentIn hy⟩

lemma value_eq_zero_of_componentRestrictions_eq_zero {Ω : Set Plane}
    (hΩ : IsOpen Ω) (f : L2 Ω)
    (hzero : ∀ x ∈ Ω,
      l2Restriction Ω (connectedComponentIn Ω x) hΩ.measurableSet f = 0) :
    f = 0 := by
  classical
  let C : Ω → Set Plane := fun x => connectedComponentIn Ω x.1
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    C (fun _ => hΩ.connectedComponentIn)
  letI : Countable T := hT.to_subtype
  have hi : ∀ i : T, ∀ᵐ y ∂(volume : Measure Plane), y ∈ C i.1 → f y = 0 := by
    intro i
    have hC : IsOpen (C i.1) := hΩ.connectedComponentIn
    have hr := coeFn_l2Restriction Ω (C i.1) hΩ.measurableSet hC.measurableSet
      (connectedComponentIn_subset Ω i.1.1) f
    have hz : (l2Restriction Ω (C i.1) hΩ.measurableSet f : Plane → ℝ)
        =ᵐ[volume.restrict (C i.1)] (0 : Plane → ℝ) := by
      rw [show l2Restriction Ω (C i.1) hΩ.measurableSet f = 0 from hzero i.1.1 i.1.2]
      exact Lp.coeFn_zero ℝ 2 (volume.restrict (C i.1))
    exact (ae_restrict_iff' hC.measurableSet).mp (hr.symm.trans hz)
  have hall : ∀ᵐ y ∂(volume : Measure Plane), ∀ i : T, y ∈ C i.1 → f y = 0 :=
    ae_all_iff.mpr hi
  have hΩzero : ∀ᵐ y ∂(volume : Measure Plane), y ∈ Ω → f y = 0 := by
    filter_upwards [hall] with y hy hyΩ
    have hyU : y ∈ ⋃ i ∈ T, C i := by
      rw [hTU]
      change y ∈ ⋃ x : Ω, connectedComponentIn Ω x.1
      rw [iUnion_connectedComponents]
      exact hyΩ
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyU
    obtain ⟨hiT, hyi⟩ := Set.mem_iUnion.mp hi
    exact hy ⟨i, hiT⟩ hyi
  apply Lp.ext
  have hf : ∀ᵐ y ∂volume.restrict Ω, f y = 0 :=
    (ae_restrict_iff' hΩ.measurableSet).mpr hΩzero
  filter_upwards [hf, Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with y hy hz
  exact hy.trans hz.symm

theorem exists_component_mass_pos {Ω : Set Plane} (hΩ : IsOpen Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hmass : 0 < energy0 v) :
    ∃ x ∈ Ω, 0 < energy0 (dataRestriction Ω (connectedComponentIn Ω x)
      hΩ.measurableSet v) := by
  classical
  by_contra hnone
  have hz : ∀ x ∈ Ω,
      l2Restriction Ω (connectedComponentIn Ω x) hΩ.measurableSet v.1 = 0 := by
    intro x hx
    have hn : ¬ 0 < energy0 (dataRestriction Ω (connectedComponentIn Ω x)
        hΩ.measurableSet v) := fun h => hnone ⟨x, hx, h⟩
    have he : energy0 (dataRestriction Ω (connectedComponentIn Ω x)
        hΩ.measurableSet v) = 0 := le_antisymm (not_lt.mp hn) (sq_nonneg _)
    have hnorm : ‖l2Restriction Ω (connectedComponentIn Ω x) hΩ.measurableSet v.1‖ = 0 := by
      exact sq_eq_zero_iff.mp he
    exact norm_eq_zero.mp hnorm
  have hf := value_eq_zero_of_componentRestrictions_eq_zero hΩ v.1 hz
  have hmasszero : energy0 v = 0 := by simp only [energy0, hf, norm_zero, zero_pow two_ne_zero]
  exact (ne_of_gt hmass) hmasszero

/-- Every nonzero sharp global minimizer has an actual nonzero restriction
to one connected component, and this restriction has the same sharp ratio.
There is no assumed component restriction or component Euler equation. -/
theorem exists_component_sharp_piece {Ω : Set Plane} (hΩ : IsOpen Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) (hmass : 0 < energy0 v)
    {eigenvalue : ℝ} (hmin : ∀ w ∈ H01 Ω, eigenvalue * energy0 w ≤ energy1 w)
    (heq : energy1 v = eigenvalue * energy0 v) :
    ∃ x ∈ Ω,
      dataRestriction Ω (connectedComponentIn Ω x) hΩ.measurableSet v ∈
        H01 (connectedComponentIn Ω x) ∧
      0 < energy0 (dataRestriction Ω (connectedComponentIn Ω x) hΩ.measurableSet v) ∧
      energy1 (dataRestriction Ω (connectedComponentIn Ω x) hΩ.measurableSet v) =
        eigenvalue * energy0 (dataRestriction Ω (connectedComponentIn Ω x) hΩ.measurableSet v) := by
  obtain ⟨x, hxΩ, hxmass⟩ := exists_component_mass_pos hΩ v hmass
  have hC : IsOpen (connectedComponentIn Ω x) := hΩ.connectedComponentIn
  have hrel := connectedComponentIn_relativeClosure hxΩ
  have hCΩ := connectedComponentIn_subset Ω x
  refine ⟨x, hxΩ, dataRestriction_mem_H01 hΩ.measurableSet hC hrel hCΩ hv, hxmass, ?_⟩
  rw [energy1_dataRestriction_eq_projection Ω _ hΩ.measurableSet hC.measurableSet hCΩ,
    energy0_dataRestriction_eq_projection Ω _ hΩ.measurableSet hC.measurableSet hCΩ]
  exact (energy1_dataProjection_eq_of_global_minimality hC hrel hCΩ hv hmin heq).1

end ComponentCutoff
end Buckling

end

end
