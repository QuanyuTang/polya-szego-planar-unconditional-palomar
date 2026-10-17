module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Propagating an actual local almost-everywhere dichotomy

SOURCE_DRAFT: not registered or native checked.
In a second countable space with positive measure on nonempty opens,
local alternatives "zero almost everywhere" and "positive almost
everywhere" propagate across an actual preconnected open domain.
Only countably many exceptional null sets are combined. The local
alternative is an input of this purely topological/measure helper;
the PDE producer must prove it separately on actual interior balls.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace Buckling.ConnectedLocalAEDichotomy

variable {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
  [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α}

/-- An arbitrary open union retains a common AE property, by extracting
a countable actual subunion before combining exceptional null sets. -/
theorem ae_on_open_iUnion {ι : Type*} (U : ι → Set α) (hU : ∀ i, IsOpen (U i))
    {p : α → Prop} (hp : ∀ i, ∀ᵐ x ∂μ.restrict (U i), p x) :
    ∀ᵐ x ∂μ.restrict (⋃ i, U i), p x := by
  classical
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U hU
  letI : Countable T := hT.to_subtype
  have hi : ∀ i : T, ∀ᵐ x ∂μ, x ∈ U i.1 → p x :=
    fun i => (ae_restrict_iff' (hU i.1).measurableSet).mp (hp i.1)
  apply (ae_restrict_iff' (isOpen_iUnion hU).measurableSet).mpr
  filter_upwards [ae_all_iff.mpr hi] with x hx hxU
  have hxT : x ∈ ⋃ i ∈ T, U i := by rw [hTU]; exact hxU
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxT
  obtain ⟨hiT, hxi⟩ := mem_iUnion.mp hi
  exact hx ⟨i, hiT⟩ hxi

variable [μ.IsOpenPosMeasure]

/-- A preconnected open domain admits only one of the two local AE
branches. No pointwise regularity of the represented function is used. -/
theorem zero_or_pos_ae_of_local {D : Set α} (hD : IsOpen D)
    (hconn : IsPreconnected D) (w : α → ℝ)
    (hlocal : ∀ x ∈ D, ∃ U : Set α, IsOpen U ∧ U ⊆ D ∧ x ∈ U ∧
      ((∀ᵐ y ∂μ.restrict U, w y = 0) ∨
        (∀ᵐ y ∂μ.restrict U, 0 < w y))) :
    (∀ᵐ x ∂μ.restrict D, w x = 0) ∨
      (∀ᵐ x ∂μ.restrict D, 0 < w x) := by
  classical
  let ZIndex := {U : Set α // IsOpen U ∧ U ⊆ D ∧ ∀ᵐ x ∂μ.restrict U, w x = 0}
  let PIndex := {U : Set α // IsOpen U ∧ U ⊆ D ∧ ∀ᵐ x ∂μ.restrict U, 0 < w x}
  let Z : Set α := ⋃ i : ZIndex, i.1
  let P : Set α := ⋃ i : PIndex, i.1
  have hZ : IsOpen Z := isOpen_iUnion fun i => i.2.1
  have hP : IsOpen P := isOpen_iUnion fun i => i.2.1
  have hZero : ∀ᵐ x ∂μ.restrict Z, w x = 0 :=
    ae_on_open_iUnion (fun i : ZIndex => i.1) (fun i => i.2.1) (fun i => i.2.2.2)
  have hPos : ∀ᵐ x ∂μ.restrict P, 0 < w x :=
    ae_on_open_iUnion (fun i : PIndex => i.1) (fun i => i.2.1) (fun i => i.2.2.2)
  have hDisjoint : Disjoint Z P := by
    apply Set.disjoint_left.mpr
    intro x hxZ hxP
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxZ
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxP
    have hz := (ae_restrict_iff' i.2.1.measurableSet).mp i.2.2.2
    have hp := (ae_restrict_iff' j.2.1.measurableSet).mp j.2.2.2
    have hnull : ∀ᵐ y ∂μ, y ∉ i.1 ∩ j.1 := by
      filter_upwards [hz, hp] with y hyz hyp hy
      have hzy := hyz hy.1
      have hpy := hyp hy.2
      rw [hzy] at hpy
      exact lt_irrefl (0 : ℝ) hpy
    have hm : μ (i.1 ∩ j.1) = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr hnull
    exact ((i.2.1.inter j.2.1).measure_pos μ ⟨x, hxi, hxj⟩).ne' hm
  have hcover : D ⊆ Z ∪ P := by
    intro x hx
    obtain ⟨U, hU, hUD, hxU, hbranch⟩ := hlocal x hx
    rcases hbranch with hz | hp
    · exact Or.inl (mem_iUnion.mpr ⟨⟨U, hU, hUD, hz⟩, hxU⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨U, hU, hUD, hp⟩, hxU⟩)
  rcases IsPreconnected.subset_or_subset hZ hP hDisjoint hcover hconn with hDZ | hDP
  · left
    have hz := (ae_restrict_iff' hZ.measurableSet).mp hZero
    apply (ae_restrict_iff' hD.measurableSet).mpr
    exact hz.mono fun x hx hxD => hx (hDZ hxD)
  · right
    have hp := (ae_restrict_iff' hP.measurableSet).mp hPos
    apply (ae_restrict_iff' hD.measurableSet).mpr
    exact hp.mono fun x hx hxD => hx (hDP hxD)

end Buckling.ConnectedLocalAEDichotomy

end

end
