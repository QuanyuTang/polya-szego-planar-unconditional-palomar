module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.Core1
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Connected.LocallyConnected

/-!
# Cutting original test functions to a relatively closed open piece

SOURCE_DRAFT: not registered or native checked.  The set `C` is open in
the plane and relatively closed in the original domain in the explicit
form `closure C ∩ Ω ⊆ C`.  No boundary regularity or finiteness assumption
is used.  The indicator cutoff is genuinely smooth at boundary points,
because every original test function vanishes in a neighbourhood there.
This file only produces test functions and their actual derivatives;
it does not assume or claim an H01 projection or spectral rigidity.
-/

@[expose] public section

noncomputable section

open Set Filter Topology

namespace Buckling
namespace ComponentCutoff

lemma connectedComponentIn_relativeClosure {Ω : Set Plane} {x : Plane}
    (hx : x ∈ Ω) : closure (connectedComponentIn Ω x) ∩ Ω ⊆
      connectedComponentIn Ω x := by
  rintro y ⟨hycl, hyΩ⟩
  have hclosed : IsClosed (connectedComponent (⟨x, hx⟩ : Ω)) :=
    isClosed_connectedComponent
  have hy : (⟨y, hyΩ⟩ : Ω) ∈ connectedComponent (⟨x, hx⟩ : Ω) := by
    apply (IsInducing.subtypeVal.isClosed_iff'.mp hclosed) ⟨y, hyΩ⟩
    simpa only [← connectedComponentIn_eq_image hx] using hycl
  rw [connectedComponentIn_eq_image hx]
  exact ⟨⟨y, hyΩ⟩, hy, rfl⟩

lemma isOpen_sdiff_of_relativeClosure {Ω C : Set Plane} (hΩ : IsOpen Ω)
    (hrel : closure C ∩ Ω ⊆ C) : IsOpen (Ω \ C) := by
  have heq : Ω \ C = Ω ∩ (closure C)ᶜ := by
    ext x
    constructor
    · rintro ⟨hxΩ, hxC⟩
      exact ⟨hxΩ, fun hxcl => hxC (hrel ⟨hxcl, hxΩ⟩)⟩
    · rintro ⟨hxΩ, hxcl⟩
      exact ⟨hxΩ, fun hxC => hxcl (subset_closure hxC)⟩
  rw [heq]
  exact hΩ.inter isClosed_closure.isOpen_compl

lemma indicator_eventuallyEq_of_mem {C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) {x : Plane} (hx : x ∈ C) :
    C.indicator φ =ᶠ[𝓝 x] φ := by
  filter_upwards [hC.mem_nhds hx] with y hy
  exact Set.indicator_of_mem hy φ

lemma indicator_eventuallyEq_zero_of_notMem {Ω C : Set Plane}
    {φ : Plane → ℝ} (hrel : closure C ∩ Ω ⊆ C)
    (hφ : IsTestFn Ω φ) {x : Plane} (hx : x ∉ C) :
    C.indicator φ =ᶠ[𝓝 x] (0 : Plane → ℝ) := by
  by_cases hxcl : x ∈ closure C
  · have hxΩ : x ∉ Ω := fun h => hx (hrel ⟨hxcl, h⟩)
    have hxφ : x ∉ tsupport φ := fun h => hxΩ (hφ.2.2 h)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxφ] with y hy
    by_cases hyC : y ∈ C
    · simpa only [Set.indicator_of_mem hyC, Pi.zero_apply] using hy
    · simp only [Set.indicator_of_notMem hyC, Pi.zero_apply]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl] with y hy
    have hyC : y ∉ C := fun h => hy (subset_closure h)
    simp only [Set.indicator_of_notMem hyC, Pi.zero_apply]

lemma contDiff_indicator {Ω C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C)
    (hφ : IsTestFn Ω φ) :
    ContDiff ℝ (⊤ : ℕ∞) (C.indicator φ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ C
  · exact hφ.1.contDiffAt.congr_of_eventuallyEq
      (indicator_eventuallyEq_of_mem hC hx)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (indicator_eventuallyEq_zero_of_notMem hrel hφ hx)

lemma tsupport_indicator_subset {Ω C : Set Plane} {φ : Plane → ℝ}
    (hrel : closure C ∩ Ω ⊆ C) (hφ : IsTestFn Ω φ) :
    tsupport (C.indicator φ) ⊆ C := by
  have hs : Function.support (C.indicator φ) ⊆ C ∩ Function.support φ := by
    rw [Set.support_indicator]
  have hcl : tsupport (C.indicator φ) ⊆ closure C :=
    closure_mono (fun _ hx => (hs hx).1)
  have hφcl : tsupport (C.indicator φ) ⊆ tsupport φ :=
    closure_mono (fun _ hx => (hs hx).2)
  intro x hx
  exact hrel ⟨hcl hx, hφ.2.2 (hφcl hx)⟩

lemma isTestFn_indicator {Ω C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C)
    (hφ : IsTestFn Ω φ) : IsTestFn C (C.indicator φ) := by
  refine ⟨contDiff_indicator hC hrel hφ, ?_,
    tsupport_indicator_subset hrel hφ⟩
  apply hφ.2.1.of_isClosed_subset (isClosed_tsupport _)
  apply closure_mono
  intro x hx
  rw [Set.support_indicator] at hx
  exact hx.2

lemma isTestFn_indicator_original {Ω C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C)
    (hCΩ : C ⊆ Ω) (hφ : IsTestFn Ω φ) :
    IsTestFn Ω (C.indicator φ) := by
  obtain ⟨hsmooth, hcompact, hsupp⟩ := isTestFn_indicator hC hrel hφ
  exact ⟨hsmooth, hcompact, hsupp.trans hCΩ⟩

lemma fderiv_indicator {Ω C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C)
    (hφ : IsTestFn Ω φ) (x : Plane) :
    fderiv ℝ (C.indicator φ) x = C.indicator (fderiv ℝ φ) x := by
  by_cases hx : x ∈ C
  · rw [Set.indicator_of_mem hx]
    exact (indicator_eventuallyEq_of_mem hC hx).fderiv_eq
  · rw [Set.indicator_of_notMem hx]
    exact (indicator_eventuallyEq_zero_of_notMem hrel hφ hx).fderiv_eq.trans
      (fderiv_const_apply (0 : ℝ))

lemma pderiv_indicator {Ω C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C)
    (hφ : IsTestFn Ω φ) (i : Fin 2) :
    pderiv i (C.indicator φ) = C.indicator (pderiv i φ) := by
  funext x
  rw [pderiv, fderiv_indicator hC hrel hφ]
  by_cases hx : x ∈ C
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    rfl

end ComponentCutoff
end Buckling

end

end
