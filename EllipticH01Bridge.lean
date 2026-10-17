module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01HilbertModel
public import EllipticPdes.Sobolev.Basic

/-!
# Identifying the original H01 with the EllipticPDE graph closure

SOURCE_DRAFT, Lean 4.35-rc3 dependency experiment; NOT compiled.
This file must not be sent to the 4.28 compiler. The pinned EllipticPDE
source is ec784093f30308ef770ff855ce624725adf6f870, lean/ subdirectory.

The ambient restricted L2 spaces and directional derivatives are the same.
Only a finite-product coordinate change is used. Equality of the actual
closed submodules is proved using their actual smooth graphs, so no
compactness, Sobolev identification, or minimizer is assumed.
-/

@[expose] public section

noncomputable section

open Set Topology

namespace Buckling

lemma isTestFn_iff_elliptic {Ω : Set Plane} {φ : Plane → ℝ} :
    IsTestFn Ω φ ↔ EllipticPdes.Sobolev.IsTestFn Ω φ := Iff.rfl

lemma h1DataToHilbert_graph_eq_elliptic {Ω : Set Plane}
    (φ : {φ // IsTestFn Ω φ}) :
    h1DataToHilbert Ω (graphH1 φ) =
      (show EllipticPdes.Sobolev.IsTestFn Ω φ.1 from φ.2).testGraph := rfl

lemma image_graphH1_eq_elliptic_testGraphSet (Ω : Set Plane) :
    h1DataToHilbert Ω '' Set.range (graphH1 (Ω := Ω)) =
      EllipticPdes.Sobolev.testGraphSet Ω := by
  ext w
  constructor
  · rintro ⟨v, ⟨φ, rfl⟩, rfl⟩
    exact ⟨φ.1, φ.2, h1DataToHilbert_graph_eq_elliptic φ⟩
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨graphH1 ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩, ?_⟩
    exact h1DataToHilbert_graph_eq_elliptic ⟨φ, hφ⟩

/-- Both sides are the closure of the same genuine test-function graphs. -/
theorem h01HilbertSubmodule_eq_elliptic (Ω : Set Plane) :
    h01HilbertSubmodule Ω = EllipticPdes.Sobolev.H01 Ω := by
  apply SetLike.coe_injective
  rw [coe_h01HilbertSubmodule, EllipticPdes.Sobolev.coe_H01]
  change h1DataToHilbert Ω '' closure (Set.range (graphH1 (Ω := Ω))) = _
  rw [(h1DataToHilbert Ω).image_closure,
    image_graphH1_eq_elliptic_testGraphSet]

/-- The ambient identity restricts to the newly proved equal subspaces. -/
def toEllipticH01 (Ω : Set Plane) :
    h01HilbertSubmodule Ω →L[ℝ] EllipticPdes.Sobolev.H01 Ω :=
  (h01HilbertSubmodule Ω).subtypeL.codRestrict (EllipticPdes.Sobolev.H01 Ω)
    (fun v => by rw [← h01HilbertSubmodule_eq_elliptic]; exact v.2)

@[simp] lemma coe_toEllipticH01 (Ω : Set Plane) (v : h01HilbertSubmodule Ω) :
    (toEllipticH01 Ω v : H1HilbertAmbient Ω) = (v : H1HilbertAmbient Ω) := rfl

@[simp] lemma norm_toEllipticH01 (Ω : Set Plane) (v : h01HilbertSubmodule Ω) :
    ‖toEllipticH01 Ω v‖ = ‖v‖ := rfl

/-- The value coordinate is exactly the original restricted L2 function. -/
lemma value_toEllipticH01_original {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    (toEllipticH01 Ω ⟨h1DataToHilbert Ω v,
      (h1DataToHilbert_mem_iff Ω v).mpr hv⟩).1 0 = v.1 := rfl

end Buckling

end

end
