module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01ComponentSelection
public import H01DirichletEuler
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Basic.ENNReal.Real

/-!
# Equality in a positive Faber--Krahn bound forces actual connectedness

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
This is explicitly an intermediate consumer of the supplied full-domain
Faber--Krahn inequality hFK with a positive real constant k. It does not
claim to have discharged hFK or to prove the final disk rigidity theorem.

The original finite-area Dirichlet minimizer has an actual nonzero sharp
restriction to a connected component. Its actual original Rayleigh
quotient bounds that component's eigenvalue. The supplied inequality
forces this component to have the entire domain's area. The remaining
relatively open set is null and therefore empty, by positivity on opens.

No finite-component, boundedness, boundary regularity, component PDE,
positive eigenfunction, prechosen minimizer or restriction assumption is
introduced. All H01 and eigenvalue objects are the original definitions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.FaberKrahnEqualityConnected

/-- Conditional only on the explicitly supplied genuine global FK lower
bound. The intended final consumer must supply that already proved bound. -/
theorem isConnected_of_faberKrahn_equality {k : ℝ} (hk : 0 < k)
    (hFK : ∀ U : Set Plane, IsOpen U → 0 < volume U → volume U < ⊤ →
      k ≤ (volume U).toReal * dirichletEig U)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k) : IsConnected Ω := by
  have hΩpos : 0 < volume Ω := hΩ.measure_pos volume hne
  have hApos : 0 < (volume Ω).toReal := ENNReal.toReal_pos hΩpos.ne' hfin.ne
  have hEigenPos : 0 < dirichletEig Ω := by
    apply (mul_pos_iff_of_pos_left hApos).mp
    rw [heq]
    exact hk
  obtain ⟨u, hu, hu0, hu1⟩ := exists_H01_dirichletEig_minimizer hΩ hne hfin
  have huMass : 0 < energy0 u := by rw [hu0]; exact zero_lt_one
  have huSharp : energy1 u = dirichletEig Ω * energy0 u := by
    simpa only [hu0, mul_one] using hu1
  have hmin : ∀ w ∈ H01 Ω, dirichletEig Ω * energy0 w ≤ energy1 w :=
    fun w hw => H01DirichletEuler.dirichletEig_mul_energy0_le w hw
  obtain ⟨x, hxΩ, hv, hvMass, hvSharp⟩ :=
    ComponentCutoff.exists_component_sharp_piece hΩ hu huMass hmin huSharp
  let C : Set Plane := connectedComponentIn Ω x
  let v : L2 C × (Fin 2 → L2 C) :=
    ComponentCutoff.dataRestriction Ω C hΩ.measurableSet u
  have hCΩ : C ⊆ Ω := connectedComponentIn_subset Ω x
  have hC : IsOpen C := hΩ.connectedComponentIn
  have hCne : C.Nonempty := ⟨x, mem_connectedComponentIn hxΩ⟩
  have hCpos : 0 < volume C := hC.measure_pos volume hCne
  have hCfin : volume C < ⊤ := lt_of_le_of_lt (measure_mono hCΩ) hfin
  have hv' : v ∈ H01 C := hv
  have hvMass' : 0 < energy0 v := hvMass
  have hvSharp' : energy1 v = dirichletEig Ω * energy0 v := hvSharp
  have hQuotient : energy1 v / energy0 v = dirichletEig Ω :=
    (div_eq_iff hvMass'.ne').mpr hvSharp'
  have hEigenLe : dirichletEig C ≤ dirichletEig Ω :=
    (H01Rayleigh.original_dirichletEig_le v hv' hvMass'.ne').trans_eq hQuotient
  have hFKC := hFK C hC hCpos hCfin
  have hAreaLe : (volume C).toReal ≤ (volume Ω).toReal :=
    ENNReal.toReal_mono hfin.ne (measure_mono hCΩ)
  have hAreaProduct : (volume Ω).toReal * dirichletEig Ω ≤
      (volume C).toReal * dirichletEig Ω := by
    rw [heq]
    exact hFKC.trans (mul_le_mul_of_nonneg_left hEigenLe ENNReal.toReal_nonneg)
  have hAreaGe : (volume Ω).toReal ≤ (volume C).toReal :=
    le_of_mul_le_mul_right hAreaProduct hEigenPos
  have hAreaEq : (volume C).toReal = (volume Ω).toReal :=
    le_antisymm hAreaLe hAreaGe
  have hVolumeEq : volume C = volume Ω :=
    (ENNReal.toReal_eq_toReal_iff' hCfin.ne hfin.ne).mp hAreaEq
  have hRelative : closure C ∩ Ω ⊆ C :=
    ComponentCutoff.connectedComponentIn_relativeClosure hxΩ
  have hRemainderOpen : IsOpen (Ω \ C) :=
    ComponentCutoff.isOpen_sdiff_of_relativeClosure hΩ hRelative
  have hRemainderZero : volume (Ω \ C) = 0 := by
    rw [measure_sdiff hCΩ hC.measurableSet.nullMeasurableSet hCfin.ne,
      hVolumeEq, tsub_self]
  have hRemainderEmpty : Ω \ C = ∅ :=
    (hRemainderOpen.measure_eq_zero_iff volume).mp hRemainderZero
  have hΩC : Ω = C := by
    apply Subset.antisymm ?_ hCΩ
    intro y hyΩ
    by_contra hyC
    have hy : y ∈ Ω \ C := ⟨hyΩ, hyC⟩
    rw [hRemainderEmpty] at hy
    exact hy
  rw [hΩC]
  exact isConnected_connectedComponentIn_iff.mpr hxΩ

end Buckling.FaberKrahnEqualityConnected

end

end
