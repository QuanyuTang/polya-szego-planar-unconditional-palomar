module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01ComponentTestCutoff
public import H01HilbertModel
public import EllipticPdes.Analysis.LpExtendByZero
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.Ring

/-!
# Projection to an open, relatively closed piece in the original H01

SOURCE_DRAFT: not registered or native checked. The projection below keeps
the original restricted measure and applies its actual indicator to each
of the three original L2 coordinates. Test cutoff and continuity produce
membership in the original H01 graph closure. Orthogonality gives the
actual mass and gradient energy decomposition. No minimizer, component
restriction principle, or extra domain regularity is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace Buckling
namespace ComponentCutoff

def l2Projection (Ω C : Set Plane) (hC : MeasurableSet C) :
    L2 Ω →L[ℝ] L2 Ω :=
  (lpExtendByZero (volume.restrict Ω) 2 C hC).toContinuousLinearMap.comp
    (LpToLpRestrictCLM Plane ℝ ℝ (volume.restrict Ω) 2 C)

lemma coeFn_l2Projection (Ω C : Set Plane) (hC : MeasurableSet C) (f : L2 Ω) :
    (l2Projection Ω C hC f : Plane → ℝ) =ᵐ[volume.restrict Ω]
      C.indicator (f : Plane → ℝ) := by
  have hr : ∀ᵐ x ∂(volume.restrict Ω), x ∈ C →
      (LpToLpRestrictCLM Plane ℝ ℝ (volume.restrict Ω) 2 C f : Plane → ℝ) x = f x :=
    (ae_restrict_iff' hC).mp (LpToLpRestrictCLM_coeFn ℝ C f)
  filter_upwards [coeFn_lpExtendByZero hC
    (LpToLpRestrictCLM Plane ℝ ℝ (volume.restrict Ω) 2 C f), hr] with x hx hrx
  change (l2Projection Ω C hC f : Plane → ℝ) x = C.indicator (f : Plane → ℝ) x
  change (lpExtendByZero (volume.restrict Ω) 2 C hC
    (LpToLpRestrictCLM Plane ℝ ℝ (volume.restrict Ω) 2 C f) : Plane → ℝ) x = _
  rw [hx]
  by_cases hxc : x ∈ C
  · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxc, hrx hxc]
  · rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxc]

lemma norm_l2Projection_le (Ω C : Set Plane) (hC : MeasurableSet C) (f : L2 Ω) :
    ‖l2Projection Ω C hC f‖ ≤ ‖f‖ := by
  change ‖lpExtendByZero (volume.restrict Ω) 2 C hC
    (LpToLpRestrictCLM Plane ℝ ℝ (volume.restrict Ω) 2 C f)‖ ≤ ‖f‖
  rw [(lpExtendByZero (volume.restrict Ω) 2 C hC).norm_map]
  exact norm_Lp_toLp_restrict_le C f

def dataProjection (Ω C : Set Plane) (hC : MeasurableSet C)
    (v : L2 Ω × (Fin 2 → L2 Ω)) : L2 Ω × (Fin 2 → L2 Ω) :=
  (l2Projection Ω C hC v.1, fun i => l2Projection Ω C hC (v.2 i))

lemma continuous_dataProjection (Ω C : Set Plane) (hC : MeasurableSet C) :
    Continuous (dataProjection Ω C hC) := by
  exact ((l2Projection Ω C hC).continuous.comp continuous_fst).prodMk
    (continuous_pi fun i => (l2Projection Ω C hC).continuous.comp
      ((continuous_apply i).comp continuous_snd))

lemma l2Projection_toL2 {Ω C : Set Plane} {φ : Plane → ℝ}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    (hφ : IsTestFn Ω φ) :
    l2Projection Ω C hC.measurableSet hφ.toL2 =
      (isTestFn_indicator_original hC hrel hCΩ hφ).toL2 := by
  apply Lp.ext
  filter_upwards [coeFn_l2Projection Ω C hC.measurableSet hφ.toL2,
    hφ.memLp.coeFn_toLp,
    (isTestFn_indicator_original hC hrel hCΩ hφ).memLp.coeFn_toLp] with x hp hf hg
  change (hφ.toL2 : Plane → ℝ) x = φ x at hf
  change ((isTestFn_indicator_original hC hrel hCΩ hφ).toL2 : Plane → ℝ) x =
    C.indicator φ x at hg
  rw [hp, hg]
  by_cases hxc : x ∈ C
  · rw [Set.indicator_of_mem hxc, Set.indicator_of_mem hxc, hf]
  · rw [Set.indicator_of_notMem hxc, Set.indicator_of_notMem hxc]

lemma dataProjection_graphH1 {Ω C : Set Plane}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    (φ : {φ // IsTestFn Ω φ}) :
    dataProjection Ω C hC.measurableSet (graphH1 φ) =
      graphH1 ⟨C.indicator φ.1, isTestFn_indicator_original hC hrel hCΩ φ.2⟩ := by
  apply Prod.ext
  · exact l2Projection_toL2 hC hrel hCΩ φ.2
  · funext i
    change l2Projection Ω C hC.measurableSet (φ.2.pderiv i).toL2 =
      ((isTestFn_indicator_original hC hrel hCΩ φ.2).pderiv i).toL2
    rw [l2Projection_toL2 hC hrel hCΩ (φ.2.pderiv i)]
    apply MemLp.toLp_congr
    exact Eventually.of_forall
      (fun x => (congrFun (pderiv_indicator hC hrel φ.2 i) x).symm)

lemma dataProjection_mem_H01 {Ω C : Set Plane}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    dataProjection Ω C hC.measurableSet v ∈ H01 Ω := by
  have hclosed : IsClosed ((dataProjection Ω C hC.measurableSet) ⁻¹' H01 Ω) :=
    (isClosed_H01 Ω).preimage (continuous_dataProjection Ω C hC.measurableSet)
  apply closure_minimal (s := Set.range (graphH1 (Ω := Ω))) ?_ hclosed hv
  rintro _ ⟨φ, rfl⟩
  change dataProjection Ω C hC.measurableSet (graphH1 φ) ∈ H01 Ω
  rw [dataProjection_graphH1 hC hrel hCΩ φ]
  exact subset_closure ⟨_, rfl⟩

lemma sub_dataProjection_mem_H01 {Ω C : Set Plane}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    v - dataProjection Ω C hC.measurableSet v ∈ H01 Ω :=
  (h01ClosedSubmodule Ω).sub_mem hv (dataProjection_mem_H01 hC hrel hCΩ hv)

lemma inner_l2Projection_sub_eq_zero (Ω C : Set Plane) (hC : MeasurableSet C)
    (f : L2 Ω) : ⟪l2Projection Ω C hC f, f - l2Projection Ω C hC f⟫_ℝ = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [coeFn_l2Projection Ω C hC f,
    Lp.coeFn_sub f (l2Projection Ω C hC f)] with x hp hs
  rw [hs, Pi.sub_apply, hp, RCLike.inner_apply, conj_trivial]
  by_cases hxc : x ∈ C
  · simp only [Set.indicator_of_mem hxc, sub_self, zero_mul, Pi.zero_apply]
  · simp only [Set.indicator_of_notMem hxc, mul_zero, Pi.zero_apply]

lemma norm_sq_l2Projection_decomposition (Ω C : Set Plane) (hC : MeasurableSet C)
    (f : L2 Ω) : ‖f‖ ^ 2 = ‖l2Projection Ω C hC f‖ ^ 2 +
      ‖f - l2Projection Ω C hC f‖ ^ 2 := by
  have hsum : l2Projection Ω C hC f + (f - l2Projection Ω C hC f) = f := by abel
  simpa only [hsum, pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (l2Projection Ω C hC f) (f - l2Projection Ω C hC f)
    (inner_l2Projection_sub_eq_zero Ω C hC f)

lemma energy0_dataProjection_decomposition (Ω C : Set Plane) (hC : MeasurableSet C)
    (v : L2 Ω × (Fin 2 → L2 Ω)) :
    energy0 v = energy0 (dataProjection Ω C hC v) +
      energy0 (v - dataProjection Ω C hC v) :=
  norm_sq_l2Projection_decomposition Ω C hC v.1

lemma energy1_dataProjection_decomposition (Ω C : Set Plane) (hC : MeasurableSet C)
    (v : L2 Ω × (Fin 2 → L2 Ω)) :
    energy1 v = energy1 (dataProjection Ω C hC v) +
      energy1 (v - dataProjection Ω C hC v) := by
  change (∑ i, ‖v.2 i‖ ^ 2) =
    (∑ i, ‖l2Projection Ω C hC (v.2 i)‖ ^ 2) +
    ∑ i, ‖v.2 i - l2Projection Ω C hC (v.2 i)‖ ^ 2
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => norm_sq_l2Projection_decomposition Ω C hC (v.2 i)

/-- A global sharp energy inequality and equality for the original tuple
force equality on both actual orthogonal pieces. This is only an algebraic
consumer of the global inequality; no component PDE or restriction to a
different L2 measure is assumed. Zero-mass pieces are permitted. -/
lemma energy1_dataProjection_eq_of_global_minimality {Ω C : Set Plane}
    (hC : IsOpen C) (hrel : closure C ∩ Ω ⊆ C) (hCΩ : C ⊆ Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) {eigenvalue : ℝ}
    (hmin : ∀ w ∈ H01 Ω, eigenvalue * energy0 w ≤ energy1 w)
    (heq : energy1 v = eigenvalue * energy0 v) :
    energy1 (dataProjection Ω C hC.measurableSet v) =
        eigenvalue * energy0 (dataProjection Ω C hC.measurableSet v) ∧
      energy1 (v - dataProjection Ω C hC.measurableSet v) =
        eigenvalue * energy0 (v - dataProjection Ω C hC.measurableSet v) := by
  have hp := hmin _ (dataProjection_mem_H01 hC hrel hCΩ hv)
  have hq := hmin _ (sub_dataProjection_mem_H01 hC hrel hCΩ hv)
  have h0 := energy0_dataProjection_decomposition Ω C hC.measurableSet v
  have h1 := energy1_dataProjection_decomposition Ω C hC.measurableSet v
  have hsum :
      energy1 (dataProjection Ω C hC.measurableSet v) +
          energy1 (v - dataProjection Ω C hC.measurableSet v) =
        eigenvalue * energy0 (dataProjection Ω C hC.measurableSet v) +
          eigenvalue * energy0 (v - dataProjection Ω C hC.measurableSet v) := by
    rw [← h1, heq, h0, mul_add]
  constructor <;> linarith

end ComponentCutoff
end Buckling

end

end
