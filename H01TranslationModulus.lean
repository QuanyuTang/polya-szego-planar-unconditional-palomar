module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EllipticH01Bridge
public import FiniteAreaTestLpBounds
public import EllipticPdes.Analysis.LpTranslation
public import EllipticPdes.Analysis.Translation
public import EllipticPdes.Analysis.LpExtendByZero

/-!
# Translation control for the original H01

SOURCE_DRAFT, Lean 4.35-rc3 only; NOT compiled.
The external analytic estimate is the actual smooth-function translation
estimate in the pinned EllipticPDE source. Its energy is identified with the
original graphH1 energy. The squared inequality is closed in the original
product topology, so it extends to the original H01 by its defining closure.
No boundedness, finite area, compact embedding, or minimizer is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology Metric
open scoped ENNReal

namespace Buckling

/-- The full-space zero extension of the original value coordinate. -/
def h01RawZeroExtension (Ω : Set Plane) (hΩm : MeasurableSet Ω) :
    (L2 Ω × (Fin 2 → L2 Ω)) →L[ℝ] EucL2 2 :=
  (lpExtendByZero volume 2 Ω hΩm).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ (L2 Ω) (Fin 2 → L2 Ω))

@[simp] lemma h01RawZeroExtension_apply (Ω : Set Plane) (hΩm : MeasurableSet Ω)
    (v : L2 Ω × (Fin 2 → L2 Ω)) :
    h01RawZeroExtension Ω hΩm v = lpExtendByZero volume 2 Ω hΩm v.1 := rfl

/-- The extended original test class has its actual smooth representative
almost everywhere in full Lebesgue measure. -/
lemma h01RawZeroExtension_graph_ae {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (φ : {φ // IsTestFn Ω φ}) :
    (h01RawZeroExtension Ω hΩm (graphH1 φ) : Plane → ℝ) =ᵐ[volume] φ.1 := by
  have hcls : (φ.2.toL2 : Plane → ℝ) =ᵐ[volume.restrict Ω] φ.1 :=
    φ.2.memLp.coeFn_toLp
  have hcls' : ∀ᵐ x ∂volume, x ∈ Ω → (φ.2.toL2 : Plane → ℝ) x = φ.1 x :=
    (ae_restrict_iff' hΩm).mp hcls
  have hext := coeFn_lpExtendByZero hΩm φ.2.toL2
  change (lpExtendByZero volume 2 Ω hΩm φ.2.toL2 : Plane → ℝ) =ᵐ[volume] φ.1
  filter_upwards [hext, hcls'] with x hx hc
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, hc hxΩ]
  · rw [Set.indicator_of_notMem hxΩ,
      FiniteAreaCore1.eq_zero_of_notMem φ.2 hxΩ]

lemma h01RawZeroExtension_graph_translation_sq {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (φ : {φ // IsTestFn Ω φ}) (h : Plane) :
    ‖transL2 h (h01RawZeroExtension Ω hΩm (graphH1 φ)) -
      h01RawZeroExtension Ω hΩm (graphH1 φ)‖ ^ 2 ≤
      ‖h‖ ^ 2 * energy1 (graphH1 φ) := by
  rw [norm_sq_transL2_sub]
  have hae := h01RawZeroExtension_graph_ae hΩm φ
  have hcomp : ∀ᵐ x ∂volume,
      (h01RawZeroExtension Ω hΩm (graphH1 φ) : Plane → ℝ) (x + h) = φ.1 (x + h) :=
    ((measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae).eventually hae
  have heq : (fun x =>
      ((h01RawZeroExtension Ω hΩm (graphH1 φ) : Plane → ℝ) (x + h) -
        h01RawZeroExtension Ω hΩm (graphH1 φ) x) ^ 2) =ᵐ[volume]
      fun x => (φ.1 (x + h) - φ.1 x) ^ 2 := by
    filter_upwards [hcomp, hae] with x hx hy
    rw [hx, hy]
  rw [integral_congr_ae heq, FiniteAreaCore1.energy1_graphH1]
  exact integral_sq_sub_translation_le (φ.2.1.of_le (by simp)) φ.2.2.1 h

/-- The real translation inequality is proved on the original H01 closure.
There is no uniform-translation hypothesis on the domain. -/
theorem h01RawZeroExtension_translation_sq {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω)
    (h : Plane) :
    ‖transL2 h (h01RawZeroExtension Ω hΩm v) -
      h01RawZeroExtension Ω hΩm v‖ ^ 2 ≤ ‖h‖ ^ 2 * energy1 v := by
  have hleft : Continuous (fun w : L2 Ω × (Fin 2 → L2 Ω) =>
      ‖transL2 h (h01RawZeroExtension Ω hΩm w) -
        h01RawZeroExtension Ω hΩm w‖ ^ 2) := by
    exact (((transL2 h).continuous.comp (h01RawZeroExtension Ω hΩm).continuous).fun_sub
      (h01RawZeroExtension Ω hΩm).continuous).norm.fun_pow 2
  have henergy : Continuous (fun w : L2 Ω × (Fin 2 → L2 Ω) => energy1 w) := by
    simp only [energy1, Fin.sum_univ_two]
    fun_prop
  have hclosed : IsClosed {w : L2 Ω × (Fin 2 → L2 Ω) |
      ‖transL2 h (h01RawZeroExtension Ω hΩm w) -
        h01RawZeroExtension Ω hΩm w‖ ^ 2 ≤ ‖h‖ ^ 2 * energy1 w} :=
    isClosed_le hleft (henergy.const_mul (‖h‖ ^ 2))
  apply (closure_minimal (t := {w : L2 Ω × (Fin 2 → L2 Ω) |
    ‖transL2 h (h01RawZeroExtension Ω hΩm w) -
      h01RawZeroExtension Ω hΩm w‖ ^ 2 ≤ ‖h‖ ^ 2 * energy1 w}) ?_ hclosed) hv
  rintro _ ⟨φ, rfl⟩
  exact h01RawZeroExtension_graph_translation_sq hΩm φ h

/-- Original values, in full space, as a continuous linear map on the actual
Hilbert model of the original H01. -/
def h01HilbertFullValue (Ω : Set Plane) (hΩm : MeasurableSet Ω) :
    h01HilbertSubmodule Ω →L[ℝ] EucL2 2 :=
  (h01RawZeroExtension Ω hΩm).comp
    ((h1DataToHilbert Ω).symm.toContinuousLinearMap.comp
      (h01HilbertSubmodule Ω).subtypeL)

lemma h01HilbertFullValue_norm_le {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (u : h01HilbertSubmodule Ω) : ‖h01HilbertFullValue Ω hΩm u‖ ≤ ‖u‖ := by
  let v := (h1DataToHilbert Ω).symm u.1
  have he : energy0 v + energy1 v = ‖u‖ ^ 2 := by
    simpa [v] using (norm_h1DataToHilbert_sq Ω v).symm
  have hg : 0 ≤ energy1 v := Finset.sum_nonneg fun i _ => sq_nonneg ‖v.2 i‖
  have hnorm : ‖h01HilbertFullValue Ω hΩm u‖ = ‖v.1‖ :=
    (lpExtendByZero volume 2 Ω hΩm).norm_map v.1
  rw [hnorm]
  change ‖v.1‖ ^ 2 + energy1 v = ‖u‖ ^ 2 at he
  nlinarith [norm_nonneg v.1, norm_nonneg u]

theorem h01HilbertFullValue_unit_translation {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (u : h01HilbertSubmodule Ω) (hu : ‖u‖ ≤ 1) (h : Plane) :
    ‖transL2 h (h01HilbertFullValue Ω hΩm u) -
      h01HilbertFullValue Ω hΩm u‖ ≤ ‖h‖ := by
  let v := (h1DataToHilbert Ω).symm u.1
  have hv : v ∈ H01 Ω := (h1DataToHilbert_mem_iff Ω v).mp (by
    simpa [v] using u.2)
  have he : energy0 v + energy1 v = ‖u‖ ^ 2 := by
    simpa [v] using (norm_h1DataToHilbert_sq Ω v).symm
  have he0 : 0 ≤ energy0 v := sq_nonneg ‖v.1‖
  have he1 : energy1 v ≤ 1 := by nlinarith [norm_nonneg u]
  have hs := h01RawZeroExtension_translation_sq hΩm v hv h
  change ‖transL2 h (h01HilbertFullValue Ω hΩm u) -
    h01HilbertFullValue Ω hΩm u‖ ^ 2 ≤ ‖h‖ ^ 2 * energy1 v at hs
  have hmul := mul_le_mul_of_nonneg_left he1 (sq_nonneg ‖h‖)
  nlinarith [norm_nonneg (transL2 h (h01HilbertFullValue Ω hΩm u) -
    h01HilbertFullValue Ω hΩm u), norm_nonneg h]

end Buckling

end

end
