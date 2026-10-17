module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01HilbertModel
public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Analysis.LpExtendByZero

/-!
# The original H01 has a genuine full-space zero-extended weak gradient

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The integration-by-parts closure argument is ported from the independently
verified Lean 4.28 H01ZeroExtension.lean. This file imports only Core1 through
H01HilbertModel, and the pinned EllipticPDE weak-gradient/zero-extension API.

All data below belong to the actual original graph closure H01. The only
domain input for zero extension is MeasurableSet Omega. No boundedness,
finite volume, openness, regular boundary, PDE, or weak-gradient assumption
is added. The final roots use the actual lpExtendByZero classes, as well as
the literal indicator representatives. No chain rule or SMP is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set Filter Topology
open scoped ENNReal

namespace Buckling.H01WeakGradientBridge

/-- Core1-only replacement for the later convenience lemma. -/
lemma test_eq_zero_of_notMem {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) {x : Plane} (hx : x ∉ Ω) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))

/-- The two actual restricted L2 classes have the expected inner product.
The helper is namespaced to avoid a collision with the later Core4 lemma. -/
lemma inner_toLp_toLp {Ω : Set Plane} {f g : Plane → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω)) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x in Ω, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/-- The continuous integration-by-parts identity passes from actual test
graphs to the actual original H01 closure. -/
theorem H01_weak_gradient {Ω : Set Plane} {v : L2 Ω × (Fin 2 → L2 Ω)}
    (hv : v ∈ H01 Ω) {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) (i : Fin 2) :
    ∫ x in Ω, v.1 x * pderiv i ψ x = -∫ x in Ω, v.2 i x * ψ x := by
  have hm : ∀ {g : Plane → ℝ}, IsTestFn univ g → MemLp g 2 (volume.restrict Ω) :=
    fun hg => (hg.1.continuous.memLp_of_hasCompactSupport hg.2.1).restrict Ω
  set g1 : L2 Ω := (hm (hψ.pderiv i)).toLp _
  set g0 : L2 Ω := (hm hψ).toLp _
  have key : ∀ w ∈ H01 Ω, inner ℝ w.1 g1 + inner ℝ (w.2 i) g0 = 0 := by
    intro w hw
    refine closure_minimal (s := Set.range (graphH1 (Ω := Ω)))
      (t := {w | inner ℝ w.1 g1 + inner ℝ (w.2 i) g0 = 0}) ?_ ?_ hw
    · rintro _ ⟨φ, rfl⟩
      simp only [mem_setOf_eq, graphH1, IsTestFn.toL2, g1, g0, inner_toLp_toLp]
      have hc : ∀ {f g : Plane → ℝ}, Continuous f → IsTestFn Ω g →
          Integrable (fun x => g x * f x) := fun hf hg =>
        (hg.1.continuous.mul hf).integrable_of_hasCompactSupport hg.2.1.mul_right
      have e1 : ∫ x in Ω, φ.1 x * pderiv i ψ x = ∫ x, φ.1 x * pderiv i ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [test_eq_zero_of_notMem φ.2 hx, zero_mul]
      have e2 : ∫ x in Ω, pderiv i φ.1 x * ψ x = ∫ x, pderiv i φ.1 x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [test_eq_zero_of_notMem (φ.2.pderiv i) hx, zero_mul]
      rw [e1, e2]
      have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
        (μ := (volume : Measure Plane)) (f := φ.1) (g := ψ)
        (v := EuclideanSpace.single i 1)
        (hc hψ.1.continuous (φ.2.pderiv i))
        (hc (hψ.pderiv i).1.continuous φ.2) (hc hψ.1.continuous φ.2)
        (fun x _ => (φ.2.1.differentiable (by simp)) x)
        (fun x _ => (hψ.1.differentiable (by simp)) x)
      simp only [pderiv] at hIBP ⊢
      linarith
    · exact isClosed_eq (by fun_prop) continuous_const
  have hIdentity := key v hv
  have c1 : inner ℝ v.1 g1 = ∫ x in Ω, v.1 x * pderiv i ψ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hm (hψ.pderiv i)).coeFn_toLp] with x hx
    simp [g1, hx, mul_comm]
  have c2 : inner ℝ (v.2 i) g0 = ∫ x in Ω, v.2 i x * ψ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hm hψ).coeFn_toLp] with x hx
    simp [g0, hx, mul_comm]
  linarith

/-- Literal zero extension of the actual representative of L2(Omega). -/
def zeroExtend {Ω : Set Plane} (f : L2 Ω) : Plane → ℝ :=
  Ω.indicator (fun x => f x)

lemma zeroExtend_eq_zero_of_notMem {Ω : Set Plane} (f : L2 Ω) {x : Plane}
    (hx : x ∉ Ω) : zeroExtend f x = 0 := by
  simp only [zeroExtend, indicator_of_notMem hx]

lemma memLp_zeroExtend {Ω : Set Plane} (hΩm : MeasurableSet Ω) (f : L2 Ω) :
    MemLp (zeroExtend f) 2 volume :=
  (memLp_indicator_iff_restrict hΩm).mpr (Lp.memLp f)

lemma integral_zeroExtend_mul {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (f : L2 Ω) (g : Plane → ℝ) :
    ∫ x, zeroExtend f x * g x = ∫ x in Ω, f x * g x := by
  rw [← integral_indicator hΩm]
  congr 1
  ext x
  by_cases hx : x ∈ Ω <;> simp [zeroExtend, hx]

/-- The definitions agree on the whole plane, with no integrability premise
silently built into either predicate. The actual L2 data is supplied below. -/
theorem hasWeakGradient_iff_hasWeakGradOn_univ {f : Plane → ℝ}
    {g : Fin 2 → Plane → ℝ} :
    HasWeakGradient f g ↔ EllipticPdes.Embedding.HasWeakGradOn univ f g := by
  constructor
  · intro h ψ hψ hc hs i
    simpa only [Measure.restrict_univ, pderiv, EllipticPdes.Sobolev.partialD] using
      h ψ ⟨hψ, hc, hs⟩ i
  · intro h ψ hψ i
    simpa only [Measure.restrict_univ, pderiv, EllipticPdes.Sobolev.partialD] using
      h ψ hψ.1 hψ.2.1 hψ.2.2 i

/-- Whole-space weak gradient of the literal zero-extended value and
derivative coordinates, produced from original H01 membership. -/
theorem H01_zeroExtend_hasWeakGradOn {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    EllipticPdes.Embedding.HasWeakGradOn univ
      (zeroExtend v.1) (fun i => zeroExtend (v.2 i)) := by
  apply hasWeakGradient_iff_hasWeakGradOn_univ.mp
  intro ψ hψ i
  rw [integral_zeroExtend_mul hΩm, integral_zeroExtend_mul hΩm]
  exact H01_weak_gradient hv hψ i

/-- All full-space L2 and weak-gradient facts for the literal representatives.
The zero statement is pointwise, stronger than an a.e. off-domain statement. -/
theorem H01_zeroExtend_data {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    MemLp (zeroExtend v.1) 2 volume ∧
      (∀ i, MemLp (zeroExtend (v.2 i)) 2 volume) ∧
      EllipticPdes.Embedding.HasWeakGradOn univ
        (zeroExtend v.1) (fun i => zeroExtend (v.2 i)) ∧
      (∀ x, x ∉ Ω → zeroExtend v.1 x = 0 ∧ ∀ i, zeroExtend (v.2 i) x = 0) := by
  refine ⟨memLp_zeroExtend hΩm v.1, fun i => memLp_zeroExtend hΩm (v.2 i),
    H01_zeroExtend_hasWeakGradOn hΩm hv, ?_⟩
  exact fun x hx => ⟨zeroExtend_eq_zero_of_notMem v.1 hx,
    fun i => zeroExtend_eq_zero_of_notMem (v.2 i) hx⟩

/-- The actual scalar isometric zero-extension used by the compactness
pipeline; this is not a newly chosen function with only matching norm. -/
abbrev fullComponent {Ω : Set Plane} (hΩm : MeasurableSet Ω) (f : L2 Ω) :
    Lp ℝ 2 (volume : Measure Plane) :=
  lpExtendByZero volume 2 Ω hΩm f

lemma coeFn_fullComponent {Ω : Set Plane} (hΩm : MeasurableSet Ω) (f : L2 Ω) :
    (fullComponent hΩm f : Plane → ℝ) =ᵐ[volume] zeroExtend f :=
  coeFn_lpExtendByZero hΩm f

/-- Transport the already proved literal identity to the actual full-space
Lp representatives. No assumption about arbitrary pointwise Lp representatives
is made: each factor is replaced only almost everywhere. -/
theorem H01_fullLp_hasWeakGradOn {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    EllipticPdes.Embedding.HasWeakGradOn univ
      (fullComponent hΩm v.1) (fun i => fullComponent hΩm (v.2 i)) := by
  intro ψ hψ hc hs i
  have h := H01_zeroExtend_hasWeakGradOn hΩm hv ψ hψ hc hs i
  simp only [Measure.restrict_univ] at h ⊢
  have hvalue :
      (∫ x, fullComponent hΩm v.1 x * EllipticPdes.Sobolev.partialD i ψ x) =
        ∫ x, zeroExtend v.1 x * EllipticPdes.Sobolev.partialD i ψ x := by
    apply integral_congr_ae
    filter_upwards [coeFn_fullComponent hΩm v.1] with x hx
    rw [hx]
  have hgrad : (∫ x, fullComponent hΩm (v.2 i) x * ψ x) =
      ∫ x, zeroExtend (v.2 i) x * ψ x := by
    apply integral_congr_ae
    filter_upwards [coeFn_fullComponent hΩm (v.2 i)] with x hx
    rw [hx]
  rw [hvalue, hgrad]
  exact h

/-- The actual global Lp value and two actual global Lp derivatives satisfy
the new weak-gradient predicate and vanish off the original measurable set. -/
theorem H01_fullLp_data {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    {v : L2 Ω × (Fin 2 → L2 Ω)} (hv : v ∈ H01 Ω) :
    MemLp (fullComponent hΩm v.1) 2 volume ∧
      (∀ i, MemLp (fullComponent hΩm (v.2 i)) 2 volume) ∧
      EllipticPdes.Embedding.HasWeakGradOn univ
        (fullComponent hΩm v.1) (fun i => fullComponent hΩm (v.2 i)) ∧
      (∀ᵐ x ∂(volume : Measure Plane), x ∉ Ω →
        fullComponent hΩm v.1 x = 0 ∧ ∀ i, fullComponent hΩm (v.2 i) x = 0) := by
  refine ⟨Lp.memLp _, fun i => Lp.memLp _, H01_fullLp_hasWeakGradOn hΩm hv, ?_⟩
  have hv0 := lpExtendByZero_ae_eq_zero hΩm v.1
  have hg0 : ∀ᵐ x ∂(volume : Measure Plane), ∀ i : Fin 2,
      x ∉ Ω → fullComponent hΩm (v.2 i) x = 0 :=
    ae_all_iff.mpr (fun i => lpExtendByZero_ae_eq_zero hΩm (v.2 i))
  filter_upwards [hv0, hg0] with x hx hg hxs
  exact ⟨hx hxs, fun i => hg i hxs⟩

/-- Recover the original tuple from the actual Hilbert closed subspace. -/
def hilbertRawData {Ω : Set Plane} (u : h01HilbertSubmodule Ω) :
    L2 Ω × (Fin 2 → L2 Ω) :=
  (h1DataToHilbert Ω).symm u.1

lemma hilbertRawData_mem_H01 {Ω : Set Plane} (u : h01HilbertSubmodule Ω) :
    hilbertRawData u ∈ H01 Ω := by
  apply (h1DataToHilbert_mem_iff Ω (hilbertRawData u)).mp
  simpa only [hilbertRawData, ContinuousLinearEquiv.apply_symm_apply] using u.2

/-- Endpoint for an element of the actual original Hilbert H01, not a
different Sobolev space or a postulated weak-gradient completion. -/
theorem h01Hilbert_fullLp_hasWeakGradOn {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (u : h01HilbertSubmodule Ω) :
    EllipticPdes.Embedding.HasWeakGradOn univ
      (fullComponent hΩm (hilbertRawData u).1)
      (fun i => fullComponent hΩm ((hilbertRawData u).2 i)) :=
  H01_fullLp_hasWeakGradOn hΩm (hilbertRawData_mem_H01 u)

theorem h01Hilbert_fullLp_data {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (u : h01HilbertSubmodule Ω) :
    MemLp (fullComponent hΩm (hilbertRawData u).1) 2 volume ∧
      (∀ i, MemLp (fullComponent hΩm ((hilbertRawData u).2 i)) 2 volume) ∧
      EllipticPdes.Embedding.HasWeakGradOn univ
        (fullComponent hΩm (hilbertRawData u).1)
        (fun i => fullComponent hΩm ((hilbertRawData u).2 i)) ∧
      (∀ᵐ x ∂(volume : Measure Plane), x ∉ Ω →
        fullComponent hΩm (hilbertRawData u).1 x = 0 ∧
          ∀ i, fullComponent hΩm ((hilbertRawData u).2 i) x = 0) :=
  H01_fullLp_data hΩm (hilbertRawData_mem_H01 u)

end Buckling.H01WeakGradientBridge

end

end
