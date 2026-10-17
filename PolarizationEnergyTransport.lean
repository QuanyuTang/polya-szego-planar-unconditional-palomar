module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationMeasure
public import PolarizationEnergy
public import EuclideanReflection
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Derivative energy transport for literal two-point polarization

SOURCE_DRAFT (2026-10-17), not compiled. This isolated module uses the actual
affine reflection constructed in `EuclideanReflection`; it does not assume
an energy identity as geometric data. No production source is modified.

The intended sequence is local branch derivatives, the actual affine
reflection derivative, orthogonal operator-norm invariance, an a.e. paired
energy identity, then equality of the extended nonnegative Dirichlet energy.
The integral is allowed to be infinite; the final cancellation is by the
finite nonzero factor 2 in ENNReal, not by subtraction of infinite values.

Successful elaboration and kernel dependency inspection of this module and its imported
development modules are still required. No Schwarz-rearrangement convergence,
Faber--Krahn inequality, or equality rigidity is asserted here.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace FaberKrahnDevelopment

section LocalBranches

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In the interior of the chosen side, the literal polarization agrees
locally with its max branch. -/
lemma twoPointPolarization_eventuallyEq_max {H : Set E} {τ : E → E}
    {f : E → ℝ} {x : E} (hx : x ∈ interior H) :
    twoPointPolarization H τ f =ᶠ[𝓝 x] (fun y => max (f y) (f (τ y))) := by
  classical
  have hSide : ∀ᶠ y in 𝓝 x, y ∈ H := mem_interior_iff_mem_nhds.mp hx
  exact hSide.mono fun y hy => by
    simp only [twoPointPolarization, if_pos hy]

/-- In the interior of the complementary side, the literal polarization
agrees locally with its min branch. -/
lemma twoPointPolarization_eventuallyEq_min {H : Set E} {τ : E → E}
    {f : E → ℝ} {x : E} (hx : x ∈ interior Hᶜ) :
    twoPointPolarization H τ f =ᶠ[𝓝 x] (fun y => min (f y) (f (τ y))) := by
  classical
  have hSide : ∀ᶠ y in 𝓝 x, y ∉ H := mem_interior_iff_mem_nhds.mp hx
  exact hSide.mono fun y hy => by
    simp only [twoPointPolarization, if_neg hy]

lemma fderiv_twoPointPolarization_of_mem_interior {H : Set E} {τ : E → E}
    {f : E → ℝ} {x : E} (hx : x ∈ interior H) :
    fderiv ℝ (twoPointPolarization H τ f) x =
      fderiv ℝ (fun y => max (f y) (f (τ y))) x :=
  (twoPointPolarization_eventuallyEq_max hx).fderiv_eq

lemma fderiv_twoPointPolarization_of_mem_interior_compl {H : Set E} {τ : E → E}
    {f : E → ℝ} {x : E} (hx : x ∈ interior Hᶜ) :
    fderiv ℝ (twoPointPolarization H τ f) x =
      fderiv ℝ (fun y => min (f y) (f (τ y))) x :=
  (twoPointPolarization_eventuallyEq_min hx).fderiv_eq

end LocalBranches

namespace EuclideanReflection

/-- The actual affine reflection has its orthogonal linear part as derivative. -/
lemma reflection_hasFDerivAt (ν : UnitNormal) (c : ℝ) (x : Plane) :
    HasFDerivAt (reflection ν c)
      (linearReflection ν).toLinearIsometry.toContinuousLinearMap x := by
  change HasFDerivAt
    (fun y : Plane => c • (ν : Plane) + linearReflection ν (y - c • (ν : Plane)))
    (linearReflection ν).toLinearIsometry.toContinuousLinearMap x
  let L : Plane →L[ℝ] Plane := (linearReflection ν).toLinearIsometry.toContinuousLinearMap
  have hsub : HasFDerivAt (fun y : Plane => y - c • (ν : Plane))
      (ContinuousLinearMap.id ℝ Plane) x :=
    (hasFDerivAt_id x).sub_const (c • (ν : Plane))
  have hlinear := L.hasFDerivAt.comp x hsub
  simpa only [Function.comp_def, L, ContinuousLinearMap.comp_id] using!
    hlinear.const_add (c • (ν : Plane))

/-- Chain rule and orthogonality give exact operator-norm preservation for
composition with the actual affine reflection. -/
lemma norm_fderiv_comp_reflection (ν : UnitNormal) (c : ℝ) {f : Plane → ℝ}
    {x : Plane} (hf : DifferentiableAt ℝ f (reflection ν c x)) :
    ‖fderiv ℝ (f ∘ reflection ν c) x‖ = ‖fderiv ℝ f (reflection ν c x)‖ := by
  rw [fderiv_comp x hf (reflection_hasFDerivAt ν c x).differentiableAt,
    (reflection_hasFDerivAt ν c x).fderiv]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ (linearReflection ν)

/-- Away from the fixed hyperplane the two reflected points lie in opposite
interiors. The boundary is not presumed absent at every point. -/
lemma reflection_interior_sides (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : x ∉ hyperplane ν c) :
    (x ∈ interior (halfspace ν c) ∧
      reflection ν c x ∈ interior (halfspace ν c)ᶜ) ∨
    (x ∈ interior (halfspace ν c)ᶜ ∧
      reflection ν c x ∈ interior (halfspace ν c)) := by
  have hpos : ∀ z : Plane, c < ⟪(ν : Plane), z⟫_ℝ → z ∈ interior (halfspace ν c) := by
    intro z hz
    have hopen : IsOpen {w : Plane | c < ⟪(ν : Plane), w⟫_ℝ} :=
      isOpen_lt continuous_const (continuous_const.inner continuous_id)
    refine interior_maximal ?_ hopen hz
    intro w hw
    change c < ⟪(ν : Plane), w⟫_ℝ at hw
    change c ≤ ⟪(ν : Plane), w⟫_ℝ
    exact hw.le
  have hneg : ∀ z : Plane, ⟪(ν : Plane), z⟫_ℝ < c → z ∈ interior (halfspace ν c)ᶜ := by
    intro z hz
    rw [(halfspace_isClosed ν c).isOpen_compl.interior_eq]
    change ¬ c ≤ ⟪(ν : Plane), z⟫_ℝ
    exact not_le.mpr hz
  change ⟪(ν : Plane), x⟫_ℝ ≠ c at hx
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · refine Or.inr ⟨hneg x hlt, hpos (reflection ν c x) ?_⟩
    rw [inner_reflection]
    linarith
  · refine Or.inl ⟨hpos x hgt, hneg (reflection ν c x) ?_⟩
    rw [inner_reflection]
    linarith

/-- A pointwise pair identity off the hyperplane. Every differentiability
premise here is produced by Rademacher in the a.e. theorem below. -/
lemma norm_fderiv_polarization_pair_off_hyperplane (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {x : Plane} (hx : x ∉ hyperplane ν c)
    (hfx : DifferentiableAt ℝ f x)
    (hfxR : DifferentiableAt ℝ f (reflection ν c x))
    (hMx : DifferentiableAt ℝ (fun y => max (f y) (f (reflection ν c y))) x)
    (hmx : DifferentiableAt ℝ (fun y => min (f y) (f (reflection ν c y))) x)
    (hMxR : DifferentiableAt ℝ (fun y => max (f y) (f (reflection ν c y)))
      (reflection ν c x))
    (hmxR : DifferentiableAt ℝ (fun y => min (f y) (f (reflection ν c y)))
      (reflection ν c x)) :
    ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f) x‖ ^ 2 +
        ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f)
          (reflection ν c x)‖ ^ 2 =
      ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ f (reflection ν c x)‖ ^ 2 := by
  let τ := reflection ν c
  let H := halfspace ν c
  let M : Plane → ℝ := fun y => max (f y) (f (τ y))
  let m : Plane → ℝ := fun y => min (f y) (f (τ y))
  have hMComp : M ∘ τ = M := by
    funext y
    simp only [M, τ, Function.comp_def, reflection_reflection, max_comm]
  have hmComp : m ∘ τ = m := by
    funext y
    simp only [m, τ, Function.comp_def, reflection_reflection, min_comm]
  have hMnorm : ‖fderiv ℝ M x‖ = ‖fderiv ℝ M (τ x)‖ := by
    have h := norm_fderiv_comp_reflection ν c (f := M) (x := x) hMxR
    change ‖fderiv ℝ (M ∘ τ) x‖ = ‖fderiv ℝ M (τ x)‖ at h
    rwa [hMComp] at h
  have hmnorm : ‖fderiv ℝ m x‖ = ‖fderiv ℝ m (τ x)‖ := by
    have h := norm_fderiv_comp_reflection ν c (f := m) (x := x) hmxR
    change ‖fderiv ℝ (m ∘ τ) x‖ = ‖fderiv ℝ m (τ x)‖ at h
    rwa [hmComp] at h
  have hcomp : DifferentiableAt ℝ (f ∘ τ) x :=
    hfxR.comp x (reflection_hasFDerivAt ν c x).differentiableAt
  have hbase := norm_fderiv_max_sq_add_min_sq hfx hcomp hMx hmx
  change ‖fderiv ℝ M x‖ ^ 2 + ‖fderiv ℝ m x‖ ^ 2 =
    ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ (f ∘ reflection ν c) x‖ ^ 2 at hbase
  rw [norm_fderiv_comp_reflection ν c (x := x) hfxR] at hbase
  rcases reflection_interior_sides ν c hx with hside | hside
  · rw [fderiv_twoPointPolarization_of_mem_interior hside.1,
      fderiv_twoPointPolarization_of_mem_interior_compl hside.2]
    change ‖fderiv ℝ M x‖ ^ 2 + ‖fderiv ℝ m (τ x)‖ ^ 2 = _
    rw [← hmnorm]
    exact hbase
  · rw [fderiv_twoPointPolarization_of_mem_interior_compl hside.1,
      fderiv_twoPointPolarization_of_mem_interior hside.2]
    change ‖fderiv ℝ m x‖ ^ 2 + ‖fderiv ℝ M (τ x)‖ ^ 2 = _
    rw [← hMnorm, add_comm (‖fderiv ℝ m x‖ ^ 2)]
    exact hbase

/-- Actual affine-halfspace polarization preserves the paired derivative
energy almost everywhere. All local differentiability data are produced here. -/
lemma ae_norm_fderiv_polarization_pair (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∀ᵐ x ∂volume,
      ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f) x‖ ^ 2 +
          ‖fderiv ℝ (twoPointPolarization (halfspace ν c) (reflection ν c) f)
            (reflection ν c x)‖ ^ 2 =
        ‖fderiv ℝ f x‖ ^ 2 + ‖fderiv ℝ f (reflection ν c x)‖ ^ 2 := by
  have hfR : LipschitzWith K (f ∘ reflection ν c) := by
    simpa only [mul_one] using hf.comp (reflection_isometry ν c).lipschitz
  have hfd := hf.ae_differentiableAt (μ := (volume : Measure Plane))
  have hMd := (hf.max hfR).ae_differentiableAt (μ := (volume : Measure Plane))
  have hmd := (hf.min hfR).ae_differentiableAt (μ := (volume : Measure Plane))
  have hmp := (reflection_measurePreserving ν c).quasiMeasurePreserving
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp (hyperplane_volume_zero ν c),
    hfd, hmp.ae hfd, hMd, hmd, hmp.ae hMd, hmp.ae hmd]
      with x hx hfx hfxR hMx hmx hMxR hmxR
  exact norm_fderiv_polarization_pair_off_hyperplane ν c hx hfx hfxR hMx hmx hMxR hmxR

/-- Extended nonnegative Dirichlet energy, with its literal integral meaning. -/
noncomputable def extendedDirichletEnergy (f : Plane → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)

/-- The integral version of the paired identity, for the actual affine
reflection and literal polarization. Infinite energy is permitted. -/
lemma extendedDirichletEnergy_polarization (ν : UnitNormal) (c : ℝ)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    extendedDirichletEnergy (twoPointPolarization (halfspace ν c) (reflection ν c) f) =
      extendedDirichletEnergy f := by
  let τ := reflection ν c
  let p := twoPointPolarization (halfspace ν c) τ f
  let ep : Plane → ℝ≥0∞ := fun x => ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2)
  let ef : Plane → ℝ≥0∞ := fun x => ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2)
  have hep : Measurable ep := ((measurable_fderiv ℝ p).norm.pow_const 2).ennreal_ofReal
  have hef : Measurable ef := ((measurable_fderiv ℝ f).norm.pow_const 2).ennreal_ofReal
  have hpair : ∀ᵐ x ∂volume, ep x + ep (τ x) = ef x + ef (τ x) := by
    filter_upwards [ae_norm_fderiv_polarization_pair ν c hf] with x hx
    change ENNReal.ofReal (‖fderiv ℝ p x‖ ^ 2) +
        ENNReal.ofReal (‖fderiv ℝ p (τ x)‖ ^ 2) =
      ENNReal.ofReal (‖fderiv ℝ f x‖ ^ 2) + ENNReal.ofReal (‖fderiv ℝ f (τ x)‖ ^ 2)
    rw [← ENNReal.ofReal_add (sq_nonneg ‖fderiv ℝ p x‖) (sq_nonneg ‖fderiv ℝ p (τ x)‖),
      ← ENNReal.ofReal_add (sq_nonneg ‖fderiv ℝ f x‖) (sq_nonneg ‖fderiv ℝ f (τ x)‖)]
    exact congrArg ENNReal.ofReal hx
  have hint := lintegral_congr_ae hpair
  have hmp : MeasurePreserving τ volume volume := reflection_measurePreserving ν c
  rw [lintegral_add_left hep, lintegral_add_left hef,
    hmp.lintegral_comp hep, hmp.lintegral_comp hef] at hint
  apply (ENNReal.mul_right_inj (a := (2 : ℝ≥0∞)) (by norm_num) (by norm_num)).mp
  change (2 : ℝ≥0∞) * (∫⁻ x, ep x) = (2 : ℝ≥0∞) * (∫⁻ x, ef x)
  simpa only [two_mul] using hint

end EuclideanReflection

end FaberKrahnDevelopment
