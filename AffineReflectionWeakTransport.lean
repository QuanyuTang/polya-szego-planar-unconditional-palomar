module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01WeakGradientBridge
public import EuclideanReflection

/-!
# Actual affine reflection of whole-space weak-gradient and subsolution data

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The reflection is the literal orthogonal affine reflection already defined
in EuclideanReflection. Its coordinate pullback gradient is produced from
whole-space L2 weak-gradient data. No classical differentiability of the
original function, global L1 hypothesis, reflected PDE hypothesis, boundary
regularity, or final polarization-rigidity conclusion is used.

In particular, HasWeakDerivAlong.sum on univ cannot be used from L2 data:
that theorem requires L1. We instead use the existing weak Frechet derivative
equivalence (which only needs local integrability) to obtain each direction
before applying the actual HasWeakDerivAlong.comp_affine theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.AffineReflectionWeakTransport

open EllipticPdes.Embedding
open FaberKrahnDevelopment.EuclideanReflection

/-- The actual translation part of the affine reflection. -/
def affineShift (ν : UnitNormal) (c : ℝ) : Plane :=
  c • (ν : Plane) - linearReflection ν (c • (ν : Plane))

lemma reflection_eq_linear_add (ν : UnitNormal) (c : ℝ) (x : Plane) :
    reflection ν c x = linearReflection ν x + affineShift ν c := by
  simp only [reflection, affineShift, map_sub]
  abel

/-- The ordinary reflection homeomorphism, with the same literal function
in both directions. It produces actual compactly supported test pullbacks. -/
def reflectionHomeomorph (ν : UnitNormal) (c : ℝ) : Plane ≃ₜ Plane where
  toFun := reflection ν c
  invFun := reflection ν c
  left_inv := reflection_involutive ν c
  right_inv := reflection_involutive ν c
  continuous_toFun := (reflection_isometry ν c).continuous
  continuous_invFun := (reflection_isometry ν c).continuous

lemma contDiff_reflection (ν : UnitNormal) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (reflection ν c) := by
  have h : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Plane => linearReflection ν x + affineShift ν c) :=
    (linearReflection ν).toContinuousLinearEquiv.contDiff.add contDiff_const
  simpa only [← reflection_eq_linear_add] using! h

lemma reflection_hasFDerivAt (ν : UnitNormal) (c : ℝ) (x : Plane) :
    HasFDerivAt (reflection ν c)
      (linearReflection ν).toLinearIsometry.toContinuousLinearMap x := by
  let L : Plane →L[ℝ] Plane := (linearReflection ν).toLinearIsometry.toContinuousLinearMap
  have hsub : HasFDerivAt (fun y : Plane => y - c • (ν : Plane))
      (ContinuousLinearMap.id ℝ Plane) x :=
    (hasFDerivAt_id x).sub_const (c • (ν : Plane))
  have hlinear := L.hasFDerivAt.comp x hsub
  simpa only [Function.comp_def, reflection, L, ContinuousLinearMap.comp_id] using!
    hlinear.const_add (c • (ν : Plane))

/-- Actual smoothness, compact support, and support condition of the
reflected original test function. -/
lemma isTestFn_reflection (ν : UnitNormal) (c : ℝ) {ψ : Plane → ℝ}
    (hψ : IsTestFn univ ψ) : IsTestFn univ (fun x => ψ (reflection ν c x)) := by
  refine ⟨hψ.1.comp (contDiff_reflection ν c), ?_, subset_univ _⟩
  exact hψ.2.1.comp_homeomorph (reflectionHomeomorph ν c)

lemma memLp_test {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) :
    MemLp ψ 2 volume :=
  hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1

/-- Matrix coefficient: first index is the input coordinate, second is
the output coordinate. The pullback uses A-transpose, as the chain rule does. -/
def coefficient (ν : UnitNormal) (i j : Fin 2) : ℝ :=
  (linearReflection ν (EuclideanSpace.single i 1)) j

lemma coefficient_symm (ν : UnitNormal) (i j : Fin 2) :
    coefficient ν i j = coefficient ν j i := by
  have hinv : linearReflection ν
      (linearReflection ν (EuclideanSpace.single j 1)) = EuclideanSpace.single j 1 := by
    simp only [linearReflection, Submodule.reflection_reflection]
  have h := (linearReflection ν).inner_map_map (EuclideanSpace.single i 1)
    (linearReflection ν (EuclideanSpace.single j 1))
  rw [hinv] at h
  simpa only [coefficient, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, map_one, one_mul, conj_trivial] using h

/-- Literal coordinate formula for the weak gradient of U composed with
the actual affine reflection. -/
def reflectedGradient (ν : UnitNormal) (c : ℝ)
    (g : Fin 2 → Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  ∑ j, coefficient ν i j * g j (reflection ν c x)

lemma gradCLM_apply_sum (g : Fin 2 → Plane → ℝ) (x v : Plane) :
    gradCLM g x v = ∑ j, v j * g j x := by
  simp [gradCLM, mul_comm]

lemma memLp_reflected_value (ν : UnitNormal) (c : ℝ) {U : Plane → ℝ}
    (hU : MemLp U 2 volume) : MemLp (fun x => U (reflection ν c x)) 2 volume :=
  hU.comp_measurePreserving (reflection_measurePreserving ν c)

lemma memLp_reflectedGradient (ν : UnitNormal) (c : ℝ)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume) (i : Fin 2) :
    MemLp (reflectedGradient ν c g i) 2 volume := by
  unfold reflectedGradient
  simpa only [Function.comp_apply] using!
    memLp_finsetSum Finset.univ (fun j _ =>
      ((hg j).comp_measurePreserving (reflection_measurePreserving ν c)).const_mul
        (coefficient ν i j))

/-- Weak Frechet differentiation supplies arbitrary directions using only
local integrability, which genuinely follows from whole L2. -/
lemma weak_derivative_direction {U : Plane → ℝ} (hU : MemLp U 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ U g) (v : Plane) :
    HasWeakDerivAlong volume v univ U (fun x => ∑ j, v j * g j x) := by
  have hF := (hasWeakGradOn_iff_hasWeakFDerivOn isOpen_univ
    ((hU.locallyIntegrable one_le_two).locallyIntegrableOn _)
    (fun i => ((hg i).locallyIntegrable one_le_two).locallyIntegrableOn _)).mp hweak
  apply hasWeakDerivAlong_iff_integral.mpr
  intro ψ hψ hc hs
  simpa only [gradCLM_apply_sum] using (hF v).integral_eq hψ hc hs

/-- Actual whole-space coordinate weak-gradient transport under an
arbitrary affine orthogonal reflection. -/
theorem hasWeakGradOn_reflection (ν : UnitNormal) (c : ℝ)
    {U : Plane → ℝ} (hU : MemLp U 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ U g) :
    HasWeakGradOn univ (fun x => U (reflection ν c x)) (reflectedGradient ν c g) := by
  rw [hasWeakGradOn_iff]
  intro i
  have hdir := weak_derivative_direction hU hg hweak
    (linearReflection ν (EuclideanSpace.single i 1))
  have hmp : MeasurePreserving
      (fun x => (linearReflection ν).toContinuousLinearEquiv x + affineShift ν c)
      volume volume := by
    change MeasurePreserving (fun x : Plane => linearReflection ν x + affineShift ν c)
      volume volume
    simpa only [← reflection_eq_linear_add] using! reflection_measurePreserving ν c
  have h := HasWeakDerivAlong.comp_affine (v := EuclideanSpace.single i 1)
    (linearReflection ν).toContinuousLinearEquiv (affineShift ν c) hmp hdir
  try simp only [preimage_univ] at h
  change HasWeakDerivAlong volume (EuclideanSpace.single i 1) univ
    (fun x : Plane => U (linearReflection ν x + affineShift ν c))
    (fun x : Plane => ∑ j, coefficient ν i j *
      g j (linearReflection ν x + affineShift ν c)) at h
  simpa only [← reflection_eq_linear_add, reflectedGradient, coefficient] using! h

lemma nonnegative_reflected_ae (ν : UnitNormal) (c : ℝ) {U : Plane → ℝ}
    (hU : ∀ᵐ x ∂volume, 0 ≤ U x) :
    ∀ᵐ x ∂volume, 0 ≤ U (reflection ν c x) :=
  (reflection_measurePreserving ν c).quasiMeasurePreserving.ae hU

/-- The ordinary derivative of a smooth function is its finite coordinate
expansion. This only concerns the test function, never the rough U. -/
lemma fderiv_apply_sum (ψ : Plane → ℝ) (x v : Plane) :
    fderiv ℝ ψ x v = ∑ j, v j * pderiv j ψ x := by
  have hv : (∑ j : Fin 2, v j • EuclideanSpace.single j 1) = v := by
    simpa using (EuclideanSpace.basisFun (Fin 2) ℝ).sum_repr v
  calc
    fderiv ℝ ψ x v = fderiv ℝ ψ x
        (∑ j : Fin 2, v j • EuclideanSpace.single j 1) := congrArg _ hv.symm
    _ = ∑ j, v j * pderiv j ψ x := by
      simp only [map_sum, map_smul, smul_eq_mul, pderiv]

lemma pderiv_reflection (ν : UnitNormal) (c : ℝ) {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin 2) (x : Plane) :
    pderiv i (fun y => ψ (reflection ν c y)) x =
      ∑ j, coefficient ν i j * pderiv j ψ (reflection ν c x) := by
  have hcomp := (hψ.differentiable (by simp) (reflection ν c x)).hasFDerivAt.comp x
    (reflection_hasFDerivAt ν c x)
  change fderiv ℝ (ψ ∘ reflection ν c) x
    (EuclideanSpace.single i 1) = _
  rw [hcomp.fderiv]
  exact fderiv_apply_sum ψ (reflection ν c x)
    (linearReflection ν (EuclideanSpace.single i 1))

/-- Pointwise orthogonal-chain-rule identity for the two test pairings. -/
lemma paired_density_reflection (ν : UnitNormal) (c : ℝ)
    (g : Fin 2 → Plane → ℝ) {ψ : Plane → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Plane) :
    (∑ i, reflectedGradient ν c g i x * pderiv i ψ x) =
      ∑ j, g j (reflection ν c x) *
        pderiv j (fun y => ψ (reflection ν c y)) (reflection ν c x) := by
  simp only [reflectedGradient, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [pderiv_reflection ν c hψ, reflection_reflection, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [coefficient_symm ν i j]
  ring

/-- Every pairing in the transported weak inequality is genuinely
integrable by actual L2 Holder; no formal use of undefined integrals. -/
lemma integrable_gradient_pairing (ν : UnitNormal) (c : ℝ)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) (i : Fin 2) :
    Integrable (fun x => reflectedGradient ν c g i x * pderiv i ψ x) volume :=
  (memLp_reflectedGradient ν c hg i).integrable_mul (memLp_test (hψ.pderiv i))

/-- The coordinate sum of actual real integral pairings changes variables
to the original gradient tested against the reflected smooth test. -/
theorem sum_integral_pair_reflection (ν : UnitNormal) (c : ℝ)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) :
    (∑ i, ∫ x, reflectedGradient ν c g i x * pderiv i ψ x) =
      ∑ i, ∫ x, g i x * pderiv i (fun y => ψ (reflection ν c y)) x := by
  have hη := isTestFn_reflection ν c hψ
  calc
    (∑ i, ∫ x, reflectedGradient ν c g i x * pderiv i ψ x) =
        ∫ x, ∑ i, reflectedGradient ν c g i x * pderiv i ψ x :=
      (integral_finsetSum Finset.univ
        (fun i _ => integrable_gradient_pairing ν c hg hψ i)).symm
    _ = ∫ x, ∑ i, g i (reflection ν c x) *
        pderiv i (fun y => ψ (reflection ν c y)) (reflection ν c x) := by
      exact integral_congr_ae (Eventually.of_forall
        (paired_density_reflection ν c g hψ.1))
    _ = ∫ x, ∑ i, g i x * pderiv i (fun y => ψ (reflection ν c y)) x := by
      simpa only using! (reflection_measurePreserving ν c).integral_comp
        (reflectionHomeomorph ν c).measurableEmbedding
        (fun x : Plane => (∑ i, g i x * pderiv i (fun y => ψ (reflection ν c y)) x : ℝ))
    _ = ∑ i, ∫ x, g i x * pderiv i (fun y => ψ (reflection ν c y)) x :=
      integral_finsetSum Finset.univ (fun i _ =>
        (hg i).integrable_mul (memLp_test (hη.pderiv i)))

lemma integrable_value_pairing (ν : UnitNormal) (c : ℝ)
    {U : Plane → ℝ} (hU : MemLp U 2 volume)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) :
    Integrable (fun x => U (reflection ν c x) * ψ x) volume :=
  (memLp_reflected_value ν c hU).integrable_mul (memLp_test hψ)

theorem integral_value_pair_reflection (ν : UnitNormal) (c : ℝ)
    (U ψ : Plane → ℝ) :
    (∫ x, U (reflection ν c x) * ψ x) =
      ∫ x, U x * ψ (reflection ν c x) := by
  calc
    (∫ x, U (reflection ν c x) * ψ x) =
        ∫ x, U (reflection ν c x) * ψ (reflection ν c (reflection ν c x)) := by
      simp only [reflection_reflection]
    _ = ∫ x, U x * ψ (reflection ν c x) := by
      simpa only using! (reflection_measurePreserving ν c).integral_comp
        (reflectionHomeomorph ν c).measurableEmbedding
        (fun x : Plane => (U x * ψ (reflection ν c x) : ℝ))

/-- Reflection transports the actual whole-space nonnegative compact
smooth-test subsolution inequality, with the same real coefficient. -/
theorem global_subsolution_reflection (ν : UnitNormal) (c eigenvalue : ℝ)
    {U : Plane → ℝ} (hU : MemLp U 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hsub : ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, g i x * pderiv i ψ x) ≤ eigenvalue * ∫ x, U x * ψ x) :
    ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, reflectedGradient ν c g i x * pderiv i ψ x) ≤
        eigenvalue * ∫ x, U (reflection ν c x) * ψ x := by
  intro ψ hψ hψN
  have hη := isTestFn_reflection ν c hψ
  have hηN : ∀ x, 0 ≤ ψ (reflection ν c x) := fun x => hψN _
  have h := hsub (fun x => ψ (reflection ν c x)) hη hηN
  rw [sum_integral_pair_reflection ν c hg hψ,
    integral_value_pair_reflection ν c U ψ]
  exact h

/-- Natural whole-space data produce all reflected data and the reflected
subsolution. There is no extra reflected weak derivative or reflected PDE
hypothesis, and no L1 requirement hidden in the transport. -/
theorem whole_data_reflection (ν : UnitNormal) (c eigenvalue : ℝ)
    {U : Plane → ℝ} (hU : MemLp U 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ U g)
    (hsub : ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
      (∑ i, ∫ x, g i x * pderiv i ψ x) ≤ eigenvalue * ∫ x, U x * ψ x) :
    MemLp (fun x => U (reflection ν c x)) 2 volume ∧
      (∀ i, MemLp (reflectedGradient ν c g i) 2 volume) ∧
      HasWeakGradOn univ (fun x => U (reflection ν c x)) (reflectedGradient ν c g) ∧
      ∀ ψ : Plane → ℝ, IsTestFn univ ψ → (∀ x, 0 ≤ ψ x) →
        (∑ i, ∫ x, reflectedGradient ν c g i x * pderiv i ψ x) ≤
          eigenvalue * ∫ x, U (reflection ν c x) * ψ x := by
  exact ⟨memLp_reflected_value ν c hU, memLp_reflectedGradient ν c hg,
    hasWeakGradOn_reflection ν c hU hg hweak,
    global_subsolution_reflection ν c eigenvalue hU hg hsub⟩

end Buckling.AffineReflectionWeakTransport

end

end
