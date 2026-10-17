module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPIntegratedCaccioppoli
public import AnchoredL2Estimate
public import EllipticPdes.Spectrum.PoincareBall

/-!
# A uniform ball L2 bound for the actual logarithmic regularizers

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The actual library Poincare inequality on a ball is squared and expressed
as real integrals. Actual logarithmic weak-gradient data and its integrated
Caccioppoli estimate are then combined with the actual positive-measure
zero-set anchoring estimate. The resulting finite real bound is independent
of the positive regularization parameter.

The ambient test domain need not be bounded or have regular boundary. A
fixed actual original smooth cutoff, equal to one on the ball, is an input
to this helper. No Poincare estimate, compact weak test admissibility,
gradient integrability, or final strong maximum principle is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.WeakSMPBallLogBound

open EllipticPdes EllipticPdes.Embedding WeakSMPRegularizers
open WeakSMPIntegratedCaccioppoli

lemma eLpNorm_two_toReal_sq {μ : Measure Plane} {f : Plane → ℝ}
    (hf : MemLp f 2 μ) : (eLpNorm f 2 μ).toReal ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← Lp.norm_toLp f hf, L2.norm_sq_eq_integral_sq]
  apply integral_congr_ae
  exact hf.coeFn_toLp.mono fun x hx => congrArg (fun r : ℝ => r ^ 2) hx

/-- This integral form is produced from the actual pinned ball Poincare
theorem. Its constant depends only on the dimension, not on the function. -/
theorem exists_ball_poincare_square_constant :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (p : Plane) (r : ℝ), 0 < r →
      ∀ (u : Plane → ℝ) (g : Fin 2 → Plane → ℝ),
        MemLp u 2 (volume.restrict (ball p r)) →
        (∀ i, MemLp (g i) 2 (volume.restrict (ball p r))) →
        HasWeakGradOn (ball p r) u g →
        (∫ x in ball p r, (u x - ⨍ y in ball p r, u y) ^ 2) ≤
          P * r ^ 2 * ∫ x in ball p r, ∑ i, g i x ^ 2 := by
  obtain ⟨C, hC⟩ := EllipticPdes.Sobolev.poincare_ball (d := 2) (by decide)
  let K : ℝ := |C| + 1
  have hK0 : 0 ≤ K := by dsimp [K]; positivity
  have hCK : C ≤ K := by dsimp [K]; linarith [le_abs_self C]
  refine ⟨K ^ 2, sq_nonneg K, ?_⟩
  intro p r hr u g hu hg hweak
  letI : IsFiniteMeasure (volume.restrict (ball p r)) :=
    isFiniteMeasure_restrict_of_isBounded isBounded_ball
  have hcenter : MemLp (fun x => u x - ⨍ y in ball p r, u y)
      2 (volume.restrict (ball p r)) := hu.sub (memLp_const _)
  have hP := hC p r hr u g hu hg hweak
  have hPK : (eLpNorm (fun x => u x - ⨍ y in ball p r, u y)
      2 (volume.restrict (ball p r))).toReal ≤
      K * r * Real.sqrt (∑ i, (eLpNorm (g i) 2 (volume.restrict (ball p r))).toReal ^ 2) :=
    hP.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCK hr.le) (Real.sqrt_nonneg _))
  have hsum0 : 0 ≤ ∑ i, (eLpNorm (g i) 2 (volume.restrict (ball p r))).toReal ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq := (sq_le_sq₀ ENNReal.toReal_nonneg
    (mul_nonneg (mul_nonneg hK0 hr.le) (Real.sqrt_nonneg _))).mpr hPK
  rw [mul_pow, mul_pow, Real.sq_sqrt hsum0, eLpNorm_two_toReal_sq hcenter] at hsq
  have hsum : (∑ i, (eLpNorm (g i) 2 (volume.restrict (ball p r))).toReal ^ 2) =
      ∫ x in ball p r, ∑ i, g i x ^ 2 := by
    rw [integral_finsetSum Finset.univ (fun i _ => (hg i).integrable_sq)]
    exact Finset.sum_congr rfl fun i _ => eLpNorm_two_toReal_sq (hg i)
  rw [hsum] at hsq
  exact hsq

/-- Restriction to the actual ball is nonnegative almost everywhere from
the given domain inequality and the actual set inclusion. -/
lemma nonneg_ae_ball {D : Set Plane} (hD : IsOpen D) {p : Plane} {r : ℝ}
    (hBD : ball p r ⊆ D) {w : Plane → ℝ}
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x) :
    ∀ᵐ x ∂volume.restrict (ball p r), 0 ≤ w x := by
  have hcond := (ae_restrict_iff' hD.measurableSet).mp hw0
  filter_upwards [ae_restrict_of_ae hcond, ae_restrict_mem measurableSet_ball] with x hx hxB
  exact hx (hBD hxB)

/-- The cutoff being one on the ball converts the actual global weighted
log-gradient estimate into an actual ball gradient-energy bound. -/
theorem integral_ball_logGradient_sq_le {D : Set Plane} (hD : IsOpen D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) {p : Plane} {r : ℝ}
    (hχone : ∀ x ∈ ball p r, χ x = 1) {δ : ℝ} (hδ : 0 < δ)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    (∫ x in ball p r, ∑ i, logGradient δ w g i x ^ 2) ≤
      8 * ∫ x, cutoffEnergy χ x := by
  calc
    (∫ x in ball p r, ∑ i, logGradient δ w g i x ^ 2) =
        ∫ x in ball p r, logEnergy δ χ w g x := by
      apply setIntegral_congr_fun measurableSet_ball
      intro x hx
      simp only [logEnergy, hχone x hx, one_pow, one_mul]
    _ ≤ ∫ x, logEnergy δ χ w g x :=
      integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
        (integrable_logEnergy hχ hδ hw hg)
    _ ≤ 8 * ∫ x, cutoffEnergy χ x :=
      integral_logEnergy_le_eight_cutoff hD hχ hδ hw hg hweak hw0 hsuper

/-- An actual positive-measure zero set in the ball yields a finite
uniform logarithmic L2 bound. The constant is chosen before delta. -/
theorem exists_uniform_ball_log_bound {D : Set Plane} (hD : IsOpen D)
    {p : Plane} {r : ℝ} (hr : 0 < r) (hBD : ball p r ⊆ D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) (hχone : ∀ x ∈ ball p r, χ x = 1)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x)
    {E : Set Plane} (hEB : E ⊆ ball p r) (hE : 0 < volume E)
    (hwE : ∀ᵐ x ∂volume.restrict E, w x = 0) :
    (∀ᵐ x ∂volume.restrict (ball p r), 0 ≤ w x) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ →
        MemLp (fun x => logarithm δ (w x)) 2 (volume.restrict (ball p r)) ∧
        (∫ x in ball p r, logarithm δ (w x) ^ 2) ≤ C := by
  refine ⟨nonneg_ae_ball hD hBD hw0, ?_⟩
  let μB : Measure Plane := volume.restrict (ball p r)
  letI : IsFiniteMeasure μB := isFiniteMeasure_restrict_of_isBounded isBounded_ball
  have hE' : 0 < μB E := by
    change 0 < (volume.restrict (ball p r)) E
    rw [Measure.restrict_eq_self volume hEB]
    exact hE
  have hm : 0 < μB.real E := AnchoredL2Estimate.real_anchor_measure_pos hE'
  obtain ⟨P, hP0, hP⟩ := exists_ball_poincare_square_constant
  let A : ℝ := 2 * (1 + μB.real univ / μB.real E)
  have hA0 : 0 ≤ A := by
    exact mul_nonneg (by norm_num) (add_nonneg (by norm_num)
      (div_nonneg measureReal_nonneg hm.le))
  have hcut0 : 0 ≤ ∫ x, cutoffEnergy χ x :=
    integral_nonneg fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨A * P * r ^ 2 * (8 * ∫ x, cutoffEnergy χ x),
    mul_nonneg (mul_nonneg (mul_nonneg hA0 hP0) (sq_nonneg r))
      (mul_nonneg (by norm_num) hcut0), ?_⟩
  intro δ hδ
  have hL := memLp_logarithm hδ hw
  have hq := memLp_logGradient hδ hw hg
  have hLweak := hasWeakGradOn_logarithm hδ hw hg hweak
  have hLB : MemLp (fun x => logarithm δ (w x)) 2 μB := hL.restrict (ball p r)
  have hqB : ∀ i, MemLp (logGradient δ w g i) 2 μB := fun i => (hq i).restrict (ball p r)
  have hzero : ∀ᵐ x ∂μB.restrict E, logarithm δ (w x) = 0 := by
    change ∀ᵐ x ∂(volume.restrict (ball p r)).restrict E, logarithm δ (w x) = 0
    rw [Measure.restrict_restrict_of_subset hEB]
    exact hwE.mono fun x hx => by rw [hx, logarithm_zero]
  have hanchor := AnchoredL2Estimate.integral_sq_le_anchored hE' hLB hzero
    (⨍ y in ball p r, logarithm δ (w y))
  have hPW := hP p r hr (fun x => logarithm δ (w x)) (logGradient δ w g) hLB hqB
    (hLweak.mono (subset_univ _))
  have hgrad := integral_ball_logGradient_sq_le hD hχ hχone hδ hw hg hweak hw0 hsuper
  refine ⟨hLB, ?_⟩
  calc
    (∫ x in ball p r, logarithm δ (w x) ^ 2) ≤
        A * (∫ x in ball p r,
          (logarithm δ (w x) - ⨍ y in ball p r, logarithm δ (w y)) ^ 2) := hanchor
    _ ≤ A * (P * r ^ 2 * ∫ x in ball p r, ∑ i, logGradient δ w g i x ^ 2) :=
      mul_le_mul_of_nonneg_left hPW hA0
    _ ≤ A * (P * r ^ 2 * (8 * ∫ x, cutoffEnergy χ x)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hgrad (mul_nonneg hP0 (sq_nonneg r))) hA0
    _ = A * P * r ^ 2 * (8 * ∫ x, cutoffEnergy χ x) := by ring

end Buckling.WeakSMPBallLogBound

end

end
