module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.Core1
public import WeakSMPRegularizers
public import EllipticPdes.Embedding.ChainRule

/-!
# The actual nonlinear compact weak test chi squared times R_delta(w)

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
This file produces the actual function, its actual full-space L2 coordinate
gradient, its compact support inside the original test domain, and its weak
gradient identity. The input is an actual full-space L2 weak-H1 function.

R_delta(0) is nonzero. Only R_delta(w)-R_delta(0) is put in global L2; each
compact smooth coefficient times R_delta(w) is then handled by splitting
off the constant. No global L2 assertion for R_delta(w) is made.
Nonnegativity of this test does not require w to be nonnegative.

No supersolution, Caccioppoli, anchored Poincare, or SMP conclusion is claimed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.WeakSMPLogTest

open EllipticPdes EllipticPdes.Embedding WeakSMPRegularizers

def test (δ : ℝ) (χ w : Plane → ℝ) (x : Plane) : ℝ :=
  χ x ^ 2 * reciprocal δ (w x)

def testGradient (δ : ℝ) (χ w : Plane → ℝ) (g : Fin 2 → Plane → ℝ)
    (i : Fin 2) (x : Plane) : ℝ :=
  2 * χ x * pderiv i χ x * reciprocal δ (w x) -
    χ x ^ 2 * (reciprocal δ (w x) / radius δ (w x)) * g i x

/-- The actual bound supplied to the library's global weak chain rule. -/
def reciprocalDerivativeBound (δ : ℝ) : ℝ≥0 :=
  ⟨2 / δ ^ 2, div_nonneg (by norm_num) (sq_nonneg δ)⟩

lemma nnnorm_deriv_reciprocal_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ‖deriv (reciprocal δ) t‖₊ ≤ reciprocalDerivativeBound δ := by
  apply NNReal.coe_le_coe.mp
  simpa only [reciprocalDerivativeBound, NNReal.coe_mk, coe_nnnorm, Real.norm_eq_abs] using!
    abs_deriv_reciprocal_le hδ t

lemma reciprocal_lipschitz {δ : ℝ} (hδ : 0 < δ) :
    LipschitzWith (reciprocalDerivativeBound δ) (reciprocal δ) :=
  lipschitzWith_of_nnnorm_deriv_le
    ((contDiff_reciprocal hδ).differentiable (by simp))
    (nnnorm_deriv_reciprocal_le hδ)

lemma memLp_centered_reciprocal {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ}
    (hw : MemLp w 2 volume) :
    MemLp (fun x => reciprocal δ (w x) - reciprocal δ 0) 2 volume := by
  have hcenter : LipschitzWith (reciprocalDerivativeBound δ)
      (fun t : ℝ => reciprocal δ t - reciprocal δ 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro a b
    simpa only [dist_sub_right] using (reciprocal_lipschitz hδ).dist_le_mul a b
  have h := hcenter.comp_memLp
    (by simp : (fun t : ℝ => reciprocal δ t - reciprocal δ 0) 0 = 0) hw
  simpa only [Function.comp_def] using h

/-- Multiplication by a genuinely bounded measurable coefficient preserves L2. -/
lemma memLp_bounded_mul {a f : Plane → ℝ} (ha : AEStronglyMeasurable a volume)
    (hf : MemLp f 2 volume) (C : ℝ) (hC : ∀ x, |a x| ≤ C) :
    MemLp (fun x => a x * f x) 2 volume := by
  refine (hf.const_mul C).of_le (ha.mul hf.aestronglyMeasurable) ?_
  exact ae_of_all _ fun x => by
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right ((hC x).trans (le_abs_self C)) (abs_nonneg (f x))

lemma memLp_compact_continuous_mul {a f : Plane → ℝ}
    (ha : Continuous a) (hc : HasCompactSupport a) (hf : MemLp f 2 volume) :
    MemLp (fun x => a x * f x) 2 volume := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous ha
  apply memLp_bounded_mul ha.aestronglyMeasurable hf C
  simpa only [Real.norm_eq_abs] using hC

/-- The constant R_delta(0) is multiplied only by the compact coefficient;
this is not an assertion that the uncut R_delta(w) belongs to global L2. -/
lemma memLp_compact_mul_reciprocal {δ : ℝ} (hδ : 0 < δ)
    {a w : Plane → ℝ} (ha : Continuous a) (hc : HasCompactSupport a)
    (hw : MemLp w 2 volume) :
    MemLp (fun x => a x * reciprocal δ (w x)) 2 volume := by
  have hcenter := memLp_compact_continuous_mul ha hc (memLp_centered_reciprocal hδ hw)
  have hconstant : MemLp (fun x => a x * reciprocal δ 0) 2 volume :=
    (ha.memLp_of_hasCompactSupport hc).mul_const (reciprocal δ 0)
  have heq : (fun x => a x * reciprocal δ (w x)) =
      (fun x => a x * (reciprocal δ (w x) - reciprocal δ 0)) +
        (fun x => a x * reciprocal δ 0) := by
    funext x
    simp only [Pi.add_apply]
    ring
  rw [heq]
  exact hcenter.add hconstant

lemma test_nonneg {δ : ℝ} (hδ : 0 < δ) (χ w : Plane → ℝ) (x : Plane) :
    0 ≤ test δ χ w x :=
  mul_nonneg (sq_nonneg (χ x)) (reciprocal_pos hδ (w x)).le

lemma tsupport_test_subset (δ : ℝ) (χ w : Plane → ℝ) :
    tsupport (test δ χ w) ⊆ tsupport χ := by
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hχ
  exact hx (by simp only [test, hχ, zero_pow (by decide : 2 ≠ 0), zero_mul])

lemma hasCompactSupport_test (δ : ℝ) {χ : Plane → ℝ} (hc : HasCompactSupport χ)
    (w : Plane → ℝ) : HasCompactSupport (test δ χ w) :=
  hc.of_isClosed_subset (isClosed_tsupport _) (tsupport_test_subset δ χ w)

lemma memLp_test {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume) :
    MemLp (test δ χ w) 2 volume :=
  memLp_compact_mul_reciprocal hδ (hχ.1.continuous.fun_pow 2)
    (hχ.2.1.comp_left (g := fun t : ℝ => t ^ 2) (by simp)) hw

lemma memLp_testGradient {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume) (i : Fin 2) :
    MemLp (testGradient δ χ w g i) 2 volume := by
  have hac : Continuous (fun x => 2 * χ x * pderiv i χ x) :=
    (continuous_const.mul hχ.1.continuous).mul (hχ.pderiv i).1.continuous
  have hacs : HasCompactSupport (fun x => 2 * χ x * pderiv i χ x) :=
    (hχ.2.1.comp_left (g := fun t : ℝ => 2 * t) (by simp)).mul_right
  have hfirst := memLp_compact_mul_reciprocal hδ hac hacs hw
  have hq : Continuous (fun t : ℝ => reciprocal δ t / radius δ t) :=
    (contDiff_reciprocal hδ).continuous.div (contDiff_radius hδ).continuous
      (fun t => (radius_pos hδ t).ne')
  have hqg : MemLp (fun x => (reciprocal δ (w x) / radius δ (w x)) * g i x) 2 volume := by
    apply memLp_bounded_mul (hq.comp_aestronglyMeasurable hw.aestronglyMeasurable) (hg i)
      (2 / δ ^ 2)
    intro x
    simpa only [abs_of_pos (div_pos (reciprocal_pos hδ (w x)) (radius_pos hδ (w x)))] using
      reciprocal_div_radius_le hδ (w x)
  have hsecond := memLp_compact_continuous_mul (hχ.1.continuous.fun_pow 2)
    (hχ.2.1.comp_left (g := fun t : ℝ => t ^ 2) (by simp)) hqg
  have heq : testGradient δ χ w g i =
      (fun x => (2 * χ x * pderiv i χ x) * reciprocal δ (w x)) -
        (fun x => χ x ^ 2 * ((reciprocal δ (w x) / radius δ (w x)) * g i x)) := by
    funext x
    simp only [testGradient, Pi.sub_apply]
    ring
  rw [heq]
  exact hfirst.sub hsecond

lemma fderiv_square_apply {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    (i : Fin 2) (x : Plane) :
    fderiv ℝ (fun y => χ y ^ 2) x (EuclideanSpace.single i 1) =
      2 * χ x * pderiv i χ x := by
  rw [fderiv_fun_pow 2 (hχ.1.differentiable (by simp) x)]
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat,
    ContinuousLinearMap.smul_apply, smul_eq_mul, pderiv]

/-- Real weak chain rule followed by the actual smooth-product theorem
produces the exact stated coordinate formula. -/
theorem hasWeakGradOn_test {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g) :
    HasWeakGradOn univ (test δ χ w) (testGradient δ χ w g) := by
  have hwF := (hasWeakGradOn_iff_hasWeakFDerivOn isOpen_univ
    ((hw.locallyIntegrable one_le_two).locallyIntegrableOn _)
    (fun i => ((hg i).locallyIntegrable one_le_two).locallyIntegrableOn _)).mp hweak
  have hR1 : ContDiff ℝ 1 (reciprocal δ) :=
    (contDiff_reciprocal hδ).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have hRF := hwF.comp_contDiff hR1 (nnnorm_deriv_reciprocal_le hδ)
  have hPF := hRF.smul_left (hχ.1.pow 2)
  intro η hη hηcs hηs i
  have hcoeff : ∀ x,
      (χ x ^ 2 • (deriv (reciprocal δ) (w x) • gradCLM g x) +
        (fderiv ℝ (fun y => χ y ^ 2) x).smulRight (reciprocal δ (w x)))
          (EuclideanSpace.single i 1) = testGradient δ χ w g i x := by
    intro x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, smul_eq_mul, gradCLM_apply_single,
      fderiv_square_apply hχ, (hasDerivAt_reciprocal hδ (w x)).deriv, testGradient]
    ring
  have hkey := (hPF (EuclideanSpace.single i 1)).integral_eq hη hηcs hηs
  simp only [hcoeff, smul_eq_mul] at hkey
  simpa only [Measure.restrict_univ, test, EllipticPdes.Sobolev.partialD, pderiv,
    mul_comm, mul_left_comm, mul_assoc] using hkey

/-- All actual data needed to feed the compact nonnegative weak-test
closure theorem, without assuming that the nonlinear test is admissible. -/
theorem nonlinear_test_data {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g) :
    (∀ x, 0 ≤ test δ χ w x) ∧ HasCompactSupport (test δ χ w) ∧
      tsupport (test δ χ w) ⊆ D ∧ MemLp (test δ χ w) 2 volume ∧
      (∀ i, MemLp (testGradient δ χ w g i) 2 volume) ∧
      HasWeakGradOn univ (test δ χ w) (testGradient δ χ w g) :=
  ⟨test_nonneg hδ χ w, hasCompactSupport_test δ hχ.2.1 w,
    (tsupport_test_subset δ χ w).trans hχ.2.2, memLp_test hχ hδ hw,
    memLp_testGradient hχ hδ hw hg, hasWeakGradOn_test hχ hδ hw hg hweak⟩

end Buckling.WeakSMPLogTest

end

end
