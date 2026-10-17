module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.Core1
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.Tactic.NormNum

/-!
# A finite-area L4 bound and tail L2 control for the original test functions

SOURCE_DRAFT (2026-10-17): uncompiled and isolated from production.
The sole analytic node is the planar GNS inequality with derivative exponent
4/3 and output exponent 4, followed by actual finite-measure exponent
comparison. Both the derivative and test function are the original objects.

The domain need not be bounded, open, or measurable. The raw extended-norm
inequality holds even at infinite area; finite area makes its uniform
coefficient finite. Tail control is stated for every actual restricted
volume measure, including volume.restrict (Omega \\ closedBall 0 R).
The last theorem uses exactly the original energy1 (graphH1 phi).

No Rellich compactness, H01 minimizer, weak-gradient extension, or equality
rigidity is assumed or proved in this file. Those are later obligations.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Buckling

/-!
SOURCE_DRAFT, Lean 4.35.0-rc3 only; not compiled.
These actual scalar-energy producers are copied from the verified v4.28
Core2 proof chain, under fresh names. They use the unchanged original
IsTestFn, graphH1, L2 and energy1 definitions from Core1. They add no
assumption on the domain and do not substitute a different gradient norm.
The GNS and tail statements and proofs below are otherwise unchanged.
-/
namespace FiniteAreaCore1

lemma norm_toLp_sq {Ω : Set Plane} {f : Plane → ℝ} (hf : MemLp f 2 (volume.restrict Ω)) :
    ‖hf.toLp f‖ ^ 2 = ∫ x in Ω, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with x hx
  simp [hx, sq]

/-- `‖∇φ‖²` as a sum of squared partial derivatives. -/
lemma norm_fderiv_sq_eq (L : Plane →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = L (EuclideanSpace.single 0 1) ^ 2 + L (EuclideanSpace.single 1 1) ^ 2 := by
  set w := (InnerProductSpace.toDual ℝ Plane).symm L with hw
  have hL : L = InnerProductSpace.toDual ℝ Plane w := by simp [hw]
  have hn : ‖L‖ = ‖w‖ := by rw [hL, LinearIsometryEquiv.norm_map]
  have hi : ∀ i, L (EuclideanSpace.single i 1) = w i := by
    intro i; rw [hL, InnerProductSpace.toDual_apply_apply]; simp [EuclideanSpace.inner_single_right]
  rw [hn, hi, hi, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

lemma integrable_sq {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    Integrable (fun x => φ x ^ 2) := by
  have hc : HasCompactSupport (fun x => φ x ^ 2) :=
    h.2.1.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact (h.1.continuous.fun_pow 2).integrable_of_hasCompactSupport hc

lemma eq_zero_of_notMem {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) {x : Plane}
    (hx : x ∉ Ω) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h' => hx (h.2.2 h'))

lemma sum_pderiv_sq (φ : Plane → ℝ) (x : Plane) :
    pderiv 0 φ x ^ 2 + pderiv 1 φ x ^ 2 = ‖fderiv ℝ φ x‖ ^ 2 := by
  rw [norm_fderiv_sq_eq]; rfl

lemma integral_sq {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    ‖h.toL2‖ ^ 2 = ∫ x, φ x ^ 2 := by
  rw [IsTestFn.toL2, norm_toLp_sq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [eq_zero_of_notMem h hx]

lemma energy1_graphH1 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    energy1 (graphH1 φ) = ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 := by
  simp only [energy1, graphH1, Fin.sum_univ_two, integral_sq]
  rw [← integral_add (integrable_sq (φ.2.pderiv 0)) (integrable_sq (φ.2.pderiv 1))]
  simp only [sum_pderiv_sq]

end FiniteAreaCore1

/-- The actual GNS constant is independent of both the domain and the test
function. Its value is not used, only its ordinary nonnegative-real type. -/
def planarTestL4GNSConstant : ℝ≥0 :=
  SNormLESNormFDerivOfEqConst ℝ (volume : Measure Plane) (4 / 3)

/-- The derivative really vanishes off the domain: its support is contained
in the topological support from the original test-function definition. -/
lemma IsTestFn.support_fderiv_subset_domain {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) : Function.support (fderiv ℝ φ) ⊆ Ω :=
  (support_fderiv_subset ℝ).trans hφ.2.2

/-- Finite-measure exponent comparison is applied to the actual restricted
volume, and support equality then recovers the full-space derivative norms. -/
lemma IsTestFn.eLpNorm_fderiv_four_thirds_le {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) :
    eLpNorm (fderiv ℝ φ) (4 / 3 : ℝ≥0∞) volume ≤
      eLpNorm (fderiv ℝ φ) 2 volume * volume Ω ^ (1 / 4 : ℝ) := by
  have hMeas : AEStronglyMeasurable (fderiv ℝ φ) volume :=
    (hφ.1.continuous_fderiv (by simp)).aestronglyMeasurable
  have hP : (4 / 3 : ℝ≥0∞) ≤ 2 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).2
    norm_num
  have hCompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict Ω) (f := fderiv ℝ φ)
    (p := (4 / 3 : ℝ≥0∞)) (q := 2) hP hMeas.restrict
  have hExponent : 1 / (4 / 3 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal =
      (1 / 4 : ℝ) := by norm_num
  have hRestrict (p : ℝ≥0∞) :
      eLpNorm (fderiv ℝ φ) p (volume.restrict Ω) =
        eLpNorm (fderiv ℝ φ) p volume := by
    apply eLpNorm_restrict_eq_of_support_subset
      (f := fderiv ℝ φ) (p := p) (μ := volume) (s := Ω) hMeas
    exact hφ.support_fderiv_subset_domain
  simpa only [hExponent, Measure.restrict_apply_univ, hRestrict] using hCompare

/-- A genuine planar L4 estimate, using GNS at 4/3 rather than the excluded
two-dimensional endpoint p=2. No boundedness of the domain is used. -/
lemma IsTestFn.eLpNorm_four_le {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) :
    eLpNorm φ 4 volume ≤
      ((planarTestL4GNSConstant : ℝ≥0∞) * volume Ω ^ (1 / 4 : ℝ)) *
        eLpNorm (fderiv ℝ φ) 2 volume := by
  have hC1 : ContDiff ℝ 1 φ := hφ.1.of_le (by simp)
  have hGNS : eLpNorm φ 4 volume ≤
      (planarTestL4GNSConstant : ℝ≥0∞) *
        eLpNorm (fderiv ℝ φ) (4 / 3 : ℝ≥0∞) volume := by
    have hP : (1 : ℝ≥0) ≤ 4 / 3 := by
      apply NNReal.coe_le_coe.mp
      norm_num
    have h := eLpNorm_le_eLpNorm_fderiv_of_eq (μ := volume) hC1 hφ.2.1
      (p := (4 / 3 : ℝ≥0)) (p' := 4) hP
      (by simp [Plane]) (by norm_num [Plane])
    simpa [planarTestL4GNSConstant] using h
  calc
    eLpNorm φ 4 volume ≤ (planarTestL4GNSConstant : ℝ≥0∞) *
        eLpNorm (fderiv ℝ φ) (4 / 3 : ℝ≥0∞) volume := hGNS
    _ ≤ (planarTestL4GNSConstant : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ φ) 2 volume * volume Ω ^ (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hφ.eLpNorm_fderiv_four_thirds_le (by positivity)
    _ = _ := by ac_rfl

/-- The actual L2 norm on an arbitrary tail set is controlled by its volume
and the global L4 norm. This does not require a common bounded support. -/
lemma IsTestFn.eLpNorm_two_restrict_le_four {Ω T : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) :
    eLpNorm φ 2 (volume.restrict T) ≤
      eLpNorm φ 4 volume * volume T ^ (1 / 4 : ℝ) := by
  have hCompare := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (μ := volume.restrict T) (f := φ) (p := 2) (q := 4)
    (by norm_num) hφ.1.continuous.aestronglyMeasurable.restrict
  have hExponent : 1 / (2 : ℝ≥0∞).toReal - 1 / (4 : ℝ≥0∞).toReal =
      (1 / 4 : ℝ) := by norm_num
  calc
    eLpNorm φ 2 (volume.restrict T) ≤
        eLpNorm φ 4 (volume.restrict T) * volume T ^ (1 / 4 : ℝ) := by
      simpa only [hExponent, Measure.restrict_apply_univ] using hCompare
    _ ≤ eLpNorm φ 4 volume * volume T ^ (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_right (eLpNorm_restrict_le φ 4 volume T) (by positivity)

/-- The full-space derivative norm is exactly the square root of the real
integral used by the project, not a replacement gradient norm. -/
lemma IsTestFn.eLpNorm_fderiv_two_eq_integral {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : IsTestFn Ω φ) :
    eLpNorm (fderiv ℝ φ) 2 volume =
      ENNReal.ofReal ((∫ x, ‖fderiv ℝ φ x‖ ^ 2) ^ (1 / 2 : ℝ)) := by
  have hMem : MemLp (fderiv ℝ φ) 2 volume :=
    (hφ.1.continuous_fderiv (by simp)).memLp_of_hasCompactSupport
      (hφ.2.1.fderiv (𝕜 := ℝ))
  have h := hMem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, one_div] using h

/-- Explicit bridge to the original graph closure's energy1. -/
lemma eLpNorm_fderiv_two_eq_graphH1_energy1 {Ω : Set Plane}
    (φ : {φ // IsTestFn Ω φ}) :
    eLpNorm (fderiv ℝ φ.1) 2 volume =
      ENNReal.ofReal ((energy1 (graphH1 φ)) ^ (1 / 2 : ℝ)) := by
  rw [FiniteAreaCore1.energy1_graphH1]
  exact φ.2.eLpNorm_fderiv_two_eq_integral

/-- One finite coefficient works for every original smooth test function,
and for every tail set, on an arbitrary finite-area domain. This is a
preliminary estimate for finite-area Rellich, not that compactness theorem. -/
theorem test_l4_and_tail_l2_bounds_finite_area {Ω : Set Plane}
    (hfin : volume Ω < ⊤) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ φ : {φ // IsTestFn Ω φ},
      eLpNorm φ.1 4 volume ≤
        C * ENNReal.ofReal ((energy1 (graphH1 φ)) ^ (1 / 2 : ℝ)) ∧
      ∀ T : Set Plane, eLpNorm φ.1 2 (volume.restrict T) ≤
        (C * ENNReal.ofReal ((energy1 (graphH1 φ)) ^ (1 / 2 : ℝ))) *
          volume T ^ (1 / 4 : ℝ) := by
  let C : ℝ≥0∞ :=
    (planarTestL4GNSConstant : ℝ≥0∞) * volume Ω ^ (1 / 4 : ℝ)
  refine ⟨C, ?_, ?_⟩
  · exact ENNReal.mul_lt_top (by simp)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne)
  · intro φ
    have hL4 : eLpNorm φ.1 4 volume ≤
        C * ENNReal.ofReal ((energy1 (graphH1 φ)) ^ (1 / 2 : ℝ)) := by
      rw [← eLpNorm_fderiv_two_eq_graphH1_energy1 φ]
      exact φ.2.eLpNorm_four_le
    refine ⟨hL4, fun T => ?_⟩
    exact (φ.2.eLpNorm_two_restrict_le_four (T := T)).trans
      (mul_le_mul_of_nonneg_right hL4 (by positivity))

end Buckling

end

end
