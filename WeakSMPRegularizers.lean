module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Smooth scalar regularizers for a later weak SMP argument

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
This file proves only real-variable properties of the actual functions
s(delta,t)=sqrt(t^2+delta^2), R(delta,t)=(s(delta,t)-t)/delta^2,
and L(delta,t)=arsinh(t/delta). All derivative bounds are global in t.

These scalar facts do not assert that a nonlinear PDE test is admissible,
or prove a Caccioppoli estimate, anchored Poincare inequality, or SMP.
No weak derivative, PDE, Sobolev, or rigidity result is an input.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace Buckling.WeakSMPRegularizers

def radius (δ t : ℝ) : ℝ := Real.sqrt (t ^ 2 + δ ^ 2)

def reciprocal (δ t : ℝ) : ℝ := (radius δ t - t) / δ ^ 2

def logarithm (δ t : ℝ) : ℝ := Real.arsinh (t / δ)

lemma radius_arg_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < t ^ 2 + δ ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg t) (pow_pos hδ 2)

lemma radius_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < radius δ t :=
  Real.sqrt_pos.mpr (radius_arg_pos hδ t)

lemma radius_sq {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    radius δ t ^ 2 = t ^ 2 + δ ^ 2 :=
  Real.sq_sqrt (radius_arg_pos hδ t).le

lemma abs_lt_radius {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : |t| < radius δ t := by
  change |t| < Real.sqrt (t ^ 2 + δ ^ 2)
  apply (Real.lt_sqrt (abs_nonneg t)).mpr
  rw [sq_abs]
  exact lt_add_of_pos_right _ (pow_pos hδ 2)

lemma delta_le_radius {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : δ ≤ radius δ t := by
  calc
    δ = Real.sqrt (δ ^ 2) := (Real.sqrt_sq hδ.le).symm
    _ ≤ radius δ t := Real.sqrt_le_sqrt (le_add_of_nonneg_left (sq_nonneg t))

lemma radius_add_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < radius δ t + t := by
  have h := abs_lt_radius hδ t
  linarith [neg_abs_le t]

lemma radius_sub_mul_add {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    (radius δ t - t) * (radius δ t + t) = δ ^ 2 := by
  nlinarith [radius_sq hδ t]

lemma reciprocal_eq_one_div {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    reciprocal δ t = 1 / (radius δ t + t) := by
  apply (div_eq_div_iff (pow_pos hδ 2).ne' (radius_add_pos hδ t).ne').mpr
  simpa only [one_mul] using radius_sub_mul_add hδ t

lemma reciprocal_pos {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : 0 < reciprocal δ t := by
  rw [reciprocal_eq_one_div hδ t]
  exact one_div_pos.mpr (radius_add_pos hδ t)

lemma radius_zero {δ : ℝ} (hδ : 0 < δ) : radius δ 0 = δ := by
  simp only [radius, zero_pow (by decide : 2 ≠ 0), zero_add, Real.sqrt_sq hδ.le]

lemma reciprocal_zero {δ : ℝ} (hδ : 0 < δ) : reciprocal δ 0 = 1 / δ := by
  rw [reciprocal_eq_one_div hδ 0, radius_zero hδ, add_zero]

lemma reciprocal_le_one_div_delta {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    reciprocal δ t ≤ 1 / δ := by
  rw [reciprocal_eq_one_div hδ t]
  exact one_div_le_one_div_of_le hδ ((delta_le_radius hδ t).trans (le_add_of_nonneg_right ht))

lemma contDiff_radius {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (radius δ) :=
  ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => (radius_arg_pos hδ t).ne')

lemma contDiff_reciprocal {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (reciprocal δ) :=
  ((contDiff_radius hδ).sub contDiff_id).div_const (δ ^ 2)

lemma contDiff_logarithm (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (logarithm δ) :=
  Real.contDiff_arsinh.comp (contDiff_id.div_const δ)

lemma hasDerivAt_radius {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (radius δ) (t / radius δ t) t := by
  have harg : HasDerivAt (fun x : ℝ => x ^ 2 + δ ^ 2) (2 * t) t := by
    simpa using ((hasDerivAt_id t).fun_pow 2).add_const (δ ^ 2)
  have h := harg.sqrt (radius_arg_pos hδ t).ne'
  apply h.congr_deriv
  change (2 * t) / (2 * radius δ t) = t / radius δ t
  field_simp [(radius_pos hδ t).ne']

lemma hasDerivAt_reciprocal {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (reciprocal δ) (-(reciprocal δ t) / radius δ t) t := by
  have h := ((hasDerivAt_radius hδ t).sub (hasDerivAt_id t)).div_const (δ ^ 2)
  apply h.congr_deriv
  change (t / radius δ t - 1) / δ ^ 2 =
    -((radius δ t - t) / δ ^ 2) / radius δ t
  field_simp [hδ.ne', (radius_pos hδ t).ne'] <;> ring

lemma reciprocal_div_radius_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    reciprocal δ t / radius δ t ≤ 2 / δ ^ 2 := by
  change ((radius δ t - t) / δ ^ 2) / radius δ t ≤ 2 / δ ^ 2
  rw [div_div]
  apply (div_le_div_iff₀ (mul_pos (pow_pos hδ 2) (radius_pos hδ t))
    (pow_pos hδ 2)).mpr
  nlinarith [mul_nonneg (sq_nonneg δ) (radius_add_pos hδ t).le]

lemma abs_deriv_reciprocal_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |deriv (reciprocal δ) t| ≤ 2 / δ ^ 2 := by
  rw [(hasDerivAt_reciprocal hδ t).deriv]
  simpa only [abs_div, abs_neg, abs_of_pos (reciprocal_pos hδ t),
    abs_of_pos (radius_pos hδ t)] using reciprocal_div_radius_le hδ t

lemma sqrt_one_add_div_sq_mul {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    Real.sqrt (1 + (t / δ) ^ 2) * δ = radius δ t := by
  apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hδ.le) (radius_pos hδ t).le).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 1 + (t / δ) ^ 2), radius_sq hδ t]
  field_simp [hδ.ne'] <;> ring

lemma hasDerivAt_logarithm {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    HasDerivAt (logarithm δ) (1 / radius δ t) t := by
  have harg : HasDerivAt (fun x : ℝ => x / δ) (1 / δ) t :=
    (hasDerivAt_id t).div_const δ
  have h := harg.arsinh
  have hcoeff : (Real.sqrt (1 + (t / δ) ^ 2))⁻¹ * (1 / δ) = 1 / radius δ t := by
    calc
      (Real.sqrt (1 + (t / δ) ^ 2))⁻¹ * (1 / δ) =
          (1 / Real.sqrt (1 + (t / δ) ^ 2)) * (1 / δ) := by simp only [one_div]
      _ = 1 / (Real.sqrt (1 + (t / δ) ^ 2) * δ) := by rw [one_div_mul_one_div]
      _ = 1 / radius δ t := by rw [sqrt_one_add_div_sq_mul hδ t]
  simpa only [logarithm, smul_eq_mul, hcoeff] using! h

lemma abs_deriv_logarithm_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |deriv (logarithm δ) t| ≤ 1 / δ := by
  rw [(hasDerivAt_logarithm hδ t).deriv,
    abs_of_pos (one_div_pos.mpr (radius_pos hδ t))]
  exact one_div_le_one_div_of_le hδ (delta_le_radius hδ t)

/-- On the nonnegative half-line, the Caccioppoli cross-term weight is at most one. -/
lemma reciprocal_mul_radius_le_one {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    reciprocal δ t * radius δ t ≤ 1 := by
  rw [reciprocal_eq_one_div hδ t, div_mul_eq_mul_div, one_mul]
  exact (div_le_one (radius_add_pos hδ t)).mpr (le_add_of_nonneg_right ht)

/-- The comparison needed for the logarithm gradient actually holds on the
whole real line; nonnegativity is only needed for the preceding upper bound. -/
lemma one_le_two_mul_reciprocal_mul_radius {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    1 ≤ 2 * reciprocal δ t * radius δ t := by
  have hts : t ≤ radius δ t := (le_abs_self t).trans (abs_lt_radius hδ t).le
  rw [reciprocal_eq_one_div hδ t]
  have heq : 2 * (1 / (radius δ t + t)) * radius δ t =
      (2 * radius δ t) / (radius δ t + t) := by ring
  rw [heq]
  apply (le_div_iff₀ (radius_add_pos hδ t)).mpr
  linarith

lemma one_div_radius_sq_le_two_reciprocal_div_radius {δ : ℝ}
    (hδ : 0 < δ) (t : ℝ) :
    1 / radius δ t ^ 2 ≤ 2 * reciprocal δ t / radius δ t := by
  apply (div_le_iff₀ (pow_pos (radius_pos hδ t) 2)).mpr
  have heq : (2 * reciprocal δ t / radius δ t) * radius δ t ^ 2 =
      2 * reciprocal δ t * radius δ t := by
    field_simp [(radius_pos hδ t).ne'] <;> ring
  rw [heq]
  exact one_le_two_mul_reciprocal_mul_radius hδ t

@[simp] lemma logarithm_zero (δ : ℝ) : logarithm δ 0 = 0 := by
  simp only [logarithm, zero_div, Real.arsinh_zero]

lemma logarithm_nonneg {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) :
    0 ≤ logarithm δ t :=
  Real.arsinh_nonneg_iff.mpr (div_nonneg ht hδ.le)

lemma logarithm_pos {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) :
    0 < logarithm δ t :=
  Real.arsinh_pos_iff.mpr (div_pos ht hδ)

lemma tendsto_arsinh_atTop : Tendsto Real.arsinh atTop atTop := by
  refine tendsto_atTop.mpr fun b => ?_
  filter_upwards [eventually_ge_atTop (Real.sinh b)] with x hx
  have h := Real.arsinh_le_arsinh.mpr hx
  simpa only [Real.arsinh_sinh] using h

/-- Every fixed positive level diverges as the positive regularization
parameter tends to zero; zero itself remains exactly zero. -/
theorem logarithm_tendsto_atTop_delta_zero {t : ℝ} (ht : 0 < t) :
    Tendsto (fun δ : ℝ => logarithm δ t) (𝓝[>] (0 : ℝ)) atTop := by
  have hinv : Tendsto (fun δ : ℝ => δ⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hdiv : Tendsto (fun δ : ℝ => t / δ) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [div_eq_mul_inv] using hinv.const_mul_atTop ht
  simpa only [Function.comp_def, logarithm] using tendsto_arsinh_atTop.comp hdiv

end Buckling.WeakSMPRegularizers

end

end
