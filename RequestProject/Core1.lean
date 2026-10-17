module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/
public import Mathlib

/- CONDITIONAL, UNCOMPILED structural experiment. See README.md. -/

/- BEGIN SOURCE 000: RequestProject/Audit/OldResidueFalse.lean -/
section ChunkedSource000

/-!
# Audit: the earlier hypothesis form of E6 was false

An earlier version of this development assumed the residue theorem in the form `OldResidue`
below, without the condition `N ≥ 1` on the number of principal-part terms. With `N = 0` the
principal parts vanish, so the statement asserts `∮ h = 2πi ∑_{a ∈ S} P(a,0)` for every
holomorphic `h` and every choice of `P`. That is false. Hence the earlier bundle of external
hypotheses could not be satisfied, and results proved from it held vacuously.

The current development does not assume any form of E6. It proves the correct statement
(`Buckling.circleIntegral_eq_explicit_residues`, with `0 < N`).
-/

@[expose] public section

namespace Buckling.Audit

/-- The earlier, incorrect hypothesis form of the residue part of E6 (kept only so that it
can be refuted). -/
def OldResidue : Prop :=
  ∀ (R : ℝ) (h g : ℂ → ℂ) (S : Finset ℂ) (N : ℕ) (P : ℂ → ℕ → ℂ) (U : Set ℂ),
      0 < R → IsOpen U → Metric.closedBall 0 R ⊆ U → (↑S : Set ℂ) ⊆ Metric.ball 0 R →
      DifferentiableOn ℂ g U →
      (∀ ζ ∈ U \ ↑S, h ζ = g ζ + ∑ a ∈ S, ∑ j ∈ Finset.range N, P a j / (ζ - a) ^ (j + 1)) →
      (∮ ζ in C(0, R), h ζ) = 2 * Real.pi * Complex.I * ∑ a ∈ S, P a 0

/-- The earlier hypothesis form of E6 is false (take `N = 0`, `h = g = 0`, `S = {0}`,
`P ≡ 1`). -/
theorem not_oldResidue : ¬ OldResidue := by
  intro H
  have := H 1 (fun _ => 0) (fun _ => 0) {0} 0 (fun _ _ => 1) Set.univ one_pos isOpen_univ
    (Set.subset_univ _) (by simp) (differentiableOn_const 0) (by simp)
  simp [circleIntegral] at this

end Buckling.Audit
end
end ChunkedSource000
/- END SOURCE 000 -/

/- BEGIN SOURCE 001: RequestProject/Bessel/Asymptotic/Fresnel.lean -/
section ChunkedSource001

/-!
# Finite Fresnel-type integrals

For `Re b ≥ 0`, `b ≠ 0`:
`∫₀¹ e^{-b s²} ds = (π/b)^{1/2}/2 - e^{-b}/(2b) + O(|b|^{-2})`.
The case `Re b > 0` follows from the Gaussian integral and two integrations by parts on
`(1, ∞)`; the case `Re b = 0` (Fresnel integrals) follows by continuity.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set

namespace Buckling

lemma norm_cexp_neg_mul_sq_le {b : ℂ} (hb : 0 ≤ b.re) (s : ℝ) : ‖cexp (-b * s ^ 2)‖ ≤ 1 := by
  rw [Complex.norm_exp]
  apply Real.exp_le_one_iff.mpr
  have : (-b * (s:ℂ) ^ 2).re = -b.re * s ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal, Complex.neg_re]
  rw [this]; nlinarith [sq_nonneg s]

lemma integrableOn_Ioi_div_pow_mul_gauss {b : ℂ} (hb : 0 < b.re) (c : ℂ) (k : ℕ) :
    IntegrableOn (fun s : ℝ => c / (s:ℂ) ^ k * cexp (-b * s ^ 2)) (Ioi 1) := by
  have hg : Integrable (fun s : ℝ => cexp (-b * (s:ℂ) ^ 2)) := integrable_cexp_neg_mul_sq hb
  refine (hg.integrableOn.norm.const_mul ‖c‖).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro s hs
    have : (s:ℂ) ≠ 0 := by exact_mod_cast (show (0:ℝ) < s by linarith [mem_Ioi.mp hs]).ne'
    have h1 : ContinuousAt (fun s : ℝ => (s:ℂ) ^ k) s :=
      (Complex.continuous_ofReal.pow k).continuousAt
    have h2 : ContinuousAt (fun s : ℝ => cexp (-b * (s:ℂ) ^ 2)) s :=
      (by fun_prop : Continuous fun s : ℝ => cexp (-b * (s:ℂ) ^ 2)).continuousAt
    exact ((continuousAt_const.div h1 (pow_ne_zero _ this)).mul h2).continuousWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    have hs1 : (1:ℝ) ≤ s := (mem_Ioi.mp hs).le
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have : 1 ≤ s ^ k := one_le_pow₀ hs1
    gcongr
    exact div_le_self (norm_nonneg _) this

/-- Two integrations by parts for the Gaussian tail. -/
lemma gauss_tail (b : ℂ) (hb : 0 < b.re) :
    ‖(∫ s in Ioi (1:ℝ), cexp (-b * s ^ 2)) - cexp (-b) / (2 * b)‖ ≤ 1 / ‖b‖ ^ 2 := by
  have hb0 : b ≠ 0 := fun h => by rw [h] at hb; simp at hb
  set v : ℝ → ℂ := fun s => cexp (-b * s ^ 2) with hv
  have hvd : ∀ s : ℝ, HasDerivAt v (-2 * b * s * cexp (-b * s ^ 2)) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -b * (s:ℂ) ^ 2) (-b * (2 * s)) s := by
      have := ((hasDerivAt_id s).ofReal_comp.pow 2).const_mul (-b)
      simpa using this
    convert h1.cexp using 1; ring
  have hs0 : ∀ s ∈ Ioi (1:ℝ), (s:ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (show (0:ℝ) < s by linarith [mem_Ioi.mp hs]).ne'
  -- the boundary term at `∞`
  have hlim : ∀ (c : ℂ) (k : ℕ), 1 ≤ k →
      Tendsto (fun s : ℝ => c / (s:ℂ) ^ k * v s) atTop (𝓝 0) := by
    intro c k hk
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := ‖c‖)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop (1:ℝ)] with s hs
    rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    have h1 : ‖v s‖ ≤ 1 := norm_cexp_neg_mul_sq_le hb.le s
    have h2 : s ≤ s ^ k := by
      calc s = s ^ 1 := (pow_one s).symm
        _ ≤ s ^ k := pow_le_pow_right₀ hs hk
    calc ‖c‖ / s ^ k * ‖v s‖ ≤ ‖c‖ / s ^ k * 1 := by gcongr
      _ ≤ ‖c‖ / s := by rw [mul_one]; gcongr
      _ = _ := rfl
  have hcont : ∀ (c : ℂ) (k : ℕ),
      Tendsto (fun s : ℝ => c / (s:ℂ) ^ k * v s) (𝓝[>] 1) (𝓝 (c * v 1)) := by
    intro c k
    have : ContinuousAt (fun s : ℝ => c / (s:ℂ) ^ k * v s) 1 :=
      (continuousAt_const.div (by fun_prop) (by simp)).mul (by fun_prop)
    have h := this.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (1:ℝ)))
    simpa using h
  have hpowd : ∀ (c : ℂ) (k : ℕ), ∀ s ∈ Ioi (1:ℝ),
      HasDerivAt (fun s : ℝ => c / (s:ℂ) ^ k) (-(k:ℂ) * c / (s:ℂ) ^ (k + 1)) s := by
    intro c k s hs
    have hs' := hs0 s hs
    have h1 : HasDerivAt (fun s : ℝ => (s:ℂ) ^ k) ((k:ℂ) * (s:ℂ) ^ (k - 1)) s := by
      simpa using! (hasDerivAt_id s).ofReal_comp.fun_pow k
    have h2 := (hasDerivAt_const s c).div h1 (pow_ne_zero k hs')
    convert h2 using 1
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      field_simp
      ring
  -- first integration by parts
  have ibp1 := integral_Ioi_mul_deriv_eq_deriv_mul (a := 1) (a' := (-1 / (2 * b)) * v 1)
    (b' := 0) (u := fun s => (-1 / (2 * b)) / (s:ℂ) ^ 1) (v := v)
    (u' := fun s => (1 / (2 * b)) / (s:ℂ) ^ 2) (v' := fun s => -2 * b * s * cexp (-b * s ^ 2))
    (fun s hs => by
      convert hpowd (-1 / (2 * b)) 1 s hs using 1
      push_cast; ring)
    (fun s _ => hvd s)
    (by
      refine (integrable_cexp_neg_mul_sq hb).integrableOn.congr_fun (fun s hs => ?_)
        measurableSet_Ioi
      simp only [Pi.mul_apply]; field_simp [hs0 s hs])
    (by
      refine (integrableOn_Ioi_div_pow_mul_gauss hb (1 / (2 * b)) 2).congr_fun
        (fun s _ => rfl) measurableSet_Ioi)
    (by simpa using! hcont (-1 / (2 * b)) 1)
    (by simpa using! hlim (-1 / (2 * b)) 1 le_rfl)
  -- second integration by parts
  have ibp2 := integral_Ioi_mul_deriv_eq_deriv_mul (a := 1) (a' := (-1 / (4 * b ^ 2)) * v 1)
    (b' := 0) (u := fun s => (-1 / (4 * b ^ 2)) / (s:ℂ) ^ 3) (v := v)
    (u' := fun s => (3 / (4 * b ^ 2)) / (s:ℂ) ^ 4)
    (v' := fun s => -2 * b * s * cexp (-b * s ^ 2))
    (fun s hs => by
      convert hpowd (-1 / (4 * b ^ 2)) 3 s hs using 1
      push_cast; ring)
    (fun s _ => hvd s)
    (by
      refine (integrableOn_Ioi_div_pow_mul_gauss hb (1 / (2 * b)) 2).congr_fun
        (fun s hs => ?_) measurableSet_Ioi
      simp only [Pi.mul_apply]; field_simp [hs0 s hs]; ring)
    (by
      refine (integrableOn_Ioi_div_pow_mul_gauss hb (3 / (4 * b ^ 2)) 4).congr_fun
        (fun s _ => rfl) measurableSet_Ioi)
    (by simpa using! hcont (-1 / (4 * b ^ 2)) 3)
    (by simpa using! hlim (-1 / (4 * b ^ 2)) 3 (by norm_num))
  beta_reduce at ibp1 ibp2
  -- rewrite the integrands
  have e1 : ∫ s in Ioi (1:ℝ), (-1 / (2 * b)) / (s:ℂ) ^ 1 * (-2 * b * s * cexp (-b * s ^ 2)) =
      ∫ s in Ioi (1:ℝ), cexp (-b * s ^ 2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    field_simp [hs0 s hs]
  have e2 : ∫ s in Ioi (1:ℝ), (1 / (2 * b)) / (s:ℂ) ^ 2 * v s =
      ∫ s in Ioi (1:ℝ), (-1 / (4 * b ^ 2)) / (s:ℂ) ^ 3 * (-2 * b * s * cexp (-b * s ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [v]; field_simp [hs0 s hs]; ring
  rw [e1] at ibp1
  rw [e2, ibp2] at ibp1
  have hv1 : v 1 = cexp (-b) := by simp [v]
  rw [hv1] at ibp1
  rw [ibp1]
  -- the remaining integral
  set R := ∫ s in Ioi (1:ℝ), (3 / (4 * b ^ 2)) / (s:ℂ) ^ 4 * v s
  have hR : ‖R‖ ≤ 3 / (4 * ‖b‖ ^ 2) * (1 / 3) := by
    have hint : IntegrableOn (fun s : ℝ => 3 / (4 * ‖b‖ ^ 2) * s ^ (-4 : ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    have hval : ∫ s in Ioi (1:ℝ), 3 / (4 * ‖b‖ ^ 2) * s ^ (-4 : ℝ) = 3 / (4 * ‖b‖ ^ 2) * (1 / 3) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
      norm_num
    rw [← hval]
    refine norm_integral_le_of_norm_le hint ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun s hs => ?_)
    have hs1 : (1:ℝ) < s := mem_Ioi.mp hs
    rw [norm_mul, norm_div, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith), norm_mul, norm_pow]
    have h1 : ‖v s‖ ≤ 1 := norm_cexp_neg_mul_sq_le hb.le s
    have h4 : s ^ (-4 : ℝ) = 1 / s ^ 4 := by
      rw [Real.rpow_neg (by linarith), one_div]; norm_cast
    rw [h4]
    have : ‖(3:ℂ)‖ = 3 := by simp
    have h44 : ‖(4:ℂ)‖ = 4 := by simp
    rw [this, h44]
    have hs4 : 0 < s ^ 4 := by positivity
    calc 3 / (4 * ‖b‖ ^ 2) / s ^ 4 * ‖v s‖ ≤ 3 / (4 * ‖b‖ ^ 2) / s ^ 4 * 1 := by gcongr
      _ = _ := by ring
  have hE : ‖cexp (-b)‖ ≤ 1 := by
    have := norm_cexp_neg_mul_sq_le hb.le 1
    simpa using this
  have hbn : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have key : (0 - -1 / (2 * b) * cexp (-b) - (0 - -1 / (4 * b ^ 2) * cexp (-b) - R)) -
      cexp (-b) / (2 * b) = -(cexp (-b) / (4 * b ^ 2)) + R := by
    field_simp; ring
  rw [key]
  calc ‖-(cexp (-b) / (4 * b ^ 2)) + R‖ ≤ ‖cexp (-b) / (4 * b ^ 2)‖ + ‖R‖ := by
        rw [← norm_neg (cexp (-b) / (4 * b ^ 2))]; exact norm_add_le _ _
    _ ≤ 1 / (4 * ‖b‖ ^ 2) + 3 / (4 * ‖b‖ ^ 2) * (1 / 3) := by
        gcongr
        rw [norm_div, norm_mul, norm_pow]
        have : ‖(4:ℂ)‖ = 4 := by simp
        rw [this]
        gcongr
    _ ≤ 1 / ‖b‖ ^ 2 := by
        have hb2 : 0 < ‖b‖ ^ 2 := by positivity
        have : 1 / (4 * ‖b‖ ^ 2) + 3 / (4 * ‖b‖ ^ 2) * (1 / 3) = 1 / (2 * ‖b‖ ^ 2) := by
          field_simp; ring
        rw [this]
        exact div_le_div_of_nonneg_left zero_le_one hb2 (by linarith)

/-- `G(b) = ∫₀¹ e^{-b s²} ds`. -/
noncomputable def gauss01 (b : ℂ) : ℂ := ∫ s in (0:ℝ)..1, cexp (-b * s ^ 2)

/-- The model `(π/b)^{1/2}/2 - e^{-b}/(2b)`. -/
noncomputable def gaussModel (b : ℂ) : ℂ := ((π : ℂ) / b) ^ (1 / 2 : ℂ) / 2 - cexp (-b) / (2 * b)

lemma gauss01_asymp_of_re_pos {b : ℂ} (hb : 0 < b.re) :
    ‖gauss01 b - gaussModel b‖ ≤ 1 / ‖b‖ ^ 2 := by
  have hg : Integrable (fun s : ℝ => cexp (-b * (s:ℂ) ^ 2)) := integrable_cexp_neg_mul_sq hb
  have h := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := 1) hg.integrableOn
    hg.integrableOn
  rw [integral_gaussian_complex_Ioi hb] at h
  have e : gauss01 b - gaussModel b =
      -((∫ s in Ioi (1:ℝ), cexp (-b * s ^ 2)) - cexp (-b) / (2 * b)) := by
    unfold gauss01 gaussModel
    linear_combination h
  rw [e, norm_neg]
  exact gauss_tail b hb

lemma continuousAt_gauss01 (b : ℂ) : ContinuousAt gauss01 b := by
  have : Continuous gauss01 := by
    unfold gauss01
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (c : ℂ) (s : ℝ) => cexp (-c * s ^ 2)) (by fun_prop) continuous_const
  exact this.continuousAt

lemma continuousAt_gaussModel {b : ℂ} (hb : 0 ≤ b.re) (hb0 : b ≠ 0) :
    ContinuousAt gaussModel b := by
  unfold gaussModel
  have hπb : 0 ≤ ((π : ℂ) / b).re ∨ ((π : ℂ) / b).im ≠ 0 := by
    left
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul]
    exact add_nonneg (div_nonneg (mul_nonneg Real.pi_pos.le hb) (Complex.normSq_nonneg _))
      (by simp)
  have h1 : ContinuousAt (fun c : ℂ => (π : ℂ) / c) b := continuousAt_const.div continuousAt_id hb0
  have h2 := (Complex.continuousAt_cpow_const_of_re_pos hπb (by norm_num : (0:ℝ) < (1/2 : ℂ).re))
  refine ((h2.comp h1).div_const 2).sub ?_
  exact ((by fun_prop : Continuous fun c : ℂ => cexp (-c)).continuousAt).div
    (continuousAt_const.mul continuousAt_id) (by simpa using hb0)

/-- **Finite Gaussian/Fresnel integral**: for `Re b ≥ 0`, `b ≠ 0`,
`|∫₀¹ e^{-bs²} ds - (π/b)^{1/2}/2 + e^{-b}/(2b)| ≤ |b|^{-2}`. -/
theorem gauss01_asymp {b : ℂ} (hb : 0 ≤ b.re) (hb0 : b ≠ 0) :
    ‖gauss01 b - gaussModel b‖ ≤ 1 / ‖b‖ ^ 2 := by
  have hpath : Tendsto (fun ε : ℝ => b + ε) (𝓝[>] 0) (𝓝 b) := by
    have : Tendsto (fun ε : ℝ => b + ε) (𝓝 0) (𝓝 (b + ((0:ℝ):ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hF : ContinuousAt (fun c => ‖gauss01 c - gaussModel c‖) b :=
    ((continuousAt_gauss01 b).sub (continuousAt_gaussModel hb hb0)).norm
  have hG : ContinuousAt (fun c : ℂ => 1 / ‖c‖ ^ 2) b :=
    continuousAt_const.div (continuous_norm.continuousAt.pow 2) (by simpa using hb0)
  refine le_of_tendsto_of_tendsto (hF.tendsto.comp hpath) (hG.tendsto.comp hpath) ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hre : 0 < (b + ε).re := by simp; linarith [mem_Ioi.mp hε]
  exact gauss01_asymp_of_re_pos hre

lemma norm_cpow_half {w : ℂ} (hw : w ≠ 0) : ‖w ^ (1 / 2 : ℂ)‖ = Real.sqrt ‖w‖ := by
  rw [Complex.norm_cpow_of_ne_zero hw]
  have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have h2 : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [h1, h2, mul_zero, Real.exp_zero, div_one, Real.sqrt_eq_rpow]

/-- A crude bound `|G(b)| ≤ 3/√|b|` for `Re b ≥ 0`, `|b| ≥ 1`. -/
lemma norm_gauss01_le {b : ℂ} (hb : 0 ≤ b.re) (hb1 : 1 ≤ ‖b‖) :
    ‖gauss01 b‖ ≤ 3 / Real.sqrt ‖b‖ := by
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hb1; linarith
  have hn : 0 < ‖b‖ := by linarith
  have hs : 0 < Real.sqrt ‖b‖ := Real.sqrt_pos.mpr hn
  have hss : Real.sqrt ‖b‖ ^ 2 = ‖b‖ := Real.sq_sqrt hn.le
  have hs1 : 1 ≤ Real.sqrt ‖b‖ := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hb1
  have h := gauss01_asymp hb hb0
  have hM : ‖gaussModel b‖ ≤ 1 / Real.sqrt ‖b‖ + 1 / (2 * Real.sqrt ‖b‖) := by
    unfold gaussModel
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_div, Complex.norm_two, norm_cpow_half (div_ne_zero (by exact_mod_cast
        Real.pi_ne_zero) hb0), norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos, Real.sqrt_div' _ hn.le]
      rw [div_div, div_le_div_iff₀ (by positivity) hs]
      have := Real.sqrt_le_sqrt (show π ≤ 4 by linarith [Real.pi_lt_d2])
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this
      nlinarith
    · rw [norm_div, norm_mul, Complex.norm_two]
      have hE : ‖cexp (-b)‖ ≤ 1 := by simpa using norm_cexp_neg_mul_sq_le hb 1
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
  have hR : 1 / ‖b‖ ^ 2 ≤ 1 / Real.sqrt ‖b‖ := by
    apply one_div_le_one_div_of_le hs
    calc Real.sqrt ‖b‖ ≤ Real.sqrt ‖b‖ ^ 2 := by nlinarith
      _ = ‖b‖ := hss
      _ ≤ ‖b‖ ^ 2 := by nlinarith
  calc ‖gauss01 b‖ ≤ ‖gauss01 b - gaussModel b‖ + ‖gaussModel b‖ := by
        have := norm_add_le (gauss01 b - gaussModel b) (gaussModel b)
        simpa using this
    _ ≤ 1 / Real.sqrt ‖b‖ + (1 / Real.sqrt ‖b‖ + 1 / (2 * Real.sqrt ‖b‖)) := add_le_add (h.trans hR) hM
    _ ≤ 3 / Real.sqrt ‖b‖ := by
        have : 1 / Real.sqrt ‖b‖ + (1 / Real.sqrt ‖b‖ + 1 / (2 * Real.sqrt ‖b‖)) =
            (5 / 2) / Real.sqrt ‖b‖ := by field_simp; ring
        rw [this]
        exact div_le_div_of_nonneg_right (by norm_num) hs.le

/-- **Partial Fresnel integrals**: `|∫₀ᵗ e^{-ixs²} ds| ≤ 3/√x` for `x > 0`, `0 ≤ t`. -/
theorem norm_partial_fresnel_le {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : 0 ≤ t) :
    ‖∫ s in (0:ℝ)..t, cexp (-((x:ℂ) * I) * s ^ 2)‖ ≤ 3 / Real.sqrt x := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · simp; positivity
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsub : ∫ s in (0:ℝ)..t, cexp (-((x:ℂ) * I) * s ^ 2) = t • gauss01 ((x * t ^ 2 : ℝ) * I) := by
    unfold gauss01
    have := intervalIntegral.integral_comp_mul_left
      (fun s : ℝ => cexp (-((x:ℂ) * I) * s ^ 2)) (a := 0) (b := 1) ht'.ne'
    simp only [mul_zero, mul_one] at this
    have e : (∫ σ in (0:ℝ)..1, cexp (-(((x * t ^ 2 : ℝ) : ℂ) * I) * σ ^ 2)) =
        ∫ σ in (0:ℝ)..1, cexp (-((x:ℂ) * I) * ((t * σ : ℝ) : ℂ) ^ 2) := by
      congr 1; funext σ; congr 1; push_cast; ring
    rw [e, this, smul_smul, mul_inv_cancel₀ ht'.ne', one_smul]
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ht']
  set b : ℂ := ((x * t ^ 2 : ℝ) : ℂ) * I
  have hbn : ‖b‖ = x * t ^ 2 := by
    simp only [b, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    rw [abs_of_pos hx, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
  have hre : 0 ≤ b.re := by simp only [b, Complex.re_ofReal_mul, Complex.I_re, mul_zero, le_refl]
  rcases le_or_gt 1 (x * t ^ 2) with h1 | h1
  · 
    have hg := norm_gauss01_le hre (hbn ▸ h1)
    rw [hbn, Real.sqrt_mul hx.le, Real.sqrt_sq ht] at hg
    calc t * ‖gauss01 b‖ ≤ t * (3 / (Real.sqrt x * t)) := by gcongr
      _ = 3 / Real.sqrt x := by field_simp
  · have hg : ‖gauss01 b‖ ≤ 1 := by
      unfold gauss01
      calc _ ≤ ∫ s in (0:ℝ)..1, ‖cexp (-b * s ^ 2)‖ :=
            intervalIntegral.norm_integral_le_integral_norm zero_le_one
        _ ≤ ∫ s in (0:ℝ)..1, (1:ℝ) := by
            refine intervalIntegral.integral_mono_on zero_le_one ?_ intervalIntegrable_const
              (fun s _ => norm_cexp_neg_mul_sq_le hre s)
            exact (by fun_prop : Continuous fun s : ℝ => ‖cexp (-b * (s:ℂ) ^ 2)‖).intervalIntegrable _ _
        _ = 1 := by simp
    have ht1 : t * Real.sqrt x < 1 := by
      have : (t * Real.sqrt x) ^ 2 < 1 := by rw [mul_pow, Real.sq_sqrt hx.le]; linarith
      nlinarith [mul_pos ht' hsx]
    calc t * ‖gauss01 b‖ ≤ t * 1 := by gcongr
      _ ≤ 3 / Real.sqrt x := by rw [le_div_iff₀ hsx]; linarith

end Buckling
end
end ChunkedSource001
/- END SOURCE 001 -/

/- BEGIN SOURCE 002: RequestProject/Bessel/Asymptotic/Oscillatory.lean -/
section ChunkedSource002

/-!
# Oscillatory integrals `∫₀¹ g(s) e^{-ixs²} ds` for large real `x`

* `norm_osc_le`: `|∫₀¹ h(s) e^{-ixs²} ds| ≤ 3 x^{-1/2} (|h(1)| + ∫₀¹ |h'|)`;
* `osc_asymp`: if `g(s) = g(0) + s k(s)` with `k(0) = 0` and `k` of class `C²` near `[0,1]`,
  then `∫₀¹ g(s) e^{-ixs²} ds = g(0)(π/(ix))^{1/2}/2 - g(1) e^{-ix}/(2ix) + O(x^{-3/2})`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set

namespace Buckling

/-- The oscillatory factor `e^{-ixs²}`. -/
noncomputable abbrev oscF (x s : ℝ) : ℂ := cexp (-((x:ℂ) * I) * (s:ℂ) ^ 2)

lemma continuous_oscF (x : ℝ) : Continuous (oscF x) := by unfold oscF; fun_prop

lemma norm_oscF (x s : ℝ) : ‖oscF x s‖ = 1 := by
  unfold oscF
  rw [show -((x:ℂ) * I) * (s:ℂ) ^ 2 = ((-(x * s ^ 2) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- **Oscillatory bound** via the bounded partial Fresnel integrals. -/
theorem norm_osc_le {x : ℝ} (hx : 0 < x) {h h' : ℝ → ℂ}
    (hd : ∀ s ∈ Icc (0:ℝ) 1, HasDerivAt h (h' s) s) (hc : ContinuousOn h' (Icc 0 1)) :
    ‖∫ s in (0:ℝ)..1, h s * oscF x s‖ ≤
      3 / Real.sqrt x * (‖h 1‖ + ∫ s in (0:ℝ)..1, ‖h' s‖) := by
  set E : ℝ → ℂ := fun t => ∫ s in (0:ℝ)..t, oscF x s with hE
  have hEd : ∀ t, HasDerivAt E (oscF x t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right ((continuous_oscF x).intervalIntegrable _ _)
      ((continuous_oscF x).stronglyMeasurableAtFilter _ _) (continuous_oscF x).continuousAt
  have hEb : ∀ t, 0 ≤ t → ‖E t‖ ≤ 3 / Real.sqrt x := fun t ht => norm_partial_fresnel_le hx ht
  have hIcc : uIcc (0:ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := h)
    (v := E) (u' := h') (v' := oscF x) (fun s hs => hd s (hIcc ▸ hs)) (fun s _ => hEd s)
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
        exact hc.integrableOn_Icc)
    ((continuous_oscF x).intervalIntegrable _ _)
  have hE0 : E 0 = 0 := by simp [E]
  rw [ibp, hE0, mul_zero, sub_zero]
  have hsx : 0 ≤ 3 / Real.sqrt x := by positivity
  have hint : ‖∫ s in (0:ℝ)..1, h' s * E s‖ ≤ ∫ s in (0:ℝ)..1, ‖h' s‖ * (3 / Real.sqrt x) := by
    refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
      (Eventually.of_forall fun s hs => ?_) ?_
    · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hEb s hs.1.le) (norm_nonneg _)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
      exact (hc.norm.mul continuousOn_const).integrableOn_Icc
  rw [intervalIntegral.integral_mul_const] at hint
  calc ‖h 1 * E 1 - ∫ s in (0:ℝ)..1, h' s * E s‖
      ≤ ‖h 1 * E 1‖ + ‖∫ s in (0:ℝ)..1, h' s * E s‖ := norm_sub_le _ _
    _ ≤ ‖h 1‖ * (3 / Real.sqrt x) + (∫ s in (0:ℝ)..1, ‖h' s‖) * (3 / Real.sqrt x) := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hEb 1 zero_le_one) (norm_nonneg _)) hint
    _ = _ := by ring

/-- `C²` data for the oscillatory asymptotics. -/
structure OscData (g k : ℝ → ℂ) : Prop where
  decomp : ∀ s ∈ Icc (0:ℝ) 1, g s = g 0 + s * k s
  k_zero : k 0 = 0
  open_nhd : ∃ U : Set ℝ, IsOpen U ∧ Icc (0:ℝ) 1 ⊆ U ∧ ContDiffOn ℝ 2 k U

lemma OscData.derivs {g k : ℝ → ℂ} (hD : OscData g k) :
    (∀ s ∈ Icc (0:ℝ) 1, HasDerivAt k (deriv k s) s) ∧
    (∀ s ∈ Icc (0:ℝ) 1, HasDerivAt (deriv k) (deriv (deriv k) s) s) ∧
    ContinuousOn (deriv (deriv k)) (Icc 0 1) ∧ ContinuousOn (deriv k) (Icc 0 1) := by
  obtain ⟨U, hU, hIU, hk⟩ := hD.open_nhd
  have h1 : ContDiffOn ℝ 1 (deriv k) U := hk.deriv_of_isOpen hU (by norm_num)
  have h0 : ContDiffOn ℝ 0 (deriv (deriv k)) U := h1.deriv_of_isOpen hU (by norm_num)
  refine ⟨fun s hs => ?_, fun s hs => ?_, h0.continuousOn.mono hIU,
    h1.continuousOn.mono hIU⟩
  · exact ((hk.differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds (hIU hs))).hasDerivAt
  · exact ((h1.differentiableOn (by norm_num)).differentiableAt
      (hU.mem_nhds (hIU hs))).hasDerivAt

/-- **Stationary phase at an endpoint.** -/
theorem osc_asymp {g k : ℝ → ℂ} (hD : OscData g k) (hg : ContinuousOn g (Icc 0 1)) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      ‖(∫ s in (0:ℝ)..1, g s * oscF x s) -
        (g 0 * (((π : ℂ) / ((x:ℂ) * I)) ^ (1 / 2 : ℂ) / 2) -
          g 1 * cexp (-((x:ℂ) * I)) / (2 * ((x:ℂ) * I)))‖ ≤ C / (x * Real.sqrt x) := by
  obtain ⟨hk1, hk2, hc2, hc1⟩ := hD.derivs
  set k1 := deriv k
  set k2 := deriv (deriv k)
  refine ⟨‖g 0‖ + 3 / 2 * (‖k1 1‖ + ∫ s in (0:ℝ)..1, ‖k2 s‖), fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsx1 : 1 ≤ Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
  have hxsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  set b : ℂ := (x:ℂ) * I with hb
  have hb0 : b ≠ 0 := by simp [b, hx0.ne']
  have hbn : ‖b‖ = x := by simp [b, abs_of_pos hx0]
  have hIcc : uIcc (0:ℝ) 1 = Icc 0 1 := uIcc_of_le zero_le_one
  -- split off `g 0`
  have hsplit : ∫ s in (0:ℝ)..1, g s * oscF x s =
      g 0 * gauss01 b + ∫ s in (0:ℝ)..1, k s * ((s:ℂ) * oscF x s) := by
    unfold gauss01
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun s hs => ?_
      rw [hIcc] at hs
      simp only [oscF, b]
      rw [hD.decomp s hs]; ring
    · exact ((continuous_const.mul (by fun_prop)).intervalIntegrable _ _)
    · rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
      refine ContinuousOn.integrableOn_Icc ?_
      exact (show ContinuousOn k (Icc 0 1) from
        fun s hs => (hk1 s hs).continuousAt.continuousWithinAt).mul
        (by fun_prop : Continuous fun s : ℝ => (s:ℂ) * oscF x s).continuousOn
  -- integrate by parts the second piece
  have hvd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => oscF x s / (-2 * b)) ((s:ℂ) * oscF x s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => -b * (s:ℂ) ^ 2) (-b * (2 * s)) s := by
      have := ((hasDerivAt_id s).ofReal_comp.pow 2).const_mul (-b)
      simpa using this
    have := h1.cexp.div_const (-2 * b)
    have e : (fun s : ℝ => oscF x s / (-2 * b)) = fun s : ℝ => cexp (-b * (s:ℂ) ^ 2) / (-2 * b) := by
      funext t; simp only [oscF, b]
    rw [e]
    convert this using 1
    simp only [oscF, b]
    have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    field_simp
  have ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := k)
    (v := fun s : ℝ => oscF x s / (-2 * b)) (u' := k1) (v' := fun s => (s:ℂ) * oscF x s)
    (fun s hs => hk1 s (hIcc ▸ hs)) (fun s _ => hvd s)
    (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
        exact hc1.integrableOn_Icc)
    ((by fun_prop : Continuous fun s : ℝ => (s:ℂ) * oscF x s).intervalIntegrable _ _)
  beta_reduce at ibp
  rw [ibp, hD.k_zero, zero_mul, sub_zero] at hsplit
  have hosc : ∫ s in (0:ℝ)..1, k1 s * (oscF x s / (-2 * b)) =
      (∫ s in (0:ℝ)..1, k1 s * oscF x s) / (-2 * b) := by
    rw [← intervalIntegral.integral_div]
    congr 1; funext s; ring
  rw [hosc] at hsplit
  have hO := norm_osc_le hx0 hk2 hc2
  have hG := gauss01_asymp (b := b) (by simp [b]) hb0
  have hg1 : g 1 = g 0 + k 1 := by
    have := hD.decomp 1 ⟨zero_le_one, le_rfl⟩; simpa using this
  have hosc1 : oscF x 1 = cexp (-b) := by simp [oscF, b]
  -- assemble
  have key : (∫ s in (0:ℝ)..1, g s * oscF x s) -
      (g 0 * (((π : ℂ) / b) ^ (1 / 2 : ℂ) / 2) - g 1 * cexp (-b) / (2 * b)) =
      g 0 * (gauss01 b - gaussModel b) -
        (∫ s in (0:ℝ)..1, k1 s * oscF x s) / (-2 * b) := by
    rw [hsplit, hg1, hosc1]
    unfold gaussModel
    field_simp
    ring
  rw [key]
  have hden : ‖-2 * b‖ = 2 * x := by
    rw [norm_mul, norm_neg, hbn]; simp
  calc ‖g 0 * (gauss01 b - gaussModel b) - (∫ s in (0:ℝ)..1, k1 s * oscF x s) / (-2 * b)‖
      ≤ ‖g 0‖ * ‖gauss01 b - gaussModel b‖ +
          ‖∫ s in (0:ℝ)..1, k1 s * oscF x s‖ / (2 * x) := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_div, hden]
    _ ≤ ‖g 0‖ * (1 / x ^ 2) +
          3 / Real.sqrt x * (‖k1 1‖ + ∫ s in (0:ℝ)..1, ‖k2 s‖) / (2 * x) := by
        gcongr
        · rw [← hbn]; exact hG
    _ ≤ (‖g 0‖ + 3 / 2 * (‖k1 1‖ + ∫ s in (0:ℝ)..1, ‖k2 s‖)) / (x * Real.sqrt x) := by
        have hA : 0 ≤ ‖k1 1‖ + ∫ s in (0:ℝ)..1, ‖k2 s‖ :=
          add_nonneg (norm_nonneg _) (intervalIntegral.integral_nonneg zero_le_one
            (fun _ _ => norm_nonneg _))
        have e1 : 1 / x ^ 2 ≤ 1 / (x * Real.sqrt x) := by
          apply one_div_le_one_div_of_le (by positivity)
          rw [sq]; exact mul_le_mul_of_nonneg_left (by nlinarith) hx0.le
        have e2 : 3 / Real.sqrt x * (‖k1 1‖ + ∫ s in (0:ℝ)..1, ‖k2 s‖) / (2 * x) =
            3 / 2 * (‖k1 1‖ + ∫ s in (0:ℝ)..1, ‖k2 s‖) / (x * Real.sqrt x) := by
          field_simp
        rw [e2, add_div]
        gcongr
        calc ‖g 0‖ * (1 / x ^ 2) ≤ ‖g 0‖ * (1 / (x * Real.sqrt x)) :=
              mul_le_mul_of_nonneg_left e1 (norm_nonneg _)
          _ = _ := by ring

end Buckling
end
end ChunkedSource002
/- END SOURCE 002 -/

/- BEGIN SOURCE 003: RequestProject/Bessel/Defs.lean -/
section ChunkedSource003

/-!
# Bessel functions of integer order (Definition 1.1 of the paper)

We define the Bessel function `J_n` of the first kind of integer order `n ≥ 0`
by its power series, both for a real and for a complex argument, the
enumeration `j_{n,1} < j_{n,2} < ⋯` of its positive zeros, the two distinguished
zeros `q = j_{0,1}` and `k = j_{1,1}`, and the finite partial sums `S_{ν,N}`
(Definition 3.4 of the paper).
-/

@[expose] public section

open scoped Nat

namespace Buckling

/-- The Bessel function `J_n(x) = ∑_{m ≥ 0} (-1)^m (x/2)^{2m+n} / (m! (m+n)!)`
of integer order `n ≥ 0`, for a real argument. -/
noncomputable def besselJ (n : ℕ) (x : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (x / 2) ^ (2 * m + n) / ((m ! : ℝ) * ((m + n) ! : ℝ))

/-- The Bessel function `J_n(ζ)` of integer order `n ≥ 0`, for a complex argument. -/
noncomputable def besselJC (n : ℕ) (ζ : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * (ζ / 2) ^ (2 * m + n) / ((m ! : ℂ) * ((m + n) ! : ℂ))

/-- Enumeration of the positive zeros of `J_n`: `besselZero n 0 = 0` is a placeholder,
and `besselZero n (k+1)` is the infimum of the zeros of `J_n` exceeding
`besselZero n k`.  Under External Theorem E1 (`ExtZeros`), `besselZero n k` is the
`k`-th positive zero `j_{n,k}` for every `k ≥ 1`. -/
noncomputable def besselZero (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sInf {x : ℝ | besselZero n k < x ∧ besselJ n x = 0}

/-- `q = j_{0,1}`, the first positive zero of `J_0`. -/
noncomputable def jq : ℝ := besselZero 0 1

/-- `k = j_{1,1}`, the first positive zero of `J_1`. -/
noncomputable def jk : ℝ := besselZero 1 1

/-- The finite Bessel sums `S_{ν,N}(x) = ∑_{m=0}^{N} (-1)^m (x/2)^{2m+ν} / (m! (m+ν)!)`
(Definition 3.4). -/
def besselPartial (ν N : ℕ) (x : ℚ) : ℚ :=
  ∑ m ∈ Finset.range (N + 1), (-1 : ℚ) ^ m * (x / 2) ^ (2 * m + ν) / ((m ! : ℚ) * ((m + ν) ! : ℚ))

/-- Real version of the finite Bessel sums. -/
noncomputable def besselPartialR (ν N : ℕ) (x : ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1), (-1 : ℝ) ^ m * (x / 2) ^ (2 * m + ν) / ((m ! : ℝ) * ((m + ν) ! : ℝ))

end Buckling
end
end ChunkedSource003
/- END SOURCE 003 -/

/- BEGIN SOURCE 004: RequestProject/Bessel/Basic.lean -/
section ChunkedSource004

/-!
# Basic properties of the Bessel series (part of Lemma 2.5)

Summability, term-by-term differentiation, and the recurrences
`J₀' = -J₁`, `J_{n+1}' = (J_n - J_{n+2})/2`, `x (J_n + J_{n+2}) = 2(n+1) J_{n+1}`.
-/

@[expose] public section

open scoped Nat
open Filter Topology

namespace Buckling

/-- The `m`-th term of the series for `J_n(x)`. -/
noncomputable def bterm (n m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * (x / 2) ^ (2 * m + n) / ((m ! : ℝ) * ((m + n) ! : ℝ))

lemma besselJ_eq_tsum (n : ℕ) (x : ℝ) : besselJ n x = ∑' m, bterm n m x := rfl

lemma abs_bterm (n m : ℕ) (x : ℝ) :
    |bterm n m x| = (|x| / 2) ^ (2 * m + n) / ((m ! : ℝ) * ((m + n) ! : ℝ)) := by
  unfold bterm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_div,
    abs_two, abs_of_pos (by positivity : (0 : ℝ) < (m ! : ℝ) * ((m + n) ! : ℝ))]

lemma abs_bterm_le (n m : ℕ) (x : ℝ) :
    |bterm n m x| ≤ (|x| / 2) ^ n * (((|x| / 2) ^ 2) ^ m / (m ! : ℝ)) := by
  rw [abs_bterm]
  have h1 : (1 : ℝ) ≤ ((m + n) ! : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  have hm : (0 : ℝ) < (m ! : ℝ) := by positivity
  rw [div_le_iff₀ (by positivity)]
  have : (|x| / 2) ^ (2 * m + n) = (|x| / 2) ^ n * ((|x| / 2) ^ 2) ^ m := by
    rw [← pow_mul, ← pow_add]; ring_nf
  rw [this]
  have hx : 0 ≤ (|x| / 2) ^ n * ((|x| / 2) ^ 2) ^ m := by positivity
  calc (|x| / 2) ^ n * ((|x| / 2) ^ 2) ^ m
      = (|x| / 2) ^ n * (((|x| / 2) ^ 2) ^ m / (m ! : ℝ)) * (m ! : ℝ) := by
        field_simp
    _ ≤ (|x| / 2) ^ n * (((|x| / 2) ^ 2) ^ m / (m ! : ℝ)) * ((m ! : ℝ) * ((m + n) ! : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith

lemma summable_abs_bterm (n : ℕ) (x : ℝ) : Summable fun m => |bterm n m x| := by
  refine Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => abs_bterm_le n m x) ?_
  exact (Real.summable_pow_div_factorial _).mul_left _

lemma summable_bterm (n : ℕ) (x : ℝ) : Summable fun m => bterm n m x :=
  (summable_abs_bterm n x).of_abs

/-- The derivative of the `m`-th term. -/
noncomputable def dbterm (n m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * (((2 * m + n : ℕ) : ℝ) * (x / 2) ^ (2 * m + n - 1) * (1 / 2)) /
    ((m ! : ℝ) * ((m + n) ! : ℝ))

lemma hasDerivAt_bterm (n m : ℕ) (x : ℝ) : HasDerivAt (bterm n m) (dbterm n m x) x := by
  unfold bterm dbterm
  have h := ((hasDerivAt_id x).div_const 2).fun_pow (2 * m + n)
  have h2 := (h.const_mul ((-1 : ℝ) ^ m)).div_const ((m ! : ℝ) * ((m + n) ! : ℝ))
  simpa only [id_eq, Pi.pow_apply] using! h2

/-- Shifted term `term (n+2) (m-1)`, zero for `m = 0`. -/
lemma dbterm_succ (n m : ℕ) (x : ℝ) :
    dbterm (n + 1) (m + 1) x = (bterm n (m + 1) x - bterm (n + 2) m x) / 2 := by
  unfold dbterm bterm
  have e1 : 2 * (m + 1) + (n + 1) - 1 = 2 * m + n + 2 := by omega
  have e2 : 2 * (m + 1) + n = 2 * m + n + 2 := by omega
  have e3 : 2 * m + (n + 2) = 2 * m + n + 2 := by omega
  rw [e1, e2, e3, show m + 1 + (n + 1) = m + n + 2 by omega,
    show m + 1 + n = m + n + 1 by omega, show m + (n + 2) = m + n + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma dbterm_zero_succ (n : ℕ) (x : ℝ) :
    dbterm (n + 1) 0 x = bterm n 0 x / 2 := by
  unfold dbterm bterm
  simp only [pow_zero, one_mul, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
    Nat.add_sub_cancel]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

lemma dbterm_zero_zero (x : ℝ) : dbterm 0 0 x = 0 := by
  simp [dbterm]

lemma dbterm_zero (m : ℕ) (x : ℝ) : dbterm 0 (m + 1) x = -bterm 1 m x := by
  unfold dbterm bterm
  rw [show 2 * (m + 1) + 0 - 1 = 2 * m + 1 by omega, show m + 1 + 0 = m + 1 by omega,
    show 2 * m + 1 = 2 * m + 1 by rfl]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Bound on the derivative of a term on `|x| ≤ R`. -/
lemma abs_dbterm_le (n m : ℕ) (x R : ℝ) (hx : |x| ≤ R) :
    |dbterm n m x| ≤ (if n = 0 then (if m = 0 then 0 else |bterm 1 (m - 1) R|)
      else (|bterm (n - 1) m R| + (if m = 0 then 0 else |bterm (n + 1) (m - 1) R|)) / 2) := by
  have mono : ∀ a b : ℕ, |bterm a b x| ≤ |bterm a b R| := by
    intro a b
    rw [abs_bterm, abs_bterm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    linarith [le_abs_self R]
  rcases n with _ | n
  · rcases m with _ | m
    · simp [dbterm_zero_zero]
    · simp only [if_true, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      rw [dbterm_zero, abs_neg]; exact mono _ _
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rcases m with _ | m
    · simp only [if_true, add_zero]
      rw [dbterm_zero_succ, abs_div, abs_two]
      exact div_le_div_of_nonneg_right (mono _ _) (by norm_num)
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [dbterm_succ, abs_div, abs_two]
      exact div_le_div_of_nonneg_right
        ((abs_sub _ _).trans (add_le_add (mono _ _) (mono _ _))) (by norm_num)

lemma summable_shift_abs (a : ℕ) (R : ℝ) :
    Summable fun m : ℕ => (if m = 0 then 0 else |bterm a (m - 1) R|) := by
  rw [← summable_nat_add_iff 1]
  simpa using summable_abs_bterm a R

lemma summable_dbound (n : ℕ) (R : ℝ) :
    Summable fun m : ℕ => (if n = 0 then (if m = 0 then 0 else |bterm 1 (m - 1) R|)
      else (|bterm (n - 1) m R| + (if m = 0 then 0 else |bterm (n + 1) (m - 1) R|)) / 2) := by
  rcases n with _ | n
  · simpa using summable_shift_abs 1 R
  · simp only [Nat.succ_ne_zero, if_false]
    exact ((summable_abs_bterm _ R).add (summable_shift_abs _ R)).div_const 2

lemma hasDerivAt_besselJ_tsum (n : ℕ) (x : ℝ) :
    HasDerivAt (besselJ n) (∑' m, dbterm n m x) x := by
  have hR : |x| < |x| + 1 := by linarith
  refine hasDerivAt_tsum_of_isPreconnected (summable_dbound n (|x| + 1))
    (isOpen_Ioo (a := -(|x| + 1)) (b := |x| + 1)) isPreconnected_Ioo
    (fun m y _ => hasDerivAt_bterm n m y) (fun m y hy => ?_) (y₀ := 0) ?_
    (summable_bterm n 0) ?_
  · rw [Real.norm_eq_abs]
    apply abs_dbterm_le
    rw [Set.mem_Ioo] at hy
    exact abs_le.mpr ⟨hy.1.le, hy.2.le⟩
  · constructor <;> linarith [abs_nonneg x]
  · constructor <;> linarith [neg_abs_le x, le_abs_self x]

/-- `J₀' = -J₁`. -/
theorem hasDerivAt_besselJ_zero (x : ℝ) : HasDerivAt (besselJ 0) (-besselJ 1 x) x := by
  convert hasDerivAt_besselJ_tsum 0 x using 1
  have hs : Summable fun m => dbterm 0 m x := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [dbterm_zero]
    exact (summable_bterm 1 x).neg
  rw [hs.tsum_eq_zero_add, dbterm_zero_zero, zero_add]
  simp only [dbterm_zero]
  rw [tsum_neg]; rfl

/-- `J_{n+1}' = (J_n - J_{n+2})/2`. -/
theorem hasDerivAt_besselJ_succ (n : ℕ) (x : ℝ) :
    HasDerivAt (besselJ (n + 1)) ((besselJ n x - besselJ (n + 2) x) / 2) x := by
  convert hasDerivAt_besselJ_tsum (n + 1) x using 1
  have hs1 : Summable fun m => (bterm n (m + 1) x - bterm (n + 2) m x) / 2 :=
    ((((summable_nat_add_iff 1).mpr (summable_bterm n x)).sub (summable_bterm (n + 2) x))).div_const 2
  have hs : Summable fun m => dbterm (n + 1) m x := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [dbterm_succ]
    exact hs1
  rw [hs.tsum_eq_zero_add, dbterm_zero_succ]
  simp only [dbterm_succ]
  rw [tsum_div_const, Summable.tsum_sub ((summable_nat_add_iff 1).mpr (summable_bterm n x))
    (summable_bterm (n + 2) x)]
  rw [besselJ_eq_tsum n, (summable_bterm n x).tsum_eq_zero_add, besselJ_eq_tsum (n + 2)]
  ring

lemma differentiable_besselJ (n : ℕ) : Differentiable ℝ (besselJ n) :=
  fun x => (hasDerivAt_besselJ_tsum n x).differentiableAt

lemma continuous_besselJ (n : ℕ) : Continuous (besselJ n) :=
  (differentiable_besselJ n).continuous

lemma deriv_besselJ_zero : deriv (besselJ 0) = fun x => -besselJ 1 x :=
  funext fun x => (hasDerivAt_besselJ_zero x).deriv

lemma deriv_besselJ_succ (n : ℕ) :
    deriv (besselJ (n + 1)) = fun x => (besselJ n x - besselJ (n + 2) x) / 2 :=
  funext fun x => (hasDerivAt_besselJ_succ n x).deriv

/-- The three-term recurrence `x (J_n(x) + J_{n+2}(x)) = 2(n+1) J_{n+1}(x)`. -/
theorem besselJ_recurrence (n : ℕ) (x : ℝ) :
    x * (besselJ n x + besselJ (n + 2) x) = 2 * (n + 1) * besselJ (n + 1) x := by
  have key : ∀ m, x * bterm n (m + 1) x + x * bterm (n + 2) m x
      = 2 * (n + 1) * bterm (n + 1) (m + 1) x := by
    intro m
    unfold bterm
    rw [show 2 * (m + 1) + n = 2 * m + n + 2 by omega,
      show 2 * m + (n + 2) = 2 * m + n + 2 by omega,
      show 2 * (m + 1) + (n + 1) = 2 * m + n + 2 + 1 by omega,
      show m + 1 + n = m + n + 1 by omega, show m + (n + 2) = m + n + 2 by omega,
      show m + 1 + (n + 1) = m + n + 2 by omega]
    simp only [Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have key0 : x * bterm n 0 x = 2 * (n + 1) * bterm (n + 1) 0 x := by
    unfold bterm
    simp only [pow_zero, one_mul, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one]
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have s1 := (summable_nat_add_iff 1).mpr (summable_bterm n x)
  have s2 := summable_bterm (n + 2) x
  calc x * (besselJ n x + besselJ (n + 2) x)
      = x * bterm n 0 x + (∑' m, x * bterm n (m + 1) x + ∑' m, x * bterm (n + 2) m x) := by
        rw [besselJ_eq_tsum, besselJ_eq_tsum, (summable_bterm n x).tsum_eq_zero_add,
          tsum_mul_left, tsum_mul_left]; ring
    _ = x * bterm n 0 x + ∑' m, (x * bterm n (m + 1) x + x * bterm (n + 2) m x) := by
        rw [Summable.tsum_add (s1.mul_left x) (s2.mul_left x)]
    _ = 2 * (n + 1) * besselJ (n + 1) x := by
        simp only [key]
        rw [key0, besselJ_eq_tsum, (summable_bterm (n + 1) x).tsum_eq_zero_add, tsum_mul_left]
        ring

lemma bterm_zero_arg (n m : ℕ) : bterm n m 0 = if m = 0 ∧ n = 0 then 1 else 0 := by
  unfold bterm
  by_cases h : m = 0 ∧ n = 0
  · obtain ⟨rfl, rfl⟩ := h; simp
  · rw [if_neg h]
    have : 2 * m + n ≠ 0 := by omega
    simp [zero_div, zero_pow this]

lemma besselJ_zero_arg (n : ℕ) : besselJ n 0 = if n = 0 then 1 else 0 := by
  rw [besselJ_eq_tsum, tsum_eq_single 0]
  · rw [bterm_zero_arg]; simp
  · intro m hm; rw [bterm_zero_arg]; simp [hm]

lemma besselJ_zero_at_zero : besselJ 0 0 = 1 := by simp [besselJ_zero_arg]

lemma bterm_neg (n m : ℕ) (x : ℝ) : bterm n m (-x) = (-1) ^ n * bterm n m x := by
  unfold bterm
  have h : (-1 : ℝ) ^ (2 * m + n) = (-1) ^ n := by rw [pow_add, pow_mul]; norm_num
  rw [neg_div, neg_pow (x / 2), h]
  ring

/-- Parity `J_n(-x) = (-1)^n J_n(x)`. -/
theorem besselJ_neg (n : ℕ) (x : ℝ) : besselJ n (-x) = (-1) ^ n * besselJ n x := by
  rw [besselJ_eq_tsum, besselJ_eq_tsum, ← tsum_mul_left]
  simp only [bterm_neg]

end Buckling
end
end ChunkedSource004
/- END SOURCE 004 -/

/- BEGIN SOURCE 005: RequestProject/Bessel/Alternating.lean -/
section ChunkedSource005

/-!
# Alternating tail bounds (Lemma 3.5) and the finite rational certificate (Lemma 3.6)
-/

@[expose] public section

open scoped Nat
open Filter Topology

namespace Buckling

/-- Strict alternating-series bounds: if `b` is strictly decreasing, nonnegative and
summable, then `0 < ∑ (-1)^i b_i < b_0`. -/
lemma alternating_strict_bounds (b : ℕ → ℝ) (hanti : StrictAnti b) (hnn : ∀ i, 0 ≤ b i)
    (hs : Summable b) :
    0 < ∑' i, (-1 : ℝ) ^ i * b i ∧ ∑' i, (-1 : ℝ) ^ i * b i < b 0 := by
  have habs : ∀ c : ℕ → ℝ, Summable c → (∀ i, 0 ≤ c i) → Summable fun i => (-1 : ℝ) ^ i * c i := by
    intro c hc hcnn
    refine Summable.of_norm ?_
    simpa [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg (hcnn _)] using hc
  have hs1 : Summable fun i => b (i + 1) := (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable fun i => b (i + 2) := (summable_nat_add_iff 2).mpr hs
  -- the tail starting at index 2 is nonnegative
  have tail_nonneg : ∀ c : ℕ → ℝ, Antitone c → Summable c → (∀ i, 0 ≤ c i) →
      0 ≤ ∑' i, (-1 : ℝ) ^ i * c i := by
    intro c hc hcs hcnn
    have hl := (habs c hcs hcnn).hasSum.tendsto_sum_nat
    have := hc.alternating_series_le_tendsto hl 0
    simpa using this
  have split1 : ∀ c : ℕ → ℝ, Summable c → (∀ i, 0 ≤ c i) →
      ∑' i, (-1 : ℝ) ^ i * c i = c 0 - ∑' i, (-1 : ℝ) ^ i * c (i + 1) := by
    intro c hc hcnn
    rw [(habs c hc hcnn).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, pow_succ, mul_neg_one, neg_mul, tsum_neg]
    ring
  have split2 : ∀ c : ℕ → ℝ, Summable c → (∀ i, 0 ≤ c i) →
      ∑' i, (-1 : ℝ) ^ i * c i = (c 0 - c 1) + ∑' i, (-1 : ℝ) ^ i * c (i + 2) := by
    intro c hc hcnn
    rw [split1 c hc hcnn, split1 (fun i => c (i + 1)) ((summable_nat_add_iff 1).mpr hc)
      (fun i => hcnn _)]
    ring
  have t2 := tail_nonneg (fun i => b (i + 2)) (fun i j hij => hanti.antitone (by omega)) hs2
    (fun i => hnn _)
  have t3 := tail_nonneg (fun i => b (i + 1 + 2)) (fun i j hij => hanti.antitone (by omega))
    ((summable_nat_add_iff 3).mpr hs) (fun i => hnn _)
  have h01 := hanti (show 0 < 1 by norm_num)
  have h12 := hanti (show 1 < 2 by norm_num)
  constructor
  · rw [split2 b hs hnn]; linarith
  · rw [split1 b hs hnn, split2 (fun i => b (i + 1)) hs1 (fun i => hnn _)]
    linarith

/-- Absolute value of the terms: `a_m = (x/2)^{2m+ν}/(m!(m+ν)!)` for `x ≥ 0`. -/
noncomputable def bAbs (ν m : ℕ) (x : ℝ) : ℝ :=
  (x / 2) ^ (2 * m + ν) / ((m ! : ℝ) * ((m + ν) ! : ℝ))

lemma bterm_eq_bAbs (ν m : ℕ) (x : ℝ) : bterm ν m x = (-1) ^ m * bAbs ν m x := by
  unfold bterm bAbs; ring

lemma bAbs_succ (ν m : ℕ) (x : ℝ) :
    bAbs ν (m + 1) x = bAbs ν m x * ((x / 2) ^ 2 / (((m + 1 : ℕ) : ℝ) * ((m + ν + 1 : ℕ) : ℝ))) := by
  unfold bAbs
  rw [show 2 * (m + 1) + ν = 2 * m + ν + 2 by omega, show m + 1 + ν = m + ν + 1 by omega,
    Nat.factorial_succ, Nat.factorial_succ (m + ν), pow_add]
  push_cast
  field_simp

lemma bAbs_pos (ν m : ℕ) {x : ℝ} (hx : 0 < x) : 0 < bAbs ν m x := by
  unfold bAbs; positivity

/-- General alternating tail bound: if `x² < 4(N+2)²`, then
`0 < (-1)^{N+1} (J_ν(x) - S_{ν,N}(x)) < a_{N+1}`. -/
lemma besselJ_tail_general (ν N : ℕ) (x : ℝ) (hx0 : 0 < x)
    (hx : x ^ 2 < 4 * ((N : ℝ) + 2) * ((N : ℝ) + 2)) :
    0 < (-1) ^ (N + 1) * (besselJ ν x - besselPartialR ν N x) ∧
      (-1) ^ (N + 1) * (besselJ ν x - besselPartialR ν N x) < bAbs ν (N + 1) x := by
  set b : ℕ → ℝ := fun i => bAbs ν (N + 1 + i) x with hb
  have hsum : Summable fun m => bterm ν m x := summable_bterm ν x
  have hsplit : besselJ ν x = besselPartialR ν N x + ∑' i, bterm ν (i + (N + 1)) x := by
    rw [besselJ_eq_tsum, ← hsum.sum_add_tsum_nat_add (N + 1)]
    rfl
  have htail : ∑' i, bterm ν (i + (N + 1)) x = (-1) ^ (N + 1) * ∑' i, (-1 : ℝ) ^ i * b i := by
    rw [← tsum_mul_left]
    congr 1; ext i
    rw [bterm_eq_bAbs, hb]
    simp only [pow_add, add_comm i (N + 1)]
    ring
  have hanti : StrictAnti b := by
    apply strictAnti_nat_of_succ_lt
    intro i
    simp only [hb]
    rw [show N + 1 + (i + 1) = (N + 1 + i) + 1 by omega, bAbs_succ]
    have hp := bAbs_pos ν (N + 1 + i) hx0
    have hr : (x / 2) ^ 2 / (((N + 1 + i + 1 : ℕ) : ℝ) * ((N + 1 + i + ν + 1 : ℕ) : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]
      push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      have : (0 : ℝ) ≤ ν := Nat.cast_nonneg ν
      have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    calc bAbs ν (N + 1 + i) x * _ < bAbs ν (N + 1 + i) x * 1 := by gcongr
      _ = _ := mul_one _
  have hnn : ∀ i, 0 ≤ b i := fun i => (bAbs_pos ν _ hx0).le
  have hsb : Summable b := by
    have := (summable_nat_add_iff (N + 1)).mpr (summable_abs_bterm ν x)
    refine this.congr fun i => ?_
    simp only [hb, bterm_eq_bAbs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      add_comm i (N + 1)]
    exact abs_of_pos (bAbs_pos ν _ hx0)
  obtain ⟨h1, h2⟩ := alternating_strict_bounds b hanti hnn hsb
  have hsq : ((-1 : ℝ) ^ (N + 1)) * ((-1 : ℝ) ^ (N + 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  rw [hsplit, htail, add_sub_cancel_left, ← mul_assoc, hsq, one_mul]
  simp only [hb, add_zero] at h2
  exact ⟨h1, h2⟩

lemma besselJ_tail_bounds (ν : ℕ) (x : ℝ) (hx0 : 0 < x) (hx : x < 11) :
    0 < besselPartialR ν 30 x - besselJ ν x ∧
      besselPartialR ν 30 x - besselJ ν x < bAbs ν 31 x := by
  have h := besselJ_tail_general ν 30 x hx0 (by norm_num; nlinarith)
  norm_num at h
  constructor <;> linarith [h.1, h.2]

lemma besselPartialR_succ (ν N : ℕ) (x : ℝ) :
    besselPartialR ν (N + 1) x = besselPartialR ν N x + (-1) ^ (N + 1) * bAbs ν (N + 1) x := by
  unfold besselPartialR
  rw [Finset.sum_range_succ]
  unfold bAbs; ring

/-- **Lemma 3.5 (alternating tail bounds).**  For every `ν` (the paper uses `ν ∈ {0,1}`) and `0 < x < 11`,
`S_{ν,31}(x) < J_ν(x) < S_{ν,30}(x)` and
`S_{ν,30}(x) - J_ν(x) < (x/2)^{62+ν}/(31!(31+ν)!)`. -/
theorem besselJ_alternating_bounds (ν : ℕ) (x : ℝ) (hx0 : 0 < x) (hx : x < 11) :
    besselPartialR ν 31 x < besselJ ν x ∧ besselJ ν x < besselPartialR ν 30 x ∧
      0 < besselPartialR ν 30 x - besselJ ν x ∧
      besselPartialR ν 30 x - besselJ ν x < (x / 2) ^ (62 + ν) / ((31 ! : ℝ) * ((31 + ν) ! : ℝ)) := by
  obtain ⟨h1, h2⟩ := besselJ_tail_bounds ν x hx0 hx
  have e : besselPartialR ν 31 x = besselPartialR ν 30 x - bAbs ν 31 x := by
    rw [besselPartialR_succ]; norm_num; ring
  have e2 : bAbs ν 31 x = (x / 2) ^ (62 + ν) / ((31 ! : ℝ) * ((31 + ν) ! : ℝ)) := by
    unfold bAbs; norm_num
  refine ⟨by rw [e]; linarith, by linarith, h1, by rw [← e2]; exact h2⟩

lemma besselPartialR_cast (ν N : ℕ) (x : ℚ) :
    besselPartialR ν N (x : ℝ) = ((besselPartial ν N x : ℚ) : ℝ) := by
  unfold besselPartialR besselPartial
  push_cast
  rfl

/-- Two-sided rational bounds for `J_ν` from the finite certificate. -/
lemma besselJ_rat_bounds (ν : ℕ) (x A B : ℚ) (hx0 : 0 < x) (hx : x < 11)
    (hA : A < besselPartial ν 31 x) (hB : besselPartial ν 30 x < B) :
    (A : ℝ) < besselJ ν x ∧ besselJ ν x < (B : ℝ) := by
  have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
  have hx' : (x : ℝ) < 11 := by exact_mod_cast hx
  obtain ⟨h1, h2, -, -⟩ := besselJ_alternating_bounds ν x hx0' hx'
  rw [besselPartialR_cast] at h1 h2
  have hA' : (A : ℝ) < (besselPartial ν 31 x : ℝ) := by exact_mod_cast hA
  have hB' : (besselPartial ν 30 x : ℝ) < B := by exact_mod_cast hB
  exact ⟨hA'.trans h1, h2.trans hB'⟩

end Buckling
end
end ChunkedSource005
/- END SOURCE 005 -/

/- BEGIN SOURCE 006: RequestProject/Bessel/Certificate.lean -/
section ChunkedSource006

/-!
# The finite rational certificate (Lemma 3.6)

Each row `(ν, x, A, B)` of the table in the paper gives
`A/10⁸ < S_{ν,31}(x) < S_{ν,30}(x) < B/10⁸`, checked by exact rational arithmetic,
and hence `A/10⁸ < J_ν(x) < B/10⁸`.
-/

@[expose] public section

namespace Buckling

/-- Row 1 of the certificate: `ν = 0`, `x = 240482/100000`. -/
theorem cert_row1 : (288 : ℚ) / 10 ^ 8 < besselPartial 0 31 (240482/100000) ∧
    besselPartial 0 31 (240482/100000) < besselPartial 0 30 (240482/100000) ∧
    besselPartial 0 30 (240482/100000) < (289 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 1: `288/10⁸ < J_0(240482/100000) < 289/10⁸`. -/
theorem besselJ_bounds_row1 :
    (288 : ℝ) / 10 ^ 8 < besselJ 0 (240482/100000) ∧ besselJ 0 (240482/100000) < (289 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 0 (240482/100000) ((288 : ℚ) / 10 ^ 8) ((289 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row1.1 cert_row1.2.2
  push_cast at h
  exact h

/-- Row 2 of the certificate: `ν = 0`, `x = 240483/100000`. -/
theorem cert_row2 : (-231 : ℚ) / 10 ^ 8 < besselPartial 0 31 (240483/100000) ∧
    besselPartial 0 31 (240483/100000) < besselPartial 0 30 (240483/100000) ∧
    besselPartial 0 30 (240483/100000) < (-230 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 2: `-231/10⁸ < J_0(240483/100000) < -230/10⁸`. -/
theorem besselJ_bounds_row2 :
    (-231 : ℝ) / 10 ^ 8 < besselJ 0 (240483/100000) ∧ besselJ 0 (240483/100000) < (-230 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 0 (240483/100000) ((-231 : ℚ) / 10 ^ 8) ((-230 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row2.1 cert_row2.2.2
  push_cast at h
  exact h

/-- Row 3 of the certificate: `ν = 1`, `x = 383170/100000`. -/
theorem cert_row3 : (240 : ℚ) / 10 ^ 8 < besselPartial 1 31 (383170/100000) ∧
    besselPartial 1 31 (383170/100000) < besselPartial 1 30 (383170/100000) ∧
    besselPartial 1 30 (383170/100000) < (241 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 3: `240/10⁸ < J_1(383170/100000) < 241/10⁸`. -/
theorem besselJ_bounds_row3 :
    (240 : ℝ) / 10 ^ 8 < besselJ 1 (383170/100000) ∧ besselJ 1 (383170/100000) < (241 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (383170/100000) ((240 : ℚ) / 10 ^ 8) ((241 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row3.1 cert_row3.2.2
  push_cast at h
  exact h

/-- Row 4 of the certificate: `ν = 1`, `x = 383171/100000`. -/
theorem cert_row4 : (-163 : ℚ) / 10 ^ 8 < besselPartial 1 31 (383171/100000) ∧
    besselPartial 1 31 (383171/100000) < besselPartial 1 30 (383171/100000) ∧
    besselPartial 1 30 (383171/100000) < (-162 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 4: `-163/10⁸ < J_1(383171/100000) < -162/10⁸`. -/
theorem besselJ_bounds_row4 :
    (-163 : ℝ) / 10 ^ 8 < besselJ 1 (383171/100000) ∧ besselJ 1 (383171/100000) < (-162 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (383171/100000) ((-163 : ℚ) / 10 ^ 8) ((-162 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row4.1 cert_row4.2.2
  push_cast at h
  exact h

/-- Row 5 of the certificate: `ν = 0`, `x = 55200/10000`. -/
theorem cert_row5 : (-2658 : ℚ) / 10 ^ 8 < besselPartial 0 31 (55200/10000) ∧
    besselPartial 0 31 (55200/10000) < besselPartial 0 30 (55200/10000) ∧
    besselPartial 0 30 (55200/10000) < (-2657 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 5: `-2658/10⁸ < J_0(55200/10000) < -2657/10⁸`. -/
theorem besselJ_bounds_row5 :
    (-2658 : ℝ) / 10 ^ 8 < besselJ 0 (55200/10000) ∧ besselJ 0 (55200/10000) < (-2657 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 0 (55200/10000) ((-2658 : ℚ) / 10 ^ 8) ((-2657 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row5.1 cert_row5.2.2
  push_cast at h
  exact h

/-- Row 6 of the certificate: `ν = 0`, `x = 55202/10000`. -/
theorem cert_row6 : (4147 : ℚ) / 10 ^ 8 < besselPartial 0 31 (55202/10000) ∧
    besselPartial 0 31 (55202/10000) < besselPartial 0 30 (55202/10000) ∧
    besselPartial 0 30 (55202/10000) < (4148 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 6: `4147/10⁸ < J_0(55202/10000) < 4148/10⁸`. -/
theorem besselJ_bounds_row6 :
    (4147 : ℝ) / 10 ^ 8 < besselJ 0 (55202/10000) ∧ besselJ 0 (55202/10000) < (4148 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 0 (55202/10000) ((4147 : ℚ) / 10 ^ 8) ((4148 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row6.1 cert_row6.2.2
  push_cast at h
  exact h

/-- Row 7 of the certificate: `ν = 1`, `x = 7015/1000`. -/
theorem cert_row7 : (-17608 : ℚ) / 10 ^ 8 < besselPartial 1 31 (7015/1000) ∧
    besselPartial 1 31 (7015/1000) < besselPartial 1 30 (7015/1000) ∧
    besselPartial 1 30 (7015/1000) < (-17607 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 7: `-17608/10⁸ < J_1(7015/1000) < -17607/10⁸`. -/
theorem besselJ_bounds_row7 :
    (-17608 : ℝ) / 10 ^ 8 < besselJ 1 (7015/1000) ∧ besselJ 1 (7015/1000) < (-17607 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (7015/1000) ((-17608 : ℚ) / 10 ^ 8) ((-17607 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row7.1 cert_row7.2.2
  push_cast at h
  exact h

/-- Row 8 of the certificate: `ν = 1`, `x = 7016/1000`. -/
theorem cert_row8 : (12404 : ℚ) / 10 ^ 8 < besselPartial 1 31 (7016/1000) ∧
    besselPartial 1 31 (7016/1000) < besselPartial 1 30 (7016/1000) ∧
    besselPartial 1 30 (7016/1000) < (12405 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 8: `12404/10⁸ < J_1(7016/1000) < 12405/10⁸`. -/
theorem besselJ_bounds_row8 :
    (12404 : ℝ) / 10 ^ 8 < besselJ 1 (7016/1000) ∧ besselJ 1 (7016/1000) < (12405 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (7016/1000) ((12404 : ℚ) / 10 ^ 8) ((12405 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row8.1 cert_row8.2.2
  push_cast at h
  exact h

/-- Row 9 of the certificate: `ν = 1`, `x = 10173/1000`. -/
theorem cert_row9 : (11689 : ℚ) / 10 ^ 8 < besselPartial 1 31 (10173/1000) ∧
    besselPartial 1 31 (10173/1000) < besselPartial 1 30 (10173/1000) ∧
    besselPartial 1 30 (10173/1000) < (11690 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 9: `11689/10⁸ < J_1(10173/1000) < 11690/10⁸`. -/
theorem besselJ_bounds_row9 :
    (11689 : ℝ) / 10 ^ 8 < besselJ 1 (10173/1000) ∧ besselJ 1 (10173/1000) < (11690 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (10173/1000) ((11689 : ℚ) / 10 ^ 8) ((11690 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row9.1 cert_row9.2.2
  push_cast at h
  exact h

/-- Row 10 of the certificate: `ν = 1`, `x = 10174/1000`. -/
theorem cert_row10 : (-13281 : ℚ) / 10 ^ 8 < besselPartial 1 31 (10174/1000) ∧
    besselPartial 1 31 (10174/1000) < besselPartial 1 30 (10174/1000) ∧
    besselPartial 1 30 (10174/1000) < (-13280 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 10: `-13281/10⁸ < J_1(10174/1000) < -13280/10⁸`. -/
theorem besselJ_bounds_row10 :
    (-13281 : ℝ) / 10 ^ 8 < besselJ 1 (10174/1000) ∧ besselJ 1 (10174/1000) < (-13280 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (10174/1000) ((-13281 : ℚ) / 10 ^ 8) ((-13280 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row10.1 cert_row10.2.2
  push_cast at h
  exact h

/-- Row 11 of the certificate: `ν = 1`, `x = 240482/100000`. -/
theorem cert_row11 : (51914869 : ℚ) / 10 ^ 8 < besselPartial 1 31 (240482/100000) ∧
    besselPartial 1 31 (240482/100000) < besselPartial 1 30 (240482/100000) ∧
    besselPartial 1 30 (240482/100000) < (51914870 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 11: `51914869/10⁸ < J_1(240482/100000) < 51914870/10⁸`. -/
theorem besselJ_bounds_row11 :
    (51914869 : ℝ) / 10 ^ 8 < besselJ 1 (240482/100000) ∧ besselJ 1 (240482/100000) < (51914870 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (240482/100000) ((51914869 : ℚ) / 10 ^ 8) ((51914870 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row11.1 cert_row11.2.2
  push_cast at h
  exact h

/-- Row 12 of the certificate: `ν = 0`, `x = 383170/100000`. -/
theorem cert_row12 : (-40275940 : ℚ) / 10 ^ 8 < besselPartial 0 31 (383170/100000) ∧
    besselPartial 0 31 (383170/100000) < besselPartial 0 30 (383170/100000) ∧
    besselPartial 0 30 (383170/100000) < (-40275939 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 12: `-40275940/10⁸ < J_0(383170/100000) < -40275939/10⁸`. -/
theorem besselJ_bounds_row12 :
    (-40275940 : ℝ) / 10 ^ 8 < besselJ 0 (383170/100000) ∧ besselJ 0 (383170/100000) < (-40275939 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 0 (383170/100000) ((-40275940 : ℚ) / 10 ^ 8) ((-40275939 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row12.1 cert_row12.2.2
  push_cast at h
  exact h

/-- Row 13 of the certificate: `ν = 1`, `x = 55201/10000`. -/
theorem cert_row13 : (-34026346 : ℚ) / 10 ^ 8 < besselPartial 1 31 (55201/10000) ∧
    besselPartial 1 31 (55201/10000) < besselPartial 1 30 (55201/10000) ∧
    besselPartial 1 30 (55201/10000) < (-34026345 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 13: `-34026346/10⁸ < J_1(55201/10000) < -34026345/10⁸`. -/
theorem besselJ_bounds_row13 :
    (-34026346 : ℝ) / 10 ^ 8 < besselJ 1 (55201/10000) ∧ besselJ 1 (55201/10000) < (-34026345 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 1 (55201/10000) ((-34026346 : ℚ) / 10 ^ 8) ((-34026345 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row13.1 cert_row13.2.2
  push_cast at h
  exact h

/-- Row 14 of the certificate: `ν = 0`, `x = 101735/10000`. -/
theorem cert_row14 : (-24970488 : ℚ) / 10 ^ 8 < besselPartial 0 31 (101735/10000) ∧
    besselPartial 0 31 (101735/10000) < besselPartial 0 30 (101735/10000) ∧
    besselPartial 0 30 (101735/10000) < (-24970487 : ℚ) / 10 ^ 8 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Consequence of row 14: `-24970488/10⁸ < J_0(101735/10000) < -24970487/10⁸`. -/
theorem besselJ_bounds_row14 :
    (-24970488 : ℝ) / 10 ^ 8 < besselJ 0 (101735/10000) ∧ besselJ 0 (101735/10000) < (-24970487 : ℝ) / 10 ^ 8 := by
  have h := besselJ_rat_bounds 0 (101735/10000) ((-24970488 : ℚ) / 10 ^ 8) ((-24970487 : ℚ) / 10 ^ 8)
    (by norm_num) (by norm_num) cert_row14.1 cert_row14.2.2
  push_cast at h
  exact h

end Buckling
end
end ChunkedSource006
/- END SOURCE 006 -/

/- BEGIN SOURCE 007: RequestProject/Bessel/Radial.lean -/
section ChunkedSource007

/-!
# The Bessel series as a function of `s²`

`J_n(s) = (s/2)^n G_n(s²)` where `G_n(y) = ∑ (-1)^m (y/4)^m / (m! (m+n)!)` is an entire
function of `y`.  This gives the smoothness of the radial functions `x ↦ J₀(c|x - a|)` on the
plane (used in Section 11 of the paper), together with the identities
`G_n' = -G_{n+1}/4` and `G₀ - G₁ + (y/4) G₂ = 0` (the Bessel equation in the variable `y`).
-/

@[expose] public section

open scoped Nat
open Filter Topology

namespace Buckling

/-- The `m`-th term of `G_n(y)`. -/
noncomputable def gterm (n m : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * (y / 4) ^ m / ((m ! : ℝ) * ((m + n) ! : ℝ))

/-- `G_n(y) = ∑_{m ≥ 0} (-1)^m (y/4)^m / (m! (m+n)!)`, so that `J_n(s) = (s/2)^n G_n(s²)`. -/
noncomputable def besselG (n : ℕ) (y : ℝ) : ℝ := ∑' m, gterm n m y

lemma abs_gterm (n m : ℕ) (y : ℝ) :
    |gterm n m y| = (|y| / 4) ^ m / ((m ! : ℝ) * ((m + n) ! : ℝ)) := by
  unfold gterm
  rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_pos (by positivity : (0 : ℝ) < (m ! : ℝ) * ((m + n) ! : ℝ))]

lemma abs_gterm_le (n m : ℕ) (y : ℝ) : |gterm n m y| ≤ (|y| / 4) ^ m / (m ! : ℝ) := by
  rw [abs_gterm]
  have h1 : (1 : ℝ) ≤ ((m + n) ! : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos _)
  rw [mul_comm, ← div_div]
  exact div_le_div_of_nonneg_right (div_le_self (by positivity) h1) (by positivity)

lemma summable_abs_gterm (n : ℕ) (y : ℝ) : Summable fun m => |gterm n m y| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => abs_gterm_le n m y)
    (Real.summable_pow_div_factorial _)

lemma summable_gterm (n : ℕ) (y : ℝ) : Summable fun m => gterm n m y :=
  (summable_abs_gterm n y).of_abs

/-- The derivative of the `m`-th term. -/
noncomputable def dgterm (n m : ℕ) (y : ℝ) : ℝ :=
  (-1 : ℝ) ^ m * ((m : ℝ) * (y / 4) ^ (m - 1) * (1 / 4)) / ((m ! : ℝ) * ((m + n) ! : ℝ))

lemma hasDerivAt_gterm (n m : ℕ) (y : ℝ) : HasDerivAt (gterm n m) (dgterm n m y) y := by
  unfold gterm dgterm
  have h := ((hasDerivAt_id y).div_const 4).fun_pow m
  have h2 := (h.const_mul ((-1 : ℝ) ^ m)).div_const ((m ! : ℝ) * ((m + n) ! : ℝ))
  simpa only [id_eq, Pi.pow_apply] using! h2

lemma dgterm_zero (n : ℕ) (y : ℝ) : dgterm n 0 y = 0 := by simp [dgterm]

lemma dgterm_succ (n m : ℕ) (y : ℝ) : dgterm n (m + 1) y = -(1 / 4) * gterm (n + 1) m y := by
  unfold dgterm gterm
  rw [Nat.add_sub_cancel, show m + 1 + n = m + (n + 1) by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma abs_dgterm_le (n m : ℕ) (y R : ℝ) (hy : |y| ≤ R) :
    |dgterm n m y| ≤ (if m = 0 then 0 else (1 / 4) * |gterm (n + 1) (m - 1) R|) := by
  rcases m with _ | m
  · simp [dgterm_zero]
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [dgterm_succ, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [abs_gterm, abs_gterm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    linarith [le_abs_self R]

lemma summable_dgbound (n : ℕ) (R : ℝ) :
    Summable fun m : ℕ => (if m = 0 then 0 else (1 / 4) * |gterm (n + 1) (m - 1) R|) := by
  rw [← summable_nat_add_iff 1]
  simpa using (summable_abs_gterm (n + 1) R).mul_left (4⁻¹)

/-- `G_n' = -G_{n+1}/4`. -/
theorem hasDerivAt_besselG (n : ℕ) (y : ℝ) :
    HasDerivAt (besselG n) (-(1 / 4) * besselG (n + 1) y) y := by
  have hR : |y| < |y| + 1 := by linarith
  have key : HasDerivAt (besselG n) (∑' m, dgterm n m y) y := by
    refine hasDerivAt_tsum_of_isPreconnected (summable_dgbound n (|y| + 1))
      (isOpen_Ioo (a := -(|y| + 1)) (b := |y| + 1)) isPreconnected_Ioo
      (fun m z _ => hasDerivAt_gterm n m z) (fun m z hz => ?_) (y₀ := 0) ?_
      (summable_gterm n 0) ?_
    · rw [Real.norm_eq_abs]
      apply abs_dgterm_le
      rw [Set.mem_Ioo] at hz
      exact abs_le.mpr ⟨hz.1.le, hz.2.le⟩
    · constructor <;> linarith [abs_nonneg y]
    · constructor <;> linarith [neg_abs_le y, le_abs_self y]
  convert key using 1
  have hs : Summable fun m => dgterm n m y := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [dgterm_succ]
    exact (summable_gterm (n + 1) y).mul_left _
  rw [hs.tsum_eq_zero_add, dgterm_zero, zero_add]
  simp only [dgterm_succ]
  rw [tsum_mul_left]; rfl

lemma differentiable_besselG (n : ℕ) : Differentiable ℝ (besselG n) :=
  fun y => (hasDerivAt_besselG n y).differentiableAt

lemma deriv_besselG (n : ℕ) : deriv (besselG n) = fun y => -(1 / 4) * besselG (n + 1) y :=
  funext fun y => (hasDerivAt_besselG n y).deriv

/-- Each `G_n` is smooth. -/
theorem contDiff_besselG (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (besselG n) := by
  have : ∀ k : ℕ, ∀ n, ContDiff ℝ k (besselG n) := by
    intro k
    induction k with
    | zero => intro n; exact contDiff_zero.mpr (differentiable_besselG n).continuous
    | succ k ih =>
      intro n
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨differentiable_besselG n, by simp, ?_⟩
      rw [deriv_besselG]
      exact contDiff_const.mul (ih (n + 1))
  exact contDiff_infty.mpr fun k => this k n

/-- `J_n(s) = (s/2)^n G_n(s²)`. -/
theorem besselJ_eq_besselG (n : ℕ) (s : ℝ) : besselJ n s = (s / 2) ^ n * besselG n (s ^ 2) := by
  unfold besselJ besselG
  rw [← tsum_mul_left]
  congr 1; ext m
  unfold gterm
  rw [pow_add, pow_mul]
  ring

lemma besselJ_zero_eq_besselG (s : ℝ) : besselJ 0 s = besselG 0 (s ^ 2) := by
  simp [besselJ_eq_besselG]

/-- The Bessel equation in the variable `y = s²`: `G₀ - G₁ + (y/4) G₂ = 0`. -/
theorem besselG_recurrence (y : ℝ) : besselG 0 y - besselG 1 y + y / 4 * besselG 2 y = 0 := by
  have key : ∀ m, gterm 0 (m + 1) y - gterm 1 (m + 1) y + y / 4 * gterm 2 m y = 0 := by
    intro m
    unfold gterm
    rw [show m + 1 + 0 = m + 1 by omega, show m + 1 + 1 = m + 2 by omega,
      show m + 2 = m + 2 by rfl]
    simp only [Nat.factorial_succ, show m + 2 = (m + 1) + 1 by omega]
    push_cast
    field_simp
    ring
  have hs0 := summable_gterm 0 y
  have hs1 := summable_gterm 1 y
  have hs2 := summable_gterm 2 y
  unfold besselG
  rw [hs0.tsum_eq_zero_add, hs1.tsum_eq_zero_add, ← tsum_mul_left]
  have : gterm 0 0 y - gterm 1 0 y = 0 := by simp [gterm]
  have h3 : ∑' m, (gterm 0 (m + 1) y - gterm 1 (m + 1) y + y / 4 * gterm 2 m y) = 0 := by
    simp [key]
  rw [Summable.tsum_add (((summable_nat_add_iff 1).mpr hs0).sub ((summable_nat_add_iff 1).mpr hs1))
    (hs2.mul_left _), Summable.tsum_sub ((summable_nat_add_iff 1).mpr hs0)
    ((summable_nat_add_iff 1).mpr hs1)] at h3
  linarith

end Buckling
end
end ChunkedSource007
/- END SOURCE 007 -/

/- BEGIN SOURCE 008: RequestProject/Bessel/Small.lean -/
section ChunkedSource008

/-!
# Small-argument bounds (Lemma 3.9 of the paper)
-/

@[expose] public section

namespace Buckling

/-- **Lemma 3.9 (small-argument bounds).**  `7/25 < J₀(19/10) < 283/1000`,
`J₁(19/10)/(19/10) > 3/10`, `J₀(2) > 11/50` and `J₁(2) < 3/5`. -/
theorem small_bessel_bounds :
    (7 / 25 : ℝ) < besselJ 0 (19 / 10) ∧ besselJ 0 (19 / 10) < 283 / 1000 ∧
    (3 / 10 : ℝ) < besselJ 1 (19 / 10) / (19 / 10) ∧
    (11 / 50 : ℝ) < besselJ 0 2 ∧ besselJ 1 2 < 3 / 5 := by
  have h1 := besselJ_rat_bounds 0 (19 / 10) (7 / 25) (283 / 1000) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have h2 := besselJ_rat_bounds 1 (19 / 10) (57 / 100) 1 (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have h3 := besselJ_rat_bounds 0 2 (11 / 50) 1 (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  have h4 := besselJ_rat_bounds 1 2 0 (3 / 5) (by norm_num) (by norm_num)
    (by decide +kernel) (by decide +kernel)
  push_cast at h1 h2 h3 h4
  refine ⟨h1.1, h1.2, ?_, h3.1, h4.2⟩
  rw [lt_div_iff₀ (by norm_num)]
  linarith [h2.1]

end Buckling
end
end ChunkedSource008
/- END SOURCE 008 -/

/- BEGIN SOURCE 009: RequestProject/Calibration/Algebra.lean -/
section ChunkedSource009

/-!
# A two-dimensional positivity criterion (Proposition 4.12)

The calibration matrix
`M = [[a, d/2, L_A/2], [d/2, K, L_C/2], [L_A/2, L_C/2, H]]` with `a = K - g²`
satisfies the kernel identities (Proposition 4.11)
`L_C = -dA - 2KC`, `L_A = -2aA - dC`, `H = aA² + dAC + KC²`.
Under `d² + 4Kg² ≤ 4K²` it is positive semidefinite and `2K - g² - d ≥ 0`.
-/

@[expose] public section

namespace Buckling

/-- The quadratic form `(X,Y,P) M (X,Y,P)ᵀ` of the calibration matrix. -/
def calibForm (a d K LA LC H X Y P : ℝ) : ℝ :=
  a * X ^ 2 + d * X * Y + K * Y ^ 2 + LA * X * P + LC * Y * P + H * P ^ 2

/-- The quadratic-form identity behind Proposition 4.12. -/
lemma calibForm_kernel (a d K A C X Y P : ℝ) :
    calibForm a d K (-2 * a * A - d * C) (-d * A - 2 * K * C) (a * A ^ 2 + d * A * C + K * C ^ 2)
      X Y P = a * (X - A * P) ^ 2 + d * (X - A * P) * (Y - C * P) + K * (Y - C * P) ^ 2 := by
  unfold calibForm; ring

/-- **Proposition 4.12 (a two-dimensional positivity criterion).**  If the kernel
identities hold and `d² + 4Kg² ≤ 4K²` with `K > 0`, then the calibration matrix is positive
semidefinite and `2K - g² - d ≥ 0`. -/
theorem positivity_criterion (K g d A C LA LC H : ℝ) (hK : 0 < K)
    (hLC : LC = -d * A - 2 * K * C) (hLA : LA = -2 * (K - g ^ 2) * A - d * C)
    (hH : H = (K - g ^ 2) * A ^ 2 + d * A * C + K * C ^ 2)
    (hpos : d ^ 2 + 4 * K * g ^ 2 ≤ 4 * K ^ 2) :
    (∀ X Y P : ℝ, 0 ≤ calibForm (K - g ^ 2) d K LA LC H X Y P) ∧ 0 ≤ 2 * K - g ^ 2 - d := by
  constructor
  · intro X Y P
    rw [hLC, hLA, hH, calibForm_kernel]
    set ξ := X - A * P
    set υ := Y - C * P
    have key : (K - g ^ 2) * ξ ^ 2 + d * ξ * υ + K * υ ^ 2
        = K * (υ + d / (2 * K) * ξ) ^ 2 + (4 * K * (K - g ^ 2) - d ^ 2) / (4 * K) * ξ ^ 2 := by
      field_simp; ring
    rw [key]
    have h1 : 0 ≤ (4 * K * (K - g ^ 2) - d ^ 2) / (4 * K) := by
      apply div_nonneg _ (by positivity); nlinarith
    positivity
  · have hg : g ^ 2 ≤ K := by nlinarith [sq_nonneg d]
    have h2 : 0 < 2 * K - g ^ 2 := by linarith
    have h3 : d ^ 2 ≤ (2 * K - g ^ 2) ^ 2 := by nlinarith [sq_nonneg g]
    nlinarith

/-- **The algebraic part of Lemma 9.18.**  At a point where `P = |∇U| > 0`, with the
local-frame Hessian entries `X, Y, Z`, the profile values `f, z, g = f - s z, b, b_s, G, G_s`
at `s = U/P`, and the divergence formulas of Lemma 9.17, the density
`K(|D²U|² - P²) - (|∇F|² - λF²) + div V₁ + div V₂` equals
`(X,Y,P) M (X,Y,P)ᵀ + (2K - g² - d) Z²`. -/
theorem density_identity (K lam s f z b bs G Gs X Y Z P : ℝ) :
    let g := f - s * z
    let d := 2 * G - s * Gs
    let LA := 2 * b - s * bs - 2 * z * g
    let LC := b + Gs
    let H := -K - z ^ 2 + lam * f ^ 2 + bs
    K * ((X ^ 2 + Y ^ 2 + 2 * Z ^ 2) - P ^ 2) - (((z * P + g * X) ^ 2 + g ^ 2 * Z ^ 2) -
        lam * (P * f) ^ 2) + (P * ((2 * b - s * bs) * X + b * Y) + bs * P ^ 2) +
        ((2 * G - s * Gs) * (X * Y - Z ^ 2) + P * Gs * Y)
      = calibForm (K - g ^ 2) d K LA LC H X Y P + (2 * K - g ^ 2 - d) * Z ^ 2 := by
  intro g d LA LC H
  simp only [calibForm, g, d, LA, LC, H]
  ring

/-- The algebraic core of Lemma 9.18 in the unit-frame coordinates `(c, d) = ∇U/P`. -/
lemma density_frame_identity (P c d s h11 h12 h22 f z b bs G Gs K lam F0 F1 V10 V11 V20 V21 : ℝ)
    (hcd : c ^ 2 + d ^ 2 = 1)
    (hF0 : F0 = (f - s * z) * (c * h11 + d * h12) + z * P * c)
    (hF1 : F1 = (f - s * z) * (c * h12 + d * h22) + z * P * d)
    (hV10 : V10 = ((b - s * bs) * (c * h11 + d * h12) + bs * P * c) * (P * c) + P * b * h11)
    (hV11 : V11 = ((b - s * bs) * (c * h12 + d * h22) + bs * P * d) * (P * d) + P * b * h22)
    (hV20 : V20 = h22 * (Gs * (P * c - s * (c * h11 + d * h12)) * c + G * h11) -
      h12 * (Gs * (P * c - s * (c * h11 + d * h12)) * d + G * h12))
    (hV21 : V21 = -(h12 * (Gs * (P * d - s * (c * h12 + d * h22)) * c + G * h12)) +
      h11 * (Gs * (P * d - s * (c * h12 + d * h22)) * d + G * h22)) :
    K * ((h11 ^ 2 + 2 * h12 ^ 2 + h22 ^ 2) - P ^ 2) - ((F0 ^ 2 + F1 ^ 2) - lam * (P * f) ^ 2) +
        (V10 + V11) + (V20 + V21) =
      calibForm (K - (f - s * z) ^ 2) (2 * G - s * Gs) K (2 * b - s * bs - 2 * z * (f - s * z))
          (b + Gs) (-K - z ^ 2 + lam * f ^ 2 + bs)
          (c ^ 2 * h11 + 2 * c * d * h12 + d ^ 2 * h22)
          (d ^ 2 * h11 - 2 * c * d * h12 + c ^ 2 * h22) P +
        (2 * K - (f - s * z) ^ 2 - (2 * G - s * Gs)) *
          (-c * d * h11 + (c ^ 2 - d ^ 2) * h12 + c * d * h22) ^ 2 := by
  subst hF0 hF1 hV10 hV11 hV20 hV21
  unfold calibForm
  linear_combination (-h22^2*K - 2*h12^2*K + 2*h12^2*G - 2*h11*h22*G - h11^2*K - d^2*h22^2*K + d^2*h22^2*f^2 - 2*d^2*h12^2*K + 2*d^2*h12^2*G + d^2*h12^2*f^2 - 2*d^2*h11*h22*G - d^2*h11^2*K - 2*d^2*s*h22^2*f*z - d^2*s*h12^2*Gs - 2*d^2*s*h12^2*f*z + d^2*s*h11*h22*Gs + d^2*s^2*h22^2*z^2 + d^2*s^2*h12^2*z^2 + 2*c*d*h12*h22*f^2 + 2*c*d*h11*h12*f^2 - 4*c*d*s*h12*h22*f*z - 4*c*d*s*h11*h12*f*z + 2*c*d*s^2*h12*h22*z^2 + 2*c*d*s^2*h11*h12*z^2 - c^2*h22^2*K - 2*c^2*h12^2*K + 2*c^2*h12^2*G + c^2*h12^2*f^2 - 2*c^2*h11*h22*G - c^2*h11^2*K + c^2*h11^2*f^2 - c^2*s*h12^2*Gs - 2*c^2*s*h12^2*f*z + c^2*s*h11*h22*Gs - 2*c^2*s*h11^2*f*z + c^2*s^2*h12^2*z^2 + c^2*s^2*h11^2*z^2 - P*h22*b - P*h11*b + P^2*bs - P^2*z^2) * hcd

end Buckling
end
end ChunkedSource009
/- END SOURCE 009 -/

/- BEGIN SOURCE 010: RequestProject/Concavity/ComplexBessel.lean -/
section ChunkedSource010

/-!
# Bessel functions of a complex argument

Term-by-term differentiation of the complex Bessel series: `J_n` is entire, `J₀' = -J₁`,
`J_{n+1}' = (J_n - J_{n+2})/2`, the three-term recurrence, parity, and agreement with the
real Bessel functions on the real axis.
-/

@[expose] public section

open scoped Nat
open Filter Topology

namespace Buckling

/-- The `m`-th term of the series for `J_n(ζ)`. -/
noncomputable def cterm (n m : ℕ) (ζ : ℂ) : ℂ :=
  (-1 : ℂ) ^ m * (ζ / 2) ^ (2 * m + n) / ((m ! : ℂ) * ((m + n) ! : ℂ))

lemma besselJC_eq_tsum (n : ℕ) (ζ : ℂ) : besselJC n ζ = ∑' m, cterm n m ζ := rfl

lemma norm_cterm (n m : ℕ) (ζ : ℂ) : ‖cterm n m ζ‖ = |bterm n m ‖ζ‖| := by
  rw [abs_bterm, abs_norm]
  unfold cterm
  rw [norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow, norm_div,
    Complex.norm_two]
  congr 1
  rw [norm_mul]
  simp only [Complex.norm_natCast]

lemma summable_norm_cterm (n : ℕ) (ζ : ℂ) : Summable fun m => ‖cterm n m ζ‖ := by
  simp only [norm_cterm]; exact summable_abs_bterm n _

lemma summable_cterm (n : ℕ) (ζ : ℂ) : Summable fun m => cterm n m ζ :=
  (summable_norm_cterm n ζ).of_norm

/-- The derivative of the `m`-th term. -/
noncomputable def dcterm (n m : ℕ) (ζ : ℂ) : ℂ :=
  (-1 : ℂ) ^ m * (((2 * m + n : ℕ) : ℂ) * (ζ / 2) ^ (2 * m + n - 1) * (1 / 2)) /
    ((m ! : ℂ) * ((m + n) ! : ℂ))

lemma hasDerivAt_cterm (n m : ℕ) (ζ : ℂ) : HasDerivAt (cterm n m) (dcterm n m ζ) ζ := by
  unfold cterm dcterm
  have h := ((hasDerivAt_id ζ).div_const 2).fun_pow (2 * m + n)
  have h2 := (h.const_mul ((-1 : ℂ) ^ m)).div_const ((m ! : ℂ) * ((m + n) ! : ℂ))
  simpa only [id_eq, Pi.pow_apply] using! h2

/-- Nonvanishing of the casts appearing in the coefficient identities. -/
lemma cast_ne_zero_aux (a : ℕ) : ((a : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero a

lemma dcterm_succ (n m : ℕ) (ζ : ℂ) :
    dcterm (n + 1) (m + 1) ζ = (cterm n (m + 1) ζ - cterm (n + 2) m ζ) / 2 := by
  unfold dcterm cterm
  have e1 : 2 * (m + 1) + (n + 1) - 1 = 2 * m + n + 2 := by omega
  have e2 : 2 * (m + 1) + n = 2 * m + n + 2 := by omega
  have e3 : 2 * m + (n + 2) = 2 * m + n + 2 := by omega
  rw [e1, e2, e3, show m + 1 + (n + 1) = m + n + 2 by omega,
    show m + 1 + n = m + n + 1 by omega, show m + (n + 2) = m + n + 2 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  have h1 := cast_ne_zero_aux m
  have h2 := cast_ne_zero_aux (m + n)
  have h3 := cast_ne_zero_aux (m + n + 1)
  have h4 : (m ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
  have h5 : ((m + n) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  push_cast at h1 h2 h3
  field_simp
  ring

lemma dcterm_zero_succ (n : ℕ) (ζ : ℂ) : dcterm (n + 1) 0 ζ = cterm n 0 ζ / 2 := by
  unfold dcterm cterm
  simp only [pow_zero, one_mul, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one,
    Nat.add_sub_cancel]
  rw [Nat.factorial_succ]
  push_cast
  field_simp

lemma dcterm_zero_zero (ζ : ℂ) : dcterm 0 0 ζ = 0 := by simp [dcterm]

lemma dcterm_zero (m : ℕ) (ζ : ℂ) : dcterm 0 (m + 1) ζ = -cterm 1 m ζ := by
  unfold dcterm cterm
  rw [show 2 * (m + 1) + 0 - 1 = 2 * m + 1 by omega, show m + 1 + 0 = m + 1 by omega]
  simp only [Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma norm_dcterm_le (n m : ℕ) (ζ : ℂ) (R : ℝ) (hζ : ‖ζ‖ ≤ R) :
    ‖dcterm n m ζ‖ ≤ (if n = 0 then (if m = 0 then 0 else |bterm 1 (m - 1) R|)
      else (|bterm (n - 1) m R| + (if m = 0 then 0 else |bterm (n + 1) (m - 1) R|)) / 2) := by
  have mono : ∀ a b : ℕ, ‖cterm a b ζ‖ ≤ |bterm a b R| := by
    intro a b
    rw [norm_cterm, abs_bterm, abs_bterm]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    rw [abs_norm]
    linarith [le_abs_self R]
  rcases n with _ | n
  · rcases m with _ | m
    · simp [dcterm_zero_zero]
    · simp only [if_true, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
      rw [dcterm_zero, norm_neg]; exact mono _ _
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rcases m with _ | m
    · simp only [if_true, add_zero]
      rw [dcterm_zero_succ, norm_div, Complex.norm_two]
      exact div_le_div_of_nonneg_right (mono _ _) (by norm_num)
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
      rw [dcterm_succ, norm_div, Complex.norm_two]
      exact div_le_div_of_nonneg_right
        ((norm_sub_le _ _).trans (add_le_add (mono _ _) (mono _ _))) (by norm_num)

lemma hasDerivAt_besselJC_tsum (n : ℕ) (ζ : ℂ) :
    HasDerivAt (besselJC n) (∑' m, dcterm n m ζ) ζ := by
  have hR : ‖ζ‖ < ‖ζ‖ + 1 := by linarith
  refine hasDerivAt_tsum_of_isPreconnected (summable_dbound n (‖ζ‖ + 1))
    (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ‖ζ‖ + 1))
    (convex_ball (0 : ℂ) _).isPreconnected
    (fun m y _ => hasDerivAt_cterm n m y) (fun m y hy => ?_) (y₀ := 0) ?_
    (summable_cterm n 0) ?_
  · apply norm_dcterm_le
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact hy.le
  · simp only [Metric.mem_ball, dist_self]; positivity
  · simpa using hR

/-- `J₀' = -J₁` (complex). -/
theorem hasDerivAt_besselJC_zero (ζ : ℂ) : HasDerivAt (besselJC 0) (-besselJC 1 ζ) ζ := by
  convert hasDerivAt_besselJC_tsum 0 ζ using 1
  have hs : Summable fun m => dcterm 0 m ζ := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [dcterm_zero]
    exact (summable_cterm 1 ζ).neg
  rw [hs.tsum_eq_zero_add, dcterm_zero_zero, zero_add]
  simp only [dcterm_zero]
  rw [tsum_neg]; rfl

/-- `J_{n+1}' = (J_n - J_{n+2})/2` (complex). -/
theorem hasDerivAt_besselJC_succ (n : ℕ) (ζ : ℂ) :
    HasDerivAt (besselJC (n + 1)) ((besselJC n ζ - besselJC (n + 2) ζ) / 2) ζ := by
  convert hasDerivAt_besselJC_tsum (n + 1) ζ using 1
  have hs1 : Summable fun m => (cterm n (m + 1) ζ - cterm (n + 2) m ζ) / 2 :=
    ((((summable_nat_add_iff 1).mpr (summable_cterm n ζ)).sub
      (summable_cterm (n + 2) ζ))).div_const 2
  have hs : Summable fun m => dcterm (n + 1) m ζ := by
    refine (summable_nat_add_iff 1).mp ?_
    simp only [dcterm_succ]
    exact hs1
  rw [hs.tsum_eq_zero_add, dcterm_zero_succ]
  simp only [dcterm_succ]
  rw [tsum_div_const, Summable.tsum_sub ((summable_nat_add_iff 1).mpr (summable_cterm n ζ))
    (summable_cterm (n + 2) ζ)]
  rw [besselJC_eq_tsum n, (summable_cterm n ζ).tsum_eq_zero_add, besselJC_eq_tsum (n + 2)]
  ring

lemma differentiable_besselJC (n : ℕ) : Differentiable ℂ (besselJC n) :=
  fun ζ => (hasDerivAt_besselJC_tsum n ζ).differentiableAt

lemma continuous_besselJC (n : ℕ) : Continuous (besselJC n) :=
  (differentiable_besselJC n).continuous

/-- The three-term recurrence `ζ (J_n(ζ) + J_{n+2}(ζ)) = 2(n+1) J_{n+1}(ζ)`. -/
theorem besselJC_recurrence (n : ℕ) (ζ : ℂ) :
    ζ * (besselJC n ζ + besselJC (n + 2) ζ) = 2 * (n + 1) * besselJC (n + 1) ζ := by
  have key : ∀ m, ζ * cterm n (m + 1) ζ + ζ * cterm (n + 2) m ζ
      = 2 * (n + 1) * cterm (n + 1) (m + 1) ζ := by
    intro m
    unfold cterm
    rw [show 2 * (m + 1) + n = 2 * m + n + 2 by omega,
      show 2 * m + (n + 2) = 2 * m + n + 2 by omega,
      show 2 * (m + 1) + (n + 1) = 2 * m + n + 2 + 1 by omega,
      show m + 1 + n = m + n + 1 by omega, show m + (n + 2) = m + n + 2 by omega,
      show m + 1 + (n + 1) = m + n + 2 by omega]
    simp only [Nat.factorial_succ]
    push_cast
    have h1 := cast_ne_zero_aux m
    have h2 := cast_ne_zero_aux (m + n)
    have h3 := cast_ne_zero_aux (m + n + 1)
    have h4 : (m ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
    have h5 : ((m + n) ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    push_cast at h1 h2 h3
    field_simp
    ring
  have key0 : ζ * cterm n 0 ζ = 2 * (n + 1) * cterm (n + 1) 0 ζ := by
    unfold cterm
    simp only [pow_zero, one_mul, mul_zero, zero_add, Nat.factorial_zero, Nat.cast_one]
    rw [Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
  have s1 := (summable_nat_add_iff 1).mpr (summable_cterm n ζ)
  have s2 := summable_cterm (n + 2) ζ
  calc ζ * (besselJC n ζ + besselJC (n + 2) ζ)
      = ζ * cterm n 0 ζ + (∑' m, ζ * cterm n (m + 1) ζ + ∑' m, ζ * cterm (n + 2) m ζ) := by
        rw [besselJC_eq_tsum, besselJC_eq_tsum, (summable_cterm n ζ).tsum_eq_zero_add,
          tsum_mul_left, tsum_mul_left]; ring
    _ = ζ * cterm n 0 ζ + ∑' m, (ζ * cterm n (m + 1) ζ + ζ * cterm (n + 2) m ζ) := by
        rw [Summable.tsum_add (s1.mul_left ζ) (s2.mul_left ζ)]
    _ = 2 * (n + 1) * besselJC (n + 1) ζ := by
        simp only [key]
        rw [key0, besselJC_eq_tsum, (summable_cterm (n + 1) ζ).tsum_eq_zero_add, tsum_mul_left]
        ring

/-- `ζ J₂(ζ) = 2 J₁(ζ) - ζ J₀(ζ)`. -/
lemma besselJC_two_mul (ζ : ℂ) : ζ * besselJC 2 ζ = 2 * besselJC 1 ζ - ζ * besselJC 0 ζ := by
  have h := besselJC_recurrence 0 ζ
  push_cast at h
  linear_combination h

/-- Agreement with the real Bessel function. -/
theorem besselJC_ofReal (n : ℕ) (x : ℝ) : besselJC n (x : ℂ) = (besselJ n x : ℂ) := by
  rw [besselJC_eq_tsum, besselJ_eq_tsum, Complex.ofReal_tsum]
  congr 1
  funext m
  unfold cterm bterm
  push_cast
  ring

lemma cterm_neg (n m : ℕ) (ζ : ℂ) : cterm n m (-ζ) = (-1) ^ n * cterm n m ζ := by
  unfold cterm
  have h : (-1 : ℂ) ^ (2 * m + n) = (-1) ^ n := by rw [pow_add, pow_mul]; norm_num
  rw [neg_div, neg_pow (ζ / 2), h]
  ring

/-- Parity `J_n(-ζ) = (-1)^n J_n(ζ)`. -/
theorem besselJC_neg (n : ℕ) (ζ : ℂ) : besselJC n (-ζ) = (-1) ^ n * besselJC n ζ := by
  rw [besselJC_eq_tsum, besselJC_eq_tsum, ← tsum_mul_left]
  simp only [cterm_neg]

lemma besselJC_zero_arg (n : ℕ) : besselJC n 0 = if n = 0 then 1 else 0 := by
  have := besselJC_ofReal n 0
  rw [Complex.ofReal_zero] at this
  rw [this, besselJ_zero_arg]
  split_ifs <;> simp

end Buckling
end
end ChunkedSource010
/- END SOURCE 010 -/

/- BEGIN SOURCE 011: RequestProject/Disk/Fourier1D.lean -/
section ChunkedSource011

/-!
# Real Fourier coefficients on `[0, 2π]`

For a continuous function `g` on `ℝ` we use the real coefficients
`cosC n g = (1/2π) ∫₀^{2π} g(θ) cos(nθ) dθ` and `sinC n g = (1/2π) ∫₀^{2π} g(θ) sin(nθ) dθ`,
`n ∈ ℤ`.  We record Parseval's identity (from Mathlib's complex version) and the rule
for derivatives of `2π`-periodic functions.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology intervalIntegral

namespace Buckling

namespace Fourier1D

/-- The cosine coefficient. -/
noncomputable def cosC (n : ℤ) (g : ℝ → ℝ) : ℝ :=
  1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, g θ * cos (n * θ)

/-- The sine coefficient. -/
noncomputable def sinC (n : ℤ) (g : ℝ → ℝ) : ℝ :=
  1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, g θ * sin (n * θ)

lemma fourierCoeffOn_ofReal (g : ℝ → ℝ) (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn (by positivity : (0 : ℝ) < 2 * π) (fun x => (g x : ℂ)) n =
      ((cosC n g : ℝ) : ℂ) - Complex.I * ((sinC n g : ℝ) : ℂ) := by
  rw [fourierCoeffOn_eq_integral]
  have hpt : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * π - 0)) • (g x : ℂ) =
      ((g x * cos (n * x) : ℝ) : ℂ) - Complex.I * ((g x * sin (n * x) : ℝ) : ℂ) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul]
    have hπc : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 pi_ne_zero
    have : (2 * ↑π * Complex.I * ↑(-n) * ↑x / ↑(2 * π - 0) : ℂ) = ((-(n * x) : ℝ) : ℂ) * Complex.I := by
      push_cast
      rw [sub_zero]
      field_simp
    rw [this, Complex.exp_mul_I]
    push_cast
    rw [Complex.cos_neg, Complex.sin_neg]
    ring
  simp_rw [hpt]
  have hi1 : IntervalIntegrable (fun x => ((g x * cos (n * x) : ℝ) : ℂ)) volume 0 (2 * π) :=
    (Complex.continuous_ofReal.comp (hg.mul (continuous_cos.comp
      (continuous_const.mul continuous_id)))).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => Complex.I * ((g x * sin (n * x) : ℝ) : ℂ)) volume 0
      (2 * π) :=
    (continuous_const.mul (Complex.continuous_ofReal.comp (hg.mul (continuous_sin.comp
      (continuous_const.mul continuous_id))))).intervalIntegrable _ _
  rw [integral_sub hi1 hi2, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  unfold cosC sinC
  rw [Complex.real_smul]
  push_cast
  rw [sub_zero]
  ring

/-- **Parseval's identity** with real coefficients. -/
theorem hasSum_parseval (g : ℝ → ℝ) (hg : Continuous g) :
    HasSum (fun n : ℤ => cosC n g ^ 2 + sinC n g ^ 2)
      (1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, g θ ^ 2) := by
  have hab : (0 : ℝ) < 2 * π := by positivity
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hg.continuousOn
  have hL2 : MemLp (fun x => (g x : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π))) := by
    refine MemLp.of_bound (Complex.continuous_ofReal.comp hg).aestronglyMeasurable C ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun x hx => ?_)
    simpa using hC x (Ioc_subset_Icc_self hx)
  have h := hasSum_sq_fourierCoeffOn hab hL2
  convert h using 1
  · ext n
    rw [fourierCoeffOn_ofReal g hg n, Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  · simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, sub_zero, smul_eq_mul]
    ring

/-- The derivative rule: for `2π`-periodic `C¹` functions,
`cosC n g' = n sinC n g` and `sinC n g' = -n cosC n g`. -/
theorem deriv_rule {g g' : ℝ → ℝ} (hd : ∀ θ, HasDerivAt g (g' θ) θ) (hc : Continuous g')
    (hper : g (2 * π) = g 0) (n : ℤ) :
    cosC n g' = n * sinC n g ∧ sinC n g' = -(n * cosC n g) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun θ => (hd θ).continuousAt
  have hcos : ∀ x, HasDerivAt (fun θ => cos (n * θ)) (-(sin (n * x)) * n) x := fun x => by
    have := ((hasDerivAt_id x).const_mul (n : ℝ)).cos
    simpa [mul_comm] using this
  have hsin : ∀ x, HasDerivAt (fun θ => sin (n * θ)) (cos (n * x) * n) x := fun x => by
    have := ((hasDerivAt_id x).const_mul (n : ℝ)).sin
    simpa [mul_comm] using this
  have c1 : Continuous fun x => -(sin (n * x)) * n :=
    ((continuous_sin.comp (continuous_const.mul continuous_id)).neg).mul continuous_const
  have c2 : Continuous fun x => cos (n * x) * n :=
    (continuous_cos.comp (continuous_const.mul continuous_id)).mul continuous_const
  have e1 := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π) (fun x _ => hcos x)
    (fun x _ => hd x) (c1.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have e2 := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * π) (fun x _ => hsin x)
    (fun x _ => hd x) (c2.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
  have hc2 : cos (n * (2 * π)) = 1 := cos_int_mul_two_pi n
  have hs2 : sin (n * (2 * π)) = 0 := by
    rw [show (n : ℝ) * (2 * π) = ((2 * n : ℤ) : ℝ) * π by push_cast; ring]
    exact sin_int_mul_pi _
  simp only [mul_zero, cos_zero, sin_zero, hc2, hs2, hper] at e1 e2
  constructor
  · unfold cosC sinC
    have : ∫ θ in (0 : ℝ)..2 * π, g' θ * cos (n * θ) = n * ∫ θ in (0 : ℝ)..2 * π, g θ * sin (n * θ) := by
      have h1 : ∫ θ in (0 : ℝ)..2 * π, g' θ * cos (n * θ) =
          ∫ θ in (0 : ℝ)..2 * π, cos (n * θ) * g' θ := by
        congr 1; ext θ; ring
      have h2 : ∫ θ in (0 : ℝ)..2 * π, -sin (n * θ) * n * g θ =
          -(n * ∫ θ in (0 : ℝ)..2 * π, g θ * sin (n * θ)) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
        congr 1; ext θ; ring
      rw [h1, e1, h2]; ring
    rw [this]; ring
  · unfold cosC sinC
    have : ∫ θ in (0 : ℝ)..2 * π, g' θ * sin (n * θ) = -(n * ∫ θ in (0 : ℝ)..2 * π, g θ * cos (n * θ)) := by
      have h1 : ∫ θ in (0 : ℝ)..2 * π, g' θ * sin (n * θ) =
          ∫ θ in (0 : ℝ)..2 * π, sin (n * θ) * g' θ := by
        congr 1; ext θ; ring
      have h2 : ∫ θ in (0 : ℝ)..2 * π, cos (n * θ) * n * g θ =
          n * ∫ θ in (0 : ℝ)..2 * π, g θ * cos (n * θ) := by
        rw [← intervalIntegral.integral_const_mul]
        congr 1; ext θ; ring
      rw [h1, e2, h2]; ring
    rw [this]; ring

lemma cosC_neg (n : ℤ) (g : ℝ → ℝ) : cosC n (fun θ => -g θ) = -cosC n g := by
  unfold cosC
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 2; ext θ; ring

lemma sinC_neg (n : ℤ) (g : ℝ → ℝ) : sinC n (fun θ => -g θ) = -sinC n g := by
  unfold sinC
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 2; ext θ; ring

/-- Nonzero coefficients of a constant vanish. -/
lemma coeff_const {n : ℤ} (hn : n ≠ 0) (c : ℝ) :
    cosC n (fun _ => c) = 0 ∧ sinC n (fun _ => c) = 0 := by
  have h := deriv_rule (g := fun _ => c) (g' := fun _ => 0) (fun θ => hasDerivAt_const θ c)
    continuous_const rfl n
  have h0 : cosC n (fun _ => 0) = 0 ∧ sinC n (fun _ => 0) = 0 := by simp [cosC, sinC]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [h0.1] at h; rw [h0.2] at h
  constructor
  · have h3 : (n : ℝ) * cosC n (fun _ => c) = 0 := by linarith [h.2]
    rcases mul_eq_zero.1 h3 with h' | h'
    · exact absurd h' hn'
    · exact h'
  · have := h.1; rcases mul_eq_zero.1 this.symm with h' | h'
    · exact absurd h' hn'
    · exact h'

/-- Coefficients of `α cos θ + β sin θ` vanish except for `n = ±1`. -/
lemma coeff_trig {n : ℤ} (h1 : n ≠ 1) (h2 : n ≠ -1) (α β : ℝ) :
    cosC n (fun θ => α * cos θ + β * sin θ) = 0 ∧
      sinC n (fun θ => α * cos θ + β * sin θ) = 0 := by
  set h : ℝ → ℝ := fun θ => α * cos θ + β * sin θ with hh
  set h' : ℝ → ℝ := fun θ => -(α * sin θ) + β * cos θ with hh'
  have hd : ∀ θ, HasDerivAt h (h' θ) θ := fun θ => by
    have := ((hasDerivAt_cos θ).const_mul α).add ((hasDerivAt_sin θ).const_mul β)
    convert this using 1; simp [hh']
  have hd' : ∀ θ, HasDerivAt h' (-h θ) θ := fun θ => by
    have := ((hasDerivAt_sin θ).const_mul α).neg.add ((hasDerivAt_cos θ).const_mul β)
    convert this using 1; simp [hh]; ring
  have hc' : Continuous h' := by simp only [hh']; fun_prop
  have hc'' : Continuous fun θ => -h θ := by simp only [hh]; fun_prop
  have hp : h (2 * π) = h 0 := by simp [hh]
  have hp' : h' (2 * π) = h' 0 := by simp [hh']
  have r1 := deriv_rule hd hc' hp n
  have r2 := deriv_rule hd' hc'' hp' n
  rw [cosC_neg, sinC_neg, r1.1, r1.2] at r2
  have hn2 : (n : ℝ) ^ 2 - 1 ≠ 0 := by
    intro h0
    have : ((n : ℝ) - 1) * ((n : ℝ) + 1) = 0 := by linear_combination h0
    rcases mul_eq_zero.1 this with h3 | h3
    · exact h1 (by exact_mod_cast (by linarith : (n : ℝ) = 1))
    · exact h2 (by exact_mod_cast (by linarith : (n : ℝ) = -1))
  constructor
  · have e : ((n : ℝ) ^ 2 - 1) * cosC n h = 0 := by linear_combination r2.1
    rcases mul_eq_zero.1 e with h3 | h3
    · exact absurd h3 hn2
    · exact h3
  · have e : ((n : ℝ) ^ 2 - 1) * sinC n h = 0 := by linear_combination r2.2
    rcases mul_eq_zero.1 e with h3 | h3
    · exact absurd h3 hn2
    · exact h3

/-- A parametric integral against a fixed bounded weight is differentiable. -/
lemma hasDerivAt_wcoeff {F F' : ℝ → ℝ → ℝ} (hF : ∀ r θ, HasDerivAt (fun r => F r θ) (F' r θ) r)
    (hFc : Continuous (Function.uncurry F)) (hF'c : Continuous (Function.uncurry F'))
    {C : ℝ} (hb : ∀ r θ, |F' r θ| ≤ C) {w : ℝ → ℝ} (hw : Continuous w)
    (hwb : ∀ θ, |w θ| ≤ 1) (r : ℝ) :
    HasDerivAt (fun r => 1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, F r θ * w θ)
      (1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, F' r θ * w θ) r := by
  have hc : ∀ x, Continuous fun θ => F x θ * w θ := fun x =>
    (hFc.comp (continuous_const.prodMk continuous_id)).mul hw
  have hc' : ∀ x, Continuous fun θ => F' x θ * w θ := fun x =>
    (hF'c.comp (continuous_const.prodMk continuous_id)).mul hw
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 2 * π) (F := fun x θ => F x θ * w θ)
    (F' := fun x θ => F' x θ * w θ) (x₀ := r) (bound := fun _ => C) (s := univ)
    Filter.univ_mem (Eventually.of_forall fun x => (hc x).aestronglyMeasurable)
    ((hc r).intervalIntegrable _ _) (hc' r).aestronglyMeasurable
    (Eventually.of_forall fun θ _ x _ => by
      rw [Real.norm_eq_abs, abs_mul]
      calc |F' x θ| * |w θ| ≤ C * 1 :=
            mul_le_mul (hb x θ) (hwb θ) (abs_nonneg _) ((abs_nonneg _).trans (hb x θ))
        _ = C := mul_one C)
    intervalIntegrable_const
    (Eventually.of_forall fun θ _ x _ => (hF x θ).mul_const (w θ))
  exact h.2.const_mul _

lemma continuous_wcoeff {F : ℝ → ℝ → ℝ} (hFc : Continuous (Function.uncurry F)) {w : ℝ → ℝ}
    (hw : Continuous w) :
    Continuous fun r => 1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, F r θ * w θ := by
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun r θ => F r θ * w θ) (hFc.mul (hw.comp continuous_snd)) _ _

lemma abs_cos_le (n : ℤ) (θ : ℝ) : |cos (n * θ)| ≤ 1 := abs_cos_le_one _
lemma abs_sin_le (n : ℤ) (θ : ℝ) : |sin (n * θ)| ≤ 1 := abs_sin_le_one _
lemma continuous_cos_n (n : ℤ) : Continuous fun θ : ℝ => cos (n * θ) :=
  continuous_cos.comp (continuous_const.mul continuous_id)
lemma continuous_sin_n (n : ℤ) : Continuous fun θ : ℝ => sin (n * θ) :=
  continuous_sin.comp (continuous_const.mul continuous_id)

/-- Linearity of the coefficients for continuous functions. -/
lemma cosC_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    cosC n (fun θ => f θ + g θ) = cosC n f + cosC n g := by
  unfold cosC
  have := integral_add (μ := volume) (a := 0) (b := 2 * π) (f := fun θ => f θ * cos (n * θ))
    (g := fun θ => g θ * cos (n * θ)) ((hf.mul (continuous_cos_n n)).intervalIntegrable _ _)
    ((hg.mul (continuous_cos_n n)).intervalIntegrable _ _)
  rw [← mul_add, ← this]
  congr 2; ext θ; ring

lemma sinC_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    sinC n (fun θ => f θ + g θ) = sinC n f + sinC n g := by
  unfold sinC
  have := integral_add (μ := volume) (a := 0) (b := 2 * π) (f := fun θ => f θ * sin (n * θ))
    (g := fun θ => g θ * sin (n * θ)) ((hf.mul (continuous_sin_n n)).intervalIntegrable _ _)
    ((hg.mul (continuous_sin_n n)).intervalIntegrable _ _)
  rw [← mul_add, ← this]
  congr 2; ext θ; ring

lemma cosC_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℤ) :
    cosC n (fun θ => c * f θ) = c * cosC n f := by
  unfold cosC
  rw [show (fun θ => c * f θ * cos (n * θ)) = fun θ => c * (f θ * cos (n * θ)) by ext; ring,
    intervalIntegral.integral_const_mul]
  ring

lemma sinC_const_mul (c : ℝ) (f : ℝ → ℝ) (n : ℤ) :
    sinC n (fun θ => c * f θ) = c * sinC n f := by
  unfold sinC
  rw [show (fun θ => c * f θ * sin (n * θ)) = fun θ => c * (f θ * sin (n * θ)) by ext; ring,
    intervalIntegral.integral_const_mul]
  ring

end Fourier1D

end Buckling
end
end ChunkedSource011
/- END SOURCE 011 -/

/- BEGIN SOURCE 012: RequestProject/Disk/Ground1D.lean -/
section ChunkedSource012

/-!
# A one-dimensional weighted ground-state inequality with a spectral gap

Let `χ > 0` on `(0, R)` solve `(r χ')' = χ / r - μ r χ`, with `χ(0) = χ(R) = 0`,
`χ'(0) > 0 > χ'(R)`.  For admissible `w` (vanishing to first order at `0` and near `R`)
the ground-state substitution `ψ = w / χ` gives
`∫ (r w'² + w²/r) - μ ∫ r w² = ∫ r χ² ψ'²`,
and a weighted Hardy (Cheeger) argument with the weight `p = r χ²` yields a gap
`∫ r χ² ψ'² ≥ δ · (∫ r w² - (∫ r χ w)² / ∫ r χ²)`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology intervalIntegral

namespace Buckling

namespace Ground1D

/-- A bounded function continuous on `(a, b)` is interval integrable. -/
lemma ii_of_bdd {a b K : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hc : ContinuousOn f (Ioo a b))
    (hb : ∀ x ∈ Ioo a b, |f x| ≤ K) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hab]
  refine Integrable.mono' (g := fun _ => K) ?_ (hc.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => by
      simpa [Real.norm_eq_abs] using hb x hx))
  exact integrableOn_const (by simp [Real.volume_Ioo])

/-- Monotonicity of interval integrals from a pointwise bound on the open interval. -/
lemma integral_mono_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ} (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b) (h : ∀ x ∈ Ioo a b, f x ≤ g x) :
    ∫ x in a..b, f x ≤ ∫ x in a..b, g x := by
  rw [integral_of_le hab, integral_of_le hab]
  refine setIntegral_mono_on_ae ?_ ?_ measurableSet_Ioc ?_
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hf
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hg
  · have hb : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
      rw [ae_iff]; simp
    filter_upwards [hb] with x hxb hx
    exact h x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩

/-- Equality of interval integrals from pointwise equality on the open interval. -/
lemma integral_congr_Ioo {a b : ℝ} (hab : a ≤ b) {f g : ℝ → ℝ}
    (h : ∀ x ∈ Ioo a b, f x = g x) : ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [integral_of_le hab, integral_of_le hab]
  refine setIntegral_congr_ae measurableSet_Ioc ?_
  have hb : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
    rw [ae_iff]; simp
  filter_upwards [hb] with x hxb hx
  exact h x ⟨hx.1, lt_of_le_of_ne hx.2 hxb⟩

/-- A function bounded by `K r` near `0⁺` tends to `0`. -/
lemma tendsto_zero_of_le_mul {G : ℝ → ℝ} {K ε : ℝ} (hε : 0 < ε)
    (h : ∀ r ∈ Ioo 0 ε, |G r| ≤ K * r) : Tendsto G (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => K * r) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => K * r) (𝓝 0) (𝓝 (K * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [Ioo_mem_nhdsGT hε] with r hr
  simpa [Real.norm_eq_abs] using h r hr

/-- Hypotheses on the one-dimensional ground state. -/
structure GroundState (R μ : ℝ) (χ dχ : ℝ → ℝ) : Prop where
  R_pos : 0 < R
  cont : Continuous χ
  dcont : Continuous dχ
  deriv : ∀ r, HasDerivAt χ (dχ r) r
  zero0 : χ 0 = 0
  zeroR : χ R = 0
  pos : ∀ r ∈ Ioo 0 R, 0 < χ r
  d0 : 0 < dχ 0
  dR : dχ R < 0
  flux : ∀ r ∈ Ioo 0 R, HasDerivAt (fun s => s * dχ s) (χ r / r - μ * r * χ r) r

/-- Admissible functions: differentiable on `(0, R)`, `O(r)` at `0`, vanishing near `R`. -/
structure Admissible (R : ℝ) (w dw : ℝ → ℝ) : Prop where
  deriv : ∀ r ∈ Ioo 0 R, HasDerivAt w (dw r) r
  dcont : ContinuousOn dw (Ioo 0 R)
  bound : ∃ C, ∀ r ∈ Ioo 0 R, |w r| ≤ C * r ∧ |dw r| ≤ C
  supp : ∃ R' ∈ Ioo 0 R, ∀ r ∈ Icc R' R, w r = 0 ∧ dw r = 0

/-- The weighted energy `∫₀ᴿ (r w'² + w²/r)`. -/
noncomputable def energy (R : ℝ) (w dw : ℝ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, (r * dw r ^ 2 + w r ^ 2 / r)

/-- The weighted mass `∫₀ᴿ r w²`. -/
noncomputable def mass (R : ℝ) (w : ℝ → ℝ) : ℝ := ∫ r in (0 : ℝ)..R, r * w r ^ 2

/-- The weighted pairing `∫₀ᴿ r f g`. -/
noncomputable def pair (R : ℝ) (f g : ℝ → ℝ) : ℝ := ∫ r in (0 : ℝ)..R, r * f r * g r

/-- The derivative of the quotient `w / χ`. -/
noncomputable def dquot (χ dχ w dw : ℝ → ℝ) (r : ℝ) : ℝ :=
  (dw r * χ r - w r * dχ r) / χ r ^ 2

variable {R μ : ℝ} {χ dχ : ℝ → ℝ}

lemma sq_le_of_abs_le {x C : ℝ} (h : |x| ≤ C) : x ^ 2 ≤ C ^ 2 := by
  rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2

lemma exists_closed_nhds_pos {f : ℝ → ℝ} (hf : Continuous f) {x₀ c : ℝ} (h : c < f x₀) :
    ∃ ε > 0, ∀ r, |r - x₀| ≤ ε → c < f r := by
  have := hf.continuousAt.eventually (lt_mem_nhds h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 this
  refine ⟨ε / 2, by positivity, fun r hr => hball ?_⟩
  rw [Real.dist_eq]; linarith

lemma exists_closed_nhds_neg {f : ℝ → ℝ} (hf : Continuous f) {x₀ c : ℝ} (h : f x₀ < c) :
    ∃ ε > 0, ∀ r, |r - x₀| ≤ ε → f r < c := by
  obtain ⟨ε, hε, h'⟩ := exists_closed_nhds_pos (f := fun r => -f r) hf.neg (c := -c)
    (by simpa using h)
  exact ⟨ε, hε, fun r hr => by simpa using h' r hr⟩


/-- Pointwise AM–GM used in the Hardy arguments. -/
lemma amgm_aux {P p g d l : ℝ} (hl : 0 < l) (hP0 : 0 ≤ P) (hP : P ≤ l * p) :
    -(1 / 2 * (p * g ^ 2) + 2 * l ^ 2 * (p * d ^ 2)) ≤ P * (2 * g * d) ∧
    P * (2 * g * d) ≤ 1 / 2 * (p * g ^ 2) + 2 * l ^ 2 * (p * d ^ 2) := by
  have hq : 0 ≤ g ^ 2 / (2 * l) + 2 * l * d ^ 2 := by positivity
  have e1 : g ^ 2 / (2 * l) + 2 * l * d ^ 2 + 2 * g * d = (g + 2 * l * d) ^ 2 / (2 * l) := by
    field_simp; ring
  have e2 : g ^ 2 / (2 * l) + 2 * l * d ^ 2 - 2 * g * d = (g - 2 * l * d) ^ 2 / (2 * l) := by
    field_simp; ring
  have h1 : 0 ≤ (g + 2 * l * d) ^ 2 / (2 * l) := by positivity
  have h2 : 0 ≤ (g - 2 * l * d) ^ 2 / (2 * l) := by positivity
  have hb : P * (g ^ 2 / (2 * l) + 2 * l * d ^ 2) ≤ l * p * (g ^ 2 / (2 * l) + 2 * l * d ^ 2) :=
    mul_le_mul_of_nonneg_right hP hq
  have e3 : l * p * (g ^ 2 / (2 * l) + 2 * l * d ^ 2) =
      1 / 2 * (p * g ^ 2) + 2 * l ^ 2 * (p * d ^ 2) := by field_simp
  constructor
  · nlinarith [mul_nonneg hP0 h1]
  · nlinarith [mul_nonneg hP0 h2]

/-- **Weighted Hardy inequality, anchored at the right endpoint.** -/
lemma hardy_left {a b l : ℝ} (hab : a < b) (hl : 0 < l) {p ψ dψ : ℝ → ℝ} (hp : Continuous p)
    (hp0 : ∀ r ∈ Icc a b, 0 ≤ p r) (hP : ∀ t ∈ Ioo a b, (∫ r in a..t, p r) ≤ l * p t)
    (hψ : ∀ r ∈ Ioo a b, HasDerivAt ψ (dψ r) r) (hψb : ContinuousAt ψ b)
    (hdc : ContinuousOn dψ (Ioo a b)) (hB : ∃ B, ∀ r ∈ Ioo a b, |ψ r| ≤ B)
    (hK : ∃ K, ∀ r ∈ Ioo a b, p r * dψ r ^ 2 ≤ K) :
    ∫ r in a..b, p r * (ψ r - ψ b) ^ 2 ≤ 4 * l ^ 2 * ∫ r in a..b, p r * dψ r ^ 2 := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨K, hK⟩ := hK
  set P : ℝ → ℝ := fun t => ∫ r in a..t, p r with hPdef
  have hPd : ∀ t, HasDerivAt P (p t) t := fun t =>
    integral_hasDerivAt_right (hp.intervalIntegrable a t) (hp.stronglyMeasurableAtFilter _ _)
      hp.continuousAt
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun t => (hPd t).continuousAt
  have hP0 : ∀ t ∈ Ioo a b, 0 ≤ P t := fun t ht =>
    integral_nonneg ht.1.le (fun r hr => hp0 r ⟨hr.1, hr.2.trans ht.2.le⟩)
  obtain ⟨Mp, hMp⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hp.continuousOn
  have hψc : ContinuousOn ψ (Ioo a b) := fun r hr => (hψ r hr).continuousAt.continuousWithinAt
  set B' := B + |ψ b|
  have hg : ∀ r ∈ Ioo a b, |ψ r - ψ b| ≤ B' := fun r hr =>
    (abs_sub _ _).trans (add_le_add_left (hB r hr) _)
  have hpI : ∀ r ∈ Ioo a b, 0 ≤ p r ∧ p r ≤ Mp := fun r hr =>
    ⟨hp0 r (Ioo_subset_Icc_self hr),
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMp r (Ioo_subset_Icc_self hr))⟩
  have hF : ∀ r ∈ Ioo a b, p r * (ψ r - ψ b) ^ 2 ≤ Mp * B' ^ 2 := fun r hr =>
    mul_le_mul (hpI r hr).2 (sq_le_of_abs_le (hg r hr)) (sq_nonneg _)
      ((hpI r hr).1.trans (hpI r hr).2)
  have iF : IntervalIntegrable (fun r => p r * (ψ r - ψ b) ^ 2) volume a b := by
    refine ii_of_bdd (K := Mp * B' ^ 2) hab.le
      (hp.continuousOn.mul ((hψc.sub continuousOn_const).pow 2)) (fun r hr => ?_)
    rw [abs_of_nonneg (mul_nonneg (hpI r hr).1 (sq_nonneg _))]; exact hF r hr
  have iD : IntervalIntegrable (fun r => p r * dψ r ^ 2) volume a b := by
    refine ii_of_bdd (K := K) hab.le (hp.continuousOn.mul (hdc.pow 2)) (fun r hr => ?_)
    rw [abs_of_nonneg (mul_nonneg (hpI r hr).1 (sq_nonneg _))]; exact hK r hr
  have iX : IntervalIntegrable (fun r => P r * (2 * (ψ r - ψ b) * dψ r)) volume a b := by
    refine ii_of_bdd (K := 1 / 2 * (Mp * B' ^ 2) + 2 * l ^ 2 * K) hab.le
      (hPc.continuousOn.mul ((continuousOn_const.mul (hψc.sub continuousOn_const)).mul hdc))
      (fun r hr => ?_)
    have h := amgm_aux (g := ψ r - ψ b) (d := dψ r) hl (hP0 r hr) (hP r hr)
    rw [abs_le]
    constructor <;> nlinarith [hF r hr, hK r hr, h.1, h.2]
  set H : ℝ → ℝ := fun t => P t * (ψ t - ψ b) ^ 2 with hH
  have hderiv : ∀ r ∈ Ioo a b, HasDerivAt H
      (p r * (ψ r - ψ b) ^ 2 + P r * (2 * (ψ r - ψ b) * dψ r)) r := by
    intro r hr
    have h := (hPd r).mul (((hψ r hr).sub_const (ψ b)).pow 2)
    convert h using 1
    simp
  have h0 : Tendsto H (𝓝[>] a) (𝓝 0) := by
    have ht : Tendsto (fun t => |P t| * B' ^ 2) (𝓝[>] a) (𝓝 0) := by
      have : Tendsto (fun t => |P t| * B' ^ 2) (𝓝 a) (𝓝 (|P a| * B' ^ 2)) :=
        ((continuous_abs.comp hPc).mul continuous_const).tendsto a
      simpa [hPdef] using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [Ioo_mem_nhdsGT hab] with t ht
    rw [Real.norm_eq_abs, hH, abs_mul, abs_of_nonneg (sq_nonneg (ψ t - ψ b))]
    exact mul_le_mul_of_nonneg_left (sq_le_of_abs_le (hg t ht)) (abs_nonneg _)
  have h1 : Tendsto H (𝓝[<] b) (𝓝 0) := by
    have : Tendsto H (𝓝 b) (𝓝 (H b)) :=
      (hPc.continuousAt.mul ((hψb.sub continuousAt_const).pow 2)).tendsto
    simpa [hH] using this.mono_left nhdsWithin_le_nhds
  have hftc := integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv (iF.add iX) h0 h1
  have hmono : ∫ r in a..b, (1 / 2 * (p r * (ψ r - ψ b) ^ 2) - 2 * l ^ 2 * (p r * dψ r ^ 2)) ≤
      ∫ r in a..b, (p r * (ψ r - ψ b) ^ 2 + P r * (2 * (ψ r - ψ b) * dψ r)) := by
    refine integral_mono_Ioo hab.le ((iF.const_mul _).sub (iD.const_mul _)) (iF.add iX)
      (fun r hr => ?_)
    have h := (amgm_aux (g := ψ r - ψ b) (d := dψ r) hl (hP0 r hr) (hP r hr)).1
    linarith
  rw [hftc, integral_sub (iF.const_mul _) (iD.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  linarith

/-- **Weighted Hardy inequality, anchored at the left endpoint.** -/
lemma hardy_right {a b l : ℝ} (hab : a < b) (hl : 0 < l) {p ψ dψ : ℝ → ℝ} (hp : Continuous p)
    (hp0 : ∀ r ∈ Icc a b, 0 ≤ p r) (hQ : ∀ t ∈ Ioo a b, (∫ r in t..b, p r) ≤ l * p t)
    (hψ : ∀ r ∈ Ioo a b, HasDerivAt ψ (dψ r) r) (hψa : ContinuousAt ψ a)
    (hdc : ContinuousOn dψ (Ioo a b)) (hB : ∃ B, ∀ r ∈ Ioo a b, |ψ r| ≤ B)
    (hK : ∃ K, ∀ r ∈ Ioo a b, p r * dψ r ^ 2 ≤ K) :
    ∫ r in a..b, p r * (ψ r - ψ a) ^ 2 ≤ 4 * l ^ 2 * ∫ r in a..b, p r * dψ r ^ 2 := by
  obtain ⟨B, hB⟩ := hB
  obtain ⟨K, hK⟩ := hK
  set Q : ℝ → ℝ := fun t => ∫ r in t..b, p r with hQdef
  have hQd : ∀ t, HasDerivAt Q (-p t) t := fun t =>
    integral_hasDerivAt_left (hp.intervalIntegrable t b) (hp.stronglyMeasurableAtFilter _ _)
      hp.continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.2 fun t => (hQd t).continuousAt
  have hQ0 : ∀ t ∈ Ioo a b, 0 ≤ Q t := fun t ht =>
    integral_nonneg ht.2.le (fun r hr => hp0 r ⟨ht.1.le.trans hr.1, hr.2⟩)
  obtain ⟨Mp, hMp⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    hp.continuousOn
  have hψc : ContinuousOn ψ (Ioo a b) := fun r hr => (hψ r hr).continuousAt.continuousWithinAt
  set B' := B + |ψ a|
  have hg : ∀ r ∈ Ioo a b, |ψ r - ψ a| ≤ B' := fun r hr =>
    (abs_sub _ _).trans (add_le_add_left (hB r hr) _)
  have hpI : ∀ r ∈ Ioo a b, 0 ≤ p r ∧ p r ≤ Mp := fun r hr =>
    ⟨hp0 r (Ioo_subset_Icc_self hr),
      (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hMp r (Ioo_subset_Icc_self hr))⟩
  have hF : ∀ r ∈ Ioo a b, p r * (ψ r - ψ a) ^ 2 ≤ Mp * B' ^ 2 := fun r hr =>
    mul_le_mul (hpI r hr).2 (sq_le_of_abs_le (hg r hr)) (sq_nonneg _)
      ((hpI r hr).1.trans (hpI r hr).2)
  have iF : IntervalIntegrable (fun r => p r * (ψ r - ψ a) ^ 2) volume a b := by
    refine ii_of_bdd (K := Mp * B' ^ 2) hab.le
      (hp.continuousOn.mul ((hψc.sub continuousOn_const).pow 2)) (fun r hr => ?_)
    rw [abs_of_nonneg (mul_nonneg (hpI r hr).1 (sq_nonneg _))]; exact hF r hr
  have iD : IntervalIntegrable (fun r => p r * dψ r ^ 2) volume a b := by
    refine ii_of_bdd (K := K) hab.le (hp.continuousOn.mul (hdc.pow 2)) (fun r hr => ?_)
    rw [abs_of_nonneg (mul_nonneg (hpI r hr).1 (sq_nonneg _))]; exact hK r hr
  have iX : IntervalIntegrable (fun r => Q r * (2 * (ψ r - ψ a) * dψ r)) volume a b := by
    refine ii_of_bdd (K := 1 / 2 * (Mp * B' ^ 2) + 2 * l ^ 2 * K) hab.le
      (hQc.continuousOn.mul ((continuousOn_const.mul (hψc.sub continuousOn_const)).mul hdc))
      (fun r hr => ?_)
    have h := amgm_aux (g := ψ r - ψ a) (d := dψ r) hl (hQ0 r hr) (hQ r hr)
    rw [abs_le]
    constructor <;> nlinarith [hF r hr, hK r hr, h.1, h.2]
  set H : ℝ → ℝ := fun t => Q t * (ψ t - ψ a) ^ 2 with hH
  have hderiv : ∀ r ∈ Ioo a b, HasDerivAt H
      (-(p r * (ψ r - ψ a) ^ 2) + Q r * (2 * (ψ r - ψ a) * dψ r)) r := by
    intro r hr
    have h := (hQd r).mul (((hψ r hr).sub_const (ψ a)).pow 2)
    convert h using 1
    simp
  have h1 : Tendsto H (𝓝[<] b) (𝓝 0) := by
    have ht : Tendsto (fun t => |Q t| * B' ^ 2) (𝓝[<] b) (𝓝 0) := by
      have : Tendsto (fun t => |Q t| * B' ^ 2) (𝓝 b) (𝓝 (|Q b| * B' ^ 2)) :=
        ((continuous_abs.comp hQc).mul continuous_const).tendsto b
      simpa [hQdef] using this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ ht
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    rw [Real.norm_eq_abs, hH, abs_mul, abs_of_nonneg (sq_nonneg (ψ t - ψ a))]
    exact mul_le_mul_of_nonneg_left (sq_le_of_abs_le (hg t ht)) (abs_nonneg _)
  have h0 : Tendsto H (𝓝[>] a) (𝓝 0) := by
    have : Tendsto H (𝓝 a) (𝓝 (H a)) :=
      (hQc.continuousAt.mul ((hψa.sub continuousAt_const).pow 2)).tendsto
    simpa [hH] using this.mono_left nhdsWithin_le_nhds
  have hftc := integral_eq_sub_of_hasDerivAt_of_tendsto hab hderiv (iF.neg.add iX) h0 h1
  have hmono : ∫ r in a..b, Q r * (2 * (ψ r - ψ a) * dψ r) ≤
      ∫ r in a..b, (1 / 2 * (p r * (ψ r - ψ a) ^ 2) + 2 * l ^ 2 * (p r * dψ r ^ 2)) := by
    refine integral_mono_Ioo hab.le iX ((iF.const_mul _).add (iD.const_mul _))
      (fun r hr => ?_)
    exact (amgm_aux (g := ψ r - ψ a) (d := dψ r) hl (hQ0 r hr) (hQ r hr)).2
  rw [integral_add (iF.const_mul _) (iD.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hmono
  have e := integral_add (μ := volume) (a := a) (b := b)
    (f := fun r => -(p r * (ψ r - ψ a) ^ 2)) (g := fun r => Q r * (2 * (ψ r - ψ a) * dψ r))
    iF.neg iX
  simp only [intervalIntegral.integral_neg] at e
  rw [e] at hftc
  linarith

namespace GroundState

variable (gs : GroundState R μ χ dχ)
include gs

lemma nonneg : ∀ r ∈ Icc 0 R, 0 ≤ χ r := by
  intro r hr
  rcases eq_or_lt_of_le hr.1 with h | h
  · rw [← h, gs.zero0]
  rcases eq_or_lt_of_le hr.2 with h' | h'
  · rw [h', gs.zeroR]
  exact (gs.pos r ⟨h, h'⟩).le

/-- Monotone near `0`, antitone near `R`. -/
lemma mono : ∃ s₁ s₂, 0 < s₁ ∧ s₁ < s₂ ∧ s₂ < R ∧ MonotoneOn χ (Icc 0 s₁) ∧
    AntitoneOn χ (Icc s₂ R) ∧ ∀ r ∈ Icc 0 s₁, dχ 0 / 2 ≤ dχ r := by
  obtain ⟨ε, hε, hε'⟩ := exists_closed_nhds_pos gs.dcont (x₀ := 0) (c := dχ 0 / 2) (by linarith [gs.d0])
  obtain ⟨ε', hε'0, hε''⟩ := exists_closed_nhds_neg gs.dcont gs.dR
  set s₁ := min ε (R / 3)
  set s₂ := max (R - ε') (2 * R / 3)
  have hR := gs.R_pos
  have hs₁ : 0 < s₁ := lt_min hε (by linarith)
  have hs₁' : s₁ ≤ R / 3 := min_le_right _ _
  have hs₂ : 2 * R / 3 ≤ s₂ := le_max_right _ _
  have hs₂' : s₂ < R := max_lt (by linarith) (by linarith)
  have hd1 : ∀ r ∈ Icc 0 s₁, dχ 0 / 2 ≤ dχ r := by
    intro r hr
    refine (hε' r ?_).le
    rw [abs_le]; constructor <;> linarith [hr.1, hr.2, min_le_left ε (R / 3)]
  refine ⟨s₁, s₂, hs₁, by linarith, hs₂', ?_, ?_, hd1⟩
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) gs.cont.continuousOn
      (fun x _ => (gs.deriv x).hasDerivWithinAt) (fun x hx => ?_)
    rw [interior_Icc] at hx
    linarith [hd1 x (Ioo_subset_Icc_self hx), gs.d0]
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) gs.cont.continuousOn
      (fun x _ => (gs.deriv x).hasDerivWithinAt) (fun x hx => ?_)
    rw [interior_Icc] at hx
    refine (hε'' x ?_).le
    rw [abs_le]; constructor <;> linarith [hx.1, hx.2, le_max_left (R - ε') (2 * R / 3)]

/-- A linear lower bound `χ(r) ≥ c r` on `(0, R']`. -/
lemma lower {R' : ℝ} (hR' : R' ∈ Ioo 0 R) : ∃ c > 0, ∀ r ∈ Ioc 0 R', c * r ≤ χ r := by
  obtain ⟨s₁, s₂, hs₁, hs₁₂, hs₂, -, -, hd⟩ := gs.mono
  set s := min s₁ R'
  have hs : 0 < s := lt_min hs₁ hR'.1
  -- linear bound on `[0, s]`
  have hlin : ∀ r ∈ Icc 0 s, dχ 0 / 2 * r ≤ χ r := by
    have hm : MonotoneOn (fun r => χ r - dχ 0 / 2 * r) (Icc 0 s) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
        (gs.cont.continuousOn.sub (continuousOn_const.mul continuousOn_id))
        (fun x _ => ((gs.deriv x).sub ((hasDerivAt_id x).const_mul _)).hasDerivWithinAt)
        (fun x hx => ?_)
      rw [interior_Icc] at hx
      have := hd x ⟨hx.1.le, hx.2.le.trans (min_le_left _ _)⟩
      simp only [mul_one]; linarith
    intro r hr
    have := hm ⟨le_refl 0, hs.le⟩ hr hr.1
    simp only [mul_zero, sub_zero, gs.zero0] at this
    linarith
  -- positive minimum on `[s, R']`
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := s) (b := R')).exists_isMinOn
    (nonempty_Icc.2 (min_le_right _ _)) gs.cont.continuousOn
  have hx₀pos : 0 < χ x₀ := gs.pos x₀ ⟨hs.trans_le hx₀.1, hx₀.2.trans_lt hR'.2⟩
  refine ⟨min (dχ 0 / 2) (χ x₀ / R'), lt_min (by linarith [gs.d0]) (div_pos hx₀pos hR'.1),
    fun r hr => ?_⟩
  rcases le_or_gt r s with h | h
  · calc min (dχ 0 / 2) (χ x₀ / R') * r ≤ dχ 0 / 2 * r :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hr.1.le
      _ ≤ χ r := hlin r ⟨hr.1.le, h⟩
  · calc min (dχ 0 / 2) (χ x₀ / R') * r ≤ χ x₀ / R' * r :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hr.1.le
      _ ≤ χ x₀ / R' * R' := mul_le_mul_of_nonneg_left hr.2 (div_pos hx₀pos hR'.1).le
      _ = χ x₀ := by field_simp [hR'.1.ne']
      _ ≤ χ r := hmin ⟨h.le, hr.2⟩


/-- Bounds on the primitives of the weight `r χ²` used in the Hardy arguments. -/
lemma weight_bounds : ∃ s₁ lL lR, 0 < s₁ ∧ s₁ < R ∧ 0 < lL ∧ 0 < lR ∧
    (∀ t ∈ Ioo 0 s₁, (∫ r in (0 : ℝ)..t, r * χ r ^ 2) ≤ lL * (t * χ t ^ 2)) ∧
    (∀ t ∈ Ioo s₁ R, (∫ r in t..R, r * χ r ^ 2) ≤ lR * (t * χ t ^ 2)) := by
  obtain ⟨s₁, s₂, hs₁, hs₁₂, hs₂, hmono, hanti, -⟩ := gs.mono
  have hR := gs.R_pos
  have hpc : Continuous fun r => r * χ r ^ 2 := continuous_id.mul (gs.cont.pow 2)
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_Icc (a := s₁) (b := s₂)).exists_isMinOn
    (nonempty_Icc.2 hs₁₂.le) gs.cont.continuousOn
  have hm : 0 < χ x₀ := gs.pos x₀ ⟨hs₁.trans_le hx₀.1, hx₀.2.trans_lt hs₂⟩
  set T := ∫ r in (0 : ℝ)..R, r * χ r ^ 2
  refine ⟨s₁, s₁ / 2, max (R ^ 2 / s₂) (T / (s₁ * χ x₀ ^ 2)) + 1, hs₁, hs₁₂.trans hs₂,
    by positivity, ?_, ?_, ?_⟩
  · have h1 := le_max_left (R ^ 2 / s₂) (T / (s₁ * χ x₀ ^ 2))
    have h2 : 0 < R ^ 2 / s₂ := div_pos (by positivity) (hs₁.trans hs₁₂)
    linarith
  · intro t ht
    have hle : ∀ r ∈ Icc 0 t, r * χ r ^ 2 ≤ r * χ t ^ 2 := by
      intro r hr
      have h1 : 0 ≤ χ r := gs.nonneg r ⟨hr.1, hr.2.trans (ht.2.le.trans (hs₁₂.trans hs₂).le)⟩
      have h2 : χ r ≤ χ t := hmono ⟨hr.1, hr.2.trans ht.2.le⟩ ⟨ht.1.le, ht.2.le⟩ hr.2
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h1 h2 2) hr.1
    calc (∫ r in (0 : ℝ)..t, r * χ r ^ 2) ≤ ∫ r in (0 : ℝ)..t, r * χ t ^ 2 :=
          integral_mono_on ht.1.le (hpc.intervalIntegrable _ _)
            ((continuous_id.mul continuous_const).intervalIntegrable _ _) hle
      _ = t / 2 * (t * χ t ^ 2) := by
          rw [intervalIntegral.integral_mul_const, integral_id]; ring
      _ ≤ s₁ / 2 * (t * χ t ^ 2) := by
          gcongr
          · exact mul_nonneg ht.1.le (sq_nonneg _)
          · exact ht.2.le
  · intro t ht
    have ht0 : 0 < t := hs₁.trans ht.1
    have hpt : 0 ≤ t * χ t ^ 2 := mul_nonneg ht0.le (sq_nonneg _)
    rcases le_or_gt s₂ t with h | h
    · have hle : ∀ r ∈ Icc t R, r * χ r ^ 2 ≤ R * χ t ^ 2 := by
        intro r hr
        have h1 : 0 ≤ χ r := gs.nonneg r ⟨ht0.le.trans hr.1, hr.2⟩
        have h2 : χ r ≤ χ t := hanti ⟨h, ht.2.le⟩ ⟨h.trans hr.1, hr.2⟩ hr.1
        exact mul_le_mul hr.2 (pow_le_pow_left₀ h1 h2 2) (sq_nonneg _) hR.le
      calc (∫ r in t..R, r * χ r ^ 2) ≤ ∫ r in t..R, R * χ t ^ 2 :=
            integral_mono_on ht.2.le (hpc.intervalIntegrable _ _)
              (continuous_const.intervalIntegrable _ _) hle
        _ = R * χ t ^ 2 * (R - t) := by simp; ring
        _ ≤ R * χ t ^ 2 * R := by gcongr; linarith
        _ = R ^ 2 / t * (t * χ t ^ 2) := by field_simp
        _ ≤ R ^ 2 / s₂ * (t * χ t ^ 2) := by gcongr; linarith [hs₁.trans hs₁₂]
        _ ≤ (max (R ^ 2 / s₂) (T / (s₁ * χ x₀ ^ 2)) + 1) * (t * χ t ^ 2) := by
            gcongr; linarith [le_max_left (R ^ 2 / s₂) (T / (s₁ * χ x₀ ^ 2))]
    · have hT : (∫ r in t..R, r * χ r ^ 2) ≤ T := by
        have hsplit := integral_add_adjacent_intervals (hpc.intervalIntegrable (μ := volume) 0 t)
          (hpc.intervalIntegrable t R)
        have h0 : 0 ≤ ∫ r in (0 : ℝ)..t, r * χ r ^ 2 :=
          integral_nonneg ht0.le (fun r hr => mul_nonneg hr.1 (sq_nonneg _))
        linarith
      have hlow : s₁ * χ x₀ ^ 2 ≤ t * χ t ^ 2 :=
        mul_le_mul ht.1.le (pow_le_pow_left₀ hm.le (hmin ⟨ht.1.le, h.le⟩) 2) (sq_nonneg _)
          ht0.le
      have hT0 : 0 ≤ T := integral_nonneg hR.le (fun r hr => mul_nonneg hr.1 (sq_nonneg _))
      calc (∫ r in t..R, r * χ r ^ 2) ≤ T := hT
        _ = T / (s₁ * χ x₀ ^ 2) * (s₁ * χ x₀ ^ 2) := by field_simp
        _ ≤ T / (s₁ * χ x₀ ^ 2) * (t * χ t ^ 2) := by gcongr
        _ ≤ (max (R ^ 2 / s₂) (T / (s₁ * χ x₀ ^ 2)) + 1) * (t * χ t ^ 2) := by
            gcongr; linarith [le_max_right (R ^ 2 / s₂) (T / (s₁ * χ x₀ ^ 2))]

lemma dbound : ∃ M, ∀ r ∈ Icc 0 R, |dχ r| ≤ M := by
  obtain ⟨x, -, hx⟩ := (isCompact_Icc (a := 0) (b := R)).exists_isMaxOn
    (nonempty_Icc.2 gs.R_pos.le) (continuous_abs.comp gs.dcont).continuousOn
  exact ⟨|dχ x|, fun r hr => hx hr⟩

end GroundState

section Admissible

variable (gs : GroundState R μ χ dχ) {w dw : ℝ → ℝ} (hw : Admissible R w dw)
include gs hw

lemma data : ∃ C R' c M, 0 ≤ C ∧ R' ∈ Ioo 0 R ∧ 0 < c ∧ 0 ≤ M ∧
    (∀ r ∈ Ioo 0 R, |w r| ≤ C * r ∧ |dw r| ≤ C) ∧ (∀ r ∈ Icc R' R, w r = 0 ∧ dw r = 0) ∧
    (∀ r ∈ Ioc 0 R', c * r ≤ χ r) ∧ (∀ r ∈ Icc 0 R, |dχ r| ≤ M) := by
  obtain ⟨C, hC⟩ := hw.bound
  obtain ⟨R', hR', hsupp⟩ := hw.supp
  obtain ⟨c, hc, hlow⟩ := gs.lower hR'
  obtain ⟨M, hM⟩ := gs.dbound
  refine ⟨|C|, R', c, |M|, abs_nonneg _, hR', hc, abs_nonneg _, fun r hr => ?_, hsupp, hlow,
    fun r hr => (hM r hr).trans (le_abs_self _)⟩
  obtain ⟨h1, h2⟩ := hC r hr
  exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hr.1.le), h2.trans (le_abs_self _)⟩

lemma quot_bound : ∃ B, ∀ r ∈ Ioo 0 R, |w r / χ r| ≤ B := by
  obtain ⟨C, R', c, M, hC, hR', hc, hM, hb, hsupp, hlow, hdχ⟩ := data gs hw
  refine ⟨C / c, fun r hr => ?_⟩
  rcases le_or_gt r R' with h | h
  · have hχ := hlow r ⟨hr.1, h⟩
    have hχpos := gs.pos r hr
    rw [abs_div, abs_of_pos hχpos, div_le_div_iff₀ hχpos hc]
    calc |w r| * c ≤ C * r * c := mul_le_mul_of_nonneg_right (hb r hr).1 hc.le
      _ = C * (c * r) := by ring
      _ ≤ C * χ r := mul_le_mul_of_nonneg_left hχ hC
  · rw [(hsupp r ⟨h.le, hr.2.le⟩).1]; simp; positivity

lemma dquot_bound : ∃ K, ∀ r ∈ Ioo 0 R, r * χ r ^ 2 * dquot χ dχ w dw r ^ 2 ≤ K := by
  obtain ⟨C, R', c, M, hC, hR', hc, hM, hb, hsupp, hlow, hdχ⟩ := data gs hw
  refine ⟨R * (C + C * M / c) ^ 2, fun r hr => ?_⟩
  have hχpos := gs.pos r hr
  have heq : r * χ r ^ 2 * dquot χ dχ w dw r ^ 2 = r * (dw r - w r * dχ r / χ r) ^ 2 := by
    unfold dquot; field_simp
  rw [heq]
  rcases le_or_gt r R' with h | h
  · have hχ := hlow r ⟨hr.1, h⟩
    have h1 : |w r * dχ r / χ r| ≤ C * M / c := by
      rw [abs_div, abs_mul, abs_of_pos hχpos, div_le_div_iff₀ hχpos hc]
      calc |w r| * |dχ r| * c ≤ (C * r) * M * c :=
            mul_le_mul_of_nonneg_right (mul_le_mul (hb r hr).1 (hdχ r ⟨hr.1.le, hr.2.le⟩)
              (abs_nonneg _) (mul_nonneg hC hr.1.le)) hc.le
        _ = C * M * (c * r) := by ring
        _ ≤ C * M * χ r := mul_le_mul_of_nonneg_left hχ (mul_nonneg hC hM)
    have h2 : |dw r - w r * dχ r / χ r| ≤ C + C * M / c :=
      (abs_sub _ _).trans (add_le_add (hb r hr).2 h1)
    have h3 : (dw r - w r * dχ r / χ r) ^ 2 ≤ (C + C * M / c) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    exact mul_le_mul hr.2.le h3 (sq_nonneg _) gs.R_pos.le
  · obtain ⟨h1, h2⟩ := hsupp r ⟨h.le, hr.2.le⟩
    rw [h1, h2]; norm_num; exact mul_nonneg gs.R_pos.le (sq_nonneg _)

/-- **Ground-state identity.** -/
lemma energy_sub_mass :
    energy R w dw - μ * mass R w = ∫ r in (0 : ℝ)..R, r * χ r ^ 2 * dquot χ dχ w dw r ^ 2 := by
  obtain ⟨C, R', c, M, hC, hR', hc, hM, hb, hsupp, hlow, hdχ⟩ := data gs hw
  obtain ⟨K, hK⟩ := dquot_bound gs hw
  have hR := gs.R_pos
  have hwc : ContinuousOn w (Ioo 0 R) := fun r hr =>
    (hw.deriv r hr).continuousAt.continuousWithinAt
  have hχc : ContinuousOn χ (Ioo 0 R) := gs.cont.continuousOn
  have i1 : IntervalIntegrable (fun r => r * dw r ^ 2) volume 0 R := by
    refine ii_of_bdd (K := R * C ^ 2) hR.le (continuousOn_id.mul (hw.dcont.pow 2))
      (fun r hr => ?_)
    rw [abs_of_nonneg (by have := hr.1; positivity)]
    exact mul_le_mul hr.2.le (sq_le_of_abs_le (hb r hr).2) (sq_nonneg _) hR.le
  have i2 : IntervalIntegrable (fun r => w r ^ 2 / r) volume 0 R := by
    refine ii_of_bdd (K := C ^ 2 * R) hR.le
      ((hwc.pow 2).div continuousOn_id (fun r hr => hr.1.ne')) (fun r hr => ?_)
    have hr0 := hr.1
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hr0]
    calc w r ^ 2 ≤ (C * r) ^ 2 := sq_le_of_abs_le (hb r hr).1
      _ = C ^ 2 * r * r := by ring
      _ ≤ C ^ 2 * R * r := by gcongr; exact hr.2.le
  have i3 : IntervalIntegrable (fun r => r * w r ^ 2) volume 0 R := by
    refine ii_of_bdd (K := R * (C * R) ^ 2) hR.le (continuousOn_id.mul (hwc.pow 2))
      (fun r hr => ?_)
    have hr0 := hr.1
    rw [abs_of_nonneg (by positivity)]
    refine mul_le_mul hr.2.le ((sq_le_of_abs_le (hb r hr).1).trans ?_) (sq_nonneg _) hR.le
    exact pow_le_pow_left₀ (mul_nonneg hC hr0.le) (mul_le_mul_of_nonneg_left hr.2.le hC) 2
  have hdqc : ContinuousOn (dquot χ dχ w dw) (Ioo 0 R) :=
    ((hw.dcont.mul hχc).sub (hwc.mul gs.dcont.continuousOn)).div (hχc.pow 2)
      (fun r hr => pow_ne_zero _ (gs.pos r hr).ne')
  have i4 : IntervalIntegrable (fun r => r * χ r ^ 2 * dquot χ dχ w dw r ^ 2) volume 0 R := by
    refine ii_of_bdd (K := K) hR.le ((continuousOn_id.mul (hχc.pow 2)).mul (hdqc.pow 2))
      (fun r hr => ?_)
    have hr0 := hr.1
    rw [abs_of_nonneg (by positivity)]
    exact hK r hr
  set G : ℝ → ℝ := fun s => s * dχ s * (w s ^ 2 / χ s) with hG
  have hderiv : ∀ r ∈ Ioo 0 R, HasDerivAt G
      ((r * dw r ^ 2 + w r ^ 2 / r - μ * (r * w r ^ 2)) -
        r * χ r ^ 2 * dquot χ dχ w dw r ^ 2) r := by
    intro r hr
    have hχ0 := (gs.pos r hr).ne'
    have hr0 := hr.1.ne'
    have h := (gs.flux r hr).mul (((hw.deriv r hr).pow 2).div (gs.deriv r) hχ0)
    convert h using 1
    simp only [Pi.div_apply, Pi.pow_apply]
    unfold dquot
    field_simp
    ring
  have h0 : Tendsto G (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_zero_of_le_mul (K := M * C ^ 2 * R' / c) hR'.1 (fun r hr => ?_)
    have hrR : r ∈ Ioo 0 R := ⟨hr.1, hr.2.trans hR'.2⟩
    have hχ := hlow r ⟨hr.1, hr.2.le⟩
    have hχpos := gs.pos r hrR
    have hr0 := hr.1
    have hq : w r ^ 2 / χ r ≤ C ^ 2 * r / c := by
      rw [div_le_div_iff₀ hχpos hc]
      calc w r ^ 2 * c ≤ (C * r) ^ 2 * c :=
            mul_le_mul_of_nonneg_right (sq_le_of_abs_le (hb r hrR).1) hc.le
        _ = C ^ 2 * r * (c * r) := by ring
        _ ≤ C ^ 2 * r * χ r := by gcongr
    have hq0 : 0 ≤ w r ^ 2 / χ r := by positivity
    simp only [hG]
    rw [abs_mul, abs_mul, abs_of_pos hr0, abs_of_nonneg hq0]
    calc r * |dχ r| * (w r ^ 2 / χ r) ≤ r * M * (C ^ 2 * r / c) := by
          gcongr
          exact hdχ r ⟨hr0.le, hrR.2.le⟩
      _ = M * C ^ 2 * r / c * r := by ring
      _ ≤ M * C ^ 2 * R' / c * r := by gcongr; exact hr.2.le
  have h1 : Tendsto G (𝓝[<] R) (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hR'.2] with r hr
    simp [hG, (hsupp r ⟨hr.1.le, hr.2.le⟩).1]
  have hint := ((i1.add i2).sub (i3.const_mul μ)).sub i4
  have hftc := integral_eq_sub_of_hasDerivAt_of_tendsto hR hderiv hint h0 h1
  rw [sub_zero, integral_sub ((i1.add i2).sub (i3.const_mul μ)) i4,
    integral_sub (i1.add i2) (i3.const_mul μ), intervalIntegral.integral_const_mul] at hftc
  unfold energy mass
  linarith

lemma quot_hasDerivAt {r : ℝ} (hr : r ∈ Ioo 0 R) :
    HasDerivAt (fun s => w s / χ s) (dquot χ dχ w dw r) r :=
  (hw.deriv r hr).div (gs.deriv r) (gs.pos r hr).ne'

lemma dquot_cont : ContinuousOn (dquot χ dχ w dw) (Ioo 0 R) := by
  have hwc : ContinuousOn w (Ioo 0 R) := fun r hr =>
    (hw.deriv r hr).continuousAt.continuousWithinAt
  exact ((hw.dcont.mul gs.cont.continuousOn).sub (hwc.mul gs.dcont.continuousOn)).div
    (gs.cont.continuousOn.pow 2) (fun r hr => pow_ne_zero _ (gs.pos r hr).ne')

lemma int_mass : IntervalIntegrable (fun r => r * w r ^ 2) volume 0 R := by
  obtain ⟨C, R', c, M, hC, hR', hc, hM, hb, hsupp, hlow, hdχ⟩ := data gs hw
  have hR := gs.R_pos
  have hwc : ContinuousOn w (Ioo 0 R) := fun r hr =>
    (hw.deriv r hr).continuousAt.continuousWithinAt
  refine ii_of_bdd (K := R * (C * R) ^ 2) hR.le (continuousOn_id.mul (hwc.pow 2))
    (fun r hr => ?_)
  have hr0 := hr.1
  rw [abs_of_nonneg (by positivity)]
  refine mul_le_mul hr.2.le ((sq_le_of_abs_le (hb r hr).1).trans ?_) (sq_nonneg _) hR.le
  exact pow_le_pow_left₀ (mul_nonneg hC hr0.le) (mul_le_mul_of_nonneg_left hr.2.le hC) 2

lemma int_pair : IntervalIntegrable (fun r => r * w r * χ r) volume 0 R := by
  obtain ⟨C, R', c, M, hC, hR', hc, hM, hb, hsupp, hlow, hdχ⟩ := data gs hw
  have hR := gs.R_pos
  have hwc : ContinuousOn w (Ioo 0 R) := fun r hr =>
    (hw.deriv r hr).continuousAt.continuousWithinAt
  obtain ⟨Mχ, hMχ⟩ := (isCompact_Icc (a := 0) (b := R)).exists_bound_of_continuousOn
    gs.cont.continuousOn
  refine ii_of_bdd (K := R * (C * R) * Mχ) hR.le
    ((continuousOn_id.mul hwc).mul gs.cont.continuousOn) (fun r hr => ?_)
  have hr0 := hr.1
  rw [abs_mul, abs_mul, abs_of_pos hr0]
  have h1 : |w r| ≤ C * R := (hb r hr).1.trans (mul_le_mul_of_nonneg_left hr.2.le hC)
  have h2 : |χ r| ≤ Mχ := by
    simpa [Real.norm_eq_abs] using hMχ r (Ioo_subset_Icc_self hr)
  exact mul_le_mul (mul_le_mul hr.2.le h1 (abs_nonneg _) hR.le) h2 (abs_nonneg _)
    (by positivity)

/-- The variance bound `∫ r w² - (∫ r χ w)² / ∫ r χ² ≤ ∫ r χ² (w/χ - c)²`. -/
lemma var_le (c : ℝ) :
    mass R w - pair R w χ ^ 2 / mass R χ ≤
      ∫ r in (0 : ℝ)..R, r * χ r ^ 2 * (w r / χ r - c) ^ 2 := by
  have hR := gs.R_pos
  have hpc : Continuous fun r => r * χ r ^ 2 := continuous_id.mul (gs.cont.pow 2)
  have i1 := int_mass gs hw
  have i2 := int_pair gs hw
  have i3 : IntervalIntegrable (fun r => r * χ r ^ 2) volume 0 R := hpc.intervalIntegrable _ _
  have hmχ : 0 < mass R χ :=
    intervalIntegral_pos_of_pos_on i3 (fun r hr => mul_pos hr.1 (pow_pos (gs.pos r hr) 2)) hR
  have hcongr : (∫ r in (0 : ℝ)..R, r * χ r ^ 2 * (w r / χ r - c) ^ 2) =
      ∫ r in (0 : ℝ)..R, (r * w r ^ 2 - 2 * c * (r * w r * χ r) + c ^ 2 * (r * χ r ^ 2)) := by
    refine integral_congr_Ioo hR.le (fun r hr => ?_)
    have := (gs.pos r hr).ne'
    field_simp
    ring
  rw [hcongr, integral_add (i1.sub (i2.const_mul _)) (i3.const_mul _),
    integral_sub i1 (i2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change mass R w - pair R w χ ^ 2 / mass R χ ≤
    mass R w - 2 * c * pair R w χ + c ^ 2 * mass R χ
  have e : mass R w - 2 * c * pair R w χ + c ^ 2 * mass R χ -
      (mass R w - pair R w χ ^ 2 / mass R χ) = (c * mass R χ - pair R w χ) ^ 2 / mass R χ := by
    field_simp; ring
  have : 0 ≤ (c * mass R χ - pair R w χ) ^ 2 / mass R χ := by positivity
  linarith

end Admissible

/-- **The one-dimensional spectral gap.** -/
theorem gap (gs : GroundState R μ χ dχ) : ∃ δ > 0, ∀ w dw, Admissible R w dw →
    δ * (mass R w - pair R w χ ^ 2 / mass R χ) ≤ energy R w dw - μ * mass R w := by
  obtain ⟨s₁, lL, lR, hs₁, hs₁R, hlL, hlR, hL, hRb⟩ := gs.weight_bounds
  have hR := gs.R_pos
  set Λ := max lL lR
  have hΛ : 0 < Λ := lt_max_of_lt_left hlL
  refine ⟨1 / (4 * Λ ^ 2), by positivity, fun w dw hw => ?_⟩
  have hpc : Continuous fun r => r * χ r ^ 2 := continuous_id.mul (gs.cont.pow 2)
  obtain ⟨B, hB⟩ := quot_bound gs hw
  obtain ⟨K, hK⟩ := dquot_bound gs hw
  have hdqc := dquot_cont gs hw
  have hψd : ∀ r ∈ Ioo 0 R, HasDerivAt (fun s => w s / χ s) (dquot χ dχ w dw r) r :=
    fun r hr => quot_hasDerivAt gs hw hr
  have hψs : ContinuousAt (fun s => w s / χ s) s₁ := (hψd s₁ ⟨hs₁, hs₁R⟩).continuousAt
  have hl := hardy_left hs₁ hlL hpc (fun r hr => mul_nonneg hr.1 (sq_nonneg _)) hL
    (fun r hr => hψd r ⟨hr.1, hr.2.trans hs₁R⟩) hψs
    (hdqc.mono (Ioo_subset_Ioo_right hs₁R.le))
    ⟨B, fun r hr => hB r ⟨hr.1, hr.2.trans hs₁R⟩⟩ ⟨K, fun r hr => hK r ⟨hr.1, hr.2.trans hs₁R⟩⟩
  have hr := hardy_right hs₁R hlR hpc (fun r hr => mul_nonneg (hs₁.le.trans hr.1) (sq_nonneg _))
    hRb (fun r hr => hψd r ⟨hs₁.trans hr.1, hr.2⟩) hψs
    (hdqc.mono (Ioo_subset_Ioo_left hs₁.le))
    ⟨B, fun r hr => hB r ⟨hs₁.trans hr.1, hr.2⟩⟩ ⟨K, fun r hr => hK r ⟨hs₁.trans hr.1, hr.2⟩⟩
  set c := w s₁ / χ s₁
  -- integrability on `[0, R]`
  obtain ⟨Mp, hMp⟩ := (isCompact_Icc (a := 0) (b := R)).exists_bound_of_continuousOn
    hpc.continuousOn
  have hψc : ContinuousOn (fun s => w s / χ s) (Ioo 0 R) := fun r hr =>
    (hψd r hr).continuousAt.continuousWithinAt
  have iF : IntervalIntegrable (fun r => r * χ r ^ 2 * (w r / χ r - c) ^ 2) volume 0 R := by
    refine ii_of_bdd (K := Mp * (B + |c|) ^ 2) hR.le
      (hpc.continuousOn.mul ((hψc.sub continuousOn_const).pow 2)) (fun r hr => ?_)
    have hp0 : 0 ≤ r * χ r ^ 2 := mul_nonneg hr.1.le (sq_nonneg _)
    have hpM : r * χ r ^ 2 ≤ Mp := (le_abs_self _).trans
      (by simpa [Real.norm_eq_abs] using hMp r (Ioo_subset_Icc_self hr))
    rw [abs_of_nonneg (mul_nonneg hp0 (sq_nonneg _))]
    exact mul_le_mul hpM
      (sq_le_of_abs_le ((abs_sub _ _).trans (add_le_add_left (hB r hr) _)))
      (sq_nonneg _) (hp0.trans hpM)
  have iD : IntervalIntegrable (fun r => r * χ r ^ 2 * dquot χ dχ w dw r ^ 2) volume 0 R := by
    refine ii_of_bdd (K := K) hR.le (hpc.continuousOn.mul (hdqc.pow 2)) (fun r hr => ?_)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg hr.1.le (sq_nonneg _)) (sq_nonneg _))]
    exact hK r hr
  have hsub1 : uIcc 0 s₁ ⊆ uIcc 0 R := by
    rw [uIcc_of_le hs₁.le, uIcc_of_le hR.le]; exact Icc_subset_Icc_right hs₁R.le
  have hsub2 : uIcc s₁ R ⊆ uIcc 0 R := by
    rw [uIcc_of_le hs₁R.le, uIcc_of_le hR.le]; exact Icc_subset_Icc_left hs₁.le
  have hsplitF := integral_add_adjacent_intervals (iF.mono_set hsub1) (iF.mono_set hsub2)
  have hsplitD := integral_add_adjacent_intervals (iD.mono_set hsub1) (iD.mono_set hsub2)
  have hD1 : 0 ≤ ∫ r in (0 : ℝ)..s₁, r * χ r ^ 2 * dquot χ dχ w dw r ^ 2 :=
    integral_nonneg hs₁.le (fun r hr => mul_nonneg (mul_nonneg hr.1 (sq_nonneg _)) (sq_nonneg _))
  have hD2 : 0 ≤ ∫ r in s₁..R, r * χ r ^ 2 * dquot χ dχ w dw r ^ 2 :=
    integral_nonneg hs₁R.le
      (fun r hr => mul_nonneg (mul_nonneg (hs₁.le.trans hr.1) (sq_nonneg _)) (sq_nonneg _))
  have hLΛ : lL ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hlL.le (le_max_left _ _) 2
  have hRΛ : lR ^ 2 ≤ Λ ^ 2 := pow_le_pow_left₀ hlR.le (le_max_right _ _) 2
  have htot : (∫ r in (0 : ℝ)..R, r * χ r ^ 2 * (w r / χ r - c) ^ 2) ≤
      4 * Λ ^ 2 * (energy R w dw - μ * mass R w) := by
    rw [energy_sub_mass gs hw, ← hsplitF, ← hsplitD]
    nlinarith [mul_le_mul_of_nonneg_right hLΛ hD1, mul_le_mul_of_nonneg_right hRΛ hD2]
  have hvar := var_le gs hw c
  calc 1 / (4 * Λ ^ 2) * (mass R w - pair R w χ ^ 2 / mass R χ)
      ≤ 1 / (4 * Λ ^ 2) * (4 * Λ ^ 2 * (energy R w dw - μ * mass R w)) := by
        gcongr; exact hvar.trans htot
    _ = energy R w dw - μ * mass R w := by field_simp

/-- **The one-dimensional ground-state inequality** `μ ∫ r w² ≤ ∫ (r w'² + w²/r)`. -/
theorem mass_le_energy (gs : GroundState R μ χ dχ) {w dw : ℝ → ℝ} (hw : Admissible R w dw) :
    μ * mass R w ≤ energy R w dw := by
  have h := energy_sub_mass gs hw
  have : 0 ≤ ∫ r in (0 : ℝ)..R, r * χ r ^ 2 * dquot χ dχ w dw r ^ 2 :=
    integral_nonneg gs.R_pos.le
      (fun r hr => mul_nonneg (mul_nonneg hr.1 (sq_nonneg _)) (sq_nonneg _))
  linarith

end Ground1D

end Buckling
end
end ChunkedSource012
/- END SOURCE 012 -/

/- BEGIN SOURCE 013: RequestProject/Disk/Mode1D.lean -/
section ChunkedSource013

/-!
# Identities and inequalities for a single angular mode

For a radial coefficient `v` of angular frequency `n` (smooth, `v(0) = 0` if `n ≠ 0`,
`v'(0) = 0` if `n ≠ 1`, vanishing near `R`) put `w = v' - n v / r`.  Then
`∫ (r v'² + n² v²/r) = ∫ r w²` and
`∫ r (v'' + v'/r - n² v/r²)² = ∫ (r w'² + w²/r) + ((n+1)² - 1) ∫ w²/r`.
Combined with the one-dimensional ground-state inequality this gives the mode
inequalities used for the disk spectral gap.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology intervalIntegral

namespace Buckling

namespace Mode1D

open Ground1D

/-- Hypotheses on a radial coefficient of angular frequency `n`. -/
structure ModeFn (R : ℝ) (n : ℕ) (v : ℝ → ℝ) : Prop where
  R_pos : 0 < R
  smooth : ContDiff ℝ 2 v
  zero : n ≠ 0 → v 0 = 0
  dzero : n ≠ 1 → deriv v 0 = 0
  supp : ∃ R' ∈ Ioo 0 R, ∀ r, R' ≤ r → v r = 0

/-- The gradient energy of a mode, `∫₀ᴿ (r v'² + n² v²/r)`. -/
noncomputable def gradE (R : ℝ) (n : ℕ) (v : ℝ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, (r * deriv v r ^ 2 + (n : ℝ) ^ 2 * v r ^ 2 / r)

/-- The Laplacian energy of a mode, `∫₀ᴿ r (v'' + v'/r - n² v/r²)²`. -/
noncomputable def lapE (R : ℝ) (n : ℕ) (v : ℝ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..R, r * (deriv (deriv v) r + deriv v r / r - (n : ℝ) ^ 2 * v r / r ^ 2) ^ 2

/-- The transformed function `w = v' - n v / r`. -/
noncomputable def wfun (n : ℕ) (v : ℝ → ℝ) (r : ℝ) : ℝ := deriv v r - n * v r / r

/-- Its derivative for `r > 0`. -/
noncomputable def dwfun (n : ℕ) (v : ℝ → ℝ) (r : ℝ) : ℝ :=
  deriv (deriv v) r - n * deriv v r / r + n * v r / r ^ 2

variable {R : ℝ} {n : ℕ} {v : ℝ → ℝ}

lemma c2_facts (hv : ContDiff ℝ 2 v) :
    Differentiable ℝ v ∧ Differentiable ℝ (deriv v) ∧ Continuous (deriv (deriv v)) := by
  have h1 := (contDiff_succ_iff_deriv (n := 1)).1 hv
  have h2 := (contDiff_succ_iff_deriv (n := 0)).1 h1.2.2
  exact ⟨h1.1, h2.1, h2.2.2.continuous⟩

namespace ModeFn

variable (hv : ModeFn R n v)
include hv

lemma diff : Differentiable ℝ v := (c2_facts hv.smooth).1
lemma ddiff : Differentiable ℝ (deriv v) := (c2_facts hv.smooth).2.1
lemma d2cont : Continuous (deriv (deriv v)) := (c2_facts hv.smooth).2.2

/-- Taylor-type bounds near `0`. -/
lemma taylor : ∃ M, 0 ≤ M ∧ ∀ r ∈ Icc 0 R,
    |deriv v r - deriv v 0| ≤ M * r ∧ |v r - v 0 - r * deriv v r| ≤ M * r * r ∧
    |deriv (deriv v) r| ≤ M ∧ |v r - v 0| ≤ M * r := by
  obtain ⟨M₂, hM₂⟩ := (isCompact_Icc (a := 0) (b := R)).exists_bound_of_continuousOn
    hv.d2cont.continuousOn
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc (a := 0) (b := R)).exists_bound_of_continuousOn
    hv.ddiff.continuous.continuousOn
  refine ⟨max (max M₂ M₁) 0, le_max_right _ _, fun r hr => ?_⟩
  set M := max (max M₂ M₁) 0
  have hM2 : ∀ s ∈ Icc 0 R, |deriv (deriv v) s| ≤ M := fun s hs =>
    (by simpa [Real.norm_eq_abs] using hM₂ s hs : |deriv (deriv v) s| ≤ M₂).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  have hM1 : ∀ s ∈ Icc 0 R, |deriv v s| ≤ M := fun s hs =>
    (by simpa [Real.norm_eq_abs] using hM₁ s hs : |deriv v s| ≤ M₁).trans
      ((le_max_right _ _).trans (le_max_left _ _))
  have hsub : ∀ s ∈ Ico 0 r, s ∈ Icc 0 R := fun s hs => ⟨hs.1, hs.2.le.trans hr.2⟩
  refine ⟨?_, ?_, hM2 r hr, ?_⟩
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv v)
      (f' := deriv (deriv v)) (C := M)
      (fun x _ => (hv.ddiff x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => by simpa [Real.norm_eq_abs] using hM2 x (hsub x hx)) r ⟨hr.1, le_rfl⟩
    simpa [Real.norm_eq_abs] using this
  · have hd : ∀ x, HasDerivAt (fun s => v s - s * deriv v s) (-(x * deriv (deriv v) x)) x := by
      intro x
      have h := (hv.diff x).hasDerivAt.sub ((hasDerivAt_id x).mul (hv.ddiff x).hasDerivAt)
      convert! h using 1 <;> try simp only [id_eq, Pi.mul_apply, Pi.sub_apply] <;> ring
    have := norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun s => v s - s * deriv v s) (f' := fun x => -(x * deriv (deriv v) x))
      (C := M * r)
      (fun x _ => (hd x).hasDerivWithinAt)
      (fun x hx => by
        rw [norm_neg, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx.1]
        calc x * |deriv (deriv v) x| ≤ r * M :=
              mul_le_mul hx.2.le (hM2 x (hsub x hx)) (abs_nonneg _) (hx.1.trans hx.2.le)
          _ = M * r := mul_comm _ _)
      r ⟨hr.1, le_rfl⟩
    simp only [zero_mul, sub_zero, sub_zero, Real.norm_eq_abs] at this
    calc |v r - v 0 - r * deriv v r| = |v r - r * deriv v r - v 0| := by ring_nf
      _ ≤ M * r * r := this
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := v) (f' := deriv v) (C := M)
      (fun x _ => (hv.diff x).hasDerivAt.hasDerivWithinAt)
      (fun x hx => by simpa [Real.norm_eq_abs] using hM1 x (hsub x hx)) r ⟨hr.1, le_rfl⟩
    simpa [Real.norm_eq_abs] using this

/-- Vanishing near `R`. -/
lemma supp' : ∃ R'' ∈ Ioo 0 R, ∀ r, R'' ≤ r →
    v r = 0 ∧ deriv v r = 0 ∧ deriv (deriv v) r = 0 := by
  obtain ⟨R', hR', h⟩ := hv.supp
  refine ⟨(R' + R) / 2, ⟨by linarith [hR'.1, hR'.2], by linarith [hR'.2]⟩, fun r hr => ?_⟩
  have hr' : R' < r := by linarith [hR'.2]
  have hev : v =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hr'] with s hs using h s hs.le
  have hev' : deriv v =ᶠ[𝓝 r] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hr'] with s hs
    have : v =ᶠ[𝓝 s] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds hs] with t ht using h t ht.le
    simpa using this.deriv_eq
  exact ⟨h r hr'.le, by simpa using hev.deriv_eq, by simpa using hev'.deriv_eq⟩

lemma w_hasDerivAt {r : ℝ} (hr : 0 < r) : HasDerivAt (wfun n v) (dwfun n v r) r := by
  have h := (hv.ddiff r).hasDerivAt.sub
    (((hv.diff r).hasDerivAt.const_mul (n : ℝ)).div (hasDerivAt_id r) hr.ne')
  unfold wfun dwfun
  convert! h using 1 <;> try simp only [id_eq, Pi.div_apply, Pi.sub_apply]
    <;> field_simp <;> ring

lemma w_bounds : ∃ C, ∀ r ∈ Ioo 0 R, |wfun n v r| ≤ C * r ∧ |dwfun n v r| ≤ C := by
  obtain ⟨M, hM0, hM⟩ := hv.taylor
  refine ⟨(2 * n + 2) * M, fun r hr => ?_⟩
  obtain ⟨h1, h2, h3, -⟩ := hM r ⟨hr.1.le, hr.2.le⟩
  have hr0 := hr.1
  -- `|v'(r)| ≤ M r` when `n ≠ 1`
  have hd : (n : ℝ) ≠ 1 → |deriv v r| ≤ M * r := fun h => by
    have : deriv v 0 = 0 := hv.dzero (fun h' => h (by simp [h']))
    simpa [this] using h1
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hd0 := hd (by norm_num)
    simp only [wfun, dwfun, Nat.cast_zero, zero_mul, zero_div, sub_zero, add_zero]
    constructor
    · nlinarith [abs_nonneg (deriv v r)]
    · nlinarith
  · have hv0 : v 0 = 0 := hv.zero hn.ne'
    have hq : |deriv v r - v r / r| ≤ M * r := by
      have e : deriv v r - v r / r = -(v r - v 0 - r * deriv v r) / r := by
        rw [hv0]; field_simp; ring
      rw [e, abs_div, abs_neg, abs_of_pos hr0, div_le_iff₀ hr0]
      exact h2
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hw : wfun n v r = (1 - n) * deriv v r + n * (deriv v r - v r / r) := by
      unfold wfun; ring
    have hdw : dwfun n v r = deriv (deriv v) r - n / r * (deriv v r - v r / r) := by
      unfold dwfun; field_simp; ring
    constructor
    · rw [hw]
      have ht1 : |(1 - (n : ℝ)) * deriv v r| ≤ (n - 1) * (M * r) := by
        rw [abs_mul, abs_of_nonpos (by linarith : (1 : ℝ) - n ≤ 0)]
        rcases eq_or_ne (n : ℝ) 1 with h | h
        · rw [h]; simp
        · have := mul_le_mul_of_nonneg_left (hd h) (by linarith : (0 : ℝ) ≤ n - 1)
          linarith
      have ht2 : |(n : ℝ) * (deriv v r - v r / r)| ≤ n * (M * r) := by
        rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)]
        exact mul_le_mul_of_nonneg_left hq (by linarith)
      calc |(1 - (n : ℝ)) * deriv v r + n * (deriv v r - v r / r)|
          ≤ (n - 1) * (M * r) + n * (M * r) := (abs_add_le _ _).trans (add_le_add ht1 ht2)
        _ ≤ (2 * n + 2) * M * r := by nlinarith
    · rw [hdw]
      have ht : |(n : ℝ) / r * (deriv v r - v r / r)| ≤ n * M := by
        rw [abs_mul, abs_div, abs_of_pos hr0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ n)]
        calc (n : ℝ) / r * |deriv v r - v r / r| ≤ n / r * (M * r) := by gcongr
          _ = n * M := by field_simp
      calc |deriv (deriv v) r - (n : ℝ) / r * (deriv v r - v r / r)|
          ≤ M + n * M := (abs_sub _ _).trans (add_le_add h3 ht)
        _ ≤ (2 * n + 2) * M := by nlinarith

lemma admissible : Admissible R (wfun n v) (dwfun n v) := by
  obtain ⟨C, hC⟩ := hv.w_bounds
  obtain ⟨R'', hR'', hsupp⟩ := hv.supp'
  refine ⟨fun r hr => hv.w_hasDerivAt hr.1, ?_, ⟨C, hC⟩, ⟨R'', hR'', fun r hr => ?_⟩⟩
  · have hc1 := hv.d2cont.continuousOn (s := Ioo 0 R)
    have hc2 := hv.ddiff.continuous.continuousOn (s := Ioo 0 R)
    have hc3 := hv.diff.continuous.continuousOn (s := Ioo 0 R)
    exact (hc1.sub ((continuousOn_const.mul hc2).div continuousOn_id
      (fun r hr => hr.1.ne'))).add ((continuousOn_const.mul hc3).div (continuousOn_id.pow 2)
      (fun r hr => pow_ne_zero _ hr.1.ne'))
  · obtain ⟨h1, h2, h3⟩ := hsupp r hr.1
    simp [wfun, dwfun, h1, h2, h3]

/-- `∫ (r v'² + n² v²/r) = ∫ r w²`. -/
lemma gradE_eq : gradE R n v = mass R (wfun n v) := by
  have hR := hv.R_pos
  obtain ⟨M, hM0, hM⟩ := hv.taylor
  obtain ⟨R'', hR'', hsupp⟩ := hv.supp'
  have hvc := hv.diff.continuous
  have hdc := hv.ddiff.continuous
  have i1 : IntervalIntegrable (fun r => r * deriv v r ^ 2 + (n : ℝ) ^ 2 * v r ^ 2 / r)
      volume 0 R := by
    refine ((continuous_id.mul (hdc.pow 2)).intervalIntegrable _ _).add ?_
    refine ii_of_bdd (K := (n : ℝ) ^ 2 * M ^ 2 * R) hR.le
      ((continuousOn_const.mul (hvc.continuousOn.pow 2)).div continuousOn_id
        (fun r hr => hr.1.ne')) (fun r hr => ?_)
    have hr0 := hr.1
    rcases eq_or_ne n 0 with hn | hn
    · subst hn; simp
    · have h4 := (hM r ⟨hr.1.le, hr.2.le⟩).2.2.2
      rw [hv.zero hn, sub_zero] at h4
      rw [abs_of_nonneg (by positivity), div_le_iff₀ hr0]
      calc (n : ℝ) ^ 2 * v r ^ 2 ≤ n ^ 2 * (M * r) ^ 2 :=
            mul_le_mul_of_nonneg_left (sq_le_of_abs_le h4) (by positivity)
        _ = n ^ 2 * M ^ 2 * r * r := by ring
        _ ≤ n ^ 2 * M ^ 2 * R * r := by gcongr; exact hr.2.le
  have i2 : IntervalIntegrable (fun r => (n : ℝ) * (2 * v r * deriv v r)) volume 0 R :=
    (continuous_const.mul ((continuous_const.mul hvc).mul hdc)).intervalIntegrable _ _
  have hcongr : mass R (wfun n v) = ∫ r in (0 : ℝ)..R,
      ((r * deriv v r ^ 2 + (n : ℝ) ^ 2 * v r ^ 2 / r) - (n : ℝ) * (2 * v r * deriv v r)) := by
    unfold mass; refine integral_congr_Ioo hR.le (fun r hr => ?_)
    have := hr.1.ne'; unfold wfun; field_simp; ring
  have hftc : ∫ r in (0 : ℝ)..R, (n : ℝ) * (2 * v r * deriv v r) =
      n * (v R ^ 2 - v 0 ^ 2) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    refine integral_eq_sub_of_hasDerivAt (f := fun x => v x ^ 2) (fun x _ => ?_)
      (Continuous.intervalIntegrable (u := fun x => 2 * v x * deriv v x)
        ((continuous_const.mul hvc).mul hdc) _ _)
    have := (hv.diff x).hasDerivAt.pow 2
    convert this using 1; simp
  have hend : (n : ℝ) * (v R ^ 2 - v 0 ^ 2) = 0 := by
    rw [(hsupp R hR''.2.le).1]
    rcases eq_or_ne n 0 with hn | hn
    · simp [hn]
    · simp [hv.zero hn]
  rw [hcongr, integral_sub i1 i2, hftc, hend, sub_zero]; rfl

/-- `∫ r (L_n v)² = ∫ (r w'² + w²/r) + ((n+1)² - 1) ∫ w²/r`. -/
lemma lapE_eq : lapE R n v = energy R (wfun n v) (dwfun n v) +
    (((n : ℝ) + 1) ^ 2 - 1) * ∫ r in (0 : ℝ)..R, wfun n v r ^ 2 / r := by
  have hR := hv.R_pos
  obtain ⟨C, hC⟩ := hv.w_bounds
  obtain ⟨R'', hR'', hsupp⟩ := hv.supp'
  have hadm := hv.admissible
  have hwc : ContinuousOn (wfun n v) (Ioo 0 R) := fun r hr =>
    (hv.w_hasDerivAt hr.1).continuousAt.continuousWithinAt
  have hdwc := hadm.dcont
  have i1 : IntervalIntegrable (fun r => r * dwfun n v r ^ 2 + wfun n v r ^ 2 / r)
      volume 0 R := by
    refine ii_of_bdd (K := R * C ^ 2 + C ^ 2 * R) hR.le
      ((continuousOn_id.mul (hdwc.pow 2)).add ((hwc.pow 2).div continuousOn_id
        (fun r hr => hr.1.ne'))) (fun r hr => ?_)
    have hr0 := hr.1
    obtain ⟨h1, h2⟩ := hC r hr
    have e1 : r * dwfun n v r ^ 2 ≤ R * C ^ 2 :=
      mul_le_mul hr.2.le (sq_le_of_abs_le h2) (sq_nonneg _) hR.le
    have e2 : wfun n v r ^ 2 / r ≤ C ^ 2 * R := by
      rw [div_le_iff₀ hr0]
      calc wfun n v r ^ 2 ≤ (C * r) ^ 2 := sq_le_of_abs_le h1
        _ = C ^ 2 * r * r := by ring
        _ ≤ C ^ 2 * R * r := by gcongr; exact hr.2.le
    rw [abs_of_nonneg (by positivity)]
    linarith
  have i2 : IntervalIntegrable (fun r => wfun n v r ^ 2 / r) volume 0 R := by
    refine ii_of_bdd (K := C ^ 2 * R) hR.le ((hwc.pow 2).div continuousOn_id
      (fun r hr => hr.1.ne')) (fun r hr => ?_)
    have hr0 := hr.1
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hr0]
    calc wfun n v r ^ 2 ≤ (C * r) ^ 2 := sq_le_of_abs_le (hC r hr).1
      _ = C ^ 2 * r * r := by ring
      _ ≤ C ^ 2 * R * r := by gcongr; exact hr.2.le
  have i3 : IntervalIntegrable (fun r => 2 * wfun n v r * dwfun n v r) volume 0 R := by
    refine ii_of_bdd (K := 2 * (C * R) * C) hR.le
      ((continuousOn_const.mul hwc).mul hdwc) (fun r hr => ?_)
    obtain ⟨h1, h2⟩ := hC r hr
    have hC0 : 0 ≤ C := (abs_nonneg _).trans h2
    rw [abs_mul, abs_mul, abs_two]
    have h1' : |wfun n v r| ≤ C * R := h1.trans (mul_le_mul_of_nonneg_left hr.2.le hC0)
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1' (by norm_num)) h2 (abs_nonneg _)
      (by positivity)
  set k : ℝ := ((n : ℝ) + 1) ^ 2 - 1
  have hcongr : lapE R n v = ∫ r in (0 : ℝ)..R, ((r * dwfun n v r ^ 2 + wfun n v r ^ 2 / r) +
      k * (wfun n v r ^ 2 / r) + ((n : ℝ) + 1) * (2 * wfun n v r * dwfun n v r)) := by
    unfold lapE; refine integral_congr_Ioo hR.le (fun r hr => ?_)
    have := hr.1.ne'; simp only [k, wfun, dwfun]; field_simp; ring
  have hftc : ∫ r in (0 : ℝ)..R, 2 * wfun n v r * dwfun n v r = 0 - 0 := by
    refine integral_eq_sub_of_hasDerivAt_of_tendsto hR (f := fun r => wfun n v r ^ 2)
      (fun r hr => ?_) i3 ?_ ?_
    · have := (hv.w_hasDerivAt hr.1).pow 2
      convert this using 1; simp
    · refine tendsto_zero_of_le_mul (K := C ^ 2 * R) hR (fun r hr => ?_)
      have hr0 := hr.1
      rw [abs_of_nonneg (sq_nonneg _)]
      calc wfun n v r ^ 2 ≤ (C * r) ^ 2 := sq_le_of_abs_le (hC r hr).1
        _ = C ^ 2 * r * r := by ring
        _ ≤ C ^ 2 * R * r := by gcongr; exact hr.2.le
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsLT hR''.2] with r hr
      obtain ⟨h1, h2, -⟩ := hsupp r hr.1.le
      simp [wfun, h1, h2]
  rw [hcongr, integral_add (i1.add (i2.const_mul k)) (i3.const_mul _), integral_add i1
    (i2.const_mul k), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    hftc]
  unfold energy
  ring

lemma int_w2r : IntervalIntegrable (fun r => wfun n v r ^ 2 / r) volume 0 R := by
  have hR := hv.R_pos
  obtain ⟨C, hC⟩ := hv.w_bounds
  have hwc : ContinuousOn (wfun n v) (Ioo 0 R) := fun r hr =>
    (hv.w_hasDerivAt hr.1).continuousAt.continuousWithinAt
  refine ii_of_bdd (K := C ^ 2 * R) hR.le ((hwc.pow 2).div continuousOn_id
    (fun r hr => hr.1.ne')) (fun r hr => ?_)
  have hr0 := hr.1
  rw [abs_of_nonneg (by positivity), div_le_iff₀ hr0]
  calc wfun n v r ^ 2 ≤ (C * r) ^ 2 := sq_le_of_abs_le (hC r hr).1
    _ = C ^ 2 * r * r := by ring
    _ ≤ C ^ 2 * R * r := by gcongr; exact hr.2.le

end ModeFn

/-- **Nonzero modes.** For `n ≠ 0` the mode quotient is at least `μ + 3/R²`. -/
theorem mode_pos {μ : ℝ} {χ dχ : ℝ → ℝ} (gs : GroundState R μ χ dχ) (hn : n ≠ 0)
    (hv : ModeFn R n v) : (μ + 3 / R ^ 2) * gradE R n v ≤ lapE R n v := by
  have hR := hv.R_pos
  have hadm := hv.admissible
  have h1 := mass_le_energy gs hadm
  rw [hv.lapE_eq, hv.gradE_eq]
  have hk : (3 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - 1 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    nlinarith
  have hI0 : 0 ≤ ∫ r in (0 : ℝ)..R, wfun n v r ^ 2 / r :=
    integral_nonneg hR.le (fun r hr => div_nonneg (sq_nonneg _) hr.1)
  have hI : mass R (wfun n v) ≤ R ^ 2 * ∫ r in (0 : ℝ)..R, wfun n v r ^ 2 / r := by
    unfold mass
    rw [← intervalIntegral.integral_const_mul]
    refine integral_mono_Ioo hR.le (int_mass gs hadm) (hv.int_w2r.const_mul _) (fun r hr => ?_)
    have hr0 := hr.1
    have e : r * wfun n v r ^ 2 = r ^ 2 * (wfun n v r ^ 2 / r) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0.le hr.2.le 2)
      (div_nonneg (sq_nonneg _) hr0.le)
  have e3 : 3 / R ^ 2 * mass R (wfun n v) ≤ 3 * ∫ r in (0 : ℝ)..R, wfun n v r ^ 2 / r := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hk hI0]

/-- **The radial mode.** A quantitative gap relative to the ground state `χ`. -/
theorem mode_zero {μ : ℝ} {χ dχ : ℝ → ℝ} (gs : GroundState R μ χ dχ) :
    ∃ δ > 0, ∀ v, ModeFn R 0 v →
      δ * (gradE R 0 v - (∫ r in (0 : ℝ)..R, r * deriv v r * χ r) ^ 2 / mass R χ) ≤
        lapE R 0 v - μ * gradE R 0 v := by
  obtain ⟨δ, hδ, h⟩ := gap gs
  refine ⟨δ, hδ, fun v hv => ?_⟩
  have := h _ _ hv.admissible
  have hw : wfun 0 v = deriv v := by ext r; simp [wfun]
  rw [hv.lapE_eq, hv.gradE_eq]
  rw [hw] at this ⊢
  unfold pair at this
  norm_num
  exact this

end Mode1D

end Buckling
end
end ChunkedSource013
/- END SOURCE 013 -/

/- BEGIN SOURCE 014: RequestProject/Disk/ModeInt.lean -/
section ChunkedSource014

/-!
# Integrability and positivity facts for radial modes
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology

namespace Buckling

namespace Mode1D

open Ground1D

variable {R : ℝ} {n : ℕ} {v : ℝ → ℝ}

namespace ModeFn

lemma lap_bracket {r : ℝ} (hr : 0 < r) :
    deriv (deriv v) r + deriv v r / r - (n : ℝ) ^ 2 * v r / r ^ 2 =
      dwfun n v r + ((n : ℝ) + 1) / r * wfun n v r := by
  unfold dwfun wfun; field_simp; ring

variable (hv : ModeFn R n v)
include hv

lemma int_grad :
    IntervalIntegrable (fun r => r * deriv v r ^ 2 + (n : ℝ) ^ 2 * v r ^ 2 / r) volume 0 R := by
  have hR := hv.R_pos
  obtain ⟨M, hM0, hM⟩ := hv.taylor
  obtain ⟨M1, hM1⟩ := (isCompact_Icc (a := 0) (b := R)).exists_bound_of_continuousOn
    hv.ddiff.continuous.continuousOn
  have hc : ContinuousOn (fun r => r * deriv v r ^ 2 + (n : ℝ) ^ 2 * v r ^ 2 / r) (Ioo 0 R) :=
    ((continuousOn_id.mul (hv.ddiff.continuous.continuousOn.pow 2)).add
      ((continuousOn_const.mul (hv.diff.continuous.continuousOn.pow 2)).div continuousOn_id
        (fun r hr => hr.1.ne')))
  refine ii_of_bdd (K := R * M1 ^ 2 + (n : ℝ) ^ 2 * (M ^ 2 * R)) hR.le hc (fun r hr => ?_)
  have hr0 := hr.1
  have hrI : r ∈ Icc 0 R := ⟨hr0.le, hr.2.le⟩
  have h1 : r * deriv v r ^ 2 ≤ R * M1 ^ 2 := by
    have : |deriv v r| ≤ M1 := by simpa [Real.norm_eq_abs] using hM1 r hrI
    exact mul_le_mul hr.2.le (sq_le_of_abs_le this) (sq_nonneg _) hR.le
  have h2 : (n : ℝ) ^ 2 * v r ^ 2 / r ≤ (n : ℝ) ^ 2 * (M ^ 2 * R) := by
    rcases eq_or_ne n 0 with hn | hn
    · simp [hn]
    · have hv0 := hv.zero hn
      have hb := (hM r hrI).2.2.2
      rw [hv0, sub_zero] at hb
      rw [mul_div_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      rw [div_le_iff₀ hr0]
      calc v r ^ 2 ≤ (M * r) ^ 2 := sq_le_of_abs_le hb
        _ = M ^ 2 * r * r := by ring
        _ ≤ M ^ 2 * R * r := by gcongr; exact hr.2.le
  rw [abs_of_nonneg (by positivity)]
  linarith

lemma int_lap : IntervalIntegrable (fun r => r * (deriv (deriv v) r + deriv v r / r -
    (n : ℝ) ^ 2 * v r / r ^ 2) ^ 2) volume 0 R := by
  have hR := hv.R_pos
  obtain ⟨C, hC⟩ := hv.w_bounds
  have hc : ContinuousOn (fun r => r * (deriv (deriv v) r + deriv v r / r -
      (n : ℝ) ^ 2 * v r / r ^ 2) ^ 2) (Ioo 0 R) := by
    refine continuousOn_id.mul (ContinuousOn.pow ?_ 2)
    exact (hv.d2cont.continuousOn.add (hv.ddiff.continuous.continuousOn.div continuousOn_id
      (fun r hr => hr.1.ne'))).sub ((continuousOn_const.mul hv.diff.continuous.continuousOn).div
        (continuousOn_id.pow 2) (fun r hr => pow_ne_zero _ hr.1.ne'))
  refine ii_of_bdd (K := R * (C + ((n : ℝ) + 1) * C) ^ 2) hR.le hc (fun r hr => ?_)
  have hr0 := hr.1
  rw [lap_bracket hr0, abs_of_nonneg (by positivity)]
  obtain ⟨h1, h2⟩ := hC r hr
  have hb : |dwfun n v r + ((n : ℝ) + 1) / r * wfun n v r| ≤ C + ((n : ℝ) + 1) * C := by
    refine (abs_add_le _ _).trans (add_le_add h2 ?_)
    rw [abs_mul, abs_div, abs_of_pos hr0, abs_of_nonneg (by positivity)]
    calc ((n : ℝ) + 1) / r * |wfun n v r| ≤ ((n : ℝ) + 1) / r * (C * r) := by gcongr
      _ = ((n : ℝ) + 1) * C := by field_simp
  exact mul_le_mul hr.2.le (sq_le_of_abs_le hb) (sq_nonneg _) hR.le

lemma gradE_nonneg : 0 ≤ gradE R n v :=
  intervalIntegral.integral_nonneg hv.R_pos.le (fun r hr => by
    rcases hr.1.eq_or_lt with h | h
    · subst h; simp
    · positivity)

/-- Every mode satisfies `μ ∫(r v'² + n² v²/r) ≤ ∫ r (L_n v)²`. -/
lemma mode_ge {μ : ℝ} {χ dχ : ℝ → ℝ} (gs : GroundState R μ χ dχ) :
    μ * gradE R n v ≤ lapE R n v := by
  have hR := hv.R_pos
  have h1 := mass_le_energy gs hv.admissible
  rw [hv.lapE_eq, hv.gradE_eq]
  have hI0 : 0 ≤ ∫ r in (0 : ℝ)..R, wfun n v r ^ 2 / r :=
    intervalIntegral.integral_nonneg hR.le (fun r hr => div_nonneg (sq_nonneg _) hr.1)
  have hk : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  nlinarith [mul_nonneg hk hI0]

end ModeFn

end Mode1D

end Buckling
end
end ChunkedSource014
/- END SOURCE 014 -/

/- BEGIN SOURCE 015: RequestProject/Elementary.lean -/
section ChunkedSource015

/-!
# Elementary analytic lemmas (Section 2 of the paper)

* Lemma 2.1 (a derivative with one change of sign),
* Lemma 2.2 (oriented zeros),
* Lemma 2.3 (a cubic interpolation inequality).
-/

@[expose] public section

open Set Filter Topology

namespace Buckling

/-- **Lemma 2.1 (a derivative with one change of sign).**  If `H` is differentiable on
`(a,b)`, tends to `0` at both endpoints, and `H' > 0` on `(a,ξ)`, `H' < 0` on `(ξ,b)`,
then `H > 0` on `(a,b)`. -/
theorem pos_of_deriv_one_change {H : ℝ → ℝ} {a b ξ : ℝ} (hξ : ξ ∈ Ioo a b)
    (hd : DifferentiableOn ℝ H (Ioo a b))
    (ha : Tendsto H (𝓝[>] a) (𝓝 0)) (hb : Tendsto H (𝓝[<] b) (𝓝 0))
    (hpos : ∀ x ∈ Ioo a ξ, 0 < deriv H x) (hneg : ∀ x ∈ Ioo ξ b, deriv H x < 0) :
    ∀ x ∈ Ioo a b, 0 < H x := by
  have hc : ContinuousOn H (Ioo a b) := hd.continuousOn
  -- strictly increasing on `(a, ξ]`
  have hinc : StrictMonoOn H (Ioc a ξ) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioc a ξ) (hc.mono fun y hy => ⟨hy.1, hy.2.trans_lt hξ.2⟩)
    intro y hy
    rw [interior_Ioc] at hy
    exact hpos y hy
  have hdec : StrictAntiOn H (Ico ξ b) := by
    apply strictAntiOn_of_deriv_neg (convex_Ico ξ b) (hc.mono fun y hy => ⟨hξ.1.trans_le hy.1, hy.2⟩)
    intro y hy
    rw [interior_Ico] at hy
    exact hneg y hy
  -- nonnegativity on each side, via limits
  have left : ∀ x ∈ Ioc a ξ, 0 ≤ H x := by
    intro x hx
    have hev : ∀ᶠ y in 𝓝[>] a, H y ≤ H x := by
      filter_upwards [Ioo_mem_nhdsGT hx.1] with y hy
      exact (hinc.le_iff_le ⟨hy.1, hy.2.le.trans hx.2⟩ hx).mpr hy.2.le
    exact le_of_tendsto ha hev
  have right : ∀ x ∈ Ico ξ b, 0 ≤ H x := by
    intro x hx
    have hev : ∀ᶠ y in 𝓝[<] b, H y ≤ H x := by
      filter_upwards [Ioo_mem_nhdsLT hx.2] with y hy
      exact (hdec.le_iff_ge ⟨hx.1.trans hy.1.le, hy.2⟩ hx).mpr hy.1.le
    exact le_of_tendsto hb hev
  intro x hx
  rcases le_or_gt x ξ with h | h
  · -- pick a point strictly between `a` and `x`
    obtain ⟨y, hay, hyx⟩ := exists_between hx.1
    have := hinc ⟨hay, hyx.le.trans h⟩ ⟨hx.1, h⟩ hyx
    linarith [left y ⟨hay, hyx.le.trans h⟩]
  · obtain ⟨y, hxy, hyb⟩ := exists_between hx.2
    have := hdec ⟨h.le, hx.2⟩ ⟨h.le.trans hxy.le, hyb⟩ hxy
    linarith [right y ⟨h.le.trans hxy.le, hyb⟩]

/-- The reversed form of Lemma 2.1: `H' < 0` then `H' > 0` gives `H < 0`. -/
theorem neg_of_deriv_one_change {H : ℝ → ℝ} {a b ξ : ℝ} (hξ : ξ ∈ Ioo a b)
    (hd : DifferentiableOn ℝ H (Ioo a b))
    (ha : Tendsto H (𝓝[>] a) (𝓝 0)) (hb : Tendsto H (𝓝[<] b) (𝓝 0))
    (hneg : ∀ x ∈ Ioo a ξ, deriv H x < 0) (hpos : ∀ x ∈ Ioo ξ b, 0 < deriv H x) :
    ∀ x ∈ Ioo a b, H x < 0 := by
  intro x hx
  have := pos_of_deriv_one_change (H := fun y => -H y) hξ hd.neg (by simpa using ha.neg)
    (by simpa using hb.neg) (fun y hy => by rw [deriv.fun_neg]; linarith [hneg y hy])
    (fun y hy => by rw [deriv.fun_neg]; linarith [hpos y hy]) x hx
  simpa using this

/-- **Lemma 2.2 (oriented zeros), first form.**  If `h` is differentiable on `(a,b)`,
positive near `a`, and `h' > 0` at every zero of `h` in `(a,b)`, then `h > 0` on
`(a,b)`. -/
theorem pos_of_oriented_zeros {h : ℝ → ℝ} {a b : ℝ} (hd : DifferentiableOn ℝ h (Ioo a b))
    (hnear : ∀ᶠ x in 𝓝[>] a, 0 < h x)
    (hzero : ∀ x ∈ Ioo a b, h x = 0 → 0 < deriv h x) :
    ∀ x ∈ Ioo a b, 0 < h x := by
  intro x1 hx1
  by_contra hneg
  push_neg at hneg
  -- a point `x0 ∈ (a, x1)` with `h x0 > 0`
  obtain ⟨x0, hx0h, hx0a, hx0x1⟩ : ∃ x0, 0 < h x0 ∧ a < x0 ∧ x0 < x1 := by
    have : ∀ᶠ x in 𝓝[>] a, 0 < h x ∧ x ∈ Ioo a x1 := hnear.and (Ioo_mem_nhdsGT hx1.1)
    obtain ⟨x, hx, hx'⟩ := this.exists
    exact ⟨x, hx, hx'.1, hx'.2⟩
  have hc : ContinuousOn h (Icc x0 x1) :=
    hd.continuousOn.mono fun y hy => ⟨hx0a.trans_le hy.1, hy.2.trans_lt hx1.2⟩
  set S := {y ∈ Icc x0 x1 | h y ≤ 0} with hS
  have hSne : S.Nonempty := ⟨x1, ⟨hx0x1.le, le_rfl⟩, hneg⟩
  have hSclosed : IsClosed S := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSbdd : BddBelow S := ⟨x0, fun y hy => hy.1.1⟩
  set z := sInf S with hz
  have hzS : z ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hpos_before : ∀ y ∈ Ico x0 z, 0 < h y := by
    intro y hy
    by_contra hy'
    push_neg at hy'
    have : z ≤ y := csInf_le hSbdd ⟨⟨hy.1, hy.2.le.trans hzS.1.2⟩, hy'⟩
    linarith [hy.2]
  have hx0z : x0 < z := by
    rcases eq_or_lt_of_le hzS.1.1 with h' | h'
    · exfalso; rw [← h'] at hzS; linarith [hzS.2]
    · exact h'
  have hzab : z ∈ Ioo a b := ⟨hx0a.trans hx0z, hzS.1.2.trans_lt hx1.2⟩
  -- `h z = 0`
  have hcz : ContinuousAt h z := hd.continuousOn.continuousAt (Ioo_mem_nhds hzab.1 hzab.2)
  have hz0 : h z = 0 := by
    apply le_antisymm hzS.2
    have hev : ∀ᶠ y in 𝓝[<] z, 0 ≤ h y := by
      filter_upwards [Ioo_mem_nhdsLT hx0z] with y hy
      exact (hpos_before y ⟨hy.1.le, hy.2⟩).le
    exact ge_of_tendsto (hcz.tendsto.mono_left nhdsWithin_le_nhds) hev
  -- the derivative at `z` is positive, but left difference quotients are negative
  have hdz := hzero z hzab hz0
  have hda : HasDerivAt h (deriv h z) z :=
    (hd.differentiableAt (Ioo_mem_nhds hzab.1 hzab.2)).hasDerivAt
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hda).mono_left
    (nhdsWithin_mono z (show Iio z ⊆ {z}ᶜ from fun y hy => ne_of_lt hy))
  have hle : deriv h z ≤ 0 := by
    apply le_of_tendsto hslope
    filter_upwards [Ioo_mem_nhdsLT hx0z] with y hy
    rw [slope_def_field, hz0, sub_zero]
    exact div_nonpos_of_nonneg_of_nonpos (hpos_before y ⟨hy.1.le, hy.2⟩).le (by linarith [hy.2])
  linarith

/-- **Lemma 2.2 (oriented zeros), second form.**  If `h` is differentiable on `(a,b)`,
positive near `b`, and `h' < 0` at every zero of `h` in `(a,b)`, then `h > 0` on
`(a,b)`. -/
theorem pos_of_oriented_zeros' {h : ℝ → ℝ} {a b : ℝ} (hd : DifferentiableOn ℝ h (Ioo a b))
    (hnear : ∀ᶠ x in 𝓝[<] b, 0 < h x)
    (hzero : ∀ x ∈ Ioo a b, h x = 0 → deriv h x < 0) :
    ∀ x ∈ Ioo a b, 0 < h x := by
  have hd' : DifferentiableOn ℝ (fun y => h (-y)) (Ioo (-b) (-a)) := by
    intro y hy
    have : DifferentiableAt ℝ h (-y) :=
      hd.differentiableAt (Ioo_mem_nhds (by linarith [hy.2]) (by linarith [hy.1]))
    exact (this.comp y differentiable_neg.differentiableAt).differentiableWithinAt
  have key := pos_of_oriented_zeros (h := fun y => h (-y)) (a := -b) (b := -a) hd' ?_ ?_
  · intro x hx
    simpa using key (-x) ⟨by linarith [hx.2], by linarith [hx.1]⟩
  · have : Tendsto (fun y : ℝ => -y) (𝓝[>] (-b)) (𝓝[<] b) := tendsto_neg_nhdsGT_neg (a := b)
    exact this.eventually hnear
  · intro y hy hy0
    have hyab : -y ∈ Ioo a b := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    have hda : HasDerivAt h (deriv h (-y)) (-y) :=
      (hd.differentiableAt (Ioo_mem_nhds hyab.1 hyab.2)).hasDerivAt
    have : deriv (fun y => h (-y)) y = -deriv h (-y) := by
      have := hda.comp y (hasDerivAt_neg y)
      simpa using! this.deriv
    rw [this]
    linarith [hzero (-y) hyab hy0]

lemma hasDerivAt_affine_aux (R0 ρ x y : ℝ) : HasDerivAt (fun y => R0 + ρ * (y - x)) ρ y := by
  have := (((hasDerivAt_id y).sub_const x).const_mul ρ).const_add R0
  simpa using this

lemma hasDerivAt_quad_aux (a b y : ℝ) :
    HasDerivAt (fun y => (b - y) * (y - a)) (-(y - a) + (b - y)) y := by
  have := ((hasDerivAt_id y).const_sub b).mul ((hasDerivAt_id y).sub_const a)
  convert! this using 1 <;> try simp only [id_eq, neg_one_mul, mul_one]

lemma hasDerivAt_quad'_aux (a b y : ℝ) : HasDerivAt (fun y : ℝ => -(y - a) + (b - y)) (-2) y := by
  have hleft : HasDerivAt (fun z : ℝ => -(z - a)) (-1) y := by
    simpa only [id_eq] using! (((hasDerivAt_id y).sub_const a).fun_neg)
  have hright : HasDerivAt (fun z : ℝ => b - z) (-1) y := by
    simpa only [id_eq] using! ((hasDerivAt_id y).const_sub b)
  have hnum : ((-1 : ℝ) + (-1)) = (-2 : ℝ) := by norm_num
  exact (hleft.fun_add hright).congr_deriv hnum

/-- **Lemma 2.3 (a cubic interpolation inequality).**  Let `E` be continuous on `[a,b]`,
three times differentiable on `(a,b)`, with `E(a) = E(b) = 0` and `E''' < 0` on
`(a,b)`.  Then `d/dx (E(x)/((b-x)(x-a))) > 0` on `(a,b)`. -/
theorem cubic_interpolation {E : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn E (Icc a b)) (hd1 : DifferentiableOn ℝ E (Ioo a b))
    (hd2 : DifferentiableOn ℝ (deriv E) (Ioo a b))
    (hd3 : DifferentiableOn ℝ (deriv (deriv E)) (Ioo a b))
    (hEa : E a = 0) (hEb : E b = 0) (h3 : ∀ x ∈ Ioo a b, deriv (deriv (deriv E)) x < 0) :
    ∀ x ∈ Ioo a b, 0 < deriv (fun y => E y / ((b - y) * (y - a))) x := by
  intro x hx
  set D : ℝ → ℝ := fun y => (b - y) * (y - a) with hD
  have hDx : D x ≠ 0 := by
    simp only [hD]; exact mul_ne_zero (by linarith [hx.2]) (by linarith [hx.1])
  have hEd : HasDerivAt E (deriv E x) x := (hd1.differentiableAt (Ioo_mem_nhds hx.1 hx.2)).hasDerivAt
  have hRd := hEd.div (hasDerivAt_quad_aux a b x) hDx
  set R0 := E x / D x
  set ρ := deriv (fun y => E y / D y) x with hρ
  have hρeq : ρ = (deriv E x * D x - E x * (-(x - a) + (b - x))) / D x ^ 2 := hRd.deriv
  change 0 < ρ
  -- the interpolating cubic
  set P : ℝ → ℝ := fun y => D y * (R0 + ρ * (y - x)) with hP
  set H : ℝ → ℝ := fun y => E y - P y with hH
  have hPdiff : ∀ y, HasDerivAt P (( -(y - a) + (b - y)) * (R0 + ρ * (y - x)) + D y * ρ) y :=
    fun y => (hasDerivAt_quad_aux a b y).mul (hasDerivAt_affine_aux R0 ρ x y)
  have hP' : deriv P = fun y => ( -(y - a) + (b - y)) * (R0 + ρ * (y - x)) + D y * ρ :=
    funext fun y => (hPdiff y).deriv
  have hPd2' : ∀ y, HasDerivAt (fun y => ( -(y - a) + (b - y)) * (R0 + ρ * (y - x)) + D y * ρ)
      (-2 * (R0 + ρ * (y - x)) + 2 * ( -(y - a) + (b - y)) * ρ) y := by
    intro y
    have := ((hasDerivAt_quad'_aux a b y).mul (hasDerivAt_affine_aux R0 ρ x y)).add
      ((hasDerivAt_quad_aux a b y).mul_const ρ)
    convert this using 1; ring
  have hP'' : deriv (deriv P) = fun y => -2 * (R0 + ρ * (y - x)) + 2 * ( -(y - a) + (b - y)) * ρ := by
    rw [hP']; exact funext fun y => (hPd2' y).deriv
  have hPd3' : ∀ y, HasDerivAt (fun y => -2 * (R0 + ρ * (y - x)) + 2 * ( -(y - a) + (b - y)) * ρ)
      (-6 * ρ) y := by
    intro y
    have := ((hasDerivAt_affine_aux R0 ρ x y).const_mul (-2)).add
      (((hasDerivAt_quad'_aux a b y).const_mul 2).mul_const ρ)
    convert this using 1; ring
  have hP''' : ∀ y, deriv (deriv (deriv P)) y = -6 * ρ := by
    intro y; rw [hP'']; exact (hPd3' y).deriv
  have hPd2 : ∀ y, HasDerivAt (deriv P) (deriv (deriv P) y) y := by
    intro y; rw [hP'', hP']; exact hPd2' y
  have hPd3 : ∀ y, HasDerivAt (deriv (deriv P)) (deriv (deriv (deriv P)) y) y := by
    intro y; rw [hP''' y, hP'']; exact hPd3' y
  -- derivatives of `H` on `(a,b)`
  have hHd1 : ∀ y ∈ Ioo a b, deriv H y = deriv E y - deriv P y := by
    intro y hy
    exact ((hd1.differentiableAt (Ioo_mem_nhds hy.1 hy.2)).hasDerivAt.sub (hPdiff y)).deriv.trans
      (by rw [(hPdiff y).deriv])
  have hEd2 : ∀ y ∈ Ioo a b, HasDerivAt (deriv E) (deriv (deriv E) y) y := fun y hy =>
    (hd2.differentiableAt (Ioo_mem_nhds hy.1 hy.2)).hasDerivAt
  have hEd3 : ∀ y ∈ Ioo a b, HasDerivAt (deriv (deriv E)) (deriv (deriv (deriv E)) y) y :=
    fun y hy => (hd3.differentiableAt (Ioo_mem_nhds hy.1 hy.2)).hasDerivAt
  -- `H` vanishes at `a`, `x`, `b`, and `H'(x) = 0`
  have hHa : H a = 0 := by simp [hH, hP, hD, hEa]
  have hHb : H b = 0 := by simp [hH, hP, hD, hEb]
  have hHx : H x = 0 := by
    simp only [hH, hP]; rw [sub_self, mul_zero, add_zero]
    simp only [R0]; field_simp; ring
  have hH'x : deriv H x = 0 := by
    rw [hHd1 x hx, hP']
    simp only [sub_self, mul_zero, add_zero]
    rw [hρeq]; simp only [R0]
    field_simp; ring
  -- continuity of `H` on `[a, b]`
  have hHc : ContinuousOn H (Icc a b) :=
    hc.sub (fun y _ => (hPdiff y).continuousAt.continuousWithinAt)
  -- Rolle's theorem three times
  obtain ⟨c1, hc1, hc1'⟩ := exists_deriv_eq_zero hx.1 (hHc.mono (Icc_subset_Icc le_rfl hx.2.le))
    (hHa.trans hHx.symm)
  obtain ⟨c2, hc2, hc2'⟩ := exists_deriv_eq_zero hx.2 (hHc.mono (Icc_subset_Icc hx.1.le le_rfl))
    (hHx.trans hHb.symm)
  have hc1ab : c1 ∈ Ioo a b := ⟨hc1.1, hc1.2.trans hx.2⟩
  have hc2ab : c2 ∈ Ioo a b := ⟨hx.1.trans hc2.1, hc2.2⟩
  -- `H'` on `(a,b)` equals `E' - P'`, differentiable there
  have hH1 : ∀ y ∈ Ioo a b, HasDerivAt (deriv H) (deriv (deriv E) y - deriv (deriv P) y) y := by
    intro y hy
    have : deriv H =ᶠ[𝓝 y] fun z => deriv E z - deriv P z := by
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      exact hHd1 z hz
    exact ((hEd2 y hy).sub (hPd2 y)).congr_of_eventuallyEq this
  have hcontH1 : ∀ s t, a < s → t < b → ContinuousOn (deriv H) (Icc s t) := by
    intro s t hs ht y hy
    exact (hH1 y ⟨hs.trans_le hy.1, hy.2.trans_lt ht⟩).continuousAt.continuousWithinAt
  obtain ⟨d1, hd1', hd1''⟩ := exists_deriv_eq_zero hc1.2 (hcontH1 c1 x hc1.1 hx.2)
    (hc1'.trans hH'x.symm)
  obtain ⟨d2, hd2', hd2''⟩ := exists_deriv_eq_zero hc2.1 (hcontH1 x c2 hx.1 hc2.2)
    (hH'x.trans hc2'.symm)
  have hd1ab : d1 ∈ Ioo a b := ⟨hc1.1.trans hd1'.1, hd1'.2.trans hx.2⟩
  have hd2ab : d2 ∈ Ioo a b := ⟨hx.1.trans hd2'.1, hd2'.2.trans hc2.2⟩
  have hH2 : ∀ y ∈ Ioo a b, deriv (deriv H) y = deriv (deriv E) y - deriv (deriv P) y :=
    fun y hy => (hH1 y hy).deriv
  have hH2d : ∀ y ∈ Ioo a b, HasDerivAt (deriv (deriv H))
      (deriv (deriv (deriv E)) y - deriv (deriv (deriv P)) y) y := by
    intro y hy
    have : deriv (deriv H) =ᶠ[𝓝 y] fun z => deriv (deriv E) z - deriv (deriv P) z := by
      filter_upwards [Ioo_mem_nhds hy.1 hy.2] with z hz
      exact hH2 z hz
    exact ((hEd3 y hy).sub (hPd3 y)).congr_of_eventuallyEq this
  have hd12 : d1 < d2 := hd1'.2.trans hd2'.1
  obtain ⟨ξ, hξ, hξ'⟩ := exists_deriv_eq_zero hd12
    (fun y hy => (hH2d y ⟨hd1ab.1.trans_le hy.1, hy.2.trans_lt hd2ab.2⟩).continuousAt.continuousWithinAt)
    (hd1''.trans hd2''.symm)
  have hξab : ξ ∈ Ioo a b := ⟨hd1ab.1.trans hξ.1, hξ.2.trans hd2ab.2⟩
  rw [(hH2d ξ hξab).deriv, hP''' ξ] at hξ'
  linarith [h3 ξ hξab]

end Buckling
end
end ChunkedSource015
/- END SOURCE 015 -/

/- BEGIN SOURCE 016: RequestProject/Functional/Perspective.lean -/
section ChunkedSource016

/-!
# Perspective extensions (Lemma 9.4 of the paper)

If `h ∈ C¹(ℝ)` with `h'` and `h - s h'` bounded, then `(A, P) ↦ P h(A/P)` is Lipschitz on
`ℝ × (0, ∞)` and extends Lipschitz-continuously to `P = 0` by its boundary limit.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- Horizontal Lipschitz bound for `P h(A/P)`. -/
lemma persp_horizontal {h : ℝ → ℝ} {C : ℝ} (hd : Differentiable ℝ h)
    (hb : ∀ s, |deriv h s| ≤ C) {P : ℝ} (hP : 0 < P) (A A' : ℝ) :
    |P * h (A / P) - P * h (A' / P)| ≤ C * |A - A'| := by
  have hmv := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := h) (C := C) (fun x _ => hd x) (fun x _ => by simpa using hb x)
    (mem_univ (A' / P)) (mem_univ (A / P))
  simp only [Real.norm_eq_abs] at hmv
  rw [← mul_sub, abs_mul, abs_of_pos hP]
  calc P * |h (A / P) - h (A' / P)| ≤ P * (C * |A / P - A' / P|) := by gcongr
    _ = C * |A - A'| := by
      rw [← sub_div, abs_div, abs_of_pos hP]; field_simp

/-- Vertical Lipschitz bound for `P h(A/P)`. -/
lemma persp_vertical {h : ℝ → ℝ} {C : ℝ} (hd : Differentiable ℝ h)
    (hb : ∀ s, |h s - s * deriv h s| ≤ C) (A : ℝ) {P P' : ℝ} (hP : 0 < P) (hP' : 0 < P') :
    |P * h (A / P) - P' * h (A / P')| ≤ C * |P - P'| := by
  have hder : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun t => t * h (A / t))
      (h (A / t) - (A / t) * deriv h (A / t)) t := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt ht
    have h1 : HasDerivAt (fun t => A / t) (A * (-(t ^ 2)⁻¹)) t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_inv ht0).const_mul A
    have h2 := ((hd (A / t)).hasDerivAt.comp t h1)
    convert! (hasDerivAt_id t).fun_mul h2 using 1
      <;> try simp only [id_eq, Function.comp_apply] <;> field_simp <;> ring
  have hmv := (convex_Ioi (0 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := fun t => t * h (A / t)) (C := C)
    (fun x hx => (hder x hx).differentiableAt)
    (fun x hx => by rw [(hder x hx).deriv]; simpa using hb (A / x)) hP' hP
  simpa [Real.norm_eq_abs] using hmv

/-- **Lemma 9.4 (perspective extension).**  If `h` is differentiable with `|h'| ≤ C`,
`|h - s h'| ≤ C`, and `Q₀` is the boundary limit of `P h(A/P)` as `P ↓ 0`, then the
extended perspective is `C`-Lipschitz on `ℝ × [0, ∞)` (for the `ℓ¹` distance). -/
lemma persp_lipschitz {h : ℝ → ℝ} {C : ℝ} (hd : Differentiable ℝ h)
    (hb1 : ∀ s, |deriv h s| ≤ C) (hb2 : ∀ s, |h s - s * deriv h s| ≤ C) (Q₀ : ℝ → ℝ)
    (hlim : ∀ A, Tendsto (fun t => t * h (A / t)) (𝓝[>] 0) (𝓝 (Q₀ A))) :
    ∀ A A' P P' : ℝ, 0 ≤ P → 0 ≤ P' →
      |(if 0 < P then P * h (A / P) else Q₀ A) - (if 0 < P' then P' * h (A' / P') else Q₀ A')|
        ≤ C * (|A - A'| + |P - P'|) := by
  -- bound for positive `P, P'`
  have hpos : ∀ A A' P P' : ℝ, 0 < P → 0 < P' →
      |P * h (A / P) - P' * h (A' / P')| ≤ C * (|A - A'| + |P - P'|) := by
    intro A A' P P' hP hP'
    calc |P * h (A / P) - P' * h (A' / P')|
        ≤ |P * h (A / P) - P * h (A' / P)| + |P * h (A' / P) - P' * h (A' / P')| :=
          abs_sub_le _ _ _
      _ ≤ C * |A - A'| + C * |P - P'| :=
          add_le_add (persp_horizontal hd hb1 hP A A') (persp_vertical hd hb2 A' hP hP')
      _ = _ := by ring
  -- the value function, continuous from the right in `P`
  set Q : ℝ → ℝ → ℝ := fun A P => if 0 < P then P * h (A / P) else Q₀ A with hQ
  have hQlim : ∀ A P, 0 ≤ P → Tendsto (fun t => Q A t) (𝓝[>] P) (𝓝 (Q A P)) := by
    intro A P hP
    rcases hP.lt_or_eq with hP | rfl
    · have hc : ContinuousAt (fun t => t * h (A / t)) P :=
        continuousAt_id.mul ((hd _).continuousAt.comp (continuousAt_const.div continuousAt_id
          hP.ne'))
      have : Tendsto (fun t => t * h (A / t)) (𝓝[>] P) (𝓝 (P * h (A / P))) :=
        hc.tendsto.mono_left nhdsWithin_le_nhds
      simp only [hQ, if_pos hP]
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp [show (0:ℝ) < t from hP.trans ht]
    · simp only [hQ, lt_irrefl, if_false]
      refine (hlim A).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp [show (0:ℝ) < t from ht]
  intro A A' P P' hP hP'
  show |Q A P - Q A' P'| ≤ C * (|A - A'| + |P - P'|)
  -- pass to the limit from positive values
  have hlim2 : Tendsto (fun st : ℝ × ℝ => |Q A st.1 - Q A' st.2|) (𝓝[>] P ×ˢ 𝓝[>] P')
      (𝓝 |Q A P - Q A' P'|) :=
    (((hQlim A P hP).comp tendsto_fst).sub ((hQlim A' P' hP').comp tendsto_snd)).abs
  have hlim3 : Tendsto (fun st : ℝ × ℝ => C * (|A - A'| + |st.1 - st.2|)) (𝓝[>] P ×ˢ 𝓝[>] P')
      (𝓝 (C * (|A - A'| + |P - P'|))) := by
    have : Tendsto (fun st : ℝ × ℝ => st) (𝓝[>] P ×ˢ 𝓝[>] P') (𝓝 (P, P')) := by
      rw [nhds_prod_eq]; exact prod_mono nhdsWithin_le_nhds nhdsWithin_le_nhds
    have h1 := (continuous_fst.tendsto _).comp this
    have h2 := (continuous_snd.tendsto _).comp this
    exact (tendsto_const_nhds.add ((h1.sub h2).abs)).const_mul C
  haveI : (𝓝[>] P ×ˢ 𝓝[>] P').NeBot := Filter.prod_neBot.mpr ⟨inferInstance, inferInstance⟩
  refine le_of_tendsto_of_tendsto hlim2 hlim3 ?_
  filter_upwards [prod_mem_prod (self_mem_nhdsWithin (s := Ioi P) (a := P))
    (self_mem_nhdsWithin (s := Ioi P') (a := P'))] with st hst
  have h1 : 0 < st.1 := lt_of_le_of_lt hP hst.1
  have h2 : 0 < st.2 := lt_of_le_of_lt hP' hst.2
  simp only [hQ, if_pos h1, if_pos h2]
  exact hpos A A' st.1 st.2 h1 h2

/-- The radial factor of the vector perspective: `|G(A/r) - G(A/r')| ≤ C (r' - r)/r` for
`0 < r ≤ r'`, when `|s G'(s)| ≤ C`. -/
lemma vpersp_radial {G : ℝ → ℝ} {C : ℝ} (hG0 : G 0 = 0)
    (hd : ∀ s, s ≠ 0 → DifferentiableAt ℝ G s) (hb : ∀ s, |s * deriv G s| ≤ C)
    (A : ℝ) {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') :
    |G (A / r) - G (A / r')| ≤ C * (r' - r) / r := by
  rcases eq_or_ne A 0 with rfl | hA
  · simp only [zero_div, hG0, sub_self, abs_zero]
    have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
    exact div_nonneg (mul_nonneg hC (by linarith)) hr.le
  have hder : ∀ t ∈ Icc r r', HasDerivAt (fun t => G (A / t))
      (-(A / t) * deriv G (A / t) / t) t := by
    intro t ht
    have ht0 : t ≠ 0 := (hr.trans_le ht.1).ne'
    have h1 : HasDerivAt (fun t => A / t) (A * (-(t ^ 2)⁻¹)) t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_inv ht0).const_mul A
    have h2 := (hd (A / t) (div_ne_zero hA ht0)).hasDerivAt.comp t h1
    convert! h2 using 1 <;> field_simp <;> ring
  have hmv := (convex_Icc r r').norm_image_sub_le_of_norm_deriv_le
    (f := fun t => G (A / t)) (C := C / r)
    (fun x hx => (hder x hx).differentiableAt)
    (fun x hx => by
      rw [(hder x hx).deriv, Real.norm_eq_abs, abs_div, neg_mul, abs_neg,
        abs_of_pos (hr.trans_le hx.1)]
      have hx0 := hr.trans_le hx.1
      have hC : 0 ≤ C := le_trans (abs_nonneg _) (hb 0)
      calc |A / x * deriv G (A / x)| / x ≤ C / x := by gcongr; exact hb _
        _ ≤ C / r := div_le_div_of_nonneg_left hC hr hx.1)
    (left_mem_Icc.mpr hrr) (right_mem_Icc.mpr hrr)
  simp only [Real.norm_eq_abs] at hmv
  rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ r' - r)] at hmv
  calc |G (A / r) - G (A / r')| ≤ C / r * (r' - r) := hmv
    _ = C * (r' - r) / r := by ring

/-- **Lemma 9.9 (Lipschitz vector perspective)**, generic form.  If `G` is `L`-Lipschitz with
`G 0 = 0`, differentiable off `0`, `|G| ≤ C` and `|s G'(s)| ≤ C`, then
`Ψ(A, ξ) = G(A/|ξ|) ξ` (with `Ψ(A, 0) = 0`) is Lipschitz. -/
lemma vpersp_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    {G : ℝ → ℝ} {L C : ℝ} (hGL : ∀ s t, |G s - G t| ≤ L * |s - t|) (hG0 : G 0 = 0)
    (hd : ∀ s, s ≠ 0 → DifferentiableAt ℝ G s) (hbG : ∀ s, |G s| ≤ C)
    (hb : ∀ s, |s * deriv G s| ≤ C) (A A' : ℝ) (ξ ξ' : E) :
    ‖(if ξ = 0 then 0 else G (A / ‖ξ‖) • ξ) - (if ξ' = 0 then 0 else G (A' / ‖ξ'‖) • ξ')‖
      ≤ L * |A - A'| + 2 * C * ‖ξ - ξ'‖ := by
  set Ψ : ℝ → E → E := fun A ξ => if ξ = 0 then 0 else G (A / ‖ξ‖) • ξ with hΨ
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hbG 0)
  -- the `A`-direction
  have h1 : ∀ A A' ξ, ‖Ψ A ξ - Ψ A' ξ‖ ≤ L * |A - A'| := by
    intro A A' ξ
    have hL : 0 ≤ L := by
      have := hGL 1 0; rw [sub_zero, abs_one, mul_one] at this; exact le_trans (abs_nonneg _) this
    by_cases hξ : ξ = 0
    · simp only [hΨ, hξ, if_true, sub_zero, norm_zero]; positivity
    simp only [hΨ, hξ, if_false, ← sub_smul, norm_smul, Real.norm_eq_abs]
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    calc |G (A / ‖ξ‖) - G (A' / ‖ξ‖)| * ‖ξ‖ ≤ L * |A / ‖ξ‖ - A' / ‖ξ‖| * ‖ξ‖ := by
          gcongr; exact hGL _ _
      _ = L * |A - A'| := by rw [← sub_div, abs_div, abs_of_pos hr]; field_simp
  -- the `ξ`-direction, ordered case
  have h2 : ∀ A ξ ξ', ‖ξ‖ ≤ ‖ξ'‖ → ‖Ψ A ξ - Ψ A ξ'‖ ≤ 2 * C * ‖ξ - ξ'‖ := by
    intro A ξ ξ' hle
    by_cases hξ : ξ = 0
    · by_cases hξ' : ξ' = 0
      · simp [hΨ, hξ, hξ']
      simp only [hΨ, hξ, hξ', if_true, if_false, zero_sub, norm_neg, norm_smul,
        Real.norm_eq_abs]
      calc |G (A / ‖ξ'‖)| * ‖ξ'‖ ≤ C * ‖ξ'‖ := by gcongr; exact hbG _
        _ ≤ 2 * C * ‖ξ'‖ := by nlinarith [norm_nonneg ξ']
    have hr : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    have hξ' : ξ' ≠ 0 := fun h => by rw [h, norm_zero] at hle; linarith
    simp only [hΨ, hξ, hξ', if_false]
    have e : G (A / ‖ξ‖) • ξ - G (A / ‖ξ'‖) • ξ' =
        G (A / ‖ξ'‖) • (ξ - ξ') + (G (A / ‖ξ‖) - G (A / ‖ξ'‖)) • ξ := by
      rw [smul_sub, sub_smul]; abel
    rw [e]
    have hrad := vpersp_radial hG0 hd hb A hr hle
    have hn : ‖ξ'‖ - ‖ξ‖ ≤ ‖ξ - ξ'‖ := by
      rw [norm_sub_rev]; exact norm_sub_norm_le _ _
    calc ‖G (A / ‖ξ'‖) • (ξ - ξ') + (G (A / ‖ξ‖) - G (A / ‖ξ'‖)) • ξ‖
        ≤ |G (A / ‖ξ'‖)| * ‖ξ - ξ'‖ + |G (A / ‖ξ‖) - G (A / ‖ξ'‖)| * ‖ξ‖ := by
          refine (norm_add_le _ _).trans ?_
          simp only [norm_smul, Real.norm_eq_abs, le_refl]
      _ ≤ C * ‖ξ - ξ'‖ + C * (‖ξ'‖ - ‖ξ‖) / ‖ξ‖ * ‖ξ‖ := by
          gcongr; exact hbG _
      _ = C * ‖ξ - ξ'‖ + C * (‖ξ'‖ - ‖ξ‖) := by field_simp
      _ ≤ 2 * C * ‖ξ - ξ'‖ := by nlinarith
  have h2' : ∀ A ξ ξ', ‖Ψ A ξ - Ψ A ξ'‖ ≤ 2 * C * ‖ξ - ξ'‖ := by
    intro A ξ ξ'
    rcases le_total ‖ξ‖ ‖ξ'‖ with h | h
    · exact h2 A ξ ξ' h
    · rw [norm_sub_rev, norm_sub_rev ξ]; exact h2 A ξ' ξ h
  show ‖Ψ A ξ - Ψ A' ξ'‖ ≤ L * |A - A'| + 2 * C * ‖ξ - ξ'‖
  calc ‖Ψ A ξ - Ψ A' ξ'‖ ≤ ‖Ψ A ξ - Ψ A' ξ‖ + ‖Ψ A' ξ - Ψ A' ξ'‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := add_le_add (h1 A A' ξ) (h2' A' ξ ξ')

/-- The boundary limit of a perspective: if `h(s)/s → a` as `s → +∞` and `h(s)/s → b` as
`s → -∞`, then `t h(A/t)` tends to `aA` (if `A > 0`), `bA` (if `A < 0`), `0` (if `A = 0`)
as `t ↓ 0`. -/
lemma persp_boundary_limit {h : ℝ → ℝ} {a b : ℝ} (htop : Tendsto (fun s => h s / s) atTop (𝓝 a))
    (hbot : Tendsto (fun s => h s / s) atBot (𝓝 b)) (A : ℝ) :
    Tendsto (fun t => t * h (A / t)) (𝓝[>] 0)
      (𝓝 (if 0 < A then a * A else if A < 0 then b * A else 0)) := by
  have key : ∀ c : ℝ, ∀ l : Filter ℝ, Tendsto (fun s => h s / s) l (𝓝 c) →
      Tendsto (fun t => A / t) (𝓝[>] 0) l → A ≠ 0 →
      Tendsto (fun t => t * h (A / t)) (𝓝[>] 0) (𝓝 (c * A)) := by
    intro c l hl hA hA0
    have := (hl.comp hA).mul_const A
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [Function.comp_apply]
    field_simp
  have hinv : Tendsto (fun t : ℝ => t⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
  rcases lt_trichotomy A 0 with hA | rfl | hA
  · rw [if_neg (not_lt.mpr hA.le), if_pos hA]
    refine key b atBot hbot ?_ hA.ne
    simpa [div_eq_mul_inv] using hinv.const_mul_atTop_of_neg hA
  · simp only [lt_irrefl, if_false, zero_div]
    have : Tendsto (fun t : ℝ => t * h 0) (𝓝[>] 0) (𝓝 (0 * h 0)) :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).mul_const _
    simpa using this
  · rw [if_pos hA]
    refine key a atTop htop ?_ hA.ne'
    simpa [div_eq_mul_inv] using hinv.const_mul_atTop hA

end Buckling
end
end ChunkedSource016
/- END SOURCE 016 -/

/- BEGIN SOURCE 017: RequestProject/Main.lean -/
section ChunkedSource017

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
end ChunkedSource017
/- END SOURCE 017 -/

/- BEGIN SOURCE 018: RequestProject/Positivity/CubicParam.lean -/
section ChunkedSource018

/-!
# A parametric form of the cubic interpolation inequality (Lemma 2.3)

Lemma 2.3 of the paper is applied to a function `E` of a variable `X` which is itself a
strictly decreasing function of `r`.  We state it directly in the parameter `r`: the
`X`-derivatives of `E` are given by functions `E₁, E₂, E₃` with `dE/dr = X' E₁` etc.
-/

@[expose] public section

open Set

namespace Buckling

/-- **Lemma 2.3, parametric form.** Let `X` be continuous on `[a,b]` with `X' < 0` on
`(a,b)`, and let `E` be continuous on `[a,b]` with `E(a) = E(b) = 0`. Suppose
`E_r = X' E₁`, `(E₁)_r = X' E₂`, `(E₂)_r = X' E₃` on `(a,b)` and `E₃ < 0`. Then, writing
`D = (X - X(a))(X - X(b))`, one has `E₁ D - E (2X - X(a) - X(b)) < 0` on `(a,b)`, i.e.
`d/dX (E/D) < 0`. -/
theorem cubic_interpolation_param {X dX E E1 E2 E3 : ℝ → ℝ} {a b : ℝ}
    (hXc : ContinuousOn X (Icc a b)) (hEc : ContinuousOn E (Icc a b))
    (hX : ∀ y ∈ Ioo a b, HasDerivAt X (dX y) y) (hdX : ∀ y ∈ Ioo a b, dX y < 0)
    (hE : ∀ y ∈ Ioo a b, HasDerivAt E (dX y * E1 y) y)
    (hE1 : ∀ y ∈ Ioo a b, HasDerivAt E1 (dX y * E2 y) y)
    (hE2 : ∀ y ∈ Ioo a b, HasDerivAt E2 (dX y * E3 y) y)
    (hEa : E a = 0) (hEb : E b = 0) (h3 : ∀ y ∈ Ioo a b, E3 y < 0)
    {x : ℝ} (hx : x ∈ Ioo a b) :
    E1 x * ((X x - X a) * (X x - X b)) - E x * (2 * X x - X a - X b) < 0 := by
  have hab : a < b := hx.1.trans hx.2
  -- `X` is strictly decreasing on `[a,b]`
  have hanti : StrictAntiOn X (Icc a b) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc a b) hXc
    intro y hy
    rw [interior_Icc] at hy
    rw [(hX y hy).deriv]; exact hdX y hy
  have hXa : X x < X a := hanti ⟨le_rfl, hab.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1
  have hXb : X b < X x := hanti ⟨hx.1.le, hx.2.le⟩ ⟨hab.le, le_rfl⟩ hx.2
  set Xa := X a
  set Xb := X b
  set X0 := X x
  set D0 := (X0 - Xa) * (X0 - Xb) with hD0
  have hD0ne : D0 ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  set R0 := E x / D0 with hR0
  set ρ := (E1 x - (2 * X0 - Xa - Xb) * R0) / D0 with hρ
  -- the cubic `P` and its derivatives
  obtain ⟨P, hP⟩ : ∃ P : ℝ → ℝ, P = fun ξ => (ξ - Xa) * (ξ - Xb) * (R0 + ρ * (ξ - X0)) := ⟨_, rfl⟩
  obtain ⟨P1, hP1⟩ : ∃ P1 : ℝ → ℝ, P1 = fun ξ => (2 * ξ - Xa - Xb) * (R0 + ρ * (ξ - X0)) +
    (ξ - Xa) * (ξ - Xb) * ρ := ⟨_, rfl⟩
  obtain ⟨P2, hP2⟩ : ∃ P2 : ℝ → ℝ, P2 = fun ξ => 2 * (R0 + ρ * (ξ - X0)) + 2 * (2 * ξ - Xa - Xb) * ρ :=
    ⟨_, rfl⟩
  have hPd : ∀ ξ, HasDerivAt P (P1 ξ) ξ := by
    intro ξ
    have h := (((hasDerivAt_id ξ).sub_const Xa).mul ((hasDerivAt_id ξ).sub_const Xb)).mul
      (((hasDerivAt_id ξ).sub_const X0).const_mul ρ |>.const_add R0)
    rw [hP]
    refine h.congr_deriv ?_
    simp only [hP1, id, Pi.mul_apply]; ring
  have hP1d : ∀ ξ, HasDerivAt P1 (P2 ξ) ξ := by
    intro ξ
    have h := ((((hasDerivAt_id ξ).const_mul 2).sub_const Xa).sub_const Xb).mul
      (((hasDerivAt_id ξ).sub_const X0).const_mul ρ |>.const_add R0) |>.add
      ((((hasDerivAt_id ξ).sub_const Xa).mul ((hasDerivAt_id ξ).sub_const Xb)).mul_const ρ)
    rw [hP1]
    refine h.congr_deriv ?_
    simp only [hP2, id]; ring
  have hP2d : ∀ ξ, HasDerivAt P2 (6 * ρ) ξ := by
    intro ξ
    have h := ((((hasDerivAt_id ξ).sub_const X0).const_mul ρ |>.const_add R0).const_mul 2).add
      (((((hasDerivAt_id ξ).const_mul 2).sub_const Xa).sub_const Xb).const_mul 2 |>.mul_const ρ)
    rw [hP2]
    refine h.congr_deriv ?_
    ring
  -- the three functions `H`, `H₁`, `H₂`
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun y => E y - P (X y) := ⟨_, rfl⟩
  obtain ⟨H1, hH1⟩ : ∃ H1 : ℝ → ℝ, H1 = fun y => E1 y - P1 (X y) := ⟨_, rfl⟩
  obtain ⟨H2, hH2⟩ : ∃ H2 : ℝ → ℝ, H2 = fun y => E2 y - P2 (X y) := ⟨_, rfl⟩
  have hHd : ∀ y ∈ Ioo a b, HasDerivAt H (dX y * H1 y) y := by
    intro y hy
    have h := (hE y hy).sub ((hPd (X y)).comp y (hX y hy))
    rw [hH]
    refine h.congr_deriv ?_
    simp only [hH1]; ring
  have hH1d : ∀ y ∈ Ioo a b, HasDerivAt H1 (dX y * H2 y) y := by
    intro y hy
    have h := (hE1 y hy).sub ((hP1d (X y)).comp y (hX y hy))
    rw [hH1]
    refine h.congr_deriv ?_
    simp only [hH2]; ring
  have hH2d : ∀ y ∈ Ioo a b, HasDerivAt H2 (dX y * (E3 y - 6 * ρ)) y := by
    intro y hy
    have h := (hE2 y hy).sub ((hP2d (X y)).comp y (hX y hy))
    rw [hH2]
    refine h.congr_deriv ?_
    ring
  have hPcont : Continuous P := by rw [hP]; fun_prop
  have hHc : ContinuousOn H (Icc a b) := by
    rw [hH]; exact hEc.sub (hPcont.comp_continuousOn hXc)
  have hH1c : ∀ s t, a < s → t < b → ContinuousOn H1 (Icc s t) := by
    intro s t hs ht y hy
    have hy' : y ∈ Ioo a b := ⟨hs.trans_le hy.1, hy.2.trans_lt ht⟩
    exact (hH1d y hy').continuousAt.continuousWithinAt
  have hH2c : ∀ s t, a < s → t < b → ContinuousOn H2 (Icc s t) := by
    intro s t hs ht y hy
    have hy' : y ∈ Ioo a b := ⟨hs.trans_le hy.1, hy.2.trans_lt ht⟩
    exact (hH2d y hy').continuousAt.continuousWithinAt
  -- values
  have hHa : H a = 0 := by rw [hH, hP]; simp [hEa, Xa]
  have hHb : H b = 0 := by rw [hH, hP]; simp [hEb, Xb]
  have hHx : H x = 0 := by
    rw [hH, hP]
    simp only [show X x = X0 from rfl, sub_self, mul_zero, add_zero]
    rw [hR0]
    field_simp
    simp [hD0]
  have hH1x : H1 x = 0 := by
    rw [hH1, hP1]
    simp only [show X x = X0 from rfl, sub_self, mul_zero, add_zero]
    rw [hρ]
    field_simp
    ring
  -- Rolle three times
  obtain ⟨y1, hy1, h1⟩ := exists_hasDerivAt_eq_zero hx.1 (hHc.mono (Icc_subset_Icc le_rfl hx.2.le))
    (hHa.trans hHx.symm) (fun y hy => hHd y ⟨hy.1, hy.2.trans hx.2⟩)
  obtain ⟨y2, hy2, h2⟩ := exists_hasDerivAt_eq_zero hx.2 (hHc.mono (Icc_subset_Icc hx.1.le le_rfl))
    (hHx.trans hHb.symm) (fun y hy => hHd y ⟨hx.1.trans hy.1, hy.2⟩)
  have hy1' : y1 ∈ Ioo a b := ⟨hy1.1, hy1.2.trans hx.2⟩
  have hy2' : y2 ∈ Ioo a b := ⟨hx.1.trans hy2.1, hy2.2⟩
  have hH1y1 : H1 y1 = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · linarith [hdX y1 hy1']
    · exact h
  have hH1y2 : H1 y2 = 0 := by
    rcases mul_eq_zero.mp h2 with h | h
    · linarith [hdX y2 hy2']
    · exact h
  obtain ⟨z1, hz1, k1⟩ := exists_hasDerivAt_eq_zero hy1.2 (hH1c y1 x hy1.1 hx.2)
    (hH1y1.trans hH1x.symm) (fun y hy => hH1d y ⟨hy1.1.trans hy.1, hy.2.trans hx.2⟩)
  obtain ⟨z2, hz2, k2⟩ := exists_hasDerivAt_eq_zero hy2.1 (hH1c x y2 hx.1 hy2.2)
    (hH1x.trans hH1y2.symm) (fun y hy => hH1d y ⟨hx.1.trans hy.1, hy.2.trans hy2.2⟩)
  have hz1' : z1 ∈ Ioo a b := ⟨hy1.1.trans hz1.1, hz1.2.trans hx.2⟩
  have hz2' : z2 ∈ Ioo a b := ⟨hx.1.trans hz2.1, hz2.2.trans hy2.2⟩
  have hH2z1 : H2 z1 = 0 := by
    rcases mul_eq_zero.mp k1 with h | h
    · linarith [hdX z1 hz1']
    · exact h
  have hH2z2 : H2 z2 = 0 := by
    rcases mul_eq_zero.mp k2 with h | h
    · linarith [hdX z2 hz2']
    · exact h
  have hz12 : z1 < z2 := hz1.2.trans hz2.1
  obtain ⟨w, hw, kw⟩ := exists_hasDerivAt_eq_zero hz12 (hH2c z1 z2 hz1'.1 hz2'.2)
    (hH2z1.trans hH2z2.symm) (fun y hy => hH2d y ⟨hz1'.1.trans hy.1, hy.2.trans hz2'.2⟩)
  have hw' : w ∈ Ioo a b := ⟨hz1'.1.trans hw.1, hw.2.trans hz2'.2⟩
  have hρneg : ρ < 0 := by
    rcases mul_eq_zero.mp kw with h | h
    · linarith [hdX w hw']
    · linarith [h3 w hw']
  -- translate `ρ < 0`
  have hD0pos : 0 < D0 ∨ D0 < 0 := lt_or_gt_of_ne hD0ne.symm
  have hD0neg : D0 < 0 := by
    simp only [hD0]; nlinarith
  have : E1 x * D0 - E x * (2 * X0 - Xa - Xb) = ρ * D0 ^ 2 := by
    rw [hρ, hR0]; field_simp
  rw [this]
  have : 0 < D0 ^ 2 := by positivity
  nlinarith

end Buckling
end
end ChunkedSource018
/- END SOURCE 018 -/

/- BEGIN SOURCE 019: RequestProject/Profiles/Taylor.lean -/
section ChunkedSource019

/-!
# One-sided Taylor bounds from derivative bounds

If `F(k) = 0` and `F' = O((k - s)^m)` as `s → k⁻`, then `F = O((k - s)^(m+1))`.
-/

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace Buckling

/-- Integration of a one-sided `O`-bound on the derivative. -/
theorem isBigO_pow_succ_of_deriv {F F' : ℝ → ℝ} {k : ℝ} {m : ℕ}
    (hd : ∀ᶠ s in 𝓝 k, HasDerivAt F (F' s) s) (h0 : F k = 0)
    (hF' : F' =O[𝓝[<] k] fun s => (k - s) ^ m) :
    F =O[𝓝[<] k] fun s => (k - s) ^ (m + 1) := by
  obtain ⟨C, hC, hCw⟩ := hF'.exists_pos
  rw [IsBigOWith] at hCw
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hd
  have hev : ∀ᶠ s in 𝓝[<] k, ‖F' s‖ ≤ C * ‖(k - s) ^ m‖ ∧ s ∈ Metric.ball k ε :=
    hCw.and (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds k hε))
  obtain ⟨a, ha, hall⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp hev
  refine IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with r hr
  have hrk : r < k := hr.2
  have hcont : ContinuousOn F (Icc r k) := by
    intro x hx
    have hx' : x ∈ Metric.ball k ε := by
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h]; exact Metric.mem_ball_self hε
      · exact (hall ⟨hr.1.trans_le hx.1, h⟩).2
    exact (hball x hx').continuousAt.continuousWithinAt
  have hdiff : ∀ x ∈ Ioo r k, HasDerivAt F (F' x) x := fun x hx =>
    hball x (hall ⟨hr.1.trans hx.1, hx.2⟩).2
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope F F' hrk hcont hdiff
  have hbound := (hall ⟨hr.1.trans hξ.1, hξ.2⟩).1
  rw [h0] at hξeq
  have hFr : F r = -(F' ξ * (k - r)) := by
    rw [hξeq]; field_simp [(sub_pos.mpr hrk).ne']; ring
  have h1 : ‖(k - ξ) ^ m‖ ≤ (k - r) ^ m := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hξ.2)]
    exact pow_le_pow_left₀ (sub_pos.mpr hξ.2).le (by linarith [hξ.1]) m
  have h2 : ‖k - r‖ = k - r := by rw [Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hrk)]
  rw [hFr, norm_neg, norm_mul, norm_pow, h2]
  calc ‖F' ξ‖ * (k - r) ≤ C * ‖(k - ξ) ^ m‖ * (k - r) :=
        mul_le_mul_of_nonneg_right hbound (sub_pos.mpr hrk).le
    _ ≤ C * (k - r) ^ m * (k - r) := by gcongr
    _ = C * (k - r) ^ (m + 1) := by ring

/-- A function continuous at `k` is `O(1)` near `k`. -/
lemma isBigO_one_of_continuousAt {F : ℝ → ℝ} {k : ℝ} (h : ContinuousAt F k) :
    F =O[𝓝[<] k] fun s => (k - s) ^ 0 := by
  simp only [pow_zero]
  exact (h.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℝ

/-- Powers of `k - s` are decreasing in the exponent near `k`. -/
lemma isBigO_pow_pow {k : ℝ} {m n : ℕ} (h : m ≤ n) :
    (fun s : ℝ => (k - s) ^ n) =O[𝓝[<] k] fun s => (k - s) ^ m := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [Ioo_mem_nhdsLT (show k - 1 < k by linarith)] with s hs
  have h0 : 0 < k - s := sub_pos.mpr hs.2
  have h1 : k - s < 1 := by linarith [hs.1]
  rw [one_mul, norm_pow, norm_pow, Real.norm_eq_abs, abs_of_pos h0]
  exact pow_le_pow_of_le_one h0.le h1.le h

/-- If `F = O((k-s)^(n+1))` then `F/(k-s)^n → 0`. -/
lemma tendsto_div_pow_of_isBigO {F : ℝ → ℝ} {k : ℝ} {n : ℕ}
    (h : F =O[𝓝[<] k] fun s => (k - s) ^ (n + 1)) :
    Tendsto (fun s => F s / (k - s) ^ n) (𝓝[<] k) (𝓝 0) := by
  obtain ⟨C, hC⟩ := h.bound
  apply squeeze_zero_norm' (a := fun s => C * (k - s))
  · filter_upwards [hC, self_mem_nhdsWithin] with s hs hs'
    have h0 : 0 < k - s := sub_pos.mpr (mem_Iio.mp hs')
    rw [norm_div, norm_pow, Real.norm_eq_abs (k - s), abs_of_pos h0, div_le_iff₀ (by positivity)]
    rw [norm_pow, Real.norm_eq_abs (k - s), abs_of_pos h0] at hs
    calc ‖F s‖ ≤ C * (k - s) ^ (n + 1) := hs
      _ = C * (k - s) * (k - s) ^ n := by ring
  · have : Tendsto (fun s : ℝ => C * (k - s)) (𝓝 k) (𝓝 (C * (k - k))) :=
      (continuous_const.mul (continuous_const.sub continuous_id)).tendsto k
    rw [sub_self, mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds

end Buckling
end
end ChunkedSource019
/- END SOURCE 019 -/

/- BEGIN SOURCE 020: RequestProject/Sobolev/Defs.lean -/
section ChunkedSource020

/-!
# Sobolev form domains and variational eigenvalues (Definition 1.2 of the paper)

For an open set `Ω ⊆ ℝ²` we realise `H₀¹(Ω)` and `H₀²(Ω)` as the closures of
`C_c^∞(Ω)` in the respective Sobolev norms.  Concretely, a test function `φ` is
identified with the tuple of its derivatives up to order `m`, viewed as an element of
a finite product of copies of `L²(Ω)`; `H₀^m(Ω)` is the closure of the set of these
tuples.  This is the completion of `C_c^∞(Ω)` in the `H^m(Ω)` norm, and the
components of a limit tuple are the function and its weak derivatives.

The energies are
* `E₀(v) = ∫_Ω v²`,
* `E₁(v) = ∫_Ω |∇v|²`,
* `E₂(v) = ∫_Ω |Δv|²`,

and the variational eigenvalues are the infima of the Rayleigh quotients
`λ₁ᴰ(Ω) = inf E₁/E₀` over `H₀¹(Ω)` and `Λ₁(Ω) = inf E₂/E₁` over `H₀²(Ω)`.
The infima are taken over the elements with nonzero denominator; by Lemma 7.3 of
the paper (nonzero denominators) these are exactly the nonzero elements.
-/

@[expose] public section

open MeasureTheory

namespace Buckling

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The partial derivative `∂ᵢ φ` of a function on the plane. -/
noncomputable def pderiv (i : Fin 2) (φ : Plane → ℝ) : Plane → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- The Laplacian `Δφ = ∂₁∂₁φ + ∂₂∂₂φ`. -/
noncomputable def laplacian (φ : Plane → ℝ) : Plane → ℝ :=
  fun x => pderiv 0 (pderiv 0 φ) x + pderiv 1 (pderiv 1 φ) x

/-- `φ ∈ C_c^∞(Ω)`: `φ` is smooth, and its support is a compact subset of `Ω`. -/
def IsTestFn (Ω : Set Plane) (φ : Plane → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- The real Hilbert space `L²(Ω)`. -/
noncomputable abbrev L2 (Ω : Set Plane) := Lp ℝ 2 (volume.restrict Ω)

lemma IsTestFn.contDiff {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    ContDiff ℝ (⊤ : ℕ∞) φ := h.1

lemma IsTestFn.pderiv {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) (i : Fin 2) :
    IsTestFn Ω (pderiv i φ) := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) :=
      h.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
    exact h1.clm_apply contDiff_const
  · exact (h.2.1.fderiv (𝕜 := ℝ)).comp_left (g := fun L => L (EuclideanSpace.single i 1))
      (by simp)
  · refine subset_trans ?_ h.2.2
    exact (tsupport_fderiv_subset ℝ).trans' (by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support] at hx ⊢
      intro h0
      exact hx (by simp [Buckling.pderiv, h0]))

lemma IsTestFn.memLp {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    MemLp φ 2 (volume.restrict Ω) :=
  (h.1.continuous.memLp_of_hasCompactSupport h.2.1).restrict Ω

/-- A test function as an element of `L²(Ω)`. -/
noncomputable def IsTestFn.toL2 {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) : L2 Ω :=
  h.memLp.toLp φ

/-- The `H¹`-data `(φ, ∂₁φ, ∂₂φ)` of a test function. -/
noncomputable def graphH1 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    L2 Ω × (Fin 2 → L2 Ω) :=
  (φ.2.toL2, fun i => (φ.2.pderiv i).toL2)

/-- The `H²`-data `(φ, (∂ᵢφ)ᵢ, (∂ᵢ∂ⱼφ)ᵢⱼ)` of a test function. -/
noncomputable def graphH2 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω) :=
  (φ.2.toL2, fun i => (φ.2.pderiv i).toL2, fun i j => ((φ.2.pderiv j).pderiv i).toL2)

/-- `H₀¹(Ω)`: the closure of `C_c^∞(Ω)` in the `H¹` norm. -/
def H01 (Ω : Set Plane) : Set (L2 Ω × (Fin 2 → L2 Ω)) :=
  closure (Set.range (graphH1 (Ω := Ω)))

/-- `H₀²(Ω)`: the closure of `C_c^∞(Ω)` in the `H²` norm. -/
def H02 (Ω : Set Plane) : Set (L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) :=
  closure (Set.range (graphH2 (Ω := Ω)))

/-- `E₀(v) = ∫_Ω v²` on `H₀¹(Ω)`. -/
noncomputable def energy0 {Ω : Set Plane} (v : L2 Ω × (Fin 2 → L2 Ω)) : ℝ := ‖v.1‖ ^ 2

/-- `E₁(v) = ∫_Ω |∇v|²` on `H₀¹(Ω)`. -/
noncomputable def energy1 {Ω : Set Plane} (v : L2 Ω × (Fin 2 → L2 Ω)) : ℝ :=
  ∑ i, ‖v.2 i‖ ^ 2

/-- `E₁(v) = ∫_Ω |∇v|²` on `H₀²(Ω)`. -/
noncomputable def energy1' {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) : ℝ :=
  ∑ i, ‖v.2.1 i‖ ^ 2

/-- `E₂(v) = ∫_Ω |Δv|²` on `H₀²(Ω)`. -/
noncomputable def energy2 {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) : ℝ :=
  ‖v.2.2 0 0 + v.2.2 1 1‖ ^ 2

/-- The first Dirichlet eigenvalue `λ₁ᴰ(Ω) = inf_{0 ≠ v ∈ H₀¹(Ω)} E₁(v)/E₀(v)`. -/
noncomputable def dirichletEig (Ω : Set Plane) : ℝ :=
  ⨅ v : {v // v ∈ H01 Ω ∧ energy0 v ≠ 0}, energy1 v.1 / energy0 v.1

/-- The first buckling eigenvalue `Λ₁(Ω) = inf_{0 ≠ v ∈ H₀²(Ω)} E₂(v)/E₁(v)`. -/
noncomputable def bucklingEig (Ω : Set Plane) : ℝ :=
  ⨅ v : {v // v ∈ H02 Ω ∧ energy1' v ≠ 0}, energy2 v.1 / energy1' v.1

end Buckling
end
end ChunkedSource020
/- END SOURCE 020 -/

/- BEGIN SOURCE 021: RequestProject/Disk/Polar.lean -/
section ChunkedSource021

/-!
# Polar coordinates in the plane

`∫ F = ∫₀ᴿ r ∫₀^{2π} F(a + r e(θ)) dθ dr` for continuous `F` vanishing outside `B_R(a)`,
where `e(θ) = (cos θ, sin θ)`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology intervalIntegral

namespace Buckling

/-- The unit vector `e(θ) = (cos θ, sin θ)`. -/
noncomputable def ePt (θ : ℝ) : Plane :=
  cos θ • EuclideanSpace.single 0 1 + sin θ • EuclideanSpace.single 1 1

/-- The rotated unit vector `e'(θ) = (-sin θ, cos θ)`. -/
noncomputable def ePt' (θ : ℝ) : Plane :=
  (-sin θ) • EuclideanSpace.single 0 1 + cos θ • EuclideanSpace.single 1 1

@[simp] lemma ePt_apply0 (θ : ℝ) : ePt θ 0 = cos θ := by simp [ePt]
@[simp] lemma ePt_apply1 (θ : ℝ) : ePt θ 1 = sin θ := by simp [ePt]
@[simp] lemma ePt'_apply0 (θ : ℝ) : ePt' θ 0 = -sin θ := by simp [ePt']
@[simp] lemma ePt'_apply1 (θ : ℝ) : ePt' θ 1 = cos θ := by simp [ePt']

lemma norm_ePt (θ : ℝ) : ‖ePt θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; simp [Fin.sum_univ_two]

lemma hasDerivAt_ePt (θ : ℝ) : HasDerivAt ePt (ePt' θ) θ := by
  have := ((hasDerivAt_cos θ).smul_const (EuclideanSpace.single 0 1 : Plane)).add
    ((hasDerivAt_sin θ).smul_const (EuclideanSpace.single 1 1 : Plane))
  simpa only [ePt, ePt'] using! this

lemma hasDerivAt_ePt' (θ : ℝ) : HasDerivAt ePt' (-ePt θ) θ := by
  have hs : HasDerivAt
      (fun t : ℝ => (-(sin t)) • (EuclideanSpace.single 0 1 : Plane) +
        cos t • (EuclideanSpace.single 1 1 : Plane))
      ((-(cos θ)) • (EuclideanSpace.single 0 1 : Plane) +
        (-(sin θ)) • (EuclideanSpace.single 1 1 : Plane)) θ :=
    ((hasDerivAt_sin θ).fun_neg.smul_const (EuclideanSpace.single 0 1 : Plane)).fun_add
      ((hasDerivAt_cos θ).smul_const (EuclideanSpace.single 1 1 : Plane))
  have hfun : (fun t : ℝ => (-(sin t)) • (EuclideanSpace.single 0 1 : Plane) +
      cos t • (EuclideanSpace.single 1 1 : Plane)) = ePt' := by
    funext t
    simp only [ePt', Pi.neg_apply]
  have hder : ((-(cos θ)) • (EuclideanSpace.single 0 1 : Plane) +
      (-(sin θ)) • (EuclideanSpace.single 1 1 : Plane)) = -ePt θ := by
    simp only [ePt, neg_add, neg_smul]
  rw [hfun] at hs
  exact hs.congr_deriv hder

lemma continuous_ePt : Continuous ePt :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_ePt θ).continuousAt

lemma continuous_ePt' : Continuous ePt' :=
  continuous_iff_continuousAt.2 fun θ => (hasDerivAt_ePt' θ).continuousAt

/-- The measurable equivalence `ℝ × ℝ ≃ Plane`. -/
noncomputable def prodToPlane : ℝ × ℝ ≃ᵐ Plane :=
  MeasurableEquiv.finTwoArrow.symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma prodToPlane_mp : MeasurePreserving prodToPlane := by
  have h1 := (volume_preserving_finTwoArrow ℝ).symm
  have h2 := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).symm
  exact h2.comp h1

lemma prodToPlane_apply (p : ℝ × ℝ) :
    prodToPlane p = p.1 • EuclideanSpace.single 0 1 + p.2 • EuclideanSpace.single 1 1 := by
  ext i
  fin_cases i <;> simp [prodToPlane, MeasurableEquiv.finTwoArrow]

/-- **Polar coordinates.** -/
theorem integral_polar {F : Plane → ℝ} (hF : Continuous F) (a : Plane) {R : ℝ} (hR : 0 < R)
    (hs : ∀ x, R ≤ ‖x - a‖ → F x = 0) :
    ∫ x, F x = ∫ r in (0 : ℝ)..R, r * ∫ θ in (0 : ℝ)..2 * π, F (a + r • ePt θ) := by
  have hsymm : ∀ p : ℝ × ℝ, prodToPlane (polarCoord.symm p) = p.1 • ePt p.2 := by
    intro p
    rw [prodToPlane_apply, polarCoord_symm_apply]
    simp only [ePt, smul_add, smul_smul]
  have hzero : ∀ r θ, R ≤ r → F (a + r • ePt θ) = 0 := by
    intro r θ hr
    apply hs
    rw [add_sub_cancel_left, norm_smul, norm_ePt, mul_one, Real.norm_eq_abs]
    exact hr.trans (le_abs_self r)
  have h1 : ∫ x, F x = ∫ p : ℝ × ℝ, F (a + prodToPlane p) := by
    rw [← integral_add_left_eq_self (fun x => F x) a]
    exact (prodToPlane_mp.integral_comp' (fun y => F (a + y))).symm
  rw [h1, ← integral_comp_polarCoord_symm]
  simp_rw [hsymm, smul_eq_mul]
  set H : ℝ × ℝ → ℝ := fun p => p.1 * F (a + p.1 • ePt p.2) with hHdef
  have hHc : Continuous H :=
    continuous_fst.mul (hF.comp (continuous_const.add
      (continuous_fst.smul (continuous_ePt.comp continuous_snd))))
  have hH : IntegrableOn H (Ioi 0 ×ˢ Ioo (-π) π) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    have hs' : IntegrableOn H (Icc 0 R ×ˢ Icc (-π) π) :=
      hHc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine (hs'.mono_set ?_ : IntegrableOn H (Ioc 0 R ×ˢ Ioo (-π) π)).of_forall_diff_eq_zero
      (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    · exact prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self
    · intro p hp
      have h1 : 0 < p.1 := hp.1.1
      have h2 : ¬ (p.1 ≤ R) := fun h => hp.2 ⟨⟨h1, h⟩, hp.1.2⟩
      simp only [hHdef]
      rw [hzero p.1 p.2 (le_of_lt (not_le.1 h2)), mul_zero]
  rw [polarCoord_target, Measure.volume_eq_prod, setIntegral_prod _ hH]
  have hinner : ∀ r : ℝ, ∫ θ in Ioo (-π) π, H (r, θ) =
      r * ∫ θ in (0 : ℝ)..2 * π, F (a + r • ePt θ) := by
    intro r
    simp only [hHdef]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [pi_pos])]
    have hper : Function.Periodic (fun θ => F (a + r • ePt θ)) (2 * π) := fun θ => by
      simp [ePt, cos_add_two_pi, sin_add_two_pi]
    have := hper.intervalIntegral_add_eq (-π) 0
    rw [show -π + 2 * π = π by ring, zero_add] at this
    exact this
  simp_rw [hinner]
  rw [intervalIntegral.integral_of_le hR.le]
  refine setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
    Ioc_subset_Ioi_self (Eventually.of_forall fun r hr => ?_)
  have hr' : R < r := lt_of_not_ge fun h => hr.2 ⟨hr.1, h⟩
  have : ∫ θ in (0 : ℝ)..2 * π, F (a + r • ePt θ) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))
      (fun θ _ => hzero r θ hr'.le)]
    simp
  rw [this, mul_zero]

end Buckling
end
end ChunkedSource021
/- END SOURCE 021 -/

/- BEGIN SOURCE 022: RequestProject/Disk/Coeff.lean -/
section ChunkedSource022

/-!
# Angular Fourier coefficients of a test function on a disk

For a smooth compactly supported `φ` and a centre `a`, put `u(r, θ) = φ(a + r e(θ))` and
let `aC n r`, `bC n r` be the cosine and sine coefficients of `u(r, ·)`.  We compute their
`r`-derivatives, express the angular derivatives through the coefficient rule, and show
that each coefficient is an admissible radial mode.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology intervalIntegral Metric

namespace Buckling

namespace DiskCoeff

open Fourier1D

variable (φ : Plane → ℝ) (a : Plane)

/-- `u(r, θ) = φ(a + r e(θ))`. -/
noncomputable def U0 (r θ : ℝ) : ℝ := φ (a + r • ePt θ)
/-- `∂ᵣ u`. -/
noncomputable def G1 (r θ : ℝ) : ℝ := fderiv ℝ φ (a + r • ePt θ) (ePt θ)
/-- `r⁻¹ ∂_θ u`. -/
noncomputable def G2 (r θ : ℝ) : ℝ := fderiv ℝ φ (a + r • ePt θ) (ePt' θ)
/-- `∂ᵣ² u`. -/
noncomputable def G11 (r θ : ℝ) : ℝ := fderiv ℝ (fderiv ℝ φ) (a + r • ePt θ) (ePt θ) (ePt θ)
/-- The second derivative in the direction `e'(θ)`. -/
noncomputable def G22 (r θ : ℝ) : ℝ := fderiv ℝ (fderiv ℝ φ) (a + r • ePt θ) (ePt' θ) (ePt' θ)

/-- The cosine coefficient of `u(r, ·)`. -/
noncomputable def aC (n : ℤ) (r : ℝ) : ℝ := cosC n (U0 φ a r)
/-- The sine coefficient of `u(r, ·)`. -/
noncomputable def bC (n : ℤ) (r : ℝ) : ℝ := sinC n (U0 φ a r)

variable {φ}

lemma path_r (r θ : ℝ) : HasDerivAt (fun r : ℝ => a + r • ePt θ) (ePt θ) r := by
  simpa using ((hasDerivAt_id r).smul_const (ePt θ)).const_add a

lemma path_θ (r θ : ℝ) : HasDerivAt (fun θ : ℝ => a + r • ePt θ) (r • ePt' θ) θ :=
  ((hasDerivAt_ePt θ).const_smul r).const_add a

lemma cont_pt : Continuous fun p : ℝ × ℝ => a + p.1 • ePt p.2 :=
  continuous_const.add (continuous_fst.smul (continuous_ePt.comp continuous_snd))

lemma contDiff_two_of {f f' f'' : ℝ → ℝ} (h1 : ∀ r, HasDerivAt f (f' r) r)
    (h2 : ∀ r, HasDerivAt f' (f'' r) r) (h3 : Continuous f'') : ContDiff ℝ 2 f := by
  have hd : deriv f = f' := funext fun r => (h1 r).deriv
  have hd' : deriv f' = f'' := funext fun r => (h2 r).deriv
  refine (contDiff_succ_iff_deriv (n := 1)).2 ⟨fun r => (h1 r).differentiableAt, by simp, ?_⟩
  rw [hd]
  refine (contDiff_succ_iff_deriv (n := 0)).2 ⟨fun r => (h2 r).differentiableAt, by simp, ?_⟩
  rw [hd']
  exact contDiff_zero.2 h3

section Smooth

variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
include hφ

lemma diff1 : Differentiable ℝ φ := hφ.differentiable (by simp)

lemma cdiff1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) :=
  hφ.fderiv_right (m := (⊤ : ℕ∞)) (by simp)

lemma diff2 : Differentiable ℝ (fderiv ℝ φ) := (cdiff1 hφ).differentiable (by simp)

lemma cont1 : Continuous (fderiv ℝ φ) := (cdiff1 hφ).continuous

lemma cont2 : Continuous (fderiv ℝ (fderiv ℝ φ)) := (cdiff1 hφ).continuous_fderiv (by simp)

lemma hasDerivAt_U0_r (r θ : ℝ) : HasDerivAt (fun r => U0 φ a r θ) (G1 φ a r θ) r :=
  ((diff1 hφ) _).hasFDerivAt.comp_hasDerivAt r (path_r a r θ)

lemma hasDerivAt_G1_r (r θ : ℝ) : HasDerivAt (fun r => G1 φ a r θ) (G11 φ a r θ) r := by
  have h1 := ((diff2 hφ) _).hasFDerivAt.comp_hasDerivAt r (path_r a r θ)
  have := h1.clm_apply (hasDerivAt_const r (ePt θ))
  simpa [G1, G11] using this

lemma hasDerivAt_U0_θ (r θ : ℝ) : HasDerivAt (fun θ => U0 φ a r θ) (r * G2 φ a r θ) θ := by
  have := ((diff1 hφ) _).hasFDerivAt.comp_hasDerivAt θ (path_θ a r θ)
  simpa [U0, G2, map_smul] using! this

lemma hasDerivAt_G2_θ (r θ : ℝ) : HasDerivAt (fun θ => r * G2 φ a r θ)
    (r ^ 2 * G22 φ a r θ - r * G1 φ a r θ) θ := by
  have h1 := ((diff2 hφ) _).hasFDerivAt.comp_hasDerivAt θ (path_θ a r θ)
  have h2 := (h1.clm_apply (hasDerivAt_ePt' θ)).const_mul r
  convert! h2 using 1
    <;> try simp only [G2, G22, G1, Function.comp_apply, map_smul, map_neg, smul_apply, smul_eq_mul]
    <;> ring

lemma cont_U0 : Continuous (Function.uncurry (U0 φ a)) :=
  hφ.continuous.comp (continuous_const.add (continuous_fst.smul (continuous_ePt.comp continuous_snd)))

lemma cont_G1 : Continuous (Function.uncurry (G1 φ a)) :=
  ((cont1 hφ).comp (cont_pt a)).clm_apply (continuous_ePt.comp continuous_snd)

lemma cont_G2 : Continuous (Function.uncurry (G2 φ a)) :=
  ((cont1 hφ).comp (cont_pt a)).clm_apply (continuous_ePt'.comp continuous_snd)

lemma cont_G11 : Continuous (Function.uncurry (G11 φ a)) :=
  (((cont2 hφ).comp (cont_pt a)).clm_apply (continuous_ePt.comp continuous_snd)).clm_apply
    (continuous_ePt.comp continuous_snd)

lemma cont_G22 : Continuous (Function.uncurry (G22 φ a)) :=
  (((cont2 hφ).comp (cont_pt a)).clm_apply (continuous_ePt'.comp continuous_snd)).clm_apply
    (continuous_ePt'.comp continuous_snd)

variable (hc : HasCompactSupport φ)
include hc

lemma bound_G1 : ∃ C, ∀ r θ, |G1 φ a r θ| ≤ C := by
  obtain ⟨C, hC⟩ := (cont1 hφ).bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  refine ⟨C, fun r θ => ?_⟩
  rw [← Real.norm_eq_abs]
  calc ‖G1 φ a r θ‖ ≤ ‖fderiv ℝ φ (a + r • ePt θ)‖ * ‖ePt θ‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ C * 1 := by rw [norm_ePt]; exact mul_le_mul_of_nonneg_right (hC _) zero_le_one
    _ = C := mul_one C

lemma bound_quad : ∃ C, ∀ x (v : Plane), ‖v‖ ≤ 1 → |fderiv ℝ (fderiv ℝ φ) x v v| ≤ C := by
  have hK : IsCompact (tsupport (fderiv ℝ φ) ×ˢ Metric.closedBall (0 : Plane) 1) :=
    (hc.fderiv (𝕜 := ℝ)).isCompact.prod (isCompact_closedBall _ _)
  have hH : Continuous fun p : Plane × Plane => fderiv ℝ (fderiv ℝ φ) p.1 p.2 p.2 :=
    (((cont2 hφ).comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨max C 0, fun x v hv => ?_⟩
  by_cases hx : x ∈ tsupport (fderiv ℝ φ)
  · have := hC (x, v) ⟨hx, by simpa using hv⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have h0 : fderiv ℝ (fderiv ℝ φ) x = 0 :=
      Function.notMem_support.1 fun h => hx (support_fderiv_subset ℝ h)
    simp [h0]

lemma bound_G11 : ∃ C, ∀ r θ, |G11 φ a r θ| ≤ C := by
  obtain ⟨C, hC⟩ := bound_quad hφ hc
  exact ⟨C, fun r θ => hC _ _ (norm_ePt θ).le⟩

/-- `r`-derivatives of the coefficients. -/
lemma hasDerivAt_aC (n : ℤ) (r : ℝ) : HasDerivAt (aC φ a n) (cosC n (G1 φ a r)) r := by
  obtain ⟨C, hC⟩ := bound_G1 a hφ hc
  exact hasDerivAt_wcoeff (hasDerivAt_U0_r a hφ) (cont_U0 a hφ) (cont_G1 a hφ) hC
    (continuous_cos_n n) (abs_cos_le n) r

lemma hasDerivAt_bC (n : ℤ) (r : ℝ) : HasDerivAt (bC φ a n) (sinC n (G1 φ a r)) r := by
  obtain ⟨C, hC⟩ := bound_G1 a hφ hc
  exact hasDerivAt_wcoeff (hasDerivAt_U0_r a hφ) (cont_U0 a hφ) (cont_G1 a hφ) hC
    (continuous_sin_n n) (abs_sin_le n) r

lemma hasDerivAt_aC1 (n : ℤ) (r : ℝ) :
    HasDerivAt (fun r => cosC n (G1 φ a r)) (cosC n (G11 φ a r)) r := by
  obtain ⟨C, hC⟩ := bound_G11 a hφ hc
  exact hasDerivAt_wcoeff (hasDerivAt_G1_r a hφ) (cont_G1 a hφ) (cont_G11 a hφ) hC
    (continuous_cos_n n) (abs_cos_le n) r

lemma hasDerivAt_bC1 (n : ℤ) (r : ℝ) :
    HasDerivAt (fun r => sinC n (G1 φ a r)) (sinC n (G11 φ a r)) r := by
  obtain ⟨C, hC⟩ := bound_G11 a hφ hc
  exact hasDerivAt_wcoeff (hasDerivAt_G1_r a hφ) (cont_G1 a hφ) (cont_G11 a hφ) hC
    (continuous_sin_n n) (abs_sin_le n) r

lemma deriv_aC (n : ℤ) : deriv (aC φ a n) = fun r => cosC n (G1 φ a r) :=
  funext fun r => (hasDerivAt_aC a hφ hc n r).deriv

lemma deriv_bC (n : ℤ) : deriv (bC φ a n) = fun r => sinC n (G1 φ a r) :=
  funext fun r => (hasDerivAt_bC a hφ hc n r).deriv

lemma deriv2_aC (n : ℤ) : deriv (deriv (aC φ a n)) = fun r => cosC n (G11 φ a r) := by
  rw [deriv_aC a hφ hc]; exact funext fun r => (hasDerivAt_aC1 a hφ hc n r).deriv

lemma deriv2_bC (n : ℤ) : deriv (deriv (bC φ a n)) = fun r => sinC n (G11 φ a r) := by
  rw [deriv_bC a hφ hc]; exact funext fun r => (hasDerivAt_bC1 a hφ hc n r).deriv

lemma contDiff_aC (n : ℤ) : ContDiff ℝ 2 (aC φ a n) :=
  contDiff_two_of (hasDerivAt_aC a hφ hc n) (hasDerivAt_aC1 a hφ hc n)
    (continuous_wcoeff (cont_G11 a hφ) (continuous_cos_n n))

lemma contDiff_bC (n : ℤ) : ContDiff ℝ 2 (bC φ a n) :=
  contDiff_two_of (hasDerivAt_bC a hφ hc n) (hasDerivAt_bC1 a hφ hc n)
    (continuous_wcoeff (cont_G11 a hφ) (continuous_sin_n n))

end Smooth

end DiskCoeff

end Buckling
end
end ChunkedSource022
/- END SOURCE 022 -/

/- BEGIN SOURCE 023: RequestProject/External.lean -/
section ChunkedSource023

/-!
# External theorems (Section 1 of the paper) — explicit, auditable hypotheses

The paper declares a fixed list of external results, labelled `E1`–`E12`, which it
quotes from the literature and does not prove.  The formalization is **conditional**:
those external results that are actually used and are neither in Mathlib nor proved in
this project are recorded below as Lean propositions and bundled in the structure
`PaperExternals`, which the main theorems take as an explicit hypothesis.  No axioms are
introduced.

Status of the twelve external results:

* `E1` zeros/interlacing (DLMF §10.21(i), Eq. 10.21.2), in the form used (orders `0` and
  `1`): **proved** in `RequestProject/Bessel/ZerosE1.lean` (`extZeros_holds`); the
  proposition `ExtZeros` is kept only as the statement being proved.
* `E2` canonical product for `J₁` (DLMF Eq. 10.21.15): **proved** in
  `RequestProject/Bessel/Product/Main.lean` (`extProduct_holds`); the proposition
  `ExtProduct` is kept only as the statement being proved.
* `E3` integral representation (DLMF Eq. 10.9.2): **proved** in
  `RequestProject/Bessel/IntegralRep.lean` (`besselJ_integral_rep`, `extIntegral_holds`);
  the proposition `ExtIntegral` is kept only as the statement being proved.
* `E4` uniform large-argument estimate (DLMF Eq. 10.17.3, §10.17(iv)): **proved** in
  `RequestProject/Bessel/Asymptotic/Main.lean` (`extAsymptotic_holds`); the proposition
  `ExtAsymptotic` is kept only as the statement being proved.
* `E5` large zeros of `J₁` (DLMF Eq. 10.21.19): **not used** by the formal proof; removed.
* `E6` Taylor series and residues (Rudin RCA Thms 10.6, 10.16, 10.42): **proved** in
  `RequestProject/Concavity/Removable.lean` (`circleIntegral_eq_explicit_residues`) from
  Mathlib's Cauchy integral theorem; only the residue part was used.  (An earlier
  hypothesis-form of E6 omitted the necessary condition `N ≥ 1` and was therefore false;
  it has been removed.)
* `E7` Rademacher / Lipschitz weak derivatives (Evans–Gariepy §3.1.2 Thm 3.2, §4.2.3):
  in Mathlib (`LipschitzWith.ae_differentiableAt`, `LipschitzWith.integral_lineDeriv_mul_eq`).
* `E8` mollification in `H¹(ℝ²)` and `H²(ℝ²)` (Evans–Gariepy §4.2.1), in the forms used:
  **proved** in `RequestProject/Sobolev/Mollification.lean` (`extMollification_holds`,
  `extMollification2_holds`); the propositions `ExtMollification`, `ExtMollification2` are
  kept only as the statements being proved.
* `E9` planar Sobolev embedding `H²(ℝ²) ⊆ L^∞` (Adams–Fournier Thm 4.12), in the form
  used (on `C_c^∞(ℝ²)`): **proved** in `RequestProject/Sobolev/Embedding.lean`
  (`extEmbedding_holds`, with constant `1`).
* `E10` Rellich compactness (Evans PDE §5.7 Thm 1): **not used**; removed.
* `E11` Fourier completeness and Parseval (Rudin RCA §4.26, Thm 4.18): in Mathlib
  (`tsum_sq_fourierCoeff`).
* `E12` Faber–Krahn inequality with equality case (Brasco–De Philippis–Velichkov, Duke
  Math. J. 164 (2015), §1.1, Eq. (1.1)): hypothesis `ExtFaberKrahn`.

-/

@[expose] public section

open MeasureTheory Real Filter Topology

namespace Buckling

/-- **E1** (positive zeros and interlacing, DLMF §10.21(i)), in the form used: for
`n ∈ {0, 1}` the positive zeros of `J_n` form an unbounded strictly increasing sequence
`j_{n,1} < j_{n,2} < ⋯` of simple zeros, enumerated by `besselZero n`, and
`j_{0,k} < j_{1,k} < j_{0,k+1}`.  (The paper states E1 for every order `n`; only the orders
`0` and `1` are used.) -/
def ExtZeros : Prop :=
  ∀ n : ℕ, n ≤ 1 →
    StrictMono (besselZero n) ∧
    Tendsto (besselZero n) atTop atTop ∧
    (∀ k, 1 ≤ k → besselJ n (besselZero n k) = 0 ∧ deriv (besselJ n) (besselZero n k) ≠ 0) ∧
    (∀ x, 0 < x → besselJ n x = 0 → ∃ k, 1 ≤ k ∧ besselZero n k = x) ∧
    (∀ k, 1 ≤ k → besselZero 0 k < besselZero 1 k ∧ besselZero 1 k < besselZero 0 (k + 1))

/-- **E2** (canonical product for `J₁`, DLMF 10.21.15):
`J₁(ζ) = (ζ/2) ∏_{n ≥ 1} (1 - ζ²/κ_n²)`, locally uniformly on `ℂ`. -/
def ExtProduct : Prop :=
  TendstoLocallyUniformly
    (fun (N : ℕ) (ζ : ℂ) =>
      ζ / 2 * ∏ n ∈ Finset.range N, (1 - ζ ^ 2 / ((besselZero 1 (n + 1) : ℝ) : ℂ) ^ 2))
    (besselJC 1) atTop

/-- **E3** (integral representation, DLMF 10.9.2):
`J_n(x) = π⁻¹ ∫₀^π cos(x sin θ - n θ) dθ`. -/
def ExtIntegral : Prop :=
  ∀ (n : ℕ) (x : ℝ),
    besselJ n x = 1 / π * ∫ θ in (0 : ℝ)..π, Real.cos (x * Real.sin θ - n * θ)

/-- **E4** (uniform large-argument estimate, DLMF 10.17): for `ν ∈ {0,1}` there are
`C, R > 0` such that for `|ζ| ≥ R`, `|arg ζ| ≤ π/2`,
`|(πζ/2)^{1/2} J_ν(ζ) - cos(ζ - νπ/2 - π/4)| ≤ C e^{|Im ζ|}/|ζ|`. -/
def ExtAsymptotic : Prop :=
  ∀ ν : ℕ, ν ≤ 1 → ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ ζ : ℂ, R ≤ ‖ζ‖ → |Complex.arg ζ| ≤ π / 2 →
    ‖((π : ℂ) * ζ / 2) ^ (1 / 2 : ℂ) * besselJC ν ζ
        - Complex.cos (ζ - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4)‖
      ≤ C * Real.exp |ζ.im| / ‖ζ‖

/-- The weak gradient relation `∫ v ∂ᵢψ = -∫ wᵢ ψ` for all test functions `ψ`. -/
def HasWeakGradient (v : Plane → ℝ) (w : Fin 2 → Plane → ℝ) : Prop :=
  ∀ ψ : Plane → ℝ, IsTestFn Set.univ ψ → ∀ i : Fin 2,
    ∫ x, v x * pderiv i ψ x = -∫ x, w i x * ψ x

/-- **E8** (mollification, Evans–Gariepy §4.2.1), in the `H¹(ℝ²)` form used in the
paper.  If `v ∈ L²(ℝ²)` has weak gradient `w ∈ L²`, and `v` vanishes a.e. outside
the closed set `K`, then for every `ε > 0` the mollification `ηε * v` is a smooth
function, supported in the closed `ε`-neighbourhood of `K`, whose gradient is
`ηε * w`, and which approximates `v` in `H¹` as `ε → 0`.  We record the
consequences used: smooth approximants supported in `K + B̄_ε` converging in `H¹`,
whose gradients vanish identically when `w = 0`. -/
def ExtMollification : Prop :=
  ∀ (v : Plane → ℝ) (w : Fin 2 → Plane → ℝ) (K : Set Plane),
    MemLp v 2 volume → (∀ i, MemLp (w i) 2 volume) → HasWeakGradient v w → IsClosed K →
    (∀ᵐ x, x ∉ K → v x = 0) →
    ∀ ε > 0, ∃ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ tsupport ψ ⊆ Metric.cthickening ε K ∧
      eLpNorm (fun x => ψ x - v x) 2 volume < ENNReal.ofReal ε ∧
      (∀ i, eLpNorm (fun x => pderiv i ψ x - w i x) 2 volume < ENNReal.ofReal ε) ∧
      ((∀ i, ∀ᵐ x, w i x = 0) → ∀ i x, pderiv i ψ x = 0)

/-- **E8, second-order case** (mollification in `H²(ℝ²)`, Evans–Gariepy §4.2.1, the case
`m = 2` of the paper's External theorem on mollification).  If `v ∈ L²(ℝ²)` has weak
gradient `w ∈ L²` and each `w j` has weak gradient `(h i j)ᵢ ∈ L²`, and `v` vanishes a.e.
outside the closed set `K`, then there are smooth functions supported in `K + B̄_ε`
approximating `v` in `H²` (values, first and second derivatives) to within `ε`. -/
def ExtMollification2 : Prop :=
  ∀ (v : Plane → ℝ) (w : Fin 2 → Plane → ℝ) (h : Fin 2 → Fin 2 → Plane → ℝ) (K : Set Plane),
    MemLp v 2 volume → (∀ i, MemLp (w i) 2 volume) → (∀ i j, MemLp (h i j) 2 volume) →
    HasWeakGradient v w → (∀ j, HasWeakGradient (w j) (fun i => h i j)) → IsClosed K →
    (∀ᵐ x, x ∉ K → v x = 0) →
    ∀ ε > 0, ∃ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ tsupport ψ ⊆ Metric.cthickening ε K ∧
      eLpNorm (fun x => ψ x - v x) 2 volume < ENNReal.ofReal ε ∧
      (∀ i, eLpNorm (fun x => pderiv i ψ x - w i x) 2 volume < ENNReal.ofReal ε) ∧
      (∀ i j, eLpNorm (fun x => pderiv i (pderiv j ψ) x - h i j x) 2 volume < ENNReal.ofReal ε)

/-- **E9** (planar Sobolev embedding `H²(ℝ²) ⊆ L^∞`, Adams–Fournier Thm 4.12), stated
on the dense class `C_c^∞(ℝ²)`: `sup |v| ≤ C ‖v‖_{H²}`. -/
def ExtEmbedding : Prop :=
  ∃ C : ℝ, ∀ (φ : Plane → ℝ) (hφ : IsTestFn Set.univ φ) (x : Plane),
    |φ x| ≤ C * Real.sqrt (‖hφ.toL2‖ ^ 2 + ∑ i, ‖(hφ.pderiv i).toL2‖ ^ 2
      + ∑ i, ∑ j, ‖((hφ.pderiv j).pderiv i).toL2‖ ^ 2)

/-- **E12** (Faber–Krahn inequality and its equality case, Brasco–De Philippis–
Velichkov §1.1): if `Ω` is open with `0 < |Ω| < ∞` and `B` is a disk with
`|B| = |Ω|`, then `λ₁ᴰ(Ω) ≥ λ₁ᴰ(B)`, and in case of equality `Ω` coincides with a
disk of the same area up to a null set. -/
def ExtFaberKrahn : Prop :=
  ∀ Ω : Set Plane, IsOpen Ω → 0 < volume Ω → volume Ω < ⊤ →
    ∀ R : ℝ, 0 < R → volume (Metric.ball (0 : Plane) R) = volume Ω →
      dirichletEig (Metric.ball (0 : Plane) R) ≤ dirichletEig Ω ∧
      (dirichletEig Ω = dirichletEig (Metric.ball (0 : Plane) R) →
        ∃ a : Plane, volume (symmDiff Ω (Metric.ball a R)) = 0)

/-- The external theorems of the paper which are neither available in Mathlib nor proved in
this project: only E12 (Faber–Krahn with equality case). -/
structure PaperExternals : Prop where
  faberKrahn : ExtFaberKrahn

end Buckling
end
end ChunkedSource023
/- END SOURCE 023 -/

/- BEGIN SOURCE 024: RequestProject/Bessel/IntegralRep.lean -/
section ChunkedSource024

/-!
# Bessel's integral representation (External theorem E3, proved)

We prove DLMF Eq. 10.9.2,
`J_n(x) = π⁻¹ ∫₀^π cos(x sin θ - n θ) dθ`, for every integer `n ≥ 0` and real `x`,
directly from the power-series definition of `J_n`.  Hence the hypothesis `ExtIntegral`
of the earlier formalization is a theorem (`extIntegral_holds`) and is no longer assumed.

Proof: expand `exp(i x sin θ) = ∑_k (i x sin θ)^k / k!`, integrate term by term against
`e^{-i n θ}` over `[0, 2π]` (dominated convergence), evaluate
`∫₀^{2π} sin^k θ e^{-inθ} dθ` with the binomial theorem and the orthogonality of the
exponentials, identify the resulting series with the Bessel series, take real parts, and
fold `[0, 2π]` onto `[0, π]` using `θ ↦ 2π - θ`.
-/

@[expose] public section

open Complex Real
open scoped Nat

namespace Buckling

/-- `∫₀^{2π} e^{i p θ} dθ = 2π [p = 0]` for an integer `p`. -/
lemma integral_exp_int_mul_I (p : ℤ) :
    ∫ θ in (0:ℝ)..2*π, Complex.exp ((p:ℂ) * I * θ) = if p = 0 then (2*π : ℂ) else 0 := by
  split_ifs with hp
  · subst hp; simp
  · have hc : (p:ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hp) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have : Complex.exp ((p:ℂ) * I * (2 * (π : ℂ))) = 1 := by
      rw [show (p:ℂ) * I * (2 * (π:ℂ)) = p * (2 * π * I) by ring]
      exact Complex.exp_int_mul_two_pi_mul_I p
    push_cast
    simp [this]

/-- Binomial expansion of `sin^k θ · e^{-inθ}` into exponentials. -/
lemma sin_pow_mul_exp_expand (k n : ℕ) (θ : ℝ) :
    ((Real.sin θ : ℝ) : ℂ) ^ k * Complex.exp (-(n:ℂ) * I * θ) =
      ((2 * I)⁻¹) ^ k * ∑ j ∈ Finset.range (k + 1),
        ((k.choose j : ℂ) * (-1) ^ (k - j)) * Complex.exp (((2 * j - k - n : ℤ) : ℂ) * I * θ) := by
  have hs : ((Real.sin θ : ℝ) : ℂ) =
      (2 * I)⁻¹ * (Complex.exp (I * θ) + (-Complex.exp (-(I * θ)))) := by
    rw [Complex.ofReal_sin, Complex.sin]; field_simp; simp [I_sq]; ring
  rw [hs, mul_pow, add_pow, mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [neg_pow, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  have e : Complex.exp (j * (I * θ)) * Complex.exp ((k - j : ℕ) * -(I * θ)) *
      Complex.exp (-(n:ℂ) * I * θ) = Complex.exp (((2 * j - k - n : ℤ) : ℂ) * I * θ) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast [Nat.cast_sub hj]; ring
  rw [← e]; ring

/-- `∫₀^{2π} sin^k θ e^{-inθ} dθ`. -/
lemma integral_sin_pow_mul_exp (k n : ℕ) :
    ∫ θ in (0:ℝ)..2*π, ((Real.sin θ : ℝ) : ℂ) ^ k * Complex.exp (-(n:ℂ) * I * θ) =
      2 * π * ((2 * I)⁻¹) ^ k * ∑ j ∈ Finset.range (k + 1),
        if (2 * j : ℤ) = k + n then (k.choose j : ℂ) * (-1) ^ (k - j) else 0 := by
  simp_rw [sin_pow_mul_exp_expand]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum]
  · have : ∀ j ∈ Finset.range (k+1), (∫ θ in (0:ℝ)..2*π, ((k.choose j : ℂ) * (-1) ^ (k - j)) *
        Complex.exp (((2 * j - k - n : ℤ) : ℂ) * I * θ)) =
        2 * π * (if (2 * j : ℤ) = k + n then (k.choose j : ℂ) * (-1) ^ (k - j) else 0) := by
      intro j _
      rw [intervalIntegral.integral_const_mul, integral_exp_int_mul_I]
      by_cases h : (2 * j : ℤ) = k + n
      · rw [if_pos (by omega), if_pos h]; ring
      · rw [if_neg (by omega), if_neg h]; ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum]; ring
  · intro j _
    exact (Continuous.intervalIntegrable (by fun_prop) _ _)

/-- The coefficient of the `k`-th term after integrating the exponential series. -/
noncomputable def besselIntCoef (n : ℕ) (x : ℝ) (k : ℕ) : ℝ :=
  (x / 2) ^ k / (k ! : ℝ) * ∑ j ∈ Finset.range (k + 1),
    if (2 * j : ℤ) = k + n then (k.choose j : ℝ) * (-1) ^ (k - j) else 0

lemma besselIntCoef_comp (n : ℕ) (x : ℝ) (m : ℕ) :
    besselIntCoef n x (n + 2 * m) = bterm n m x := by
  unfold besselIntCoef bterm
  rw [Finset.sum_eq_single (n + m)]
  · rw [if_pos (by push_cast; ring), show n + 2 * m - (n + m) = m by omega]
    have hc := Nat.choose_mul_factorial_mul_factorial (show n + m ≤ n + 2 * m by omega)
    rw [show n + 2 * m - (n + m) = m by omega] at hc
    have hc' : ((n + 2 * m).choose (n + m) : ℝ) * (n + m)! * m ! = (n + 2 * m)! := by
      exact_mod_cast hc
    have h0 : ((n + 2 * m).choose (n + m) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    rw [show 2 * m + n = n + 2 * m by ring, show m + n = n + m by ring, ← hc']
    field_simp
  · intro j _ hj
    rw [if_neg]; push_cast; omega
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

lemma besselIntCoef_eq_zero (n : ℕ) (x : ℝ) (k : ℕ)
    (hk : k ∉ Set.range (fun m => n + 2 * m)) : besselIntCoef n x k = 0 := by
  unfold besselIntCoef
  rw [Finset.sum_eq_zero, mul_zero]
  intro j hj
  rw [if_neg]
  intro h
  apply hk
  have hj := Finset.mem_range.mp hj
  exact ⟨j - n, by simp only; omega⟩

lemma hasSum_besselIntCoef (n : ℕ) (x : ℝ) : HasSum (besselIntCoef n x) (besselJ n x) := by
  have hinj : Function.Injective (fun m : ℕ => n + 2 * m) := fun a b h => by simp at h; omega
  rw [← hinj.hasSum_iff (besselIntCoef_eq_zero n x)]
  have : (besselIntCoef n x ∘ fun m => n + 2 * m) = fun m => bterm n m x :=
    funext (besselIntCoef_comp n x)
  rw [this, besselJ_eq_tsum]; exact (summable_bterm n x).hasSum

lemma hasSum_integral_exp_sin (n : ℕ) (x : ℝ) :
    HasSum (fun k => 2 * (π : ℂ) * (besselIntCoef n x k : ℂ))
      (∫ θ in (0:ℝ)..2*π, Complex.exp (I * x * Real.sin θ) * Complex.exp (-(n:ℂ) * I * θ)) := by
  set F : ℕ → ℝ → ℂ := fun k θ =>
    (I * x) ^ k / (k ! : ℂ) * (((Real.sin θ : ℝ) : ℂ) ^ k * Complex.exp (-(n:ℂ) * I * θ))
  have hF : ∀ k, ∫ θ in (0:ℝ)..2*π, F k θ = 2 * (π : ℂ) * (besselIntCoef n x k : ℂ) := by
    intro k
    simp only [F]
    rw [intervalIntegral.integral_const_mul, integral_sin_pow_mul_exp, besselIntCoef]
    simp only [Complex.ofReal_mul, Complex.ofReal_sum, apply_ite ((↑) : ℝ → ℂ),
      Complex.ofReal_zero]
    push_cast
    have hI : (I * x) ^ k * ((2 * I)⁻¹) ^ k = ((x:ℂ) / 2) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (2 * π * ∑ j ∈ Finset.range (k + 1),
        if (2 * j : ℤ) = k + n then (k.choose j : ℂ) * (-1) ^ (k - j) else 0) / (k ! : ℂ) * hI
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => |x| ^ k / (k ! : ℝ)) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, one_mul]
    rw [Complex.norm_exp]
    have h1 : (-(n:ℂ) * I * θ).re = 0 := by simp
    rw [h1, Real.exp_zero, mul_one]
    have h2 : |Real.sin θ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)
    have h3 : 0 ≤ |x| ^ k / (k ! : ℝ) := by positivity
    calc |x| ^ k / (k ! : ℝ) * |Real.sin θ| ^ k ≤ |x| ^ k / (k ! : ℝ) * 1 := by gcongr
      _ = _ := mul_one _
  · exact Filter.Eventually.of_forall fun θ _ => Real.summable_pow_div_factorial |x|
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have := NormedSpace.expSeries_div_hasSum_exp (I * x * Real.sin θ)
    rw [← Complex.exp_eq_exp_ℂ] at this
    convert this.mul_right (Complex.exp (-(n:ℂ) * I * θ)) using 1
    ext k; simp only [F]; rw [mul_pow (I * x)]; ring

/-- The complex form: `∫₀^{2π} e^{i x sin θ} e^{-inθ} dθ = 2π J_n(x)`. -/
lemma integral_exp_sin_eq (n : ℕ) (x : ℝ) :
    ∫ θ in (0:ℝ)..2*π, Complex.exp (I * x * Real.sin θ) * Complex.exp (-(n:ℂ) * I * θ) =
      2 * (π : ℂ) * (besselJ n x : ℂ) := by
  have h1 := hasSum_integral_exp_sin n x
  have h2 : HasSum (fun k => 2 * (π : ℂ) * (besselIntCoef n x k : ℂ))
      (2 * (π : ℂ) * (besselJ n x : ℂ)) :=
    (Complex.hasSum_ofReal.mpr (hasSum_besselIntCoef n x)).mul_left _
  exact h1.unique h2

lemma cos_two_pi_sub_sym (n : ℕ) (x θ : ℝ) :
    Real.cos (x * Real.sin (2 * π - θ) - n * (2 * π - θ)) = Real.cos (x * Real.sin θ - n * θ) := by
  rw [Real.sin_two_pi_sub, show x * -Real.sin θ - n * (2 * π - θ) =
      -(x * Real.sin θ - n * θ) - (n : ℕ) * (2 * π) by ring,
    Real.cos_sub_nat_mul_two_pi, Real.cos_neg]

lemma integral_cos_two_pi_eq (n : ℕ) (x : ℝ) :
    ∫ θ in (0:ℝ)..2*π, Real.cos (x * Real.sin θ - n * θ) =
      2 * ∫ θ in (0:ℝ)..π, Real.cos (x * Real.sin θ - n * θ) := by
  have hc : ∀ a b : ℝ, IntervalIntegrable (fun θ => Real.cos (x * Real.sin θ - n * θ))
      MeasureTheory.volume a b :=
    fun a b => (Continuous.intervalIntegrable (by fun_prop) _ _)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc 0 π) (hc π (2*π))]
  have : ∫ θ in π..2*π, Real.cos (x * Real.sin θ - n * θ) =
      ∫ θ in (0:ℝ)..π, Real.cos (x * Real.sin θ - n * θ) := by
    calc ∫ θ in π..2*π, Real.cos (x * Real.sin θ - n * θ)
        = ∫ θ in (0:ℝ)..π, Real.cos (x * Real.sin (2 * π - θ) - n * (2 * π - θ)) := by
          rw [intervalIntegral.integral_comp_sub_left
            (fun θ => Real.cos (x * Real.sin θ - n * θ))]
          norm_num [two_mul]
      _ = _ := by simp only [cos_two_pi_sub_sym]
  rw [this]; ring

lemma re_exp_sin_mul_exp (n : ℕ) (x θ : ℝ) :
    (Complex.exp (I * x * Real.sin θ) * Complex.exp (-(n:ℂ) * I * θ)).re =
      Real.cos (x * Real.sin θ - n * θ) := by
  rw [← Complex.exp_add, show I * x * Real.sin θ + -(n:ℂ) * I * θ =
      ((x * Real.sin θ - n * θ : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_ofReal_mul_I_re]

/-- **External theorem E3 (DLMF Eq. 10.9.2), proved.**
`J_n(x) = π⁻¹ ∫₀^π cos(x sin θ - n θ) dθ` for every `n : ℕ` and `x : ℝ`. -/
theorem besselJ_integral_rep (n : ℕ) (x : ℝ) :
    besselJ n x = 1 / π * ∫ θ in (0 : ℝ)..π, Real.cos (x * Real.sin θ - n * θ) := by
  have h := congrArg Complex.re (integral_exp_sin_eq n x)
  have hre := Complex.reCLM.intervalIntegral_comp_comm
    (μ := MeasureTheory.volume) (a := 0) (b := 2 * π)
    (f := fun θ : ℝ => Complex.exp (I * x * Real.sin θ) * Complex.exp (-(n:ℂ) * I * θ))
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  simp only [Complex.reCLM_apply, re_exp_sin_mul_exp] at hre
  rw [← hre] at h
  rw [integral_cos_two_pi_eq] at h
  have h' : (2 * (π : ℂ) * (besselJ n x : ℂ)).re = 2 * π * besselJ n x := by
    rw [show (2 * (π : ℂ) * (besselJ n x : ℂ)) = ((2 * π * besselJ n x : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [h'] at h
  field_simp
  linarith

/-- The hypothesis form `ExtIntegral` holds. -/
theorem extIntegral_holds : ExtIntegral := besselJ_integral_rep

end Buckling
end
end ChunkedSource024
/- END SOURCE 024 -/

/- BEGIN SOURCE 025: RequestProject/Bessel/IntegralRepC.lean -/
section ChunkedSource025

/-!
# Bessel's integral representation for a complex argument

`2π J_n(z) = ∫₀^{2π} e^{i z sin θ} e^{-inθ} dθ` for every complex `z`, and the consequences
`J₀(z) = (2/π) ∫₀^{π/2} cos(z cos t) dt`, `J₁(z) = (2/π) ∫₀^{π/2} sin(z cos t) cos t dt`.
-/

@[expose] public section

open Complex Real
open scoped Nat

namespace Buckling

/-- The coefficient of the `k`-th term after integrating the exponential series (complex
argument). -/
noncomputable def besselIntCoefC (n : ℕ) (z : ℂ) (k : ℕ) : ℂ :=
  (z / 2) ^ k / (k ! : ℂ) * ∑ j ∈ Finset.range (k + 1),
    if (2 * j : ℤ) = k + n then (k.choose j : ℂ) * (-1) ^ (k - j) else 0

lemma besselIntCoefC_comp (n : ℕ) (z : ℂ) (m : ℕ) :
    besselIntCoefC n z (n + 2 * m) = cterm n m z := by
  unfold besselIntCoefC cterm
  rw [Finset.sum_eq_single (n + m)]
  · rw [if_pos (by push_cast; ring), show n + 2 * m - (n + m) = m by omega]
    have hc := Nat.choose_mul_factorial_mul_factorial (show n + m ≤ n + 2 * m by omega)
    rw [show n + 2 * m - (n + m) = m by omega] at hc
    have hc' : ((n + 2 * m).choose (n + m) : ℂ) * (n + m)! * m ! = (n + 2 * m)! := by
      exact_mod_cast hc
    have h0 : ((n + 2 * m).choose (n + m) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega)).ne'
    have h1 : ((n + m)! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have h2 : (m ! : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [show 2 * m + n = n + 2 * m by ring, show m + n = n + m by ring, ← hc']
    field_simp
  · intro j _ hj
    rw [if_neg]; push_cast; omega
  · intro h; exfalso; exact h (Finset.mem_range.mpr (by omega))

lemma besselIntCoefC_eq_zero (n : ℕ) (z : ℂ) (k : ℕ)
    (hk : k ∉ Set.range (fun m => n + 2 * m)) : besselIntCoefC n z k = 0 := by
  unfold besselIntCoefC
  rw [Finset.sum_eq_zero, mul_zero]
  intro j hj
  rw [if_neg]
  intro h
  apply hk
  have hj := Finset.mem_range.mp hj
  exact ⟨j - n, by simp only; omega⟩

lemma hasSum_besselIntCoefC (n : ℕ) (z : ℂ) : HasSum (besselIntCoefC n z) (besselJC n z) := by
  have hinj : Function.Injective (fun m : ℕ => n + 2 * m) := fun a b h => by simp at h; omega
  rw [← hinj.hasSum_iff (besselIntCoefC_eq_zero n z)]
  have : (besselIntCoefC n z ∘ fun m => n + 2 * m) = fun m => cterm n m z :=
    funext (besselIntCoefC_comp n z)
  rw [this, besselJC_eq_tsum]; exact (summable_cterm n z).hasSum

lemma hasSum_integral_exp_sinC (n : ℕ) (z : ℂ) :
    HasSum (fun k => 2 * (π : ℂ) * besselIntCoefC n z k)
      (∫ θ in (0:ℝ)..2*π, Complex.exp (I * z * Real.sin θ) * Complex.exp (-(n:ℂ) * I * θ)) := by
  set F : ℕ → ℝ → ℂ := fun k θ =>
    (I * z) ^ k / (k ! : ℂ) * (((Real.sin θ : ℝ) : ℂ) ^ k * Complex.exp (-(n:ℂ) * I * θ))
  have hF : ∀ k, ∫ θ in (0:ℝ)..2*π, F k θ = 2 * (π : ℂ) * besselIntCoefC n z k := by
    intro k
    simp only [F]
    rw [intervalIntegral.integral_const_mul, integral_sin_pow_mul_exp, besselIntCoefC]
    have hI : (I * z) ^ k * ((2 * I)⁻¹) ^ k = (z / 2) ^ k := by
      rw [← mul_pow]; congr 1; field_simp
    linear_combination (2 * π * ∑ j ∈ Finset.range (k + 1),
        if (2 * j : ℤ) = k + n then (k.choose j : ℂ) * (-1) ^ (k - j) else 0) / (k ! : ℂ) * hI
  simp_rw [← hF]
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun k _ => ‖z‖ ^ k / (k ! : ℝ)) (fun k => ?_) (fun k => ?_) ?_ ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_I, one_mul]
    rw [Complex.norm_exp]
    have h1 : (-(n:ℂ) * I * θ).re = 0 := by simp
    rw [h1, Real.exp_zero, mul_one]
    have h2 : |Real.sin θ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one θ)
    have h3 : 0 ≤ ‖z‖ ^ k / (k ! : ℝ) := by positivity
    calc ‖z‖ ^ k / (k ! : ℝ) * |Real.sin θ| ^ k ≤ ‖z‖ ^ k / (k ! : ℝ) * 1 := by gcongr
      _ = _ := mul_one _
  · exact Filter.Eventually.of_forall fun θ _ => Real.summable_pow_div_factorial ‖z‖
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall fun θ _ => ?_
    have := NormedSpace.expSeries_div_hasSum_exp (I * z * Real.sin θ)
    rw [← Complex.exp_eq_exp_ℂ] at this
    convert this.mul_right (Complex.exp (-(n:ℂ) * I * θ)) using 1
    ext k; simp only [F]; rw [mul_pow (I * z)]; ring

/-- **Bessel's integral, complex argument**:
`∫₀^{2π} e^{i z sin θ} e^{-inθ} dθ = 2π J_n(z)`. -/
theorem integral_exp_sin_eqC (n : ℕ) (z : ℂ) :
    ∫ θ in (0:ℝ)..2*π, Complex.exp (I * z * Real.sin θ) * Complex.exp (-(n:ℂ) * I * θ) =
      2 * (π : ℂ) * besselJC n z :=
  (hasSum_integral_exp_sinC n z).unique ((hasSum_besselIntCoefC n z).mul_left _)

end Buckling

namespace Buckling

/-- Folding `[0, 2π]` onto `[0, π/2]`. -/
lemma integral_fold_quarter (f : ℝ → ℂ) (hf : Continuous f) :
    ∫ θ in (0:ℝ)..2*π, f θ = ∫ t in (0:ℝ)..π/2,
      (f (π/2 - t) + f (π/2 + t) + f (3*π/2 - t) + f (3*π/2 + t)) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b :=
    fun a b => hf.intervalIntegrable a b
  have hc : ∀ g : ℝ → ℂ, Continuous g → ∀ a b : ℝ,
      IntervalIntegrable g MeasureTheory.volume a b := fun g hg a b => hg.intervalIntegrable a b
  rw [intervalIntegral.integral_add (hc _ (by fun_prop) _ _) (hc _ (by fun_prop) _ _),
    intervalIntegral.integral_add (hc _ (by fun_prop) _ _) (hc _ (by fun_prop) _ _),
    intervalIntegral.integral_add (hc _ (by fun_prop) _ _) (hc _ (by fun_prop) _ _)]
  rw [intervalIntegral.integral_comp_sub_left (fun x => f x),
    intervalIntegral.integral_comp_add_left (fun x => f x),
    intervalIntegral.integral_comp_sub_left (fun x => f x),
    intervalIntegral.integral_comp_add_left (fun x => f x)]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 (π/2)) (hi (π/2) (2*π)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (π/2) π) (hi π (2*π)),
    ← intervalIntegral.integral_add_adjacent_intervals (hi π (3*π/2)) (hi (3*π/2) (2*π))]
  ring_nf

/-- `J₀(z) = (2/π) ∫₀^{π/2} cos(z cos t) dt` for complex `z`. -/
theorem besselJC_zero_integral (z : ℂ) :
    besselJC 0 z = 2 / π * ∫ t in (0:ℝ)..π/2, Complex.cos (z * Real.cos t) := by
  have h := integral_exp_sin_eqC 0 z
  rw [integral_fold_quarter _ (by fun_prop)] at h
  have hpt : ∀ t : ℝ,
      (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((0:ℕ):ℂ) * I * θ))
          (π/2 - t) +
        (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((0:ℕ):ℂ) * I * θ))
          (π/2 + t) +
        (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((0:ℕ):ℂ) * I * θ))
          (3*π/2 - t) +
        (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((0:ℕ):ℂ) * I * θ))
          (3*π/2 + t) = 4 * Complex.cos (z * Real.cos t) := by
    intro t
    simp only [Nat.cast_zero, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    have s1 : Real.sin (π/2 - t) = Real.cos t := Real.sin_pi_div_two_sub t
    have s2 : Real.sin (π/2 + t) = Real.cos t := by rw [Real.sin_add]; simp
    have s3 : Real.sin (3*π/2 - t) = -Real.cos t := by
      rw [show 3*π/2 - t = (π/2 - t) + π by ring, Real.sin_add_pi, s1]
    have s4 : Real.sin (3*π/2 + t) = -Real.cos t := by
      rw [show 3*π/2 + t = (π/2 + t) + π by ring, Real.sin_add_pi, s2]
    rw [s1, s2, s3, s4, Complex.cos]
    push_cast
    ring_nf
  simp_rw [hpt] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show besselJC _ z = (2 * (π : ℂ) * besselJC _ z) / (2 * π) by field_simp, ← h]
  ring

/-- `J₁(z) = (2/π) ∫₀^{π/2} sin(z cos t) cos t dt` for complex `z`. -/
theorem besselJC_one_integral (z : ℂ) :
    besselJC 1 z = 2 / π * ∫ t in (0:ℝ)..π/2, Complex.sin (z * Real.cos t) * Real.cos t := by
  have h := integral_exp_sin_eqC 1 z
  rw [integral_fold_quarter _ (by fun_prop)] at h
  have hpt : ∀ t : ℝ,
      (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((1:ℕ):ℂ) * I * θ))
          (π/2 - t) +
        (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((1:ℕ):ℂ) * I * θ))
          (π/2 + t) +
        (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((1:ℕ):ℂ) * I * θ))
          (3*π/2 - t) +
        (fun θ : ℝ => Complex.exp (I * z * Real.sin θ) * Complex.exp (-((1:ℕ):ℂ) * I * θ))
          (3*π/2 + t) = 4 * (Complex.sin (z * Real.cos t) * Real.cos t) := by
    intro t
    have s1 : Real.sin (π/2 - t) = Real.cos t := Real.sin_pi_div_two_sub t
    have s2 : Real.sin (π/2 + t) = Real.cos t := by rw [Real.sin_add]; simp
    have s3 : Real.sin (3*π/2 - t) = -Real.cos t := by
      rw [show 3*π/2 - t = (π/2 - t) + π by ring, Real.sin_add_pi, s1]
    have s4 : Real.sin (3*π/2 + t) = -Real.cos t := by
      rw [show 3*π/2 + t = (π/2 + t) + π by ring, Real.sin_add_pi, s2]
    simp only [s1, s2, s3, s4]
    have hA : Complex.exp (-(π/2 : ℂ) * I) = -I := by
      rw [show -(π/2 : ℂ) * I = ((-(π/2) : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_two, Real.sin_pi_div_two]
      simp
    have hB : Complex.exp (-(π : ℂ) * I) = -1 := by
      rw [show -(π : ℂ) * I = ((-π : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
      rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
        Real.cos_pi, Real.sin_pi]
      simp
    have e1 : Complex.exp (-((1:ℕ):ℂ) * I * ((π/2 - t : ℝ) : ℂ)) = -I * Complex.exp (I * t) := by
      rw [show -((1:ℕ):ℂ) * I * ((π/2 - t : ℝ) : ℂ) = I * t + (-(π/2 : ℂ) * I) by push_cast; ring,
        Complex.exp_add, hA]
      ring
    have e2 : Complex.exp (-((1:ℕ):ℂ) * I * ((π/2 + t : ℝ) : ℂ)) = -I * Complex.exp (-(I * t)) := by
      rw [show -((1:ℕ):ℂ) * I * ((π/2 + t : ℝ) : ℂ) = -(I * t) + (-(π/2 : ℂ) * I) by push_cast; ring,
        Complex.exp_add, hA]
      ring
    have e3 : Complex.exp (-((1:ℕ):ℂ) * I * ((3*π/2 - t : ℝ) : ℂ)) = I * Complex.exp (I * t) := by
      rw [show -((1:ℕ):ℂ) * I * ((3*π/2 - t : ℝ) : ℂ) = I * t + (-(π/2 : ℂ) * I) + (-(π : ℂ) * I)
        by push_cast; ring, Complex.exp_add, Complex.exp_add, hA, hB]
      ring
    have e4 : Complex.exp (-((1:ℕ):ℂ) * I * ((3*π/2 + t : ℝ) : ℂ)) = I * Complex.exp (-(I * t)) := by
      rw [show -((1:ℕ):ℂ) * I * ((3*π/2 + t : ℝ) : ℂ) = -(I * t) + (-(π/2 : ℂ) * I) + (-(π : ℂ) * I)
        by push_cast; ring, Complex.exp_add, Complex.exp_add, hA, hB]
      ring
    rw [e1, e2, e3, e4, Complex.ofReal_neg]
    have hc : ((Real.cos t : ℝ) : ℂ) = (Complex.exp (I * t) + Complex.exp (-(I * t))) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]; ring_nf
    generalize ((Real.cos t : ℝ) : ℂ) = c at hc ⊢
    rw [Complex.sin, show z * c * I = I * z * c by ring, show -(z*c)*I = I*z*(-c) by ring]
    subst hc
    ring
  simp_rw [hpt] at h
  rw [intervalIntegral.integral_const_mul] at h
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show besselJC _ z = (2 * (π : ℂ) * besselJC _ z) / (2 * π) by field_simp, ← h]
  ring

end Buckling
end
end ChunkedSource025
/- END SOURCE 025 -/

/- BEGIN SOURCE 026: RequestProject/Bessel/Asymptotic/Subst.lean -/
section ChunkedSource026

/-!
# The substitution `cos t = 1 - s²`

`∫₀^{π/2} f(cos t) dt = ∫₀¹ f(1 - s²) · 2/√(2 - s²) ds`, and the resulting representations
`J₀(z) = (2/π) ∫₀¹ w(s) cos(z(1-s²)) ds`, `J₁(z) = (2/π) ∫₀¹ w(s)(1-s²) sin(z(1-s²)) ds`
with `w(s) = 2/√(2 - s²)`.
-/

@[expose] public section

open Complex Real

namespace Buckling

/-- The weight `w(s) = 2/√(2 - s²)`. -/
noncomputable def wgt (s : ℝ) : ℝ := 2 / Real.sqrt (2 - s ^ 2)

lemma sqrt_two_sub_sq_pos {s : ℝ} (hs : s ^ 2 < 2) : 0 < Real.sqrt (2 - s ^ 2) :=
  Real.sqrt_pos.mpr (by linarith)

lemma continuousOn_wgt : ContinuousOn wgt (Set.Icc (-1) 1) := by
  intro s hs
  have h1 : s ^ 2 ≤ 1 := by nlinarith [hs.1, hs.2]
  apply ContinuousAt.continuousWithinAt
  unfold wgt
  exact continuousAt_const.div (by fun_prop) (sqrt_two_sub_sq_pos (by linarith)).ne'

lemma hasDerivAt_arcsin_subst {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (fun s => 2 * Real.arcsin (s / Real.sqrt 2)) (wgt s) s := by
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hlt : s / Real.sqrt 2 < 1 := by
    rw [div_lt_one h2]
    have : (1:ℝ) < Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith [hs.2]
  have hgt : -1 < s / Real.sqrt 2 := by
    have : 0 ≤ s / Real.sqrt 2 := div_nonneg hs.1 h2.le
    linarith
  have hd := ((Real.hasDerivAt_arcsin hgt.ne' hlt.ne).comp s
    ((hasDerivAt_id s).div_const (Real.sqrt 2))).const_mul 2
  convert! hd using 1
  unfold wgt
  simp only [one_div]
  have hpos : 0 < 1 - (s / Real.sqrt 2) ^ 2 := by nlinarith
  have hrel : Real.sqrt (2 - s ^ 2) = Real.sqrt 2 * Real.sqrt (1 - (s / Real.sqrt 2) ^ 2) := by
    rw [← Real.sqrt_mul (by norm_num)]
    congr 1
    rw [div_pow, hs2]; field_simp
  rw [hrel]
  have : 0 < Real.sqrt (1 - (s / Real.sqrt 2) ^ 2) := Real.sqrt_pos.mpr hpos
  field_simp

lemma arcsin_inv_sqrt_two : Real.arcsin (1 / Real.sqrt 2) = π / 4 := by
  have h : Real.sin (π / 4) = 1 / Real.sqrt 2 := by
    rw [Real.sin_pi_div_four]
    have h2 : Real.sqrt 2 ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt (by norm_num)]
  rw [← h, Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

lemma cos_two_arcsin_subst {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    Real.cos (2 * Real.arcsin (s / Real.sqrt 2)) = 1 - s ^ 2 := by
  have h2 : (0:ℝ) < Real.sqrt 2 := by positivity
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hle : s / Real.sqrt 2 ≤ 1 := by
    rw [div_le_one h2]
    have : (1:ℝ) ≤ Real.sqrt 2 := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
    linarith [hs.2]
  have hge : -1 ≤ s / Real.sqrt 2 := by
    have : 0 ≤ s / Real.sqrt 2 := div_nonneg hs.1 h2.le
    linarith
  rw [Real.cos_two_mul, Real.cos_sq', Real.sin_arcsin hge hle, div_pow, hs2]
  ring

/-- **The substitution** `cos t = 1 - s²`. -/
theorem integral_cos_subst (f : ℝ → ℂ) (hf : Continuous f) :
    ∫ t in (0:ℝ)..π/2, f (Real.cos t) = ∫ s in (0:ℝ)..1, (wgt s : ℂ) * f (1 - s ^ 2) := by
  have h := intervalIntegral.integral_comp_smul_deriv (a := 0) (b := 1)
    (f := fun s => 2 * Real.arcsin (s / Real.sqrt 2)) (f' := wgt)
    (g := fun t => f (Real.cos t))
    (fun s hs => hasDerivAt_arcsin_subst (by rwa [Set.uIcc_of_le zero_le_one] at hs))
    (by rw [Set.uIcc_of_le zero_le_one]
        exact continuousOn_wgt.mono (Set.Icc_subset_Icc (by norm_num) le_rfl))
    (by fun_prop)
  simp only [zero_div, Real.arcsin_zero, mul_zero, arcsin_inv_sqrt_two] at h
  rw [show 2 * (π / 4) = π / 2 by ring] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  simp only [Function.comp, Complex.real_smul]
  rw [cos_two_arcsin_subst hs]

/-- `J₀(z) = (2/π) ∫₀¹ w(s) cos(z(1-s²)) ds`. -/
theorem besselJC_zero_subst (z : ℂ) :
    besselJC 0 z = 2 / π * ∫ s in (0:ℝ)..1, (wgt s : ℂ) * Complex.cos (z * (1 - s ^ 2 : ℝ)) := by
  rw [besselJC_zero_integral, integral_cos_subst (fun c => Complex.cos (z * c)) (by fun_prop)]

/-- `J₁(z) = (2/π) ∫₀¹ w(s)(1-s²) sin(z(1-s²)) ds`. -/
theorem besselJC_one_subst (z : ℂ) :
    besselJC 1 z = 2 / π * ∫ s in (0:ℝ)..1,
      (wgt s : ℂ) * (Complex.sin (z * (1 - s ^ 2 : ℝ)) * (1 - s ^ 2 : ℝ)) := by
  rw [besselJC_one_integral,
    integral_cos_subst (fun c => Complex.sin (z * c) * c) (by fun_prop)]

end Buckling
end
end ChunkedSource026
/- END SOURCE 026 -/

/- BEGIN SOURCE 027: RequestProject/Bessel/Asymptotic/RealAxis.lean -/
section ChunkedSource027

/-!
# Large-argument asymptotics of `J₀`, `J₁` on the positive real axis

`|√(πx/2) J₀(x) - cos(x - π/4)| ≤ C/x` and `|√(πx/2) J₁(x) - cos(x - 3π/4)| ≤ C/x`
for `x ≥ 1`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set

namespace Buckling

/-- `(π/(ix))^{1/2} = √(π/x) e^{-iπ/4}` for `x > 0`. -/
lemma cpow_half_pi_div_mul_I {x : ℝ} (hx : 0 < x) :
    ((π : ℂ) / ((x:ℂ) * I)) ^ (1 / 2 : ℂ) =
      (Real.sqrt (π / x) : ℂ) * cexp (((-(π / 4)) : ℝ) * I) := by
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : (π : ℂ) / ((x:ℂ) * I) = ((π / x : ℝ) : ℂ) * (-I) := by
    push_cast; field_simp; rw [Complex.I_sq]; ring
  have hpx : 0 < π / x := div_pos Real.pi_pos hx
  rw [e, Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hpx.ne') (by simp)),
    Complex.log_ofReal_mul hpx (by simp), Complex.log_neg_I]
  rw [show (((Real.log (π / x) : ℝ) : ℂ) + -((π : ℂ) / 2) * I) * (1 / 2) =
      ((Real.log (π / x) / 2 : ℝ) : ℂ) + (((-(π / 4)) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hpx]

/-- The oscillatory integral `Φ_g(x) = ∫₀¹ g(s) e^{-ixs²} ds`. -/
noncomputable def oscInt (g : ℝ → ℝ) (x : ℝ) : ℂ := ∫ s in (0:ℝ)..1, (g s : ℂ) * oscF x s

/-- Asymptotics of `e^{ix} Φ_g(x)` for real `g`. -/
theorem exp_mul_oscInt_asymp {g k : ℝ → ℝ} (hD : OscData (fun s => (g s : ℂ)) (fun s => (k s : ℂ)))
    (hg : ContinuousOn g (Icc 0 1)) :
    ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x →
      |(cexp ((x:ℂ) * I) * oscInt g x).re - g 0 / 2 * Real.sqrt (π / x) * Real.cos (x - π / 4)|
        ≤ C / (x * Real.sqrt x) ∧
      |(cexp ((x:ℂ) * I) * oscInt g x).im - g 0 / 2 * Real.sqrt (π / x) * Real.sin (x - π / 4)
        - g 1 / (2 * x)| ≤ C / (x * Real.sqrt x) := by
  obtain ⟨C, hC⟩ := osc_asymp hD (Complex.continuous_ofReal.comp_continuousOn hg)
  refine ⟨C, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx' : (x:ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have h := hC x hx
  set D := (∫ s in (0:ℝ)..1, (g s : ℂ) * oscF x s) -
    ((g 0 : ℂ) * (((π : ℂ) / ((x:ℂ) * I)) ^ (1 / 2 : ℂ) / 2) -
      (g 1 : ℂ) * cexp (-((x:ℂ) * I)) / (2 * ((x:ℂ) * I))) with hDdef
  have hnorm : ‖cexp ((x:ℂ) * I) * D‖ ≤ C / (x * Real.sqrt x) := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]; exact h
  have hexp : cexp ((x:ℂ) * I) * oscInt g x =
      ((g 0 / 2 * Real.sqrt (π / x) : ℝ) : ℂ) * cexp (((x - π / 4 : ℝ) : ℂ) * I) +
        ((g 1 / (2 * x) : ℝ) : ℂ) * I + cexp ((x:ℂ) * I) * D := by
    rw [hDdef, cpow_half_pi_div_mul_I hx0, oscInt]
    have e1 : cexp ((x:ℂ) * I) * cexp (((-(π / 4)) : ℝ) * I) = cexp (((x - π / 4 : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : cexp ((x:ℂ) * I) * cexp (-((x:ℂ) * I)) = 1 := by
      rw [← Complex.exp_add]; simp
    have hdivI : ∀ w : ℂ, w / (2 * ((x:ℂ) * I)) = -(w / (2 * x)) * I := by
      intro w; field_simp; ring_nf; rw [Complex.I_sq]; ring
    rw [hdivI]
    have : cexp ((x:ℂ) * I) * ((∫ s in (0:ℝ)..1, (g s : ℂ) * oscF x s) -
        ((g 0 : ℂ) * ((Real.sqrt (π / x) : ℂ) * cexp (((-(π / 4)) : ℝ) * I) / 2) -
          -((g 1 : ℂ) * cexp (-((x:ℂ) * I)) / (2 * x)) * I)) =
        cexp ((x:ℂ) * I) * (∫ s in (0:ℝ)..1, (g s : ℂ) * oscF x s) -
        ((g 0 : ℂ) * (Real.sqrt (π / x) : ℂ) / 2 * (cexp ((x:ℂ) * I) * cexp (((-(π / 4)) : ℝ) * I))
          + (g 1 : ℂ) / (2 * x) * (cexp ((x:ℂ) * I) * cexp (-((x:ℂ) * I))) * I) := by ring
    rw [this, e1, e2]
    push_cast
    ring
  have hre := Complex.abs_re_le_norm (cexp ((x:ℂ) * I) * D)
  have him := Complex.abs_im_le_norm (cexp ((x:ℂ) * I) * D)
  rw [hexp]
  constructor
  · simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
      Complex.I_re, mul_zero, add_zero]
    convert hre.trans hnorm using 2
    ring
  · simp only [Complex.add_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
      Complex.I_im, mul_one]
    convert him.trans hnorm using 2
    ring

/-! ### The two weights -/

/-- `k₀(s) = √2 s / (√(2-s²)(√2 + √(2-s²)))`, so that `w(s) = √2 + s k₀(s)`. -/
noncomputable def kW (s : ℝ) : ℝ :=
  Real.sqrt 2 * s / (Real.sqrt (2 - s ^ 2) * (Real.sqrt 2 + Real.sqrt (2 - s ^ 2)))

/-- The weight of `J₁`: `g₁(s) = w(s)(1 - s²)`. -/
noncomputable def wgt1 (s : ℝ) : ℝ := wgt s * (1 - s ^ 2)

/-- `k₁(s) = (1 - s²) k₀(s) - √2 s`, so that `g₁(s) = √2 + s k₁(s)`. -/
noncomputable def kW1 (s : ℝ) : ℝ := (1 - s ^ 2) * kW s - Real.sqrt 2 * s

lemma wgt_zero : wgt 0 = Real.sqrt 2 := by
  unfold wgt
  have h : Real.sqrt 2 ≠ 0 := by positivity
  rw [show (2:ℝ) - 0 ^ 2 = 2 by norm_num]
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

lemma wgt_one : wgt 1 = 2 := by unfold wgt; norm_num

lemma wgt_decomp {s : ℝ} (hs : s ^ 2 < 2) : wgt s = Real.sqrt 2 + s * kW s := by
  unfold wgt kW
  have h2 : 0 < Real.sqrt 2 := by positivity
  have hr : 0 < Real.sqrt (2 - s ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2 : Real.sqrt (2 - s ^ 2) ^ 2 = 2 - s ^ 2 := Real.sq_sqrt (by linarith)
  field_simp
  nlinarith [hs2, hr2]

/-- The open set `{s : s² < 2}`. -/
def nbhdU : Set ℝ := {s | s ^ 2 < 2}

lemma isOpen_nbhdU : IsOpen nbhdU := isOpen_lt (by fun_prop) continuous_const

lemma Icc_subset_nbhdU : Icc (0:ℝ) 1 ⊆ nbhdU := fun s hs => by
  simp only [nbhdU, mem_setOf_eq]; nlinarith [hs.1, hs.2]

lemma contDiffOn_kW : ContDiffOn ℝ 2 kW nbhdU := by
  have hsq : ContDiffOn ℝ 2 (fun s : ℝ => Real.sqrt (2 - s ^ 2)) nbhdU :=
    (by fun_prop : ContDiff ℝ 2 fun s : ℝ => 2 - s ^ 2).contDiffOn.sqrt
      (fun s hs => by simp only [nbhdU, mem_setOf_eq] at hs; linarith)
  unfold kW
  refine (contDiffOn_const.mul contDiffOn_id).div (hsq.mul (contDiffOn_const.add hsq)) ?_
  intro s hs
  simp only [nbhdU, mem_setOf_eq] at hs
  have hr : 0 < Real.sqrt (2 - s ^ 2) := Real.sqrt_pos.mpr (by linarith)
  have h2 : 0 < Real.sqrt 2 := by positivity
  positivity

lemma contDiffOn_ofReal_comp {f : ℝ → ℝ} {U : Set ℝ} (hf : ContDiffOn ℝ 2 f U) :
    ContDiffOn ℝ 2 (fun s => (f s : ℂ)) U :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hf

lemma oscData_wgt : OscData (fun s => (wgt s : ℂ)) (fun s => (kW s : ℂ)) where
  decomp s hs := by
    rw [wgt_decomp (Icc_subset_nbhdU hs), wgt_zero]; push_cast; ring
  k_zero := by simp [kW]
  open_nhd := ⟨nbhdU, isOpen_nbhdU, Icc_subset_nbhdU, contDiffOn_ofReal_comp contDiffOn_kW⟩

lemma oscData_wgt1 : OscData (fun s => (wgt1 s : ℂ)) (fun s => (kW1 s : ℂ)) where
  decomp s hs := by
    simp only [wgt1, kW1]
    rw [wgt_decomp (Icc_subset_nbhdU hs), wgt_decomp (by norm_num : (0:ℝ) ^ 2 < 2)]
    simp only [kW]
    push_cast; ring
  k_zero := by simp [kW1, kW]
  open_nhd := ⟨nbhdU, isOpen_nbhdU, Icc_subset_nbhdU, contDiffOn_ofReal_comp
    (((contDiffOn_const.sub (contDiffOn_id.pow 2)).mul contDiffOn_kW).sub
      (contDiffOn_const.mul contDiffOn_id))⟩

lemma continuousOn_wgt' : ContinuousOn wgt (Icc 0 1) :=
  continuousOn_wgt.mono (Icc_subset_Icc (by norm_num) le_rfl)

lemma continuousOn_wgt1 : ContinuousOn wgt1 (Icc 0 1) :=
  continuousOn_wgt'.mul (by fun_prop)

/-! ### Real representations -/

lemma intervalIntegrable_wgt_mul {f : ℝ → ℂ} (hf : Continuous f) :
    IntervalIntegrable (fun s => (wgt s : ℂ) * f s) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
  exact ((Complex.continuous_ofReal.comp_continuousOn continuousOn_wgt').mul
    hf.continuousOn).integrableOn_Icc

lemma exp_mul_oscInt (g : ℝ → ℝ) (x : ℝ) :
    cexp ((x:ℂ) * I) * oscInt g x =
      ∫ s in (0:ℝ)..1, (g s : ℂ) * cexp (((x * (1 - s ^ 2) : ℝ) : ℂ) * I) := by
  rw [oscInt, ← intervalIntegral.integral_const_mul]
  congr 1; funext s
  simp only [oscF]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `J₀(x) = (2/π) Re(e^{ix} Φ_w(x))`. -/
theorem besselJ_zero_eq_re (x : ℝ) :
    besselJ 0 x = 2 / π * (cexp ((x:ℂ) * I) * oscInt wgt x).re := by
  have h := besselJC_zero_subst (x : ℂ)
  rw [besselJC_ofReal] at h
  rw [exp_mul_oscInt]
  have hint : IntervalIntegrable (fun s => (wgt s : ℂ) * cexp (((x * (1 - s ^ 2) : ℝ) : ℂ) * I))
      volume 0 1 := intervalIntegrable_wgt_mul (by fun_prop)
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint]
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have e : (∫ s in (0:ℝ)..1, (wgt s : ℂ) * Complex.cos ((x:ℂ) * ((1 - s ^ 2 : ℝ) : ℂ))) =
      ((∫ s in (0:ℝ)..1, wgt s * Real.cos (x * (1 - s ^ 2))) : ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext s; push_cast; rfl
  rw [e] at h
  exact_mod_cast h

/-- `J₁(x) = (2/π) Im(e^{ix} Φ_{g₁}(x))`. -/
theorem besselJ_one_eq_im (x : ℝ) :
    besselJ 1 x = 2 / π * (cexp ((x:ℂ) * I) * oscInt wgt1 x).im := by
  have h := besselJC_one_subst (x : ℂ)
  rw [besselJC_ofReal] at h
  rw [exp_mul_oscInt]
  have hint : IntervalIntegrable (fun s => (wgt1 s : ℂ) * cexp (((x * (1 - s ^ 2) : ℝ) : ℂ) * I))
      volume 0 1 := by
    have := intervalIntegrable_wgt_mul (f := fun s : ℝ => ((1 - s ^ 2 : ℝ) : ℂ) *
      cexp (((x * (1 - s ^ 2) : ℝ) : ℂ) * I)) (by fun_prop)
    exact this.congr (fun s _ => by simp only [wgt1]; push_cast; ring)
  rw [← Complex.imCLM_apply, ← Complex.imCLM.intervalIntegral_comp_comm hint]
  simp only [Complex.imCLM_apply, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have e : (∫ s in (0:ℝ)..1, (wgt s : ℂ) *
      (Complex.sin ((x:ℂ) * ((1 - s ^ 2 : ℝ) : ℂ)) * ((1 - s ^ 2 : ℝ) : ℂ))) =
      ((∫ s in (0:ℝ)..1, wgt1 s * Real.sin (x * (1 - s ^ 2))) : ℝ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext s; simp only [wgt1]; push_cast; ring
  rw [e] at h
  exact_mod_cast h

/-! ### The real-axis asymptotics -/

lemma sqrt_mul_coeff {x : ℝ} (hx : 0 < x) :
    Real.sqrt (π * x / 2) * (2 / π) * (Real.sqrt 2 / 2 * Real.sqrt (π / x)) = 1 := by
  have h1 : Real.sqrt (π * x / 2) * Real.sqrt (π / x) = π / Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show π * x / 2 * (π / x) = π ^ 2 / 2 by field_simp, Real.sqrt_div' _ (by norm_num),
      Real.sqrt_sq Real.pi_pos.le]
  have h2 : Real.sqrt 2 ≠ 0 := by positivity
  calc Real.sqrt (π * x / 2) * (2 / π) * (Real.sqrt 2 / 2 * Real.sqrt (π / x))
      = (Real.sqrt (π * x / 2) * Real.sqrt (π / x)) * Real.sqrt 2 / π := by
        field_simp
    _ = 1 := by rw [h1]; field_simp

/-- **`J₀` on the real axis**: `|√(πx/2) J₀(x) - cos(x - π/4)| ≤ C/x` for `x ≥ 1`. -/
theorem besselJ_zero_real_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |Real.sqrt (π * x / 2) * besselJ 0 x - Real.cos (x - π / 4)| ≤ C / x := by
  obtain ⟨C, hC⟩ := exp_mul_oscInt_asymp oscData_wgt continuousOn_wgt'
  refine ⟨|C| * (Real.sqrt (π / 2) * (2 / π)), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  obtain ⟨h1, -⟩ := hC x hx
  rw [wgt_zero] at h1
  set r := (cexp ((x:ℂ) * I) * oscInt wgt x).re
  have hJ : besselJ 0 x = 2 / π * r := besselJ_zero_eq_re x
  have key : Real.sqrt (π * x / 2) * besselJ 0 x - Real.cos (x - π / 4) =
      Real.sqrt (π * x / 2) * (2 / π) *
        (r - Real.sqrt 2 / 2 * Real.sqrt (π / x) * Real.cos (x - π / 4)) := by
    rw [hJ]
    have := sqrt_mul_coeff hx0
    linear_combination (Real.cos (x - π / 4)) * this
  rw [key, abs_mul, abs_of_nonneg (by positivity)]
  have hsq : Real.sqrt (π * x / 2) = Real.sqrt (π / 2) * Real.sqrt x := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  calc Real.sqrt (π * x / 2) * (2 / π) *
        |r - Real.sqrt 2 / 2 * Real.sqrt (π / x) * Real.cos (x - π / 4)|
      ≤ Real.sqrt (π * x / 2) * (2 / π) * (|C| / (x * Real.sqrt x)) := by
        gcongr; exact h1.trans (by gcongr; exact le_abs_self C)
    _ = |C| * (Real.sqrt (π / 2) * (2 / π)) / x := by
        rw [hsq]; field_simp

/-- **`J₁` on the real axis**: `|√(πx/2) J₁(x) - cos(x - 3π/4)| ≤ C/x` for `x ≥ 1`. -/
theorem besselJ_one_real_asymp :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |Real.sqrt (π * x / 2) * besselJ 1 x - Real.cos (x - 3 * π / 4)| ≤ C / x := by
  obtain ⟨C, hC⟩ := exp_mul_oscInt_asymp oscData_wgt1 continuousOn_wgt1
  refine ⟨|C| * (Real.sqrt (π / 2) * (2 / π)), by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  obtain ⟨-, h1⟩ := hC x hx
  have hg0 : wgt1 0 = Real.sqrt 2 := by simp [wgt1, wgt_zero]
  have hg1 : wgt1 1 = 0 := by simp [wgt1]
  rw [hg0, hg1, zero_div, sub_zero] at h1
  set r := (cexp ((x:ℂ) * I) * oscInt wgt1 x).im
  have hJ : besselJ 1 x = 2 / π * r := besselJ_one_eq_im x
  have hcos : Real.cos (x - 3 * π / 4) = Real.sin (x - π / 4) := by
    rw [show x - 3 * π / 4 = (x - π / 4) - π / 2 by ring, Real.cos_sub_pi_div_two]
  have key : Real.sqrt (π * x / 2) * besselJ 1 x - Real.cos (x - 3 * π / 4) =
      Real.sqrt (π * x / 2) * (2 / π) *
        (r - Real.sqrt 2 / 2 * Real.sqrt (π / x) * Real.sin (x - π / 4)) := by
    rw [hJ, hcos]
    have := sqrt_mul_coeff hx0
    linear_combination (Real.sin (x - π / 4)) * this
  rw [key, abs_mul, abs_of_nonneg (by positivity)]
  have hsq : Real.sqrt (π * x / 2) = Real.sqrt (π / 2) * Real.sqrt x := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  calc Real.sqrt (π * x / 2) * (2 / π) *
        |r - Real.sqrt 2 / 2 * Real.sqrt (π / x) * Real.sin (x - π / 4)|
      ≤ Real.sqrt (π * x / 2) * (2 / π) * (|C| / (x * Real.sqrt x)) := by
        gcongr; exact h1.trans (by gcongr; exact le_abs_self C)
    _ = |C| * (Real.sqrt (π / 2) * (2 / π)) / x := by
        rw [hsq]; field_simp

end Buckling
end
end ChunkedSource027
/- END SOURCE 027 -/

/- BEGIN SOURCE 028: RequestProject/Bessel/Asymptotic/ImagAxis.lean -/
section ChunkedSource028

/-!
# Large-argument asymptotics of `J₀`, `J₁` on the positive imaginary axis

Laplace's method: for `y ≥ 1`,
`|(π i y/2)^{1/2} J_ν(iy) - cos(iy - νπ/2 - π/4)| ≤ C e^y / y` (`ν = 0, 1`).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set

namespace Buckling

lemma mul_exp_neg_half_sq_le (u : ℝ) : u * Real.exp (-(u ^ 2 / 2)) ≤ 1 := by
  have h1 : u ≤ Real.exp (u ^ 2 / 2) := by
    nlinarith [Real.add_one_le_exp (u ^ 2 / 2), sq_nonneg (u - 1)]
  have h2 : Real.exp (-(u ^ 2 / 2)) * Real.exp (u ^ 2 / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-(u ^ 2 / 2)) := Real.exp_pos _
  nlinarith

lemma integral_sq_mul_exp_le {y : ℝ} (hy : 0 < y) :
    ∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-y * s ^ 2) ≤ 1 / (y * Real.sqrt y) := by
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have hpt : ∀ s ∈ Icc (0:ℝ) 1, s ^ 2 * Real.exp (-y * s ^ 2) ≤
      1 / Real.sqrt y * (s * Real.exp (-y * s ^ 2 / 2)) := by
    intro s hs
    have h := mul_exp_neg_half_sq_le (s * Real.sqrt y)
    rw [mul_pow, Real.sq_sqrt hy.le] at h
    have e : Real.exp (-y * s ^ 2) = Real.exp (-y * s ^ 2 / 2) * Real.exp (-y * s ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [e, show -(s ^ 2 * y / 2) = -y * s ^ 2 / 2 by ring] at *
    have hE := Real.exp_pos (-y * s ^ 2 / 2)
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hsy]
    have := mul_le_mul_of_nonneg_left h (mul_nonneg hs.1 hE.le)
    nlinarith [hs.1]
  have hint : ∫ s in (0:ℝ)..1, s * Real.exp (-y * s ^ 2 / 2) = (1 - Real.exp (-y / 2)) / y := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
      (f := fun s => -Real.exp (-y * s ^ 2 / 2) / y) (f' := fun s => s * Real.exp (-y * s ^ 2 / 2))
      (fun s _ => by
        have h := ((((hasDerivAt_id s).fun_pow 2).const_mul (-y)).div_const 2).exp.neg.div_const y
        convert! h using 1
          <;> try simp only [id_eq, Pi.pow_apply, Pi.neg_apply, Pi.div_apply]
          <;> field_simp <;> ring)
      ((by fun_prop : Continuous fun s : ℝ => s * Real.exp (-y * s ^ 2 / 2)).intervalIntegrable _ _)
    rw [this]; field_simp; ring_nf; rw [Real.exp_zero]; ring
  calc ∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-y * s ^ 2)
      ≤ ∫ s in (0:ℝ)..1, 1 / Real.sqrt y * (s * Real.exp (-y * s ^ 2 / 2)) :=
        intervalIntegral.integral_mono_on zero_le_one
          ((by fun_prop : Continuous fun s : ℝ => s ^ 2 * Real.exp (-y * s ^ 2)).intervalIntegrable _ _)
          ((by fun_prop : Continuous fun s : ℝ => 1 / Real.sqrt y * (s * Real.exp (-y * s ^ 2 / 2))).intervalIntegrable _ _) hpt
    _ = 1 / Real.sqrt y * ((1 - Real.exp (-y / 2)) / y) := by
        rw [intervalIntegral.integral_const_mul, hint]
    _ ≤ 1 / Real.sqrt y * (1 / y) := by
        gcongr; linarith [Real.exp_pos (-y / 2)]
    _ = 1 / (y * Real.sqrt y) := by field_simp

/-- The real Gaussian on `[0,1]`. -/
lemma real_gauss01_asymp {y : ℝ} (hy : 1 ≤ y) :
    |(∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) - Real.sqrt (π / y) / 2| ≤ 2 / (y * Real.sqrt y) := by
  have hy0 : 0 < y := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hsy1 : Real.sqrt y ≤ y := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h := gauss01_asymp (b := (y:ℂ)) (by simp; linarith) (by exact_mod_cast hy0.ne')
  have e1 : gauss01 (y:ℂ) = ((∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) : ℝ) := by
    rw [gauss01, ← intervalIntegral.integral_ofReal]
    congr 1; funext s; push_cast; rfl
  have e2 : gaussModel (y:ℂ) = ((Real.sqrt (π / y) / 2 - Real.exp (-y) / (2 * y) : ℝ) : ℂ) := by
    rw [gaussModel, show (π : ℂ) / (y:ℂ) = ((π / y : ℝ) : ℂ) by push_cast; ring,
      show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    push_cast; ring
  rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy0] at h
  have hE : Real.exp (-y) / (2 * y) ≤ 1 / (y * Real.sqrt y) := by
    have : Real.exp (-y) * Real.sqrt y ≤ 1 := by
      have h1 : Real.sqrt y ≤ Real.exp y := hsy1.trans (by linarith [Real.add_one_le_exp y])
      have h2 : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (-y)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [Real.exp_pos (-y)]
  have hY : 1 / y ^ 2 ≤ 1 / (y * Real.sqrt y) := by
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_left hsy1 hy0.le
  have e3 : (∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) - Real.sqrt (π / y) / 2 =
      ((∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) - (Real.sqrt (π / y) / 2 - Real.exp (-y) / (2 * y)))
        + -(Real.exp (-y) / (2 * y)) := by ring
  rw [e3]
  refine (abs_add_le _ _).trans ?_
  rw [abs_neg, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-y) / (2 * y))]
  have : (2:ℝ) / (y * Real.sqrt y) = 1 / (y * Real.sqrt y) + 1 / (y * Real.sqrt y) := by ring
  linarith

/-- **Laplace's method at an endpoint.** -/
theorem laplace_asymp {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1)) {M : ℝ}
    (hM : ∀ s ∈ Icc (0:ℝ) 1, |g s - g 0| ≤ M * s ^ 2) {y : ℝ} (hy : 1 ≤ y) :
    |(∫ s in (0:ℝ)..1, g s * Real.exp (-y * s ^ 2)) - g 0 * (Real.sqrt (π / y) / 2)| ≤
      (2 * |g 0| + M) / (y * Real.sqrt y) := by
  have hy0 : 0 < y := by linarith
  have hgi : IntervalIntegrable (fun s => g s * Real.exp (-y * s ^ 2)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (hg.mul (by fun_prop)).integrableOn_Icc
  have hei : IntervalIntegrable (fun s : ℝ => Real.exp (-y * s ^ 2)) volume 0 1 :=
    (by fun_prop : Continuous fun s : ℝ => Real.exp (-y * s ^ 2)).intervalIntegrable _ _
  have hsplit : (∫ s in (0:ℝ)..1, g s * Real.exp (-y * s ^ 2)) =
      g 0 * (∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) +
        ∫ s in (0:ℝ)..1, (g s - g 0) * Real.exp (-y * s ^ 2) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hei.const_mul _)]
    · congr 1; funext s; ring
    · exact (hgi.sub (hei.const_mul _)).congr (fun s _ => by ring)
  have hR : |∫ s in (0:ℝ)..1, (g s - g 0) * Real.exp (-y * s ^ 2)| ≤ M / (y * Real.sqrt y) := by
    have hM0 : 0 ≤ M := by
      have := hM 1 ⟨zero_le_one, le_rfl⟩
      nlinarith [abs_nonneg (g 1 - g 0)]
    calc |∫ s in (0:ℝ)..1, (g s - g 0) * Real.exp (-y * s ^ 2)|
        ≤ ∫ s in (0:ℝ)..1, M * (s ^ 2 * Real.exp (-y * s ^ 2)) := by
          rw [← Real.norm_eq_abs]
          refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
            (Eventually.of_forall fun s hs => ?_) ((by fun_prop : Continuous fun s : ℝ =>
              M * (s ^ 2 * Real.exp (-y * s ^ 2))).intervalIntegrable _ _)
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
          have := hM s ⟨hs.1.le, hs.2⟩
          calc |g s - g 0| * Real.exp (-y * s ^ 2) ≤ M * s ^ 2 * Real.exp (-y * s ^ 2) := by
                gcongr
            _ = _ := by ring
      _ = M * ∫ s in (0:ℝ)..1, s ^ 2 * Real.exp (-y * s ^ 2) :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ M * (1 / (y * Real.sqrt y)) := by gcongr; exact integral_sq_mul_exp_le hy0
      _ = _ := by ring
  have hG := real_gauss01_asymp hy
  rw [hsplit]
  have e : g 0 * (∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) +
      (∫ s in (0:ℝ)..1, (g s - g 0) * Real.exp (-y * s ^ 2)) - g 0 * (Real.sqrt (π / y) / 2) =
      g 0 * ((∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) - Real.sqrt (π / y) / 2) +
        ∫ s in (0:ℝ)..1, (g s - g 0) * Real.exp (-y * s ^ 2) := by ring
  rw [e]
  calc _ ≤ |g 0 * ((∫ s in (0:ℝ)..1, Real.exp (-y * s ^ 2)) - Real.sqrt (π / y) / 2)| +
        |∫ s in (0:ℝ)..1, (g s - g 0) * Real.exp (-y * s ^ 2)| := abs_add_le _ _
    _ ≤ |g 0| * (2 / (y * Real.sqrt y)) + M / (y * Real.sqrt y) := by
        rw [abs_mul]; gcongr
    _ = _ := by ring

/-! ### The Bessel functions on the imaginary axis -/

lemma integral_ofReal_mul_cosh (g : ℝ → ℝ) (y : ℝ) :
    ∫ s in (0:ℝ)..1, (g s : ℂ) * Complex.cos ((y:ℂ) * I * ((1 - s ^ 2 : ℝ) : ℂ)) =
      ((∫ s in (0:ℝ)..1, g s * Real.cosh (y * (1 - s ^ 2))) : ℝ) := by
  rw [← intervalIntegral.integral_ofReal]
  congr 1; funext s
  rw [show (y:ℂ) * I * ((1 - s ^ 2 : ℝ) : ℂ) = ((y * (1 - s ^ 2) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.cos_mul_I, ← Complex.ofReal_cosh]
  push_cast; ring

lemma wgt_nonneg {s : ℝ} : 0 ≤ wgt s := by unfold wgt; positivity

lemma wgt_le_two {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : wgt s ≤ 2 := by
  unfold wgt
  have h1 : 1 ≤ Real.sqrt (2 - s ^ 2) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith [hs.1, hs.2])
  rw [div_le_iff₀ (by linarith)]; linarith

lemma kW_nonneg {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : 0 ≤ kW s := by
  unfold kW
  have := hs.1
  positivity

lemma kW_le {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : kW s ≤ s := by
  unfold kW
  have h1 : 1 ≤ Real.sqrt (2 - s ^ 2) := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by nlinarith [hs.1, hs.2])
  have h2 : 1 ≤ Real.sqrt 2 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
  have h3 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [div_le_iff₀ (by positivity)]
  have hs0 := hs.1
  nlinarith [mul_le_mul h1 (by linarith : Real.sqrt 2 + 1 ≤ Real.sqrt 2 + Real.sqrt (2 - s ^ 2))
    (by positivity) (by positivity)]

lemma wgt_sub_le {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : |wgt s - wgt 0| ≤ 1 * s ^ 2 := by
  rw [wgt_decomp (Icc_subset_nbhdU hs), wgt_zero, add_sub_cancel_left, abs_of_nonneg
    (mul_nonneg hs.1 (kW_nonneg hs))]
  nlinarith [kW_le hs, hs.1]

lemma wgt1_sub_le {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : |wgt1 s - wgt1 0| ≤ 3 * s ^ 2 := by
  have hd := oscData_wgt1.decomp s hs
  have hd' : wgt1 s - wgt1 0 = s * kW1 s := by exact_mod_cast (sub_eq_of_eq_add' hd)
  rw [hd']
  unfold kW1
  have h1 := kW_le hs
  have h2 := kW_nonneg hs
  have h3 : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h4 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hs0 := hs.1
  have hs1 := hs.2
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hs0 h2, mul_nonneg (mul_nonneg hs0 hs0) h2]

lemma wgt1_nonneg {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : 0 ≤ wgt1 s := by
  unfold wgt1; exact mul_nonneg wgt_nonneg (by nlinarith [hs.1, hs.2])

lemma wgt1_le_two {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) : wgt1 s ≤ 2 := by
  unfold wgt1
  have := wgt_le_two hs
  have := wgt_nonneg (s := s)
  nlinarith [hs.1, hs.2, sq_nonneg s]

lemma abs_integral_mul_exp_neg_le {g : ℝ → ℝ} (hg : ContinuousOn g (Icc 0 1))
    (hg0 : ∀ s ∈ Icc (0:ℝ) 1, 0 ≤ g s) (hg2 : ∀ s ∈ Icc (0:ℝ) 1, g s ≤ 2) (y : ℝ) (hy : 0 ≤ y) :
    |∫ s in (0:ℝ)..1, g s * Real.exp (-(y * (1 - s ^ 2)))| ≤ 2 := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ s in (0:ℝ)..1, g s * Real.exp (-(y * (1 - s ^ 2)))‖ ≤ ∫ s in (0:ℝ)..1, (2:ℝ) := by
        refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
          (Eventually.of_forall fun s hs => ?_) intervalIntegrable_const
        have hs' : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg0 s hs'), abs_of_pos (Real.exp_pos _)]
        have : Real.exp (-(y * (1 - s ^ 2))) ≤ 1 := Real.exp_le_one_iff.mpr (by
          have : 0 ≤ 1 - s ^ 2 := by nlinarith [hs'.1, hs'.2]
          nlinarith)
        nlinarith [hg2 s hs', hg0 s hs']
    _ = 2 := by simp

/-- `J₀(iy) = π⁻¹ (e^y ∫₀¹ w e^{-ys²} + ∫₀¹ w e^{-y(1-s²)})`. -/
theorem besselJC_zero_mul_I (y : ℝ) :
    besselJC 0 ((y:ℂ) * I) = ((1 / π * (Real.exp y * (∫ s in (0:ℝ)..1, wgt s * Real.exp (-y * s ^ 2))
      + ∫ s in (0:ℝ)..1, wgt s * Real.exp (-(y * (1 - s ^ 2))))) : ℝ) := by
  rw [besselJC_zero_subst, integral_ofReal_mul_cosh]
  have hi1 : IntervalIntegrable (fun s => wgt s * Real.exp (-y * s ^ 2)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (continuousOn_wgt'.mul (by fun_prop)).integrableOn_Icc
  have hi2 : IntervalIntegrable (fun s => wgt s * Real.exp (-(y * (1 - s ^ 2)))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (continuousOn_wgt'.mul (by fun_prop)).integrableOn_Icc
  have e : (∫ s in (0:ℝ)..1, wgt s * Real.cosh (y * (1 - s ^ 2))) =
      (Real.exp y * (∫ s in (0:ℝ)..1, wgt s * Real.exp (-y * s ^ 2)) +
        ∫ s in (0:ℝ)..1, wgt s * Real.exp (-(y * (1 - s ^ 2)))) / 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hi1.const_mul _) hi2,
      ← intervalIntegral.integral_div]
    congr 1; funext s
    rw [Real.cosh_eq, show Real.exp (y * (1 - s ^ 2)) = Real.exp y * Real.exp (-y * s ^ 2) by
      rw [← Real.exp_add]; ring_nf]
    ring
  rw [e]; push_cast; ring

/-- `J₁(iy) = i π⁻¹ (e^y ∫₀¹ g₁ e^{-ys²} - ∫₀¹ g₁ e^{-y(1-s²)})`. -/
theorem besselJC_one_mul_I (y : ℝ) :
    besselJC 1 ((y:ℂ) * I) = I * ((1 / π * (Real.exp y *
      (∫ s in (0:ℝ)..1, wgt1 s * Real.exp (-y * s ^ 2))
      - ∫ s in (0:ℝ)..1, wgt1 s * Real.exp (-(y * (1 - s ^ 2))))) : ℝ) := by
  rw [besselJC_one_subst]
  have hrw : ∫ s in (0:ℝ)..1, (wgt s : ℂ) * (Complex.sin ((y:ℂ) * I * ((1 - s ^ 2 : ℝ) : ℂ)) *
      ((1 - s ^ 2 : ℝ) : ℂ)) = I * ((∫ s in (0:ℝ)..1, wgt1 s * Real.sinh (y * (1 - s ^ 2))) : ℝ) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    congr 1; funext s
    rw [show (y:ℂ) * I * ((1 - s ^ 2 : ℝ) : ℂ) = ((y * (1 - s ^ 2) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
    simp only [wgt1]; push_cast; ring
  rw [hrw]
  have hi1 : IntervalIntegrable (fun s => wgt1 s * Real.exp (-y * s ^ 2)) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (continuousOn_wgt1.mul (by fun_prop)).integrableOn_Icc
  have hi2 : IntervalIntegrable (fun s => wgt1 s * Real.exp (-(y * (1 - s ^ 2)))) volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one]
    exact (continuousOn_wgt1.mul (by fun_prop)).integrableOn_Icc
  have e : (∫ s in (0:ℝ)..1, wgt1 s * Real.sinh (y * (1 - s ^ 2))) =
      (Real.exp y * (∫ s in (0:ℝ)..1, wgt1 s * Real.exp (-y * s ^ 2)) -
        ∫ s in (0:ℝ)..1, wgt1 s * Real.exp (-(y * (1 - s ^ 2)))) / 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub (hi1.const_mul _) hi2,
      ← intervalIntegral.integral_div]
    congr 1; funext s
    rw [Real.sinh_eq, show Real.exp (y * (1 - s ^ 2)) = Real.exp y * Real.exp (-y * s ^ 2) by
      rw [← Real.exp_add]; ring_nf]
    ring
  rw [e]; push_cast; ring

/-- `(π i y/2)^{1/2} = √(πy/2) e^{iπ/4}` for `y > 0`. -/
lemma cpow_half_pi_mul_I {y : ℝ} (hy : 0 < y) :
    ((π : ℂ) * ((y:ℂ) * I) / 2) ^ (1 / 2 : ℂ) =
      (Real.sqrt (π * y / 2) : ℂ) * cexp (((π / 4) : ℝ) * I) := by
  have e : (π : ℂ) * ((y:ℂ) * I) / 2 = ((π * y / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have hpy : 0 < π * y / 2 := by positivity
  rw [e, Complex.cpow_def_of_ne_zero (mul_ne_zero (by exact_mod_cast hpy.ne') Complex.I_ne_zero),
    Complex.log_ofReal_mul hpy Complex.I_ne_zero, Complex.log_I]
  rw [show (((Real.log (π * y / 2) : ℝ) : ℂ) + (π : ℂ) / 2 * I) * (1 / 2) =
      ((Real.log (π * y / 2) / 2 : ℝ) : ℂ) + (((π / 4) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_half, Real.exp_log hpy]

lemma sqrt_le_exp_div {y : ℝ} (hy : 1 ≤ y) : Real.sqrt y ≤ 2 * Real.exp y / y := by
  have hy0 : 0 < y := by linarith
  have h1 : Real.sqrt y ≤ y := by rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have h2 := Real.quadratic_le_exp_of_nonneg hy0.le
  rw [le_div_iff₀ hy0]
  nlinarith

lemma one_le_exp_div {y : ℝ} (hy : 1 ≤ y) : 1 ≤ Real.exp y / y := by
  have hy0 : 0 < y := by linarith
  rw [le_div_iff₀ hy0]; linarith [Real.add_one_le_exp y]

/-- Core estimate on the imaginary axis. -/
lemma imag_core {y A B K : ℝ} (hy : 1 ≤ y) (hA : |A - Real.sqrt 2 * (Real.sqrt (π / y) / 2)| ≤
    K / (y * Real.sqrt y)) (hB : |B| ≤ 2) (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖u * (Real.exp y * ((Real.sqrt (π * y / 2) / π * A - 1 / 2 : ℝ) : ℂ)) +
      u * ((Real.sqrt (π * y / 2) / π * B : ℝ) : ℂ) - Real.exp (-y) * v / 2‖ ≤
      (|K| + 3) * Real.exp y / y := by
  have hy0 : 0 < y := by linarith
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
  have hp : Real.sqrt (π * y / 2) = Real.sqrt (π / 2) * Real.sqrt y := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  have hpi2 : Real.sqrt (π / 2) ≤ π / 2 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [Real.pi_gt_three]
  have hcoef : Real.sqrt (π * y / 2) / π * (Real.sqrt 2 * (Real.sqrt (π / y) / 2)) = 1 / 2 := by
    have := sqrt_mul_coeff hy0
    field_simp at this ⊢
    linarith
  have h1 : |Real.sqrt (π * y / 2) / π * A - 1 / 2| ≤ |K| / (2 * y) := by
    rw [← hcoef, ← mul_sub, abs_mul, abs_of_nonneg (by positivity), hp]
    calc Real.sqrt (π / 2) * Real.sqrt y / π * |A - Real.sqrt 2 * (Real.sqrt (π / y) / 2)|
        ≤ (π / 2) * Real.sqrt y / π * (|K| / (y * Real.sqrt y)) := by
          gcongr; exact hA.trans (by gcongr; exact le_abs_self K)
      _ = |K| / (2 * y) := by field_simp
  have h2 : |Real.sqrt (π * y / 2) / π * B| ≤ Real.sqrt y := by
    rw [abs_mul, abs_of_nonneg (by positivity), hp]
    calc Real.sqrt (π / 2) * Real.sqrt y / π * |B| ≤ (π / 2) * Real.sqrt y / π * 2 := by gcongr
      _ = Real.sqrt y := by field_simp
  have h3 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE1 := one_le_exp_div hy
  have hE2 := sqrt_le_exp_div hy
  calc _ ≤ ‖u * (Real.exp y * ((Real.sqrt (π * y / 2) / π * A - 1 / 2 : ℝ) : ℂ))‖ +
        ‖u * ((Real.sqrt (π * y / 2) / π * B : ℝ) : ℂ)‖ + ‖Real.exp (-y) * v / 2‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr; exact norm_add_le _ _
    _ ≤ Real.exp y * (|K| / (2 * y)) + Real.sqrt y + 1 / 2 := by
        have n1 : ‖u * (Real.exp y * ((Real.sqrt (π * y / 2) / π * A - 1 / 2 : ℝ) : ℂ))‖ =
            Real.exp y * |Real.sqrt (π * y / 2) / π * A - 1 / 2| := by
          rw [norm_mul, hu, one_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        have n2 : ‖u * ((Real.sqrt (π * y / 2) / π * B : ℝ) : ℂ)‖ =
            |Real.sqrt (π * y / 2) / π * B| := by
          rw [norm_mul, hu, one_mul, Complex.norm_real, Real.norm_eq_abs]
        have n3 : ‖(Real.exp (-y) : ℂ) * v / 2‖ = Real.exp (-y) / 2 := by
          rw [norm_div, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          simp
        rw [n1, n2, n3]
        have := mul_le_mul_of_nonneg_left h1 (Real.exp_pos y).le
        linarith
    _ ≤ (|K| + 3) * Real.exp y / y := by
        have : Real.exp y * (|K| / (2 * y)) ≤ |K| * Real.exp y / y := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hy0]
          nlinarith [mul_nonneg (mul_nonneg (abs_nonneg K) (Real.exp_pos y).le) hy0.le]
        have e : (|K| + 3) * Real.exp y / y = |K| * Real.exp y / y + 2 * Real.exp y / y +
            Real.exp y / y := by ring
        rw [e]
        linarith

/-- **`J₀` on the imaginary axis.** -/
theorem besselJC_zero_imag_asymp :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖((π : ℂ) * ((y:ℂ) * I) / 2) ^ (1 / 2 : ℂ) * besselJC 0 ((y:ℂ) * I) -
        Complex.cos ((y:ℂ) * I - (π : ℂ) / 4)‖ ≤ C * Real.exp y / y := by
  refine ⟨|2 * |wgt 0| + 1| + 3, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set A := ∫ s in (0:ℝ)..1, wgt s * Real.exp (-y * s ^ 2)
  set B := ∫ s in (0:ℝ)..1, wgt s * Real.exp (-(y * (1 - s ^ 2)))
  have hA := laplace_asymp continuousOn_wgt' (fun s hs => wgt_sub_le hs) hy
  rw [wgt_zero] at hA
  rw [wgt_zero]
  have hB : |B| ≤ 2 := abs_integral_mul_exp_neg_le continuousOn_wgt'
    (fun s _ => wgt_nonneg) (fun s hs => wgt_le_two hs) y hy0.le
  have key := imag_core hy hA hB (cexp (((π / 4) : ℝ) * I)) (cexp ((-(π / 4) : ℝ) * I))
    (Complex.norm_exp_ofReal_mul_I _) (Complex.norm_exp_ofReal_mul_I _)
  convert key using 2
  rw [cpow_half_pi_mul_I hy0, besselJC_zero_mul_I]
  have hcos : Complex.cos ((y:ℂ) * I - (π : ℂ) / 4) =
      (Real.exp (-y) * cexp ((-(π / 4) : ℝ) * I) + Real.exp y * cexp (((π / 4) : ℝ) * I)) / 2 := by
    rw [Complex.cos, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring_nf <;> rw [Complex.I_sq] <;> ring
  rw [hcos]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-- **`J₁` on the imaginary axis.** -/
theorem besselJC_one_imag_asymp :
    ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖((π : ℂ) * ((y:ℂ) * I) / 2) ^ (1 / 2 : ℂ) * besselJC 1 ((y:ℂ) * I) -
        Complex.cos ((y:ℂ) * I - (π : ℂ) / 2 - (π : ℂ) / 4)‖ ≤ C * Real.exp y / y := by
  refine ⟨|2 * |wgt1 0| + 3| + 3, fun y hy => ?_⟩
  have hy0 : 0 < y := by linarith
  set A := ∫ s in (0:ℝ)..1, wgt1 s * Real.exp (-y * s ^ 2)
  set B := ∫ s in (0:ℝ)..1, wgt1 s * Real.exp (-(y * (1 - s ^ 2)))
  have hg0 : wgt1 0 = Real.sqrt 2 := by simp [wgt1, wgt_zero]
  have hA := laplace_asymp continuousOn_wgt1 (fun s hs => wgt1_sub_le hs) hy
  rw [hg0] at hA
  rw [hg0]
  have hB : |-B| ≤ 2 := by
    rw [abs_neg]
    exact abs_integral_mul_exp_neg_le continuousOn_wgt1 (fun s hs => wgt1_nonneg hs)
      (fun s hs => wgt1_le_two hs) y hy0.le
  have key := imag_core hy hA hB (cexp (((3 * π / 4) : ℝ) * I)) (cexp ((-(3 * π / 4) : ℝ) * I))
    (Complex.norm_exp_ofReal_mul_I _) (Complex.norm_exp_ofReal_mul_I _)
  convert key using 2
  rw [cpow_half_pi_mul_I hy0, besselJC_one_mul_I]
  have hωI : cexp (((π / 4) : ℝ) * I) * I = cexp (((3 * π / 4) : ℝ) * I) := by
    have : cexp (((π / 2) : ℝ) * I) = I := by
      push_cast; exact Complex.exp_pi_div_two_mul_I
    calc cexp (((π / 4) : ℝ) * I) * I = cexp (((π / 4) : ℝ) * I) * cexp (((π / 2) : ℝ) * I) := by
          rw [this]
      _ = _ := by rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hcos : Complex.cos ((y:ℂ) * I - (π : ℂ) / 2 - (π : ℂ) / 4) =
      (Real.exp (-y) * cexp ((-(3 * π / 4) : ℝ) * I) +
        Real.exp y * cexp (((3 * π / 4) : ℝ) * I)) / 2 := by
    rw [Complex.cos, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 2 <;> push_cast <;> ring_nf <;> rw [Complex.I_sq] <;> ring
  rw [hcos, ← hωI]
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

end Buckling
end
end ChunkedSource028
/- END SOURCE 028 -/

/- BEGIN SOURCE 029: RequestProject/Bessel/Asymptotic/Main.lean -/
section ChunkedSource029

/-!
# External theorem E4 (large-argument asymptotics of `J₀`, `J₁`), proved

For `ν ∈ {0, 1}` put `E_ν(z) = (πz/2)^{1/2} J_ν(z) - cos(z - νπ/2 - π/4)`.  On the positive
real axis `|E_ν(x)| ≤ C/x` (stationary phase, `RealAxis.lean`) and on the positive imaginary
axis `|E_ν(iy)| ≤ C e^y/y` (Laplace's method, `ImagAxis.lean`).  The function
`z E_ν(z) e^{iz}` is holomorphic in the open first quadrant, continuous up to the boundary and of
exponential type, and it is bounded on both boundary rays; by the Phragmén–Lindelöf principle
it is bounded in the closed quadrant, i.e. `|E_ν(z)| ≤ C e^{Im z}/|z|` there.  The fourth
quadrant follows by complex conjugation.  This is `ExtAsymptotic` (`extAsymptotic_holds`).
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set

namespace Buckling

lemma norm_ccos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h : Complex.cos w = (Complex.exp (w * I) + Complex.exp (-w * I)) / 2 := rfl
  rw [h, norm_div, Complex.norm_two]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  have := norm_add_le (Complex.exp (w * I)) (Complex.exp (-w * I))
  linarith

lemma norm_csin_le_exp (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have h : Complex.sin w = (Complex.exp (-w * I) - Complex.exp (w * I)) * I / 2 := rfl
  rw [h, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_two]
  have h1 : ‖Complex.exp (w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  have h2 : ‖Complex.exp (-w * I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  have := norm_sub_le (Complex.exp (-w * I)) (Complex.exp (w * I))
  linarith

lemma abs_im_mul_cos_le (z : ℂ) (t : ℝ) : |(z * (Real.cos t : ℂ)).im| ≤ |z.im| := by
  rw [Complex.im_mul_ofReal, abs_mul]
  calc |z.im| * |Real.cos t| ≤ |z.im| * 1 := by gcongr; exact Real.abs_cos_le_one t
    _ = _ := mul_one _

/-- `|J_ν(z)| ≤ e^{|Im z|}` for `ν ∈ {0,1}`. -/
theorem norm_besselJC_le_exp {ν : ℕ} (hν : ν ≤ 1) (z : ℂ) :
    ‖besselJC ν z‖ ≤ Real.exp |z.im| := by
  have hpi : 0 < π := Real.pi_pos
  have key : ∀ f : ℝ → ℂ, (∀ t, ‖f t‖ ≤ Real.exp |z.im|) →
      ‖(2 / π : ℂ) * ∫ t in (0:ℝ)..π/2, f t‖ ≤ Real.exp |z.im| := by
    intro f hf
    rw [norm_mul]
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π / 2)
      (fun t _ => hf t)
    have h2 : ‖(2 / π : ℂ)‖ = 2 / π := by
      rw [norm_div, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
    rw [h2]
    calc 2 / π * ‖∫ t in (0:ℝ)..π/2, f t‖ ≤ 2 / π * (Real.exp |z.im| * |π / 2 - 0|) := by
          gcongr
      _ = Real.exp |z.im| := by rw [sub_zero, abs_of_pos (by positivity : (0:ℝ) < π / 2)]; field_simp
  interval_cases ν
  · rw [besselJC_zero_integral]
    exact key _ fun t => (norm_ccos_le_exp _).trans
      (Real.exp_le_exp.mpr (abs_im_mul_cos_le z t))
  · rw [besselJC_one_integral]
    refine key _ fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖Complex.sin (z * (Real.cos t : ℂ))‖ * |Real.cos t| ≤ Real.exp |z.im| * 1 := by
          gcongr
          · exact (norm_csin_le_exp _).trans (Real.exp_le_exp.mpr (abs_im_mul_cos_le z t))
          · exact Real.abs_cos_le_one t
      _ = _ := mul_one _

/-- The error term `E_ν(z) = (πz/2)^{1/2} J_ν(z) - cos(z - νπ/2 - π/4)`. -/
noncomputable def asymErr (ν : ℕ) (z : ℂ) : ℂ :=
  ((π : ℂ) * z / 2) ^ (1 / 2 : ℂ) * besselJC ν z - Complex.cos (z - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4)

lemma norm_asymErr_le {ν : ℕ} (hν : ν ≤ 1) (z : ℂ) :
    ‖asymErr ν z‖ ≤ (Real.sqrt (π * ‖z‖ / 2) + 1) * Real.exp |z.im| := by
  unfold asymErr
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have h1 : ‖((π : ℂ) * z / 2) ^ (1 / 2 : ℂ)‖ ≤ Real.sqrt (π * ‖z‖ / 2) := by
    by_cases hz : z = 0
    · subst hz; simp
    · rw [norm_cpow_half (by simp [hz, Real.pi_ne_zero])]
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        Complex.norm_two]
  have h2 := norm_besselJC_le_exp hν z
  have h3 : ‖Complex.cos (z - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4)‖ ≤ Real.exp |z.im| := by
    refine (norm_ccos_le_exp _).trans (le_of_eq ?_)
    congr 2; simp
  calc ‖((π : ℂ) * z / 2) ^ (1 / 2 : ℂ)‖ * ‖besselJC ν z‖ +
        ‖Complex.cos (z - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4)‖
      ≤ Real.sqrt (π * ‖z‖ / 2) * Real.exp |z.im| + Real.exp |z.im| := by gcongr
    _ = _ := by ring

/-! ### Boundary values -/

lemma cpow_half_ofReal {x : ℝ} (hx : 0 ≤ x) :
    ((π : ℂ) * (x:ℂ) / 2) ^ (1 / 2 : ℂ) = (Real.sqrt (π * x / 2) : ℂ) := by
  rw [show (π : ℂ) * (x:ℂ) / 2 = ((π * x / 2 : ℝ) : ℂ) by push_cast; ring,
    show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow (by positivity), Real.sqrt_eq_rpow]

lemma asymErr_ofReal (ν : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    asymErr ν (x:ℂ) = ((Real.sqrt (π * x / 2) * besselJ ν x - Real.cos (x - ν * π / 2 - π / 4) : ℝ) : ℂ) := by
  unfold asymErr
  rw [cpow_half_ofReal hx, besselJC_ofReal]
  push_cast
  ring_nf

theorem asymErr_real_bound {ν : ℕ} (hν : ν ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → ‖(x:ℂ) * asymErr ν (x:ℂ)‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |Real.sqrt (π * x / 2) * besselJ ν x - Real.cos (x - ν * π / 2 - π / 4)| ≤ C / x := by
    interval_cases ν
    · obtain ⟨C, hC0, hC⟩ := besselJ_zero_real_asymp
      exact ⟨C, hC0, fun x hx => by simpa using hC x hx⟩
    · obtain ⟨C, hC0, hC⟩ := besselJ_one_real_asymp
      refine ⟨C, hC0, fun x hx => ?_⟩
      have := hC x hx
      convert this using 4; push_cast; ring
  refine ⟨max C (Real.sqrt (π / 2) + 1), le_max_of_le_left hC0, fun x hx => ?_⟩
  rcases le_or_gt 1 x with h1 | h1
  · rw [asymErr_ofReal ν hx, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hx]
    have := hC x h1
    have hx0 : 0 < x := by linarith
    calc x * |Real.sqrt (π * x / 2) * besselJ ν x - Real.cos (x - ν * π / 2 - π / 4)|
        ≤ x * (C / x) := by gcongr
      _ = C := by field_simp
      _ ≤ _ := le_max_left _ _
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]
    have h := norm_asymErr_le hν (x:ℂ)
    simp only [Complex.ofReal_im, abs_zero, Real.exp_zero, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hx] at h
    have hs : Real.sqrt (π * x / 2) ≤ Real.sqrt (π / 2) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    calc x * ‖asymErr ν (x:ℂ)‖ ≤ 1 * (Real.sqrt (π / 2) + 1) := by
          apply mul_le_mul h1.le (h.trans (by linarith)) (norm_nonneg _) zero_le_one
      _ ≤ _ := by rw [one_mul]; exact le_max_right _ _

theorem asymErr_imag_bound {ν : ℕ} (hν : ν ≤ 1) :
    ∃ C : ℝ, ∀ y : ℝ, 0 ≤ y →
      ‖((y:ℂ) * I) * asymErr ν ((y:ℂ) * I) * cexp (I * ((y:ℂ) * I))‖ ≤ C := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ y : ℝ, 1 ≤ y →
      ‖asymErr ν ((y:ℂ) * I)‖ ≤ C * Real.exp y / y := by
    interval_cases ν
    · obtain ⟨C, hC⟩ := besselJC_zero_imag_asymp
      refine ⟨C, fun y hy => ?_⟩
      have e : asymErr 0 ((y:ℂ) * I) = ((π : ℂ) * ((y:ℂ) * I) / 2) ^ (1 / 2 : ℂ) *
          besselJC 0 ((y:ℂ) * I) - Complex.cos ((y:ℂ) * I - (π : ℂ) / 4) := by
        unfold asymErr; rw [show ((0:ℕ):ℂ) * (π:ℂ) / 2 = 0 by simp, sub_zero]
      rw [e]; exact hC y hy
    · obtain ⟨C, hC⟩ := besselJC_one_imag_asymp
      refine ⟨C, fun y hy => ?_⟩
      have e : asymErr 1 ((y:ℂ) * I) = ((π : ℂ) * ((y:ℂ) * I) / 2) ^ (1 / 2 : ℂ) *
          besselJC 1 ((y:ℂ) * I) - Complex.cos ((y:ℂ) * I - (π : ℂ) / 2 - (π : ℂ) / 4) := by
        unfold asymErr; rw [show ((1:ℕ):ℂ) * (π:ℂ) / 2 = (π:ℂ) / 2 by simp]
      rw [e]; exact hC y hy
  refine ⟨max C ((Real.sqrt (π / 2) + 1) * Real.exp 1), fun y hy => ?_⟩
  have hexp : ‖cexp (I * ((y:ℂ) * I))‖ = Real.exp (-y) := by
    rw [Complex.norm_exp]; congr 1; simp
  have hyn : ‖(y:ℂ) * I‖ = y := by simp [abs_of_nonneg hy]
  rw [norm_mul, norm_mul, hexp, hyn]
  rcases le_or_gt 1 y with h1 | h1
  · have hy0 : 0 < y := by linarith
    have := hC y h1
    have he : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
    calc y * ‖asymErr ν ((y:ℂ) * I)‖ * Real.exp (-y) ≤ y * (C * Real.exp y / y) * Real.exp (-y) := by
          gcongr
      _ = C := by field_simp; rw [mul_assoc, he, mul_one]
      _ ≤ _ := le_max_left _ _
  · have h := norm_asymErr_le hν ((y:ℂ) * I)
    rw [hyn] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.ofReal_im,
      Complex.I_re, mul_zero, add_zero, abs_of_nonneg hy] at h
    have hs : Real.sqrt (π * y / 2) ≤ Real.sqrt (π / 2) :=
      Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos])
    have he : Real.exp y ≤ Real.exp 1 := Real.exp_le_exp.mpr h1.le
    have he' : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc y * ‖asymErr ν ((y:ℂ) * I)‖ * Real.exp (-y)
        ≤ 1 * ((Real.sqrt (π / 2) + 1) * Real.exp 1) * 1 := by
          gcongr
          · exact h.trans (by gcongr)
      _ ≤ _ := by rw [one_mul, mul_one]; exact le_max_right _ _

/-! ### Phragmén–Lindelöf -/

lemma slitPlane_or_zero {z : ℂ} (hz : 0 ≤ z.re) :
    0 ≤ ((π : ℂ) * z / 2).re ∨ ((π : ℂ) * z / 2).im ≠ 0 := by
  left
  have : ((π : ℂ) * z / 2).re = π * z.re / 2 := by simp
  rw [this]; positivity

lemma differentiableAt_asymErr (ν : ℕ) {z : ℂ} (hz : 0 < z.re) : DifferentiableAt ℂ (asymErr ν) z := by
  unfold asymErr
  have hslit : (π : ℂ) * z / 2 ∈ slitPlane := by
    left; have : ((π : ℂ) * z / 2).re = π * z.re / 2 := by simp
    rw [this]; positivity
  refine DifferentiableAt.sub ?_ (by fun_prop)
  refine DifferentiableAt.mul ?_ ((differentiable_besselJC ν).differentiableAt)
  exact (differentiableAt_id.const_mul _ |>.div_const 2).cpow_const hslit

lemma continuousAt_asymErr (ν : ℕ) {z : ℂ} (hz : 0 ≤ z.re) : ContinuousAt (asymErr ν) z := by
  unfold asymErr
  refine ContinuousAt.sub ?_ (by fun_prop)
  refine ContinuousAt.mul ?_ (continuous_besselJC ν).continuousAt
  have h := Complex.continuousAt_cpow_const_of_re_pos (slitPlane_or_zero hz)
    (by norm_num : (0:ℝ) < (1/2 : ℂ).re)
  exact h.comp (f := fun w : ℂ => (π : ℂ) * w / 2) (by fun_prop)

/-- The quadrant bound. -/
theorem asymErr_quadrant_bound {ν : ℕ} (hν : ν ≤ 1) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → 0 ≤ z.im → ‖z * asymErr ν z * cexp (I * z)‖ ≤ C := by
  obtain ⟨C1, hC10, hC1⟩ := asymErr_real_bound hν
  obtain ⟨C2, hC2⟩ := asymErr_imag_bound hν
  refine ⟨max C1 C2, fun z hre him => ?_⟩
  have hd : DiffContOnCl ℂ (fun z => z * asymErr ν z * cexp (I * z)) (Ioi 0 ×ℂ Ioi 0) := by
    refine ⟨fun w hw => ?_, ?_⟩
    · have hw' : 0 < w.re := hw.1
      exact ((differentiableAt_id.mul (differentiableAt_asymErr ν hw')).mul
        (by fun_prop)).differentiableWithinAt
    · intro w hw
      have hw2 : w ∈ closure (Ioi (0:ℝ)) ×ℂ closure (Ioi 0) := by rwa [← closure_reProdIm]
      rw [closure_Ioi] at hw2
      have hw' : 0 ≤ w.re := hw2.1
      exact ((continuousAt_id.mul (continuousAt_asymErr ν hw')).mul
        (by fun_prop)).continuousWithinAt
  have hgrowth : ∃ c < (2:ℝ), ∃ B, (fun z => z * asymErr ν z * cexp (I * z)) =O[Bornology.cobounded ℂ ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)]
      fun z => Real.exp (B * ‖z‖ ^ c) := by
    refine ⟨1, by norm_num, 4, ?_⟩
    refine Asymptotics.IsBigO.of_bound 2 (Eventually.of_forall fun w => ?_)
    have h := norm_asymErr_le hν w
    have him' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    have hn := norm_nonneg w
    have h1 : ‖w‖ ≤ Real.exp ‖w‖ := by linarith [Real.add_one_le_exp ‖w‖]
    have h2 : Real.sqrt (π * ‖w‖ / 2) ≤ Real.exp ‖w‖ := by
      calc Real.sqrt (π * ‖w‖ / 2) ≤ ‖w‖ + 1 := by
            rw [Real.sqrt_le_left (by positivity)]; nlinarith [Real.pi_lt_d2]
        _ ≤ Real.exp ‖w‖ := Real.add_one_le_exp _
    have h3 : ‖cexp (I * w)‖ ≤ Real.exp ‖w‖ := by
      rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_sub]
      linarith [neg_abs_le w.im]
    have h4 : Real.exp |w.im| ≤ Real.exp ‖w‖ := Real.exp_le_exp.mpr him'
    have h5 : 1 ≤ Real.exp ‖w‖ := Real.one_le_exp hn
    simp only [Real.rpow_one, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hE : ‖asymErr ν w‖ ≤ 2 * Real.exp ‖w‖ * Real.exp ‖w‖ := by
      calc ‖asymErr ν w‖ ≤ (Real.sqrt (π * ‖w‖ / 2) + 1) * Real.exp |w.im| := h
        _ ≤ (Real.exp ‖w‖ + Real.exp ‖w‖) * Real.exp ‖w‖ := by gcongr
        _ = _ := by ring
    have e4 : Real.exp (4 * ‖w‖) = Real.exp ‖w‖ ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [e4]
    have hx := Real.exp_pos ‖w‖
    calc ‖w‖ * ‖asymErr ν w‖ * ‖cexp (I * w)‖
        ≤ Real.exp ‖w‖ * (2 * Real.exp ‖w‖ * Real.exp ‖w‖) * Real.exp ‖w‖ := by gcongr
      _ = 2 * Real.exp ‖w‖ ^ 4 := by ring
  refine PhragmenLindelof.quadrant_I (f := fun z => z * asymErr ν z * cexp (I * z)) hd hgrowth
    (fun x hx => ?_) (fun y hy => ?_) hre him
  · have : ‖cexp (I * (x:ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
    rw [norm_mul, this, mul_one]
    exact (hC1 x hx).trans (le_max_left _ _)
  · exact (hC2 y hy).trans (le_max_right _ _)

/-- Complex conjugation symmetry of `J_ν`. -/
lemma besselJC_conj (ν : ℕ) (z : ℂ) : besselJC ν ((starRingEnd ℂ) z) = (starRingEnd ℂ) (besselJC ν z) := by
  unfold besselJC
  rw [Complex.conj_tsum]
  congr 1; funext m
  simp [map_div₀, map_mul, map_pow, map_ofNat]

lemma asymErr_conj (ν : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    asymErr ν ((starRingEnd ℂ) z) = (starRingEnd ℂ) (asymErr ν z) := by
  unfold asymErr
  have harg : ((π : ℂ) * z / 2).arg ≠ π := by
    intro h
    have := Complex.arg_eq_pi_iff.mp h
    have hre : ((π : ℂ) * z / 2).re = π * z.re / 2 := by simp
    rw [hre] at this
    have : 0 ≤ π * z.re / 2 := by positivity
    linarith [this]
  have hc := Complex.cpow_conj ((π : ℂ) * z / 2) (1 / 2) harg
  have h12 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by simp [map_ofNat]
  rw [h12] at hc
  have hconj : (starRingEnd ℂ) ((π : ℂ) * z / 2) = (π : ℂ) * (starRingEnd ℂ) z / 2 := by
    simp [map_div₀, map_ofNat]
  rw [hconj] at hc
  rw [map_sub, map_mul, besselJC_conj, ← Complex.cos_conj]
  have : (starRingEnd ℂ) (((π : ℂ) * (starRingEnd ℂ) z / 2) ^ (1 / 2 : ℂ)) =
      ((π : ℂ) * z / 2) ^ (1 / 2 : ℂ) := by
    rw [hc]
  rw [← this, Complex.conj_conj]
  congr 2
  rw [map_sub, map_sub, map_div₀, map_div₀, map_mul, Complex.conj_ofReal, map_natCast, map_ofNat,
    map_ofNat]

/-- **External theorem E4 (DLMF 10.17.3 with remainder), proved** in the form
`ExtAsymptotic`. -/
theorem extAsymptotic_holds : ExtAsymptotic := by
  intro ν hν
  obtain ⟨C, hC⟩ := asymErr_quadrant_bound hν
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 le_rfl le_rfl)
  refine ⟨C + 1, 1, by linarith, one_pos, fun ζ hζ harg => ?_⟩
  have hre : 0 ≤ ζ.re := Complex.abs_arg_le_pi_div_two_iff.mp harg
  have hζ0 : 0 < ‖ζ‖ := by linarith
  -- reduce to the first quadrant
  have key : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ w.im → 0 < ‖w‖ →
      ‖asymErr ν w‖ ≤ C * Real.exp |w.im| / ‖w‖ := by
    intro w hwr hwi hw0
    have h := hC w hwr hwi
    have hexp : ‖cexp (I * w)‖ = Real.exp (-w.im) := by
      rw [Complex.norm_exp]; congr 1; simp
    rw [norm_mul, norm_mul, hexp] at h
    rw [abs_of_nonneg hwi, le_div_iff₀ hw0]
    have he : Real.exp (-w.im) * Real.exp w.im = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos w.im).le
    calc ‖asymErr ν w‖ * ‖w‖ = ‖w‖ * ‖asymErr ν w‖ * (Real.exp (-w.im) * Real.exp w.im) := by
          rw [he]; ring
      _ = ‖w‖ * ‖asymErr ν w‖ * Real.exp (-w.im) * Real.exp w.im := by ring
      _ ≤ C * Real.exp w.im := this
  have hmain : ‖asymErr ν ζ‖ ≤ C * Real.exp |ζ.im| / ‖ζ‖ := by
    rcases le_or_gt 0 ζ.im with him | him
    · exact key ζ hre him hζ0
    · have h := key ((starRingEnd ℂ) ζ) (by simpa using hre) (by simp; linarith)
        (by simpa using hζ0)
      rw [asymErr_conj ν hre, Complex.norm_conj, Complex.conj_im, abs_neg, Complex.norm_conj] at h
      exact h
  have : C * Real.exp |ζ.im| / ‖ζ‖ ≤ (C + 1) * Real.exp |ζ.im| / ‖ζ‖ := by
    gcongr; linarith
  exact hmain.trans this

end Buckling
end
end ChunkedSource029
/- END SOURCE 029 -/

/- BEGIN SOURCE 030: RequestProject/Bessel/Zeros.lean -/
section ChunkedSource030

/-!
# Bessel equations, separation of zeros, and certified root intervals

* Bessel equations for `J₀` and `J₁` (part of Lemma 2.5),
* positivity of `J₁` near the origin,
* a Sturm comparison lemma and Lemma 3.3 (separation of consecutive positive zeros of
  `J₁` by more than `π`),
* Lemma 3.7 (certified root intervals).
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-! ### Derivative identities -/

lemma besselJ_two_eq (x : ℝ) (hx : x ≠ 0) : besselJ 2 x = 2 * besselJ 1 x / x - besselJ 0 x := by
  have h := besselJ_recurrence 0 x
  field_simp
  push_cast at h
  linarith

lemma besselJ_three_eq (x : ℝ) (hx : x ≠ 0) :
    besselJ 3 x = 4 * besselJ 2 x / x - besselJ 1 x := by
  have h := besselJ_recurrence 1 x
  field_simp
  push_cast at h
  linarith

/-- `J₁' = J₀ - J₁/x` for `x ≠ 0`. -/
lemma hasDerivAt_besselJ_one (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (besselJ 1) (besselJ 0 x - besselJ 1 x / x) x := by
  convert hasDerivAt_besselJ_succ 0 x using 1
  rw [besselJ_two_eq x hx]; field_simp; ring

/-- The derivative of `J₁'`: `J₁'' = -J₁'/x - (1 - 1/x²) J₁` for `x ≠ 0`. -/
lemma hasDerivAt_deriv_besselJ_one (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (deriv (besselJ 1))
      (-(besselJ 0 x - besselJ 1 x / x) / x - (1 - 1 / x ^ 2) * besselJ 1 x) x := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, deriv_besselJ_succ 0]
  have h0 := hasDerivAt_besselJ_zero x
  have h2 := hasDerivAt_besselJ_succ 1 x
  convert (h0.sub h2).div_const 2 using 1
  rw [besselJ_three_eq x hx, besselJ_two_eq x hx]
  field_simp
  ring

/-! ### Positivity of `J₁` near the origin -/

lemma besselPartialR_one_one (x : ℝ) : besselPartialR 1 1 x = x / 2 - x ^ 3 / 16 := by
  simp [besselPartialR, Finset.sum_range_succ]
  ring

/-- `J₁(r) > r/2 - r³/16 ≥ 0` for `0 < r ≤ 2.8`. -/
lemma besselJ_one_pos_small (r : ℝ) (hr0 : 0 < r) (hr : r ≤ 28 / 10) : 0 < besselJ 1 r := by
  have h := besselJ_tail_general 1 1 r hr0 (by push_cast; nlinarith)
  rw [besselPartialR_one_one] at h
  norm_num at h
  have : 0 ≤ r / 2 - r ^ 3 / 16 := by
    have : r ^ 2 ≤ 8 := by nlinarith
    nlinarith
  linarith [h.1]

/-! ### A Sturm comparison lemma -/

/-- If `y'' = -Q y` on `[a,b]` with `Q < 1`, `y(a) = y(b) = 0` and `y ≠ 0` on `(a,b)`,
then `b - a > π`. -/
theorem sturm_gap {y y' Q : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hy : ∀ r ∈ Icc a b, HasDerivAt y (y' r) r)
    (hy' : ∀ r ∈ Icc a b, HasDerivAt y' (-(Q r) * y r) r)
    (hQ : ∀ r ∈ Ioo a b, Q r < 1) (ha : y a = 0) (hb : y b = 0)
    (hne : ∀ r ∈ Ioo a b, y r ≠ 0) : π < b - a := by
  by_contra hcon
  push_neg at hcon
  set ω := π / (b - a) with hω
  have hba : 0 < b - a := by linarith
  have hω1 : 1 ≤ ω := by rw [hω, le_div_iff₀ hba]; linarith
  set w : ℝ → ℝ := fun r => Real.sin (ω * (r - a)) with hw
  set w' : ℝ → ℝ := fun r => ω * Real.cos (ω * (r - a)) with hw'
  have hwd : ∀ r, HasDerivAt w (w' r) r := by
    intro r
    have := ((hasDerivAt_id r).sub_const a).const_mul ω |>.sin
    simp only [hw, hw']
    convert! this using 1 <;> try simp only [id_eq, mul_one] <;> ring
  have hwd' : ∀ r, HasDerivAt w' (-(ω ^ 2) * w r) r := by
    intro r
    have := (((hasDerivAt_id r).sub_const a).const_mul ω |>.cos).const_mul ω
    simp only [hw, hw']
    convert! this using 1 <;> try simp only [id_eq, mul_one] <;> ring
  have hwpos : ∀ r ∈ Ioo a b, 0 < w r := by
    intro r hr
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact mul_pos (by linarith) (by linarith [hr.1])
    · have : ω * (r - a) < ω * (b - a) := by
        apply mul_lt_mul_of_pos_left (by linarith [hr.2]) (by linarith)
      have h2 : ω * (b - a) = π := by rw [hω]; field_simp
      linarith
  set W : ℝ → ℝ := fun r => y' r * w r - y r * w' r with hW
  have hWd : ∀ r ∈ Icc a b, HasDerivAt W ((ω ^ 2 - Q r) * y r * w r) r := by
    intro r hr
    have := ((hy' r hr).mul (hwd r)).sub ((hy r hr).mul (hwd' r))
    simp only [hW]
    convert this using 1; ring
  have hWa : W a = 0 := by simp [hW, hw, ha]
  have hWb : W b = 0 := by
    simp only [hW, hw, hb, zero_mul, sub_zero]
    have h2 : ω * (b - a) = π := by rw [hω]; field_simp
    rw [h2, Real.sin_pi, mul_zero]
  have hcont : ContinuousOn y (Icc a b) := fun r hr => (hy r hr).continuousAt.continuousWithinAt
  -- `y` has a constant sign on `(a,b)`
  have hsign : (∀ r ∈ Ioo a b, 0 < y r) ∨ (∀ r ∈ Ioo a b, y r < 0) := by
    by_contra hns
    push_neg at hns
    obtain ⟨⟨r1, hr1, hr1'⟩, ⟨r2, hr2, hr2'⟩⟩ := hns
    have hr1' : y r1 < 0 := lt_of_le_of_ne hr1' (hne r1 hr1)
    have hr2' : 0 < y r2 := lt_of_le_of_ne hr2' (hne r2 hr2).symm
    rcases lt_or_gt_of_ne (show r1 ≠ r2 by rintro rfl; linarith) with h | h
    · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo h.le (hcont.mono
        (Icc_subset_Icc hr1.1.le hr2.2.le)) ⟨hr1', hr2'⟩
      exact hne c ⟨hr1.1.trans hc.1, hc.2.trans hr2.2⟩ hc0
    · obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' h.le (hcont.mono
        (Icc_subset_Icc hr2.1.le hr1.2.le)) ⟨hr1', hr2'⟩
      exact hne c ⟨hr2.1.trans hc.1, hc.2.trans hr1.2⟩ hc0
  have hWc : ContinuousOn W (Icc a b) := fun r hr => (hWd r hr).continuousAt.continuousWithinAt
  rcases hsign with hpos | hneg
  · have hmono : StrictMonoOn W (Icc a b) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc a b) hWc
      intro r hr
      rw [interior_Icc] at hr
      rw [(hWd r (Ioo_subset_Icc_self hr)).deriv]
      have := hQ r hr
      have := hpos r hr
      have := hwpos r hr
      have : 0 < ω ^ 2 - Q r := by nlinarith
      positivity
    have := hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
    linarith
  · have hmono : StrictAntiOn W (Icc a b) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc a b) hWc
      intro r hr
      rw [interior_Icc] at hr
      rw [(hWd r (Ioo_subset_Icc_self hr)).deriv]
      have := hQ r hr
      have := hneg r hr
      have := hwpos r hr
      have : 0 < ω ^ 2 - Q r := by nlinarith
      have : (ω ^ 2 - Q r) * y r < 0 := mul_neg_of_pos_of_neg this (hneg r hr)
      exact mul_neg_of_neg_of_pos this (hwpos r hr)
    have := hmono (left_mem_Icc.mpr hab.le) (right_mem_Icc.mpr hab.le) hab
    linarith

/-! ### The Liouville normal form `y = √r J₁` -/

/-- `y(r) = √r J₁(r)` satisfies `y'' + (1 - 3/(4r²)) y = 0` for `r > 0`. -/
lemma sqrt_besselJ_one_ode (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s => Real.sqrt s * besselJ 1 s)
        (besselJ 1 r / (2 * Real.sqrt r) + Real.sqrt r * (besselJ 0 r - besselJ 1 r / r)) r ∧
    HasDerivAt (fun s => besselJ 1 s / (2 * Real.sqrt s) + Real.sqrt s * (besselJ 0 s - besselJ 1 s / s))
        (-(1 - 3 / (4 * r ^ 2)) * (Real.sqrt r * besselJ 1 r)) r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hsd : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt r)) r := Real.hasDerivAt_sqrt hr.ne'
  have hJ1 := hasDerivAt_besselJ_one r hr.ne'
  have hJ0 := hasDerivAt_besselJ_zero r
  constructor
  · convert hsd.mul hJ1 using 1; ring
  · have e1 := hJ1.div ((hsd.const_mul 2)) (by positivity)
    have e2 := hsd.mul ((hJ0.sub (hJ1.div (hasDerivAt_id r) hr.ne')))
    convert! e1.fun_add e2 using 1
      <;> try simp only [Pi.sub_apply, Pi.div_apply, id_eq]
      <;> field_simp
      <;> try rw [show Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 by ring, hsq]
      <;> ring

/-! ### Separation of consecutive zeros of `J₁` (Lemma 3.3) -/

/-- Under E1, every positive zero of `J₁` is simple-enumerated; consecutive positive zeros
of `J₁` are separated by more than `π`. -/
theorem besselZero_one_gap (hZ : ExtZeros) (m : ℕ) (hm : 1 ≤ m) :
    π < besselZero 1 (m + 1) - besselZero 1 m := by
  obtain ⟨hmono, -, hzero, hall, -⟩ := hZ 1 (by norm_num)
  set a := besselZero 1 m
  set b := besselZero 1 (m + 1)
  have hab : a < b := hmono (Nat.lt_succ_self m)
  have ha0 : 0 < a := by
    have := hmono (show 0 < m by omega); simpa [besselZero] using this
  have hpos : ∀ r ∈ Icc a b, 0 < r := fun r hr => ha0.trans_le hr.1
  refine sturm_gap (y := fun s => Real.sqrt s * besselJ 1 s)
    (y' := fun s => besselJ 1 s / (2 * Real.sqrt s) + Real.sqrt s * (besselJ 0 s - besselJ 1 s / s))
    (Q := fun s => 1 - 3 / (4 * s ^ 2)) hab
    (fun r hr => (sqrt_besselJ_one_ode r (hpos r hr)).1)
    (fun r hr => (sqrt_besselJ_one_ode r (hpos r hr)).2) ?_ ?_ ?_ ?_
  · intro r hr
    have : 0 < r := hpos r (Ioo_subset_Icc_self hr)
    have : 0 < 3 / (4 * r ^ 2) := by positivity
    linarith
  · simp [(hzero m hm).1, a]
  · simp [(hzero (m + 1) (by omega)).1, b]
  · intro r hr hr0
    have hr0' : 0 < r := hpos r (Ioo_subset_Icc_self hr)
    have hJ : besselJ 1 r = 0 := by
      rcases mul_eq_zero.mp hr0 with h | h
      · exact absurd h (Real.sqrt_pos.mpr hr0').ne'
      · exact h
    obtain ⟨k, hk1, hk⟩ := hall r hr0' hJ
    have h1 : m < k := hmono.lt_iff_lt.mp (hk ▸ hr.1)
    have h2 : k < m + 1 := hmono.lt_iff_lt.mp (hk ▸ hr.2)
    omega

/-- Lemma 3.3 for arbitrary distinct enumerated zeros. -/
theorem besselZero_one_sep (hZ : ExtZeros) (m n : ℕ) (hm : 1 ≤ m) (hmn : m < n) :
    (n - m : ℕ) * π < besselZero 1 n - besselZero 1 m := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp hmn with h | h
    · have := ih h
      have hg := besselZero_one_gap hZ n (by omega)
      have : ((n + 1 - m : ℕ) : ℝ) = (n - m : ℕ) + 1 := by
        rw [show n + 1 - m = (n - m) + 1 by omega]; push_cast; ring
      rw [this]; linarith
    · subst h
      have hg := besselZero_one_gap hZ m hm
      simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
      exact hg

/-! ### Certified root intervals (Lemma 3.7) -/

/-- **Lemma 3.7 (certified root intervals).**
`q ∈ (2.40482, 2.40483)`, `k ∈ (3.83170, 3.83171)`, `q₂ ∈ (5.5200, 5.5202)`,
`κ₂ ∈ (7.015, 7.016)` and `κ₃ ∈ (10.173, 10.174)`. -/
theorem root_boxes (hZ : ExtZeros) :
    (240482 / 100000 : ℝ) < jq ∧ jq < 240483 / 100000 ∧
    (383170 / 100000 : ℝ) < jk ∧ jk < 383171 / 100000 ∧
    (55200 / 10000 : ℝ) < besselZero 0 2 ∧ besselZero 0 2 < 55202 / 10000 ∧
    (7015 / 1000 : ℝ) < besselZero 1 2 ∧ besselZero 1 2 < 7016 / 1000 ∧
    (10173 / 1000 : ℝ) < besselZero 1 3 ∧ besselZero 1 3 < 10174 / 1000 := by
  obtain ⟨hmono1, -, hzero1, hall1, -⟩ := hZ 1 (by norm_num)
  obtain ⟨hmono0, -, hzero0, hall0, hinter0⟩ := hZ 0 (by norm_num)
  have hc0 := continuous_besselJ 0
  have hc1 := continuous_besselJ 1
  -- zeros of `J₁` in the three boxes
  obtain ⟨a1, ha1, ha1z⟩ : ∃ a1 ∈ Ioo (383170 / 100000 : ℝ) (383171 / 100000), besselJ 1 a1 = 0 :=
    intermediate_value_Ioo' (by norm_num) hc1.continuousOn
      ⟨by linarith [besselJ_bounds_row4.2], by linarith [besselJ_bounds_row3.1]⟩
  obtain ⟨a2, ha2, ha2z⟩ : ∃ a2 ∈ Ioo (7015 / 1000 : ℝ) (7016 / 1000), besselJ 1 a2 = 0 :=
    intermediate_value_Ioo (by norm_num) hc1.continuousOn
      ⟨by linarith [besselJ_bounds_row7.2], by linarith [besselJ_bounds_row8.1]⟩
  obtain ⟨a3, ha3, ha3z⟩ : ∃ a3 ∈ Ioo (10173 / 1000 : ℝ) (10174 / 1000), besselJ 1 a3 = 0 :=
    intermediate_value_Ioo' (by norm_num) hc1.continuousOn
      ⟨by linarith [besselJ_bounds_row10.2], by linarith [besselJ_bounds_row9.1]⟩
  obtain ⟨b1, hb1, hb1z⟩ : ∃ b1 ∈ Ioo (240482 / 100000 : ℝ) (240483 / 100000), besselJ 0 b1 = 0 :=
    intermediate_value_Ioo' (by norm_num) hc0.continuousOn
      ⟨by linarith [besselJ_bounds_row2.2], by linarith [besselJ_bounds_row1.1]⟩
  obtain ⟨b2, hb2, hb2z⟩ : ∃ b2 ∈ Ioo (55200 / 10000 : ℝ) (55202 / 10000), besselJ 0 b2 = 0 :=
    intermediate_value_Ioo (by norm_num) hc0.continuousOn
      ⟨by linarith [besselJ_bounds_row5.2], by linarith [besselJ_bounds_row6.1]⟩
  obtain ⟨m1, hm1, rfl⟩ := hall1 a1 (by linarith [ha1.1]) ha1z
  obtain ⟨m2, hm2, rfl⟩ := hall1 a2 (by linarith [ha2.1]) ha2z
  obtain ⟨m3, hm3, rfl⟩ := hall1 a3 (by linarith [ha3.1]) ha3z
  obtain ⟨n1, hn1, rfl⟩ := hall0 b1 (by linarith [hb1.1]) hb1z
  obtain ⟨n2, hn2, rfl⟩ := hall0 b2 (by linarith [hb2.1]) hb2z
  have hpi := Real.pi_gt_three
  -- `j_{1,1} > 2.8`
  have hj11 : (28 / 10 : ℝ) < besselZero 1 1 := by
    by_contra h
    push_neg at h
    have h0 : 0 < besselZero 1 1 := by
      have := hmono1 (show 0 < 1 by norm_num); simpa [besselZero] using this
    exact (besselJ_one_pos_small _ h0 h).ne' (hzero1 1 le_rfl).1
  -- `m1 = 1`
  have hm1e : m1 = 1 := by
    by_contra h
    have h2 : 1 < m1 := by omega
    have := besselZero_one_sep hZ 1 m1 le_rfl h2
    have : (1 : ℝ) ≤ ((m1 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ m1 - 1)
    nlinarith [ha1.2]
  subst hm1e
  -- `m2 = 2`
  have hm2e : m2 = 2 := by
    have h12 : 1 < m2 := hmono1.lt_iff_lt.mp (ha1.2.trans (by norm_num) |>.trans ha2.1)
    by_contra h
    have h3 : 1 < m2 - 1 := by omega
    have := besselZero_one_sep hZ 1 m2 le_rfl h12
    have : (2 : ℝ) ≤ ((m2 - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m2 - 1)
    nlinarith [ha1.1, ha2.2]
  subst hm2e
  have hm3e : m3 = 3 := by
    have h23 : 2 < m3 := hmono1.lt_iff_lt.mp (ha2.2.trans (by norm_num) |>.trans ha3.1)
    by_contra h
    have := besselZero_one_sep hZ 2 m3 (by norm_num) h23
    have : (2 : ℝ) ≤ ((m3 - 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 2 ≤ m3 - 2)
    nlinarith [ha2.1, ha3.2]
  subst hm3e
  -- interlacing for `J₀`
  have hI1 := hinter0 1 le_rfl
  have hI2 := hinter0 2 (by norm_num)
  have hn1e : n1 = 1 := by
    by_contra h
    have : besselZero 0 2 ≤ besselZero 0 n1 := hmono0.le_iff_le.mpr (by omega)
    linarith [hb1.2, ha1.1, hI1.2]
  subst hn1e
  have hn2e : n2 = 2 := by
    rcases lt_trichotomy n2 2 with h | h | h
    · have : n2 = 1 := by omega
      subst this; linarith [hb1.2, hb2.1]
    · exact h
    · have : besselZero 0 3 ≤ besselZero 0 n2 := hmono0.le_iff_le.mpr (by omega)
      linarith [hb2.2, ha2.1, hI2.2]
  subst hn2e
  exact ⟨hb1.1, hb1.2, ha1.1, ha1.2, hb2.1, hb2.2, ha2.1, ha2.2, ha3.1, ha3.2⟩

end Buckling
end
end ChunkedSource030
/- END SOURCE 030 -/

