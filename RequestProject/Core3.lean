module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/
public import RequestProject.Core2

/- CONDITIONAL, UNCOMPILED structural experiment. See README.md. -/

/- BEGIN SOURCE 061: RequestProject/Bessel/Product/MittagLeffler.lean -/
section ChunkedSource061

/-!
# Mittag-Leffler expansion of `J₀/J₁`

For `z ≠ 0` with `J₁(z) ≠ 0`,
`J₀(z)/J₁(z) - 2/z = ∑_{n ≥ 1} 2z/(z² - κ_n²)`.

Proof: apply the residue theorem to `h(ζ) = 2z J₀(ζ) / (J₁(ζ)(ζ² - z²))` on the circles
`|ζ| = R_N = (N + 3/4)π`.  The poles inside are `0` (residue `-4/z`), `±z` (residue
`J₀(z)/J₁(z)` each) and `±κ_n` (residue `2z/(κ_n² - z²)` each); all zeros of `J₁` are real
(`besselJC_one_eq_zero'`).  On the circles `|J₀/J₁|` is bounded (large-argument asymptotics),
so the contour integral is `O(1/R_N)`.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set Metric

namespace Buckling

/-- A simple pole: if `G(a) = 0 ≠ G'(a)`, then `F/G - (F(a)/G'(a))/(z - a)` is bounded near
`a`. -/
lemma bdd_simple_pole {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    {a : ℂ} (hGa : G a = 0) (hG'a : deriv G a ≠ 0) :
    ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖F z / G z - F a / deriv G a / (z - a) ^ 1‖ ≤ C := by
  have hu : (univ : Set ℂ) ∈ 𝓝 a := univ_mem
  have hf1 : DifferentiableOn ℂ (dslope F a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hF.differentiableOn
  have hg1 : DifferentiableOn ℂ (dslope G a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hG.differentiableOn
  have hg2 : DifferentiableOn ℂ (dslope (dslope G a) a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hg1
  have hg1a : dslope G a a ≠ 0 := by rwa [dslope_same]
  have hg1c : ContinuousAt (dslope G a) a := (hg1.differentiableAt hu).continuousAt
  have hcont : ContinuousAt (fun z => (dslope F a z * dslope G a a -
      F a * dslope (dslope G a) a z) / (dslope G a z * dslope G a a)) a :=
    (((hf1.differentiableAt hu).continuousAt.mul continuousAt_const).sub
      (continuousAt_const.mul (hg2.differentiableAt hu).continuousAt)).div
      (hg1c.mul continuousAt_const) (mul_ne_zero hg1a hg1a)
  obtain ⟨C, hC⟩ := bdd_of_continuousAt hcont
  refine ⟨C, ?_⟩
  have hne : ∀ᶠ z in 𝓝[≠] a, dslope G a z ≠ 0 :=
    (hg1c.eventually_ne hg1a).filter_mono nhdsWithin_le_nhds
  filter_upwards [hC, self_mem_nhdsWithin, hne] with z hz hza hgz
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have e1 := sub_smul_dslope F a z
  have e3 := sub_smul_dslope G a z
  have e4 := sub_smul_dslope (dslope G a) a z
  simp only [smul_eq_mul, hGa, sub_zero] at e1 e3 e4
  have hd : deriv G a = dslope G a a := (dslope_same G a).symm
  have : F z / G z - F a / deriv G a / (z - a) ^ 1 = (dslope F a z * dslope G a a -
      F a * dslope (dslope G a) a z) / (dslope G a z * dslope G a a) := by
    rw [hd, ← e3, pow_one]
    generalize dslope G a a = g at e4 hg1a ⊢
    generalize dslope (dslope G a) a z = g2 at e4 ⊢
    generalize dslope G a z = g1 at e4 hgz ⊢
    have hFz : F z = F a + (z - a) * dslope F a z := by linear_combination -e1
    rw [hFz]
    have key : (F a + (z - a) * dslope F a z) * g - F a * g1 =
        (z - a) * (dslope F a z * g - F a * g2) := by linear_combination (F a) * e4
    rw [div_div, div_sub_div _ _ (mul_ne_zero hza' hgz) (mul_ne_zero hg1a hza'),
      div_eq_div_iff (mul_ne_zero (mul_ne_zero hza' hgz) (mul_ne_zero hg1a hza'))
        (mul_ne_zero hgz hg1a)]
    linear_combination ((z - a) * g1 * g) * key
  rw [this]; exact hz

/-- The positive zeros of `J₁`, as complex numbers. -/
noncomputable def kc (n : ℕ) : ℂ := ((besselZero 1 (n + 1) : ℝ) : ℂ)

/-- The Mittag-Leffler terms. -/
noncomputable def mlTerm (z : ℂ) (n : ℕ) : ℂ := 2 * z / (z ^ 2 - kc n ^ 2)

/-- Numerator and denominator of the residue kernel. -/
noncomputable def mlF (z : ℂ) (ζ : ℂ) : ℂ := 2 * z * besselJC 0 ζ
noncomputable def mlG (z : ℂ) (ζ : ℂ) : ℂ := besselJC 1 ζ * (ζ ^ 2 - z ^ 2)

/-- Indices of the zeros `κ_{n+1} < R`. -/
noncomputable def mlT (R : ℝ) : Finset ℕ :=
  (Finset.range (⌈R⌉₊ + 1)).filter (fun n => besselZero 1 (n + 1) < R)

/-- The poles inside `|ζ| < R`. -/
noncomputable def mlS (z : ℂ) (R : ℝ) : Finset ℂ :=
  {0, z, -z} ∪ ((mlT R).image kc ∪ (mlT R).image (fun n => -kc n))

lemma kc_pos (n : ℕ) : 0 < besselZero 1 (n + 1) := besselZero_one_pos extZeros_holds n

lemma norm_kc (n : ℕ) : ‖kc n‖ = besselZero 1 (n + 1) := by
  rw [kc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kc_pos n)]

lemma besselJC_one_kc (n : ℕ) : besselJC 1 (kc n) = 0 := by
  rw [kc, besselJC_ofReal, ((extZeros_holds 1 le_rfl).2.2.1 (n + 1) (by omega)).1,
    Complex.ofReal_zero]

lemma besselJC_one_neg_kc (n : ℕ) : besselJC 1 (-kc n) = 0 := by
  rw [besselJC_neg, besselJC_one_kc, mul_zero]

lemma besselJC_zero_kc_ne (n : ℕ) : besselJC 0 (kc n) ≠ 0 := by
  rw [kc, besselJC_ofReal]
  exact_mod_cast besselJ_zero_besselZero_one_ne extZeros_holds (by omega)

lemma kc_ne_zero (n : ℕ) : kc n ≠ 0 := by
  rw [kc]; exact_mod_cast (kc_pos n).ne'

lemma kc_injective : Function.Injective kc := by
  intro m n h
  have h' : besselZero 1 (m + 1) = besselZero 1 (n + 1) := Complex.ofReal_injective h
  have := (extZeros_holds 1 le_rfl).1.injective h'
  omega

lemma hasDerivAt_mlG (z a : ℂ) :
    HasDerivAt (mlG z) (dJ1C a * (a ^ 2 - z ^ 2) + besselJC 1 a * (2 * a)) a := by
  have h := (hasDerivAt_besselJC_one a).fun_mul ((hasDerivAt_pow 2 a).sub_const (z ^ 2))
  simpa [mlG] using! h

lemma differentiable_mlF (z : ℂ) : Differentiable ℂ (mlF z) :=
  (differentiable_const _).mul (differentiable_besselJC 0)

lemma differentiable_mlG (z : ℂ) : Differentiable ℂ (mlG z) :=
  fun a => (hasDerivAt_mlG z a).differentiableAt

lemma dJ1C_zero : dJ1C 0 = 1 / 2 := by
  simp [dJ1C, besselJC_zero_arg]

lemma dJ1C_of_zero {a : ℂ} (ha : a ≠ 0) (h : besselJC 1 a = 0) : dJ1C a = besselJC 0 a := by
  have := mul_dJ1C a
  rw [h, sub_zero] at this
  exact mul_left_cancel₀ ha this

/-- The zeros of `mlG z`. -/
lemma mlG_eq_zero {z ζ : ℂ} (h : mlG z ζ = 0) :
    ζ = 0 ∨ ζ = z ∨ ζ = -z ∨ ∃ n, ζ = kc n ∨ ζ = -kc n := by
  rcases mul_eq_zero.mp h with h1 | h1
  · rcases besselJC_one_eq_zero' h1 with h2 | ⟨n, h2⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inr (Or.inr ⟨n, h2⟩))
  · have : ζ ^ 2 = z ^ 2 := by linear_combination h1
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Or.inl h2))

section Residues

variable {z : ℂ} (hz0 : z ≠ 0) (hz : besselJC 1 z ≠ 0)
include hz0 hz

lemma kc_sq_ne (n : ℕ) : kc n ^ 2 - z ^ 2 ≠ 0 := by
  intro h
  have : z ^ 2 = kc n ^ 2 := by linear_combination -h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h2 | h2
  · exact hz (h2 ▸ besselJC_one_kc n)
  · exact hz (h2 ▸ besselJC_one_neg_kc n)

/-- Residue data at the poles: `G(a) = 0`, `G'(a) ≠ 0`, and the value of `F(a)/G'(a)`. -/
lemma mlres_zero : mlG z 0 = 0 ∧ deriv (mlG z) 0 ≠ 0 ∧
    mlF z 0 / deriv (mlG z) 0 = -4 / z := by
  rw [(hasDerivAt_mlG z 0).deriv, dJ1C_zero]
  simp only [mlG, mlF, besselJC_zero_arg]
  norm_num
  refine ⟨hz0, ?_⟩
  field_simp
  ring

lemma mlres_z : mlG z z = 0 ∧ deriv (mlG z) z ≠ 0 ∧
    mlF z z / deriv (mlG z) z = besselJC 0 z / besselJC 1 z := by
  rw [(hasDerivAt_mlG z z).deriv]
  simp only [mlG, mlF, sub_self, mul_zero, zero_add, true_and]
  refine ⟨by simp [hz, hz0], ?_⟩
  field_simp

lemma mlres_negz : mlG z (-z) = 0 ∧ deriv (mlG z) (-z) ≠ 0 ∧
    mlF z (-z) / deriv (mlG z) (-z) = besselJC 0 z / besselJC 1 z := by
  rw [(hasDerivAt_mlG z (-z)).deriv]
  simp only [mlG, mlF, neg_sq, sub_self, mul_zero, zero_add, true_and, besselJC_neg]
  norm_num
  refine ⟨⟨hz, hz0⟩, ?_⟩
  field_simp

lemma mlres_kc (n : ℕ) : mlG z (kc n) = 0 ∧ deriv (mlG z) (kc n) ≠ 0 ∧
    mlF z (kc n) / deriv (mlG z) (kc n) = -mlTerm z n := by
  rw [(hasDerivAt_mlG z (kc n)).deriv, dJ1C_of_zero (kc_ne_zero n) (besselJC_one_kc n)]
  simp only [mlG, mlF, mlTerm, besselJC_one_kc, zero_mul, add_zero, true_and]
  have h1 := besselJC_zero_kc_ne n
  have h2 := kc_sq_ne hz0 hz n
  have h3 : z ^ 2 - kc n ^ 2 ≠ 0 := by intro h; apply h2; linear_combination -h
  refine ⟨mul_ne_zero h1 h2, ?_⟩
  field_simp
  ring

lemma mlres_negkc (n : ℕ) : mlG z (-kc n) = 0 ∧ deriv (mlG z) (-kc n) ≠ 0 ∧
    mlF z (-kc n) / deriv (mlG z) (-kc n) = -mlTerm z n := by
  have hne : -kc n ≠ 0 := neg_ne_zero.mpr (kc_ne_zero n)
  rw [(hasDerivAt_mlG z (-kc n)).deriv, dJ1C_of_zero hne (besselJC_one_neg_kc n),
    besselJC_one_neg_kc]
  simp only [mlG, mlF, mlTerm, besselJC_one_neg_kc, zero_mul, add_zero, true_and, neg_sq]
  rw [besselJC_neg 0]
  simp only [pow_zero, one_mul]
  have h1 := besselJC_zero_kc_ne n
  have h2 := kc_sq_ne hz0 hz n
  have h3 : z ^ 2 - kc n ^ 2 ≠ 0 := by intro h; apply h2; linear_combination -h
  refine ⟨mul_ne_zero h1 h2, ?_⟩
  field_simp
  ring

lemma mlres_mem {R : ℝ} {a : ℂ} (ha : a ∈ mlS z R) :
    mlG z a = 0 ∧ deriv (mlG z) a ≠ 0 := by
  simp only [mlS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_image] at ha
  rcases ha with (rfl | rfl | rfl) | (⟨n, -, rfl⟩ | ⟨n, -, rfl⟩)
  · exact ⟨(mlres_zero hz0 hz).1, (mlres_zero hz0 hz).2.1⟩
  · exact ⟨(mlres_z hz0 hz).1, (mlres_z hz0 hz).2.1⟩
  · exact ⟨(mlres_negz hz0 hz).1, (mlres_negz hz0 hz).2.1⟩
  · exact ⟨(mlres_kc hz0 hz n).1, (mlres_kc hz0 hz n).2.1⟩
  · exact ⟨(mlres_negkc hz0 hz n).1, (mlres_negkc hz0 hz n).2.1⟩

/-- The sum of the residues. -/
lemma mlres_sum (R : ℝ) :
    ∑ a ∈ mlS z R, mlF z a / deriv (mlG z) a =
      -4 / z + 2 * (besselJC 0 z / besselJC 1 z) - 2 * ∑ n ∈ mlT R, mlTerm z n := by
  have hz' : besselJC 1 (-z) ≠ 0 := by rw [besselJC_neg]; simpa using hz
  have hdisj1 : Disjoint ({0, z, -z} : Finset ℂ)
      ((mlT R).image kc ∪ (mlT R).image (fun n => -kc n)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_union, Finset.mem_image] at hb
    have hJ : besselJC 1 a = 0 ∧ a ≠ 0 := by
      rcases hb with ⟨n, -, rfl⟩ | ⟨n, -, rfl⟩
      · exact ⟨besselJC_one_kc n, kc_ne_zero n⟩
      · exact ⟨besselJC_one_neg_kc n, neg_ne_zero.mpr (kc_ne_zero n)⟩
    rcases ha with rfl | rfl | rfl
    · exact hJ.2 rfl
    · exact hz hJ.1
    · exact hz' hJ.1
  have hdisj2 : Disjoint ((mlT R).image kc) ((mlT R).image (fun n => -kc n)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_image] at ha hb
    obtain ⟨m, -, rfl⟩ := ha
    obtain ⟨n, -, hn⟩ := hb
    have := congrArg Complex.re hn
    simp only [kc, Complex.neg_re, Complex.ofReal_re] at this
    linarith [kc_pos m, kc_pos n]
  have h0z : (0 : ℂ) ∉ ({z, -z} : Finset ℂ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hz0.symm, fun h => hz0 (neg_eq_zero.mp h.symm)⟩
  have hzz : z ∉ ({-z} : Finset ℂ) := by
    simp only [Finset.mem_singleton]
    intro h
    apply hz0
    linear_combination h / 2
  rw [mlS, Finset.sum_union hdisj1, Finset.sum_insert h0z, Finset.sum_insert hzz,
    Finset.sum_singleton, Finset.sum_union hdisj2,
    Finset.sum_image (fun m _ n _ h => kc_injective h),
    Finset.sum_image (fun m _ n _ h => kc_injective (neg_injective h)),
    (mlres_zero hz0 hz).2.2, (mlres_z hz0 hz).2.2, (mlres_negz hz0 hz).2.2]
  simp only [fun n => (mlres_kc hz0 hz n).2.2, fun n => (mlres_negkc hz0 hz n).2.2,
    Finset.sum_neg_distrib]
  ring

/-- The residue theorem for the kernel on a circle free of zeros of `J₁`. -/
lemma ml_circle {R : ℝ} (hR : ‖z‖ < R) (hcirc : ∀ ζ : ℂ, ‖ζ‖ = R → besselJC 1 ζ ≠ 0) :
    (∮ ζ in C(0, R), mlF z ζ / mlG z ζ) =
      2 * π * I * (-4 / z + 2 * (besselJC 0 z / besselJC 1 z) - 2 * ∑ n ∈ mlT R, mlTerm z n) := by
  have hR0 : 0 < R := (norm_nonneg z).trans_lt hR
  set S := mlS z R
  -- all poles lie inside
  have hS : (S : Set ℂ) ⊆ ball 0 R := by
    intro a ha
    simp only [S, mlS, Finset.coe_union, Finset.coe_insert, Finset.coe_singleton,
      Finset.coe_image, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_image, Finset.mem_coe] at ha
    rw [mem_ball, dist_zero_right]
    rcases ha with (rfl | rfl | rfl) | (⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩)
    · simpa using hR0
    · exact hR
    · rwa [norm_neg]
    · rw [norm_kc]; exact (Finset.mem_filter.mp hn).2
    · rw [norm_neg, norm_kc]; exact (Finset.mem_filter.mp hn).2
  -- all zeros of `G` inside the disk are poles
  have hzeros : ∀ ζ : ℂ, ‖ζ‖ < R → mlG z ζ = 0 → ζ ∈ S := by
    intro ζ hζ h
    have hmemT : ∀ n, besselZero 1 (n + 1) < R → n ∈ mlT R := by
      intro n hn
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hn⟩
      have h1 := besselZero_one_gt extZeros_holds n
      have h2 : (n : ℝ) < ⌈R⌉₊ := by
        have := Nat.le_ceil R
        push_cast at h1
        nlinarith [Real.pi_gt_three]
      exact_mod_cast (show (n : ℝ) < ⌈R⌉₊ + 1 by linarith)
    simp only [S, mlS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_image]
    rcases mlG_eq_zero h with h0 | h0 | h0 | ⟨n, h0 | h0⟩
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr (Or.inl h0))
    · exact Or.inl (Or.inr (Or.inr h0))
    · subst h0; rw [norm_kc] at hζ
      exact Or.inr (Or.inl ⟨n, hmemT n hζ, rfl⟩)
    · subst h0; rw [norm_neg, norm_kc] at hζ
      exact Or.inr (Or.inr ⟨n, hmemT n hζ, rfl⟩)
  set U : Set ℂ := ball 0 R ∪ {ζ | mlG z ζ ≠ 0}
  have hU : IsOpen U :=
    isOpen_ball.union (isOpen_ne_fun (differentiable_mlG z).continuous continuous_const)
  have hRU : closedBall (0 : ℂ) R ⊆ U := by
    intro ζ hζ
    rw [mem_closedBall, dist_zero_right] at hζ
    rcases hζ.lt_or_eq with h | h
    · exact Or.inl (by rwa [mem_ball, dist_zero_right])
    · refine Or.inr ?_
      simp only [Set.mem_setOf_eq, mlG]
      refine mul_ne_zero (hcirc ζ h) ?_
      intro h2
      have : ζ ^ 2 = z ^ 2 := by linear_combination h2
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h3 | h3
      · rw [h3] at h; linarith
      · rw [h3, norm_neg] at h; linarith
  have hd : DifferentiableOn ℂ (fun ζ => mlF z ζ / mlG z ζ) (U \ S) := by
    intro ζ hζ
    have hG : mlG z ζ ≠ 0 := by
      rcases hζ.1 with h | h
      · intro h0
        rw [mem_ball, dist_zero_right] at h
        exact hζ.2 (hzeros ζ h h0)
      · exact h
    exact (((differentiable_mlF z) ζ).div ((differentiable_mlG z) ζ) hG).differentiableWithinAt
  have hb : ∀ a ∈ S, ∃ C, ∀ᶠ ζ in 𝓝[≠] a, ‖mlF z ζ / mlG z ζ -
      princPart 1 (fun b _ => mlF z b / deriv (mlG z) b) a ζ‖ ≤ C := by
    intro a ha
    obtain ⟨h1, h2⟩ := mlres_mem hz0 hz ha
    obtain ⟨C, hC⟩ := bdd_simple_pole (differentiable_mlF z) (differentiable_mlG z) h1 h2
    refine ⟨C, ?_⟩
    simpa [princPart] using hC
  rw [circleIntegral_eq_residues hR0 hU hRU S hS _ 1 one_pos _ hd hb, mlres_sum hz0 hz]

end Residues

/-- **Mittag-Leffler expansion.** -/
theorem hasSum_mlTerm {z : ℂ} (hz0 : z ≠ 0) (hz : besselJC 1 z ≠ 0) :
    HasSum (mlTerm z) (besselJC 0 z / besselJC 1 z - 2 / z) := by
  obtain ⟨c, N1, hc, hlow⟩ := besselJC_one_lower extAsymptotic_holds
  obtain ⟨C0, R0, hC0, hR0, h0⟩ := besselJC_upper extAsymptotic_holds (ν := 0) (by norm_num)
  set K := C0 / c with hK
  have hK0 : 0 ≤ K := by positivity
  set L := besselJC 0 z / besselJC 1 z - 2 / z with hL
  set Rn : ℕ → ℝ := fun N => ((N : ℝ) + 3 / 4) * π with hRn
  have hRnN : ∀ N : ℕ, (N : ℝ) < Rn N := by
    intro N; simp only [hRn]; nlinarith [Real.pi_gt_three, Nat.cast_nonneg (α := ℝ) N]
  set A : ℕ → ℂ := fun N => ∑ n ∈ mlT (Rn N), mlTerm z n with hA
  set N2 := max (max N1 1) ⌈R0 + 2 * ‖z‖⌉₊
  -- the error bound
  have hbd : ∀ N ≥ N2, ‖A N - L‖ ≤ 2 * ‖z‖ * K / N := by
    intro N hN
    have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
    have hN1' : (1 : ℝ) ≤ N := by
      exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
    have hNR : R0 + 2 * ‖z‖ ≤ N := by
      have := Nat.le_ceil (R0 + 2 * ‖z‖)
      have h2 : (⌈R0 + 2 * ‖z‖⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
      linarith
    set R := Rn N with hR
    have hRN := hRnN N
    have hRpos : 0 < R := by linarith
    have hzR : 2 * ‖z‖ ≤ R := by linarith
    have hR0R : R0 ≤ R := by linarith [norm_nonneg z]
    have hcirc : ∀ ζ : ℂ, ‖ζ‖ = R → besselJC 1 ζ ≠ 0 := by
      intro ζ hζ
      have h := hlow N hN1 ζ hζ
      have hζ0 : 0 < ‖ζ‖ := by rw [hζ]; exact hRpos
      have : 0 < c * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ := by
        have := Real.sqrt_pos.mpr hζ0; positivity
      exact norm_pos_iff.mp (this.trans_le h)
    have hzR' : ‖z‖ < R := by
      rcases eq_or_lt_of_le (norm_nonneg z) with h | h
      · rw [← h]; exact hRpos
      · linarith
    have hint := ml_circle hz0 hz hzR' hcirc
    -- bound on the circle
    have hsph : ∀ ζ ∈ sphere (0 : ℂ) R, ‖mlF z ζ / mlG z ζ‖ ≤ 4 * ‖z‖ * K / R ^ 2 := by
      intro ζ hζ
      rw [mem_sphere, dist_zero_right] at hζ
      have hζ0 : 0 < ‖ζ‖ := by rw [hζ]; exact hRpos
      have hl := hlow N hN1 ζ hζ
      have hu := h0 ζ (by rw [hζ]; exact hR0R)
      have hJ1 : 0 < ‖besselJC 1 ζ‖ := norm_pos_iff.mpr (hcirc ζ hζ)
      have hJ0 : ‖besselJC 0 ζ‖ ≤ K * ‖besselJC 1 ζ‖ := by
        calc ‖besselJC 0 ζ‖ ≤ C0 * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ := hu
          _ = K * (c * Real.exp |ζ.im| / Real.sqrt ‖ζ‖) := by
              rw [hK]; field_simp
          _ ≤ K * ‖besselJC 1 ζ‖ := mul_le_mul_of_nonneg_left hl hK0
      have hq : R ^ 2 / 2 ≤ ‖ζ ^ 2 - z ^ 2‖ := by
        have := norm_sub_norm_le (ζ ^ 2) (z ^ 2)
        rw [norm_pow, norm_pow, hζ] at this
        nlinarith [norm_nonneg z]
      have hq0 : 0 < ‖ζ ^ 2 - z ^ 2‖ := lt_of_lt_of_le (by positivity) hq
      simp only [mlF, mlG]
      rw [norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
        div_le_div_iff₀ (mul_pos hJ1 hq0) (by positivity)]
      calc 2 * ‖z‖ * ‖besselJC 0 ζ‖ * R ^ 2 ≤ 2 * ‖z‖ * (K * ‖besselJC 1 ζ‖) * R ^ 2 := by
            gcongr
        _ = 4 * ‖z‖ * K * (‖besselJC 1 ζ‖ * (R ^ 2 / 2)) := by ring
        _ ≤ 4 * ‖z‖ * K * (‖besselJC 1 ζ‖ * ‖ζ ^ 2 - z ^ 2‖) := by gcongr
    have hI := circleIntegral.norm_integral_le_of_norm_le_const hRpos.le hsph
    rw [hint] at hI
    have heq : 2 * ↑π * I * (-4 / z + 2 * (besselJC 0 z / besselJC 1 z) -
        2 * ∑ n ∈ mlT R, mlTerm z n) = (4 * π : ℂ) * I * (L - A N) := by
      simp only [hL, hA, hR]; ring
    rw [heq, norm_mul, norm_mul, Complex.norm_I, mul_one, norm_sub_rev] at hI
    have h4 : ‖(4 * π : ℂ)‖ = 4 * π := by
      rw [show (4 * π : ℂ) = ((4 * π : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [h4] at hI
    have hpi := Real.pi_pos
    have h5 : ‖A N - L‖ ≤ 2 * ‖z‖ * K / R := by
      rw [le_div_iff₀ hRpos]
      have : 2 * π * R * (4 * ‖z‖ * K / R ^ 2) = 4 * π * (2 * ‖z‖ * K / R) := by
        field_simp
      rw [this] at hI
      have := le_of_mul_le_mul_left hI (by positivity)
      rw [le_div_iff₀ hRpos] at this
      exact this
    calc ‖A N - L‖ ≤ 2 * ‖z‖ * K / R := h5
      _ ≤ 2 * ‖z‖ * K / N := by
          apply div_le_div_of_nonneg_left (by positivity) (by linarith) hRN.le
  have hAL : Tendsto A atTop (𝓝 L) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_
      (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖z‖ * K))
    exact eventually_atTop.mpr ⟨N2, hbd⟩
  -- summability
  have hsum : Summable (mlTerm z) := by
    refine Summable.of_norm_bounded_eventually
      ((summable_inv_besselZero_sq extZeros_holds).mul_left (4 * ‖z‖)) ?_
    rw [Nat.cofinite_eq_atTop]
    refine eventually_atTop.mpr ⟨⌈2 * ‖z‖⌉₊, fun n hn => ?_⟩
    have hk := besselZero_one_gt extZeros_holds n
    have hkpos := kc_pos n
    have hn' : 2 * ‖z‖ ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hkz : 2 * ‖z‖ ≤ besselZero 1 (n + 1) := by
      push_cast at hk; nlinarith [Real.pi_gt_three]
    have hq : besselZero 1 (n + 1) ^ 2 / 2 ≤ ‖z ^ 2 - kc n ^ 2‖ := by
      have := norm_sub_norm_le (kc n ^ 2) (z ^ 2)
      rw [norm_pow, norm_pow, norm_kc, norm_sub_rev] at this
      nlinarith [norm_nonneg z]
    have hq0 : 0 < ‖z ^ 2 - kc n ^ 2‖ := lt_of_lt_of_le (by positivity) hq
    simp only [mlTerm]
    rw [norm_div, norm_mul, Complex.norm_ofNat, div_le_iff₀ hq0]
    calc 2 * ‖z‖ = 4 * ‖z‖ * (1 / besselZero 1 (n + 1) ^ 2) * (besselZero 1 (n + 1) ^ 2 / 2) := by
          field_simp; ring
      _ ≤ _ := by gcongr
  -- the index sets exhaust `ℕ`
  have hT : Tendsto (fun N => mlT (Rn N)) atTop atTop := by
    apply tendsto_atTop_finset_of_monotone
    · intro N M hNM n hn
      have hRm : Rn N ≤ Rn M := by
        simp only [hRn]; gcongr
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨?_, h2.trans_le hRm⟩
      rw [Finset.mem_range] at h1 ⊢
      have := Nat.ceil_mono hRm
      omega
    · intro n
      refine ⟨⌈besselZero 1 (n + 1)⌉₊, ?_⟩
      have hk := besselZero_one_gt extZeros_holds n
      have hlt : besselZero 1 (n + 1) < Rn ⌈besselZero 1 (n + 1)⌉₊ :=
        lt_of_le_of_lt (Nat.le_ceil _) (hRnN _)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hlt⟩
      have h2 : (n : ℝ) < ⌈Rn ⌈besselZero 1 (n + 1)⌉₊⌉₊ := by
        have := Nat.le_ceil (Rn ⌈besselZero 1 (n + 1)⌉₊)
        push_cast at hk
        nlinarith [Real.pi_gt_three]
      exact_mod_cast (show (n : ℝ) < ⌈Rn ⌈besselZero 1 (n + 1)⌉₊⌉₊ + 1 by linarith)
  have hlim : Tendsto A atTop (𝓝 (∑' n, mlTerm z n)) := hsum.hasSum.comp hT
  have := tendsto_nhds_unique hlim hAL
  rw [← this]
  exact hsum.hasSum

end Buckling
end
end ChunkedSource061
/- END SOURCE 061 -/

/- BEGIN SOURCE 062: RequestProject/Bessel/Product/Main.lean -/
section ChunkedSource062

/-!
# External theorem E2 (canonical product of `J₁`), proved

Let `Q(ζ) = ∏_{n ≥ 1} (1 - ζ²/κ_n²)`; the product converges locally uniformly on `ℂ` since
`∑ 1/κ_n² < ∞`.  On the disk `|ζ - κ₁/2| < κ₁/4`, which contains no zero of `J₁` or of `Q`,
the logarithmic derivative of `(ζ/2) Q(ζ)` is `1/ζ + ∑ 2ζ/(ζ² - κ_n²)`, which by the
Mittag-Leffler expansion (`hasSum_mlTerm`) equals `J₀(ζ)/J₁(ζ) - 1/ζ = J₁'(ζ)/J₁(ζ)`.  Hence
`J₁ = c (ζ/2) Q` there, hence on `ℂ` (identity theorem), and comparing derivatives at `0` gives
`c = 1`.  This is `ExtProduct` (`extProduct_holds`).
-/

@[expose] public section

open Complex Real Filter Topology Set Metric

namespace Buckling

/-- The canonical product `∏ (1 - ζ²/κ_n²)`. -/
noncomputable def j1Q (ζ : ℂ) : ℂ := ∏' n, (1 + -(ζ ^ 2 / kc n ^ 2))

lemma hasProdLocallyUniformlyOn_j1Q :
    HasProdLocallyUniformlyOn (fun n ζ => 1 + -(ζ ^ 2 / kc n ^ 2)) j1Q univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K _ hK
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  refine Summable.hasProdUniformlyOn_nat_one_add hK
    ((summable_inv_besselZero_sq extZeros_holds).mul_left (M ^ 2))
    (Eventually.of_forall fun n x hx => ?_) (fun n => by fun_prop)
  rw [norm_neg, norm_div, norm_pow, norm_pow, norm_kc]
  have := pow_le_pow_left₀ (norm_nonneg x) (hM x hx) 2
  have hk := kc_pos n
  rw [mul_one_div]
  gcongr

lemma tendstoLocallyUniformlyOn_j1Q :
    TendstoLocallyUniformlyOn (fun N ζ => ∏ n ∈ Finset.range N, (1 + -(ζ ^ 2 / kc n ^ 2)))
      j1Q atTop univ :=
  hasProdLocallyUniformlyOn_j1Q.tendstoLocallyUniformlyOn_finsetRange

lemma differentiable_j1Q : Differentiable ℂ j1Q := by
  have h := tendstoLocallyUniformlyOn_j1Q.differentiableOn
    (Eventually.of_forall fun N => by fun_prop) isOpen_univ
  exact fun ζ => (h ζ (mem_univ ζ)).differentiableAt univ_mem

lemma j1Q_zero : j1Q 0 = 1 := by simp [j1Q]

/-- The disk `|ζ - κ₁/2| < κ₁/4`. -/
noncomputable def diskV : Set ℂ := ball (((jk / 2 : ℝ)) : ℂ) (jk / 4)

lemma jk_le_kc (n : ℕ) : jk ≤ besselZero 1 (n + 1) :=
  (extZeros_holds 1 le_rfl).1.monotone (by omega : 1 ≤ n + 1)

lemma norm_lt_of_mem_diskV {ζ : ℂ} (hζ : ζ ∈ diskV) : jk / 4 < ‖ζ‖ ∧ ‖ζ‖ < jk := by
  have hk := jk_pos extZeros_holds
  rw [diskV, mem_ball, dist_eq_norm] at hζ
  have hc : ‖(((jk / 2 : ℝ)) : ℂ)‖ = jk / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 := norm_sub_norm_le ζ (((jk / 2 : ℝ)) : ℂ)
  have h2 := norm_sub_norm_le (((jk / 2 : ℝ)) : ℂ) ζ
  rw [norm_sub_rev] at h2
  rw [hc] at h1 h2
  constructor <;> linarith

lemma factor_ne_zero_of_mem_diskV {ζ : ℂ} (hζ : ζ ∈ diskV) (n : ℕ) :
    1 + -(ζ ^ 2 / kc n ^ 2) ≠ 0 := by
  intro h
  have hk := kc_ne_zero n
  have : ζ ^ 2 = kc n ^ 2 := by
    field_simp at h
    linear_combination -h
  have h3 := congrArg (‖·‖) this
  simp only [norm_pow, norm_kc] at h3
  have h4 := (norm_lt_of_mem_diskV hζ).2
  have h5 := jk_le_kc n
  have : ‖ζ‖ ^ 2 < besselZero 1 (n + 1) ^ 2 := by
    have := norm_nonneg ζ
    nlinarith
  linarith

lemma ne_zero_of_mem_diskV {ζ : ℂ} (hζ : ζ ∈ diskV) : ζ ≠ 0 := by
  intro h
  have := (norm_lt_of_mem_diskV hζ).1
  rw [h, norm_zero] at this
  linarith [jk_pos extZeros_holds]

lemma besselJC_one_ne_zero_of_mem_diskV {ζ : ℂ} (hζ : ζ ∈ diskV) : besselJC 1 ζ ≠ 0 := by
  intro h
  have h2 := (norm_lt_of_mem_diskV hζ).2
  rcases besselJC_one_eq_zero' h with h0 | ⟨n, h0 | h0⟩
  · exact ne_zero_of_mem_diskV hζ h0
  · have := jk_le_kc n
    rw [h0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kc_pos n)] at h2
    linarith
  · have := jk_le_kc n
    rw [h0, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (kc_pos n)] at h2
    linarith

lemma logDeriv_factor {ζ : ℂ} (hζ : ζ ∈ diskV) (n : ℕ) :
    logDeriv (fun w => 1 + -(w ^ 2 / kc n ^ 2)) ζ = mlTerm ζ n := by
  have hk := kc_ne_zero n
  have hf := factor_ne_zero_of_mem_diskV hζ n
  have hd : HasDerivAt (fun w => 1 + -(w ^ 2 / kc n ^ 2)) (-(2 * ζ / kc n ^ 2)) ζ := by
    have := (((hasDerivAt_pow 2 ζ).div_const (kc n ^ 2)).neg).const_add 1
    convert this using 1
    push_cast; ring
  rw [logDeriv_apply, hd.deriv, mlTerm]
  have h2 : ζ ^ 2 - kc n ^ 2 ≠ 0 := by
    intro h; apply hf; field_simp; linear_combination -h
  rw [div_eq_div_iff hf h2]
  field_simp
  ring

lemma logDeriv_j1Q {ζ : ℂ} (hζ : ζ ∈ diskV) :
    logDeriv j1Q ζ = besselJC 0 ζ / besselJC 1 ζ - 2 / ζ := by
  have hs := hasSum_mlTerm (ne_zero_of_mem_diskV hζ) (besselJC_one_ne_zero_of_mem_diskV hζ)
  have hsum : Summable fun n => ‖-(ζ ^ 2 / kc n ^ 2)‖ := by
    refine ((summable_inv_besselZero_sq extZeros_holds).mul_left (‖ζ‖ ^ 2)).congr fun n => ?_
    rw [norm_neg, norm_div, norm_pow, norm_pow, norm_kc, mul_one_div]
  have hnez : ∏' n, (1 + -(ζ ^ 2 / kc n ^ 2)) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable (factor_ne_zero_of_mem_diskV hζ) hsum
  have h := logDeriv_tprod_eq_tsum isOpen_univ (mem_univ ζ)
    (f := fun n w => 1 + -(w ^ 2 / kc n ^ 2)) (factor_ne_zero_of_mem_diskV hζ)
    (fun n => by fun_prop) (hs.summable.congr fun n => (logDeriv_factor hζ n).symm)
    ⟨_, hasProdLocallyUniformlyOn_j1Q⟩ hnez
  have heq : (fun w => ∏' n, (fun n w => 1 + -(w ^ 2 / kc n ^ 2)) n w) = j1Q := rfl
  rw [heq] at h
  rw [h, tsum_congr (logDeriv_factor hζ), hs.tsum_eq]

lemma logDeriv_besselJC_one {ζ : ℂ} (hζ0 : ζ ≠ 0) (hJ : besselJC 1 ζ ≠ 0) :
    logDeriv (besselJC 1) ζ = besselJC 0 ζ / besselJC 1 ζ - 1 / ζ := by
  rw [logDeriv_apply, deriv_besselJC_one]
  have := mul_dJ1C ζ
  field_simp
  linear_combination this

/-- `J₁(ζ) = c (ζ/2) Q(ζ)` on `ℂ` for some constant `c`. -/
lemma besselJC_one_eq_const_mul :
    ∃ c : ℂ, ∀ ζ, besselJC 1 ζ = c * (ζ / 2 * j1Q ζ) := by
  set P : ℂ → ℂ := fun ζ => ζ / 2 * j1Q ζ with hP
  have hPd : Differentiable ℂ P := by
    have := differentiable_j1Q
    fun_prop
  have hV : IsOpen diskV := isOpen_ball
  have hVc : IsPreconnected diskV := (convex_ball _ _).isPreconnected
  have hQne : ∀ ζ ∈ diskV, j1Q ζ ≠ 0 := by
    intro ζ hζ
    have hsum : Summable fun n => ‖-(ζ ^ 2 / kc n ^ 2)‖ := by
      refine ((summable_inv_besselZero_sq extZeros_holds).mul_left (‖ζ‖ ^ 2)).congr fun n => ?_
      rw [norm_neg, norm_div, norm_pow, norm_pow, norm_kc, mul_one_div]
    exact tprod_one_add_ne_zero_of_summable (factor_ne_zero_of_mem_diskV hζ) hsum
  have hPne : ∀ ζ ∈ diskV, P ζ ≠ 0 := fun ζ hζ =>
    mul_ne_zero (div_ne_zero (ne_zero_of_mem_diskV hζ) two_ne_zero) (hQne ζ hζ)
  have hlog : EqOn (logDeriv (besselJC 1)) (logDeriv P) diskV := by
    intro ζ hζ
    have hζ0 := ne_zero_of_mem_diskV hζ
    rw [logDeriv_besselJC_one hζ0 (besselJC_one_ne_zero_of_mem_diskV hζ), hP,
      logDeriv_fun_mul (f := fun w : ℂ => w / 2) (g := j1Q) ζ (div_ne_zero hζ0 two_ne_zero) (hQne ζ hζ) (by fun_prop)
        (differentiable_j1Q ζ), logDeriv_j1Q hζ]
    have : logDeriv (fun w : ℂ => w / 2) ζ = 1 / ζ := by
      rw [logDeriv_apply, deriv_div_const, deriv_id'']
      field_simp
    rw [this]
    ring
  obtain ⟨c, -, hc⟩ := (logDeriv_eqOn_iff (differentiable_besselJC 1).differentiableOn
    hPd.differentiableOn hV hVc hPne (fun ζ hζ => besselJC_one_ne_zero_of_mem_diskV hζ)).mp hlog
  refine ⟨c, fun ζ => ?_⟩
  have hz0 : (((jk / 2 : ℝ)) : ℂ) ∈ diskV := by
    rw [diskV]; exact mem_ball_self (by linarith [jk_pos extZeros_holds])
  have han1 : AnalyticOnNhd ℂ (besselJC 1) univ :=
    (differentiable_besselJC 1).differentiableOn.analyticOnNhd isOpen_univ
  have han2 : AnalyticOnNhd ℂ (c • P) univ :=
    ((hPd.const_smul c).differentiableOn).analyticOnNhd isOpen_univ
  have hev : besselJC 1 =ᶠ[𝓝 (((jk / 2 : ℝ)) : ℂ)] c • P :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hz0) hc
  have := han1.eqOn_of_preconnected_of_eventuallyEq han2 isPreconnected_univ (mem_univ _) hev
    (mem_univ ζ)
  simpa [hP] using this

/-- **E2**: `J₁(ζ) = (ζ/2) ∏_{n ≥ 1} (1 - ζ²/κ_n²)`. -/
theorem besselJC_one_eq_prod (ζ : ℂ) : besselJC 1 ζ = ζ / 2 * j1Q ζ := by
  obtain ⟨c, hc⟩ := besselJC_one_eq_const_mul
  have hc1 : c = 1 := by
    have h1 : HasDerivAt (besselJC 1) (1 / 2) 0 := by
      have := hasDerivAt_besselJC_one 0
      rwa [dJ1C_zero] at this
    have h2 : HasDerivAt (fun ζ => c * (ζ / 2 * j1Q ζ))
        (c * (1 / 2 * j1Q 0 + 0 / 2 * deriv j1Q 0)) 0 := by
      have := (((hasDerivAt_id (0 : ℂ)).div_const 2).mul
        (differentiable_j1Q 0).hasDerivAt).const_mul c
      simpa using this
    have heq : besselJC 1 = fun ζ => c * (ζ / 2 * j1Q ζ) := funext hc
    rw [heq] at h1
    have := h1.unique h2
    rw [j1Q_zero] at this
    linear_combination -2 * this
  rw [hc, hc1, one_mul]

/-- **External theorem E2**, proved. -/
theorem extProduct_holds : ExtProduct := by
  have hconst : TendstoLocallyUniformly (fun (_ : ℕ) (ζ : ℂ) => ζ / 2) (fun ζ => ζ / 2) atTop :=
    TendstoUniformly.tendstoLocallyUniformly
      (fun u hu => Eventually.of_forall fun _ _ => refl_mem_uniformity hu)
  have h := hconst.mul₀ (tendstoLocallyUniformlyOn_univ.mp tendstoLocallyUniformlyOn_j1Q)
    (by fun_prop) differentiable_j1Q.continuous
  unfold ExtProduct
  have hJ : besselJC 1 = (fun ζ : ℂ => ζ / 2) * j1Q := funext besselJC_one_eq_prod
  rw [hJ]
  simpa only [kc, sub_eq_add_neg] using! h

end Buckling
end
end ChunkedSource062
/- END SOURCE 062 -/

/- BEGIN SOURCE 063: RequestProject/Concavity/Coefficients.lean -/
section ChunkedSource063

/-!
# Signs of the Taylor coefficients of `G` (Lemma 8.8 and Proposition 8.9 of the paper)

For `m ≥ 2`, the residue theorem applied to `G(ζ)/ζ^{2m+1}` on the circles `|ζ| = R_N`
expresses the Taylor coefficient `[ζ^{2m}] G` as `-2 ∑ (positive residues)` plus a contour
integral which is `O(R_N^{2-2m})`.  Hence `Re [ζ^{2m}] G ≤ 0`.
-/

@[expose] public section

open Filter Topology Metric Set Real

namespace Buckling

/-- The zeros of `J₁`, indexed by `j ≥ 1`. -/
lemma besselJC_one_zero_cases (hZ : ExtZeros) (hP : ExtProduct) {z : ℂ}
    (h : besselJC 1 z = 0) :
    z = 0 ∨ ∃ j, 1 ≤ j ∧ (z = (besselZero 1 j : ℂ) ∨ z = -(besselZero 1 j : ℂ)) := by
  rcases besselJC_one_eq_zero hZ hP h with h0 | ⟨n, hn⟩
  · exact Or.inl h0
  · exact Or.inr ⟨n + 1, by omega, hn⟩

lemma norm_besselZero_one (hZ : ExtZeros) {j : ℕ} (hj : 1 ≤ j) :
    ‖((besselZero 1 j : ℝ) : ℂ)‖ = besselZero 1 j := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (besselZero_pos hZ 1 j hj)]

lemma norm_neg_besselZero_one (hZ : ExtZeros) {j : ℕ} (hj : 1 ≤ j) :
    ‖-((besselZero 1 j : ℝ) : ℂ)‖ = besselZero 1 j := by
  rw [norm_neg, norm_besselZero_one hZ hj]

/-- `Ghol` is holomorphic on `|ζ| < κ₂`. -/
lemma differentiableOn_Ghol_ball (hZ : ExtZeros) (hP : ExtProduct) :
    DifferentiableOn ℂ Ghol (ball 0 (besselZero 1 2)) := by
  refine differentiableOn_Ghol hZ isOpen_ball fun z hz h => ?_
  rw [mem_ball, dist_zero_right] at hz
  rcases besselJC_one_zero_cases hZ hP h with rfl | ⟨j, hj, hz'⟩
  · simp [Gsing]
  · have hj2 : j < 2 := by
      by_contra hcon
      have : besselZero 1 2 ≤ besselZero 1 j := (hZ 1 (by norm_num)).1.monotone (by omega)
      rcases hz' with rfl | rfl
      · rw [norm_besselZero_one hZ hj] at hz; linarith
      · rw [norm_neg_besselZero_one hZ hj] at hz; linarith
    have : j = 1 := by omega
    subst this
    rcases hz' with rfl | rfl <;> simp [Gsing, jk]

lemma princPart_congr {N : ℕ} {P Q : ℂ → ℕ → ℂ} {a : ℂ} (h : P a = Q a) (z : ℂ) :
    princPart N P a z = princPart N Q a z := by
  simp only [princPart, h]

lemma princPart_two {N : ℕ} (hN : 2 ≤ N) {P : ℂ → ℕ → ℂ} {a : ℂ}
    (hP : ∀ j, 2 ≤ j → P a j = 0) (z : ℂ) :
    princPart N P a z = P a 0 / (z - a) ^ 1 + P a 1 / (z - a) ^ 2 := by
  unfold princPart
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hN)]
  · simp [Finset.sum_range_succ]
  · intro j hj hj2
    rw [Finset.mem_range] at hj hj2
    rw [hP j (by omega), zero_div]

/-- **Proposition 8.9 (signs of the Taylor coefficients)**: for `m ≥ 2`,
`Re [ζ^{2m}] G ≤ 0`. -/
theorem tcoef_Ghol_re_nonpos {m : ℕ} (hm : 2 ≤ m) :
    (tcoef Ghol (2 * m)).re ≤ 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hZ := extZeros_holds
  have hP := extProduct_holds
  obtain ⟨C, N0, hcirc⟩ := circle_bound hZ extAsymptotic_holds
  obtain ⟨-, -, hk1, hk2, -⟩ := root_boxes hZ
  have hκmono := (hZ 1 (by norm_num)).1
  set κ : ℕ → ℝ := besselZero 1 with hκdef
  -- the coefficient bound on each circle
  have key : ∀ N : ℕ, max N0 1 ≤ N →
      (tcoef Ghol (2 * (n + 1))).re ≤ C / (((N : ℝ) + 3 / 4) * π) ^ (2 * n) := by
    intro N hN
    set R : ℝ := ((N : ℝ) + 3 / 4) * π with hRdef
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    have hR0 : 0 < R := by positivity
    have hRk : jk < R := by
      have := Real.pi_gt_three
      have : (7 / 4 : ℝ) * 3 ≤ R := by
        rw [hRdef]; apply mul_le_mul (by linarith) this.le (by norm_num) (by linarith)
      linarith
    have hc := hcirc N ((le_max_left _ _).trans hN)
    -- the first zero beyond `R`
    have hex : ∃ j, R < κ j := ((hZ 1 (by norm_num)).2.1.eventually (eventually_gt_atTop R)).exists
    classical
    set M := Nat.find hex with hMdef
    have hM : R < κ M := Nat.find_spec hex
    have hM' : ∀ j < M, κ j ≤ R := fun j hj => not_lt.mp (Nat.find_min hex hj)
    have hM2 : 2 ≤ M := by
      by_contra hcon
      have : M = 0 ∨ M = 1 := by omega
      rcases this with h | h
      · rw [h] at hM; simp [κ, besselZero] at hM; linarith
      · rw [h] at hM; change R < jk at hM; linarith
    have hκlt : ∀ j, 2 ≤ j → j < M → κ j < R := by
      intro j hj2 hjM
      refine lt_of_le_of_ne (hM' j hjM) fun heq => ?_
      have := (hc ((κ j : ℝ) : ℂ) (by rw [norm_besselZero_one hZ (by omega)]; exact heq)).1
      exact this (by rw [besselJC_ofReal, ((hZ 1 (by norm_num)).2.2.1 j (by omega)).1, Complex.ofReal_zero])
    set S' : Finset ℂ := (Finset.Ico 2 M).image (fun j => ((κ j : ℝ) : ℂ)) ∪
      (Finset.Ico 2 M).image (fun j => -((κ j : ℝ) : ℂ)) with hS'def
    have hS'mem : ∀ a ∈ S', ∃ j, 2 ≤ j ∧ j < M ∧ (a = ((κ j : ℝ) : ℂ) ∨ a = -((κ j : ℝ) : ℂ)) := by
      intro a ha
      rcases Finset.mem_union.mp ha with h | h <;>
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h <;>
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
      · exact ⟨j, hj1, hj2, Or.inl rfl⟩
      · exact ⟨j, hj1, hj2, Or.inr rfl⟩
    have hS'0 : (0 : ℂ) ∉ S' := by
      intro h
      obtain ⟨j, hj2, -, hj⟩ := hS'mem 0 h
      have hpos := besselZero_pos hZ 1 j (by omega)
      rcases hj with h | h
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    set S : Finset ℂ := insert 0 S'
    set P : ℂ → ℕ → ℂ := fun a i => if a = 0 then tcoef Ghol (2 * (n + 1) - i)
      else if i = 0 then residG (n + 1) a else if i = 1 then resid2 (n + 1) a else 0
    set h : ℂ → ℂ := fun z => Ghol z / z ^ (2 * (n + 1) + 1)
    -- poles are not removable singularities and have the right data
    have hpole : ∀ a ∈ S', a ≠ 0 ∧ a ∉ Gsing ∧ besselJC 1 a = 0 ∧ besselJC 0 a ≠ 0 ∧
        0 ≤ (residG (n + 1) a).re := by
      intro a ha
      obtain ⟨j, hj2, hjM, hj⟩ := hS'mem a ha
      have hpos := besselZero_pos hZ 1 j (by omega)
      have hkj : jk < κ j := by
        have := hκmono (show 1 < j by omega); exact this
      have hJ1 : besselJ 1 (κ j) = 0 := ((hZ 1 (by norm_num)).2.2.1 j (by omega)).1
      have hJ0 := besselJ_zero_besselZero_one_ne hZ (show 1 ≤ j by omega)
      obtain ⟨hr1, hr2⟩ := residG_pos hZ extIntegral_holds hj2 (show 2 ≤ n + 1 by omega)
      rcases hj with rfl | rfl
      · refine ⟨by exact_mod_cast hpos.ne', ?_, by rw [besselJC_ofReal, hJ1]; simp,
          by rw [besselJC_ofReal]; exact_mod_cast hJ0, hr1.le⟩
        simp only [Gsing, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨by exact_mod_cast hpos.ne', fun h => ?_, fun h => ?_⟩
        · have := congrArg Complex.re h; simp at this; linarith
        · have := congrArg Complex.re h; simp at this; linarith [jk_pos hZ]
      · refine ⟨neg_ne_zero.mpr (by exact_mod_cast hpos.ne'), ?_,
          by rw [besselJC_neg, besselJC_ofReal, hJ1]; simp,
          by rw [besselJC_neg, besselJC_ofReal]; simpa using hJ0, hr2.le⟩
        simp only [Gsing, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨neg_ne_zero.mpr (by exact_mod_cast hpos.ne'), fun h => ?_, fun h => ?_⟩
        · have := congrArg Complex.re h; simp at this; linarith [jk_pos hZ]
        · have := congrArg Complex.re h; simp at this; linarith
    -- holomorphy of `h` off `S`
    have hS'c : IsClosed (S' : Set ℂ) := S'.finite_toSet.isClosed
    have hGd : DifferentiableOn ℂ Ghol (ball 0 (κ M) ∩ (S' : Set ℂ)ᶜ) := by
      refine differentiableOn_Ghol hZ (isOpen_ball.inter hS'c.isOpen_compl) fun z hz hz0 => ?_
      obtain ⟨hzb, hzS⟩ := hz
      rw [mem_ball, dist_zero_right] at hzb
      rcases besselJC_one_zero_cases hZ hP hz0 with rfl | ⟨j, hj, hz'⟩
      · simp [Gsing]
      · have hjM : j < M := by
          by_contra hcon
          have : κ M ≤ κ j := hκmono.monotone (by omega)
          rcases hz' with rfl | rfl
          · rw [norm_besselZero_one hZ hj] at hzb; linarith
          · rw [norm_neg_besselZero_one hZ hj] at hzb; linarith
        rcases (show j = 1 ∨ 2 ≤ j by omega) with rfl | hj2
        · rcases hz' with rfl | rfl <;> simp [Gsing, jk]
        · exfalso; apply hzS
          rcases hz' with rfl | rfl
          · exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_image.mpr
              ⟨j, Finset.mem_Ico.mpr ⟨hj2, hjM⟩, rfl⟩))
          · exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_image.mpr
              ⟨j, Finset.mem_Ico.mpr ⟨hj2, hjM⟩, rfl⟩))
    have hd : DifferentiableOn ℂ h (ball 0 (κ M) \ S) := by
      intro z hz
      have hz0 : z ≠ 0 := fun h0 => hz.2 (Finset.mem_coe.mpr (h0 ▸ Finset.mem_insert_self 0 S'))
      have hzS' : z ∉ S' := fun h' => hz.2 (Finset.mem_coe.mpr (Finset.mem_insert_of_mem h'))
      refine DifferentiableWithinAt.div ?_ (differentiableWithinAt_id.pow _) (pow_ne_zero _ hz0)
      exact (hGd z ⟨hz.1, hzS'⟩).mono fun w hw => ⟨hw.1, fun h' => hw.2
        (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp h')))⟩
    -- boundedness near the singular points
    have hb : ∀ a ∈ S, ∃ C', ∀ᶠ z in 𝓝[≠] a, ‖h z - princPart (2 * (n + 1) + 1) P a z‖ ≤ C' := by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha'
      · obtain ⟨C0, hC0⟩ := bdd_div_pow_sub_principal (r := ⟨κ 2, (besselZero_pos hZ 1 2
          (by norm_num)).le⟩) (besselZero_pos hZ 1 2 (by norm_num))
          (differentiableOn_Ghol_ball hZ hP) (2 * (n + 1))
        refine ⟨C0, hC0.mono fun z hz => ?_⟩
        rw [princPart_congr (Q := fun _ i => tcoef Ghol (2 * (n + 1) - i)) (by simp [P])]
        exact hz
      · obtain ⟨ha0, haS, h1, h0, -⟩ := hpole a ha'
        obtain ⟨C1, hC1⟩ := Ghol_principal_part n ha0 haS h1 h0
        refine ⟨C1, hC1.mono fun z hz => ?_⟩
        rw [princPart_two (by omega) (fun j hj => by
          have h0' : j ≠ 0 := by omega
          have h1' : j ≠ 1 := by omega
          simp [P, ha0, h0', h1'])]
        simpa [P, ha0] using hz
    have hSball : (S : Set ℂ) ⊆ ball 0 R := by
      intro a ha
      rcases Finset.mem_insert.mp (Finset.mem_coe.mp ha) with rfl | ha'
      · simpa using hR0
      · obtain ⟨j, hj2, hjM, hj⟩ := hS'mem a ha'
        rw [mem_ball, dist_zero_right]
        rcases hj with rfl | rfl
        · rw [norm_besselZero_one hZ (by omega)]; exact hκlt j hj2 hjM
        · rw [norm_neg_besselZero_one hZ (by omega)]; exact hκlt j hj2 hjM
    have hres := circleIntegral_eq_residues hR0 isOpen_ball
      (closedBall_subset_ball hM) S hSball h (2 * (n + 1) + 1) (by omega) P hd hb
    -- the sum of residues
    have hsum : (tcoef Ghol (2 * (n + 1))).re ≤ (∑ a ∈ S, P a 0).re := by
      rw [Finset.sum_insert hS'0, Complex.add_re, Complex.re_sum]
      have h00 : P 0 0 = tcoef Ghol (2 * (n + 1)) := by simp [P]
      rw [h00]
      have : 0 ≤ ∑ a ∈ S', (P a 0).re := by
        refine Finset.sum_nonneg fun a ha => ?_
        obtain ⟨ha0, -, -, -, hre⟩ := hpole a ha
        simpa [P, ha0] using hre
      linarith
    -- the contour bound
    have hcont : ‖∮ z in C(0, R), h z‖ ≤ 2 * π * R * (C * R ^ 2 / R ^ (2 * (n + 1) + 1)) := by
      apply circleIntegral.norm_integral_le_of_norm_le_const hR0.le
      intro z hz
      rw [mem_sphere, dist_zero_right] at hz
      have hzS : z ∉ Gsing := by
        simp only [Gsing, Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
        · simp at hz; linarith
        · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (jk_pos hZ)] at hz; linarith
        · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (jk_pos hZ)] at hz
          linarith
      simp only [h]
      rw [Ghol_of_notMem hzS, norm_div, norm_pow, hz]
      exact div_le_div_of_nonneg_right (hc z hz).2 (by positivity)
    have hfin : (∑ a ∈ S, P a 0).re ≤ ‖∮ z in C(0, R), h z‖ / (2 * π) := by
      have h2pi : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have : ∑ a ∈ S, P a 0 = (∮ z in C(0, R), h z) / (2 * π * Complex.I) := by
        rw [hres]; field_simp
      rw [this]
      refine (Complex.re_le_norm _).trans (le_of_eq ?_)
      rw [norm_div]
      congr 1
      simp [abs_of_pos Real.pi_pos]
    calc (tcoef Ghol (2 * (n + 1))).re ≤ ‖∮ z in C(0, R), h z‖ / (2 * π) := hsum.trans hfin
      _ ≤ 2 * π * R * (C * R ^ 2 / R ^ (2 * (n + 1) + 1)) / (2 * π) := by
          gcongr
      _ = C / R ^ (2 * n) := by
          field_simp
          ring
  -- pass to the limit
  have hlim : Tendsto (fun N : ℕ => C / (((N : ℝ) + 3 / 4) * π) ^ (2 * n)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 3 / 4) * π) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const Real.pi_pos
    exact tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by omega)).comp h1)
  exact ge_of_tendsto hlim (eventually_atTop.mpr ⟨max N0 1, key⟩)

end Buckling
end
end ChunkedSource063
/- END SOURCE 063 -/

/- BEGIN SOURCE 064: RequestProject/Profiles/Transfer.lean -/
section ChunkedSource064

/-!
# From the radial variable to the profiles on the real line

Derivatives of `f, G, b` in the variable `t` (Definition 4.4), their parity extensions
(Definition 9.2), and the reduction of the matrix positivity and coupling conditions of
`ProfileFacts` to the inequality `d² + 4Kg² ≤ 4K²` (Proposition 4.10).
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

lemma rT_eq (r : ℝ) : rT r = -(rp r ^ 2 + ru r * deriv rp r) / rp r ^ 2 := rfl

lemma rT_ne (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) : rT r ≠ 0 :=
  (rT_neg hZ hr0 hrk).ne

lemma hasDerivAt_rOf' (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) :
    HasDerivAt rOf (rT (rOf t))⁻¹ t := hasDerivAt_rOf hZ ht

/-- `f_t = z`. -/
theorem hasDerivAt_pf (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) :
    HasDerivAt pf (rz (rOf t)) t := by
  obtain ⟨⟨h0, h1⟩, -⟩ := rOf_spec hZ ht
  have h := (hasDerivAt_rf hZ h0 h1).comp t (hasDerivAt_rOf' hZ ht)
  rw [(profile_identities_alg hZ h0 h1).2.2.1] at h
  have hT := rT_ne hZ h0 h1
  have hD : rT (rOf t) * rz (rOf t) * (rT (rOf t))⁻¹ = rz (rOf t) := by
    field_simp [hT] <;> ring
  simpa only [pf, rf, Function.comp_apply] using! (h.congr_deriv hD)

/-- `G_t = G_r / T`. -/
theorem hasDerivAt_pG (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) :
    HasDerivAt pG (rGt (rOf t)) t := by
  obtain ⟨⟨h0, h1⟩, -⟩ := rOf_spec hZ ht
  have h := (hasDerivAt_rG hZ h0 h1).comp t (hasDerivAt_rOf' hZ ht)
  exact h

/-- `b_t = b_r / T`. -/
theorem hasDerivAt_pb (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) :
    HasDerivAt pb (rbt (rOf t)) t := by
  obtain ⟨⟨h0, h1⟩, -⟩ := rOf_spec hZ ht
  have h := (hasDerivAt_rb hZ h0 h1).comp t (hasDerivAt_rOf' hZ ht)
  exact h

/-! ### The parity extensions away from `0` -/

lemma fExt_eventually_pos {s : ℝ} (hs : 0 < s) : fExt =ᶠ[𝓝 s] pf := by
  filter_upwards [Ioi_mem_nhds hs] with y hy
  simp [fExt, (mem_Ioi.mp hy).ne', abs_of_pos (mem_Ioi.mp hy)]

lemma fExt_eventually_neg {s : ℝ} (hs : s < 0) : fExt =ᶠ[𝓝 s] fun y => pf (-y) := by
  filter_upwards [Iio_mem_nhds hs] with y hy
  simp [fExt, (mem_Iio.mp hy).ne, abs_of_neg (mem_Iio.mp hy)]

lemma GExt_eventually_pos {s : ℝ} (hs : 0 < s) : GExt =ᶠ[𝓝 s] pG := by
  filter_upwards [Ioi_mem_nhds hs] with y hy
  simp [GExt, (mem_Ioi.mp hy).ne', abs_of_pos (mem_Ioi.mp hy)]

lemma GExt_eventually_neg {s : ℝ} (hs : s < 0) : GExt =ᶠ[𝓝 s] fun y => pG (-y) := by
  filter_upwards [Iio_mem_nhds hs] with y hy
  simp [GExt, (mem_Iio.mp hy).ne, abs_of_neg (mem_Iio.mp hy)]

lemma bExt_eventually_pos {s : ℝ} (hs : 0 < s) : bExt =ᶠ[𝓝 s] pb := by
  filter_upwards [Ioi_mem_nhds hs] with y hy
  simp [bExt, (mem_Ioi.mp hy).ne', abs_of_pos (mem_Ioi.mp hy), mem_Ioi.mp hy]

lemma bExt_eventually_neg {s : ℝ} (hs : s < 0) : bExt =ᶠ[𝓝 s] fun y => -pb (-y) := by
  filter_upwards [Iio_mem_nhds hs] with y hy
  simp [bExt, (mem_Iio.mp hy).ne, abs_of_neg (mem_Iio.mp hy), mem_Iio.mp hy]

theorem hasDerivAt_fExt_pos (hZ : ExtZeros) {s : ℝ} (hs : 0 < s) :
    HasDerivAt fExt (rz (rOf s)) s :=
  (hasDerivAt_pf hZ hs).congr_of_eventuallyEq (fExt_eventually_pos hs)

theorem hasDerivAt_fExt_neg (hZ : ExtZeros) {s : ℝ} (hs : s < 0) :
    HasDerivAt fExt (-rz (rOf (-s))) s := by
  have h := (hasDerivAt_pf hZ (neg_pos.mpr hs)).comp s (hasDerivAt_neg s)
  simp only [mul_neg, mul_one] at h
  exact h.congr_of_eventuallyEq (fExt_eventually_neg hs)

theorem hasDerivAt_GExt_pos (hZ : ExtZeros) {s : ℝ} (hs : 0 < s) :
    HasDerivAt GExt (rGt (rOf s)) s :=
  (hasDerivAt_pG hZ hs).congr_of_eventuallyEq (GExt_eventually_pos hs)

theorem hasDerivAt_GExt_neg (hZ : ExtZeros) {s : ℝ} (hs : s < 0) :
    HasDerivAt GExt (-rGt (rOf (-s))) s := by
  have h := (hasDerivAt_pG hZ (neg_pos.mpr hs)).comp s (hasDerivAt_neg s)
  simp only [mul_neg, mul_one] at h
  exact h.congr_of_eventuallyEq (GExt_eventually_neg hs)

theorem hasDerivAt_bExt_pos (hZ : ExtZeros) {s : ℝ} (hs : 0 < s) :
    HasDerivAt bExt (rbt (rOf s)) s :=
  (hasDerivAt_pb hZ hs).congr_of_eventuallyEq (bExt_eventually_pos hs)

theorem hasDerivAt_bExt_neg (hZ : ExtZeros) {s : ℝ} (hs : s < 0) :
    HasDerivAt bExt (rbt (rOf (-s))) s := by
  have h := ((hasDerivAt_pb hZ (neg_pos.mpr hs)).comp s (hasDerivAt_neg s)).neg
  simp only [mul_neg, mul_one, neg_neg] at h
  exact h.congr_of_eventuallyEq (bExt_eventually_neg hs)

/-! ### Reduction of the matrix conditions (Propositions 4.9 and 4.10) -/

/-- The remaining one-variable inequality `d² + 4Kg² ≤ 4K²` of Proposition 4.10, in the
radial variable, with `d = 2G - tG_t` and `g = f - t f_t`. -/
def RemainingPositivity : Prop :=
  ∀ r ∈ Ioo 0 jk, (2 * rG r - rt r * rGt r) ^ 2 + 4 * pK * rg r ^ 2 ≤ 4 * pK ^ 2

/-- Matrix positivity and the coupling estimate at a radius, from the kernel identities. -/
lemma radial_matrix_pos (hZ : ExtZeros) (hR : RemainingPositivity) {r : ℝ} (hr0 : 0 < r)
    (hrk : r < jk) :
    (∀ X Y P : ℝ, 0 ≤ calibForm (pK - rg r ^ 2) (2 * rG r - rt r * rGt r) pK
      (2 * rb r - rt r * rbt r - 2 * rz r * rg r) (rb r + rGt r)
      (-pK - rz r ^ 2 + pLam * rf r ^ 2 + rbt r) X Y P) ∧
      0 ≤ 2 * pK - rg r ^ 2 - (2 * rG r - rt r * rGt r) := by
  obtain ⟨h1, h2, h3⟩ := kernel_identities hZ hr0 hrk
  have hK : 0 < pK := (parameter_signs hZ).2.2.2.2.2.2.2.2
  exact positivity_criterion pK (rg r) _ (rA r) (rC r) _ _ _ hK
    (by linarith) (by linarith) (by linarith) (hR r ⟨hr0, hrk⟩)

lemma calibForm_neg_LA_LC (a d K LA LC H X Y P : ℝ) :
    calibForm a d K (-LA) (-LC) H X Y P = calibForm a d K LA LC H X Y (-P) := by
  unfold calibForm; ring

/-- **Proposition 4.10, transferred to the real line**: the matrix positivity and coupling
conditions of `ProfileFacts` follow from `d² + 4Kg² ≤ 4K²`. -/
theorem matrix_coupling_of_remaining (hZ : ExtZeros) (hR : RemainingPositivity) :
    (∀ s, s ≠ 0 → ∀ X Y P, 0 ≤ calibAt s X Y P) ∧ (∀ s, s ≠ 0 → 0 ≤ couplingAt s) := by
  have key : ∀ s, s ≠ 0 → (∀ X Y P, 0 ≤ calibAt s X Y P) ∧ 0 ≤ couplingAt s := by
    intro s hs
    rcases lt_or_gt_of_ne hs with hneg | hpos
    · set s' := -s with hs'
      have hs'0 : 0 < s' := neg_pos.mpr hneg
      obtain ⟨⟨h0, h1⟩, hrt⟩ := rOf_spec hZ hs'0
      set r := rOf s'
      have hf : fExt s = rf r := by
        simp [fExt, hneg.ne, abs_of_neg hneg, pf, rf, r, s']
      have hG : GExt s = rG r := by simp [GExt, hneg.ne, abs_of_neg hneg, pG, r, s']
      have hb : bExt s = -rb r := by simp [bExt, hneg.ne, abs_of_neg hneg, pb, hneg, r, s']
      have hf' : deriv fExt s = -rz r := (hasDerivAt_fExt_neg hZ hneg).deriv
      have hG' : deriv GExt s = -rGt r := (hasDerivAt_GExt_neg hZ hneg).deriv
      have hb' : deriv bExt s = rbt r := (hasDerivAt_bExt_neg hZ hneg).deriv
      have hss : s = -rt r := by rw [hrt, hs', neg_neg]
      obtain ⟨hM, hC⟩ := radial_matrix_pos hZ hR h0 h1
      refine ⟨fun X Y P => ?_, ?_⟩
      · have e : calibAt s X Y P = calibForm (pK - rg r ^ 2) (2 * rG r - rt r * rGt r) pK
            (2 * rb r - rt r * rbt r - 2 * rz r * rg r) (rb r + rGt r)
            (-pK - rz r ^ 2 + pLam * rf r ^ 2 + rbt r) X Y (-P) := by
          unfold calibAt calibForm
          rw [hf, hG, hb, hf', hG', hb', hss, rg_eq hZ h0 h1]
          ring
        rw [e]; exact hM X Y (-P)
      · have e : couplingAt s = 2 * pK - rg r ^ 2 - (2 * rG r - rt r * rGt r) := by
          unfold couplingAt
          rw [hf, hG, hf', hG', hss, rg_eq hZ h0 h1]
          ring
        rw [e]; exact hC
    · obtain ⟨⟨h0, h1⟩, hrt⟩ := rOf_spec hZ hpos
      set r := rOf s
      have hf : fExt s = rf r := by simp [fExt, hpos.ne', abs_of_pos hpos, pf, rf, r]
      have hG : GExt s = rG r := by simp [GExt, hpos.ne', abs_of_pos hpos, pG, r]
      have hb : bExt s = rb r := by simp [bExt, hpos.ne', abs_of_pos hpos, pb, hpos, r]
      have hf' : deriv fExt s = rz r := (hasDerivAt_fExt_pos hZ hpos).deriv
      have hG' : deriv GExt s = rGt r := (hasDerivAt_GExt_pos hZ hpos).deriv
      have hb' : deriv bExt s = rbt r := (hasDerivAt_bExt_pos hZ hpos).deriv
      have hss : s = rt r := hrt.symm
      obtain ⟨hM, hC⟩ := radial_matrix_pos hZ hR h0 h1
      refine ⟨fun X Y P => ?_, ?_⟩
      · have e : calibAt s X Y P = calibForm (pK - rg r ^ 2) (2 * rG r - rt r * rGt r) pK
            (2 * rb r - rt r * rbt r - 2 * rz r * rg r) (rb r + rGt r)
            (-pK - rz r ^ 2 + pLam * rf r ^ 2 + rbt r) X Y P := by
          unfold calibAt calibForm
          rw [hf, hG, hb, hf', hG', hb', hss, rg_eq hZ h0 h1]
        rw [e]; exact hM X Y P
      · have e : couplingAt s = 2 * pK - rg r ^ 2 - (2 * rG r - rt r * rGt r) := by
          unfold couplingAt
          rw [hf, hG, hf', hG', hss, rg_eq hZ h0 h1]
        rw [e]; exact hC
  exact ⟨fun s hs => (key s hs).1, fun s hs => (key s hs).2⟩

end Buckling
end
end ChunkedSource064
/- END SOURCE 064 -/

/- BEGIN SOURCE 065: RequestProject/Profiles/Infinity.lean -/
section ChunkedSource065

/-!
# Behaviour of the profiles as `t → ∞` (the radial centre `r → 0`)

Part of Lemma 9.1 of the paper: `f(t)/t → ℓ`, `b(t)/t → 2λℓ` and `G(t) → 2λ - K`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

lemma tendsto_besselJ_one_div :
    Tendsto (fun x => besselJ 1 x / x) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have h := hasDerivAt_besselJ_succ 0 0
  have h2 : besselJ 2 0 = 0 := by simp [besselJ_zero_arg]
  rw [h2, besselJ_zero_at_zero] at h
  have := (hasDerivAt_iff_tendsto_slope.mp h)
  refine (this.congr' ?_).trans (by norm_num)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [slope_def_field]
  simp [besselJ_zero_arg]

lemma tendsto_besselJ_one_div_pos :
    Tendsto (fun x => besselJ 1 x / x) (𝓝[>] 0) (𝓝 (1 / 2)) :=
  tendsto_besselJ_one_div.mono_left (nhdsWithin_mono _ (fun _ hx => ne_of_gt hx))

/-- `r(t) → 0⁺` as `t → ∞`. -/
theorem tendsto_rOf_atTop (hZ : ExtZeros) : Tendsto rOf atTop (𝓝[>] 0) := by
  have hk0 : 0 < jk := (parameter_signs hZ).1.trans (parameter_signs hZ).2.1
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    set e := min ε (jk / 2)
    have he0 : 0 < e := lt_min hε (by linarith)
    have hek : e < jk := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    filter_upwards [eventually_gt_atTop (rt e), eventually_gt_atTop 0] with s hs hs0
    have hpos := rt_pos hZ he0 hek
    have h1 := (rOf_spec hZ hs0).1
    have h2 : rOf s < rOf (rt e) := rOf_strictAntiOn hZ (mem_Ioi.mpr hpos) (mem_Ioi.mpr hs0) hs
    rw [rOf_rt hZ ⟨he0, hek⟩] at h2
    rw [Real.dist_eq, sub_zero, abs_of_pos h1.1]
    exact lt_of_lt_of_le h2 (min_le_left _ _)
  · filter_upwards [eventually_gt_atTop 0] with s hs
    exact (rOf_spec hZ hs).1.1

/-- `p'(r) → 1/2` as `r → 0⁺`. -/
lemma tendsto_deriv_rp_zero : Tendsto (deriv rp) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h0 : Tendsto (besselJ 0) (𝓝[>] 0) (𝓝 1) := by
    have := (continuous_besselJ 0).tendsto 0
    rw [besselJ_zero_at_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := h0.sub tendsto_besselJ_one_div_pos
  refine (this.congr' ?_).trans (by norm_num)
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [deriv_rp_eq x (ne_of_gt hx)]

/-- `B(x)/x → 1/2` as `x → 0⁺`. -/
lemma tendsto_besselB_div : Tendsto (fun x => besselB x / x) (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have h0 : Tendsto (besselJ 0) (𝓝[>] 0) (𝓝 1) := by
    have := (continuous_besselJ 0).tendsto 0
    rw [besselJ_zero_at_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (besselJ 1) (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_besselJ 1).tendsto 0
    simp only [besselJ_zero_arg] at this
    exact this.mono_left nhdsWithin_le_nhds
  have := ((h0.pow 2).add (h1.pow 2)).sub (h0.mul tendsto_besselJ_one_div_pos)
  refine (this.congr' ?_).trans (by norm_num)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ≠ 0 := ne_of_gt hx
  simp only [besselB]
  field_simp

/-- Composition with `α r` preserves limits at `0⁺`. -/
lemma tendsto_alpha_mul (hZ : ExtZeros) :
    Tendsto (fun r => pAlpha * r) (𝓝[>] 0) (𝓝[>] 0) := by
  have hα := (parameter_signs hZ).2.2.1
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have : Tendsto (fun r : ℝ => pAlpha * r) (𝓝 0) (𝓝 (pAlpha * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact mul_pos hα hr

/-- `G(r) → 2λ - K` as `r → 0⁺`. -/
theorem tendsto_rG_zero (hZ : ExtZeros) : Tendsto rG (𝓝[>] 0) (𝓝 (2 * pLam - pK)) := by
  have hα := (parameter_signs hZ).2.2.1
  have hBa := tendsto_besselB_div.comp (tendsto_alpha_mul hZ)
  have hB := tendsto_besselB_div
  have hp := tendsto_besselJ_one_div_pos
  have := tendsto_const_nhds (x := pK) |>.add
    (((tendsto_const_nhds (x := pAlpha ^ 2)).mul hBa |>.sub
      ((tendsto_const_nhds (x := pK)).mul hB)).div (hp.pow 2) (by norm_num))
  refine (this.congr' ?_).trans ?_
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hr' : r ≠ 0 := ne_of_gt hr
    simp only [Function.comp, rG, rp, Pi.div_apply]
    field_simp
  · rw [pLam_eq]; norm_num; ring

lemma tendsto_besselJ_zero_pos : Tendsto (besselJ 0) (𝓝[>] 0) (𝓝 1) := by
  have := (continuous_besselJ 0).tendsto 0
  rw [besselJ_zero_at_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma tendsto_ru_zero : Tendsto ru (𝓝[>] 0) (𝓝 pSigma) := by
  have := tendsto_besselJ_zero_pos.add_const pc
  simpa [ru, pSigma] using! this

lemma tendsto_rPhi_zero (hZ : ExtZeros) : Tendsto rPhi (𝓝[>] 0) (𝓝 1) :=
  tendsto_besselJ_zero_pos.comp (tendsto_alpha_mul hZ)

lemma pSigma_pos (hZ : ExtZeros) : 0 < pSigma := by
  have := (parameter_signs hZ).2.2.2.2.2.2.1
  unfold pSigma; linarith

/-- Transfer of a radial limit at `r → 0⁺` to `t → ∞`. -/
lemma tendsto_atTop_of_radial (hZ : ExtZeros) {F : ℝ → ℝ} (h : ℝ → ℝ) {L : ℝ}
    (hF : Tendsto h (𝓝[>] 0) (𝓝 L)) (heq : ∀ r ∈ Ioo 0 jk, F (rt r) = h r) :
    Tendsto F atTop (𝓝 L) := by
  refine (hF.comp (tendsto_rOf_atTop hZ)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with s hs
  obtain ⟨hr, hrt⟩ := rOf_spec hZ hs
  have := heq _ hr
  rw [hrt] at this
  exact this.symm

/-- `f(t)/t → ℓ` as `t → ∞`. -/
theorem tendsto_fExt_div_atTop (hZ : ExtZeros) :
    Tendsto (fun s => fExt s / s) atTop (𝓝 pEll) := by
  have hσ := pSigma_pos hZ
  have h : Tendsto (fun r => rPhi r / ru r) (𝓝[>] 0) (𝓝 pEll) := by
    have := (tendsto_rPhi_zero hZ).div tendsto_ru_zero hσ.ne'
    simpa [pEll] using! this
  refine tendsto_atTop_of_radial hZ _ h fun r hr => ?_
  have hs := rt_pos hZ hr.1 hr.2
  obtain ⟨hp, hu, -⟩ := radial_equations hZ _ hr.1 hr.2
  simp only [fExt, hs.ne', if_false, abs_of_pos hs, pf, rOf_rt hZ hr]
  unfold rt
  field_simp

/-- `f(s)/s → -ℓ` as `s → -∞`. -/
theorem tendsto_fExt_div_atBot (hZ : ExtZeros) :
    Tendsto (fun s => fExt s / s) atBot (𝓝 (-pEll)) := by
  have h := (tendsto_fExt_div_atTop hZ).neg.comp tendsto_neg_atBot_atTop
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with s hs
  simp only [Function.comp, fExt, hs.ne, (neg_pos.mpr hs).ne', if_false, abs_neg]
  rw [abs_of_neg hs]
  field_simp

/-- `b(t)/t → 2λℓ` as `t → ∞`. -/
theorem tendsto_bExt_div_atTop (hZ : ExtZeros) :
    Tendsto (fun s => bExt s / s) atTop (𝓝 (2 * pLam * pEll)) := by
  have hσ := pSigma_pos hZ
  have hα := (parameter_signs hZ).2.2.1
  have hk0 : 0 < jk := (parameter_signs hZ).1.trans (parameter_signs hZ).2.1
  have hJa := tendsto_besselJ_one_div_pos.comp (tendsto_alpha_mul hZ)
  have hJ := tendsto_besselJ_one_div_pos
  have hφ := tendsto_rPhi_zero hZ
  have hnum := ((tendsto_const_nhds (x := pK)).mul tendsto_deriv_rp_zero).add
    ((tendsto_rG_zero hZ).mul hJ) |>.add
    ((tendsto_const_nhds (x := pAlpha ^ 2)).mul (hφ.mul hJa) |>.div hJ (by norm_num))
  have h := hnum.div tendsto_ru_zero hσ.ne'
  have hlim : (pK * (1 / 2) + (2 * pLam - pK) * (1 / 2) + pAlpha ^ 2 * (1 * (1 / 2)) / (1 / 2)) /
      pSigma = 2 * pLam * pEll := by
    rw [pLam_eq, pEll]; field_simp; ring
  rw [hlim] at h
  refine tendsto_atTop_of_radial hZ (fun r => rb r / rt r) (h.congr' ?_) fun r hr => ?_
  · filter_upwards [Ioo_mem_nhdsGT hk0] with r hr
    obtain ⟨hp, hu, -⟩ := radial_equations hZ r hr.1 hr.2
    have hr0 : r ≠ 0 := hr.1.ne'
    simp only [Function.comp, rb, rt, deriv_rPhi_eq, rPhi, rp, Pi.div_apply] at hp ⊢
    field_simp
    ring
  · have hs := rt_pos hZ hr.1 hr.2
    simp only [bExt, hs.ne', if_false, abs_of_pos hs, pb, sign_pos hs, SignType.coe_one, one_mul,
      rOf_rt hZ hr]

/-- `b(s)/s → 2λℓ` as `s → -∞` (`b` is odd). -/
theorem tendsto_bExt_div_atBot (hZ : ExtZeros) :
    Tendsto (fun s => bExt s / s) atBot (𝓝 (2 * pLam * pEll)) := by
  have h := (tendsto_bExt_div_atTop hZ).comp tendsto_neg_atBot_atTop
  refine h.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with s hs
  simp only [Function.comp, bExt, hs.ne, (neg_pos.mpr hs).ne', if_false, abs_neg,
    sign_neg hs, sign_pos (neg_pos.mpr hs), SignType.coe_one, SignType.coe_neg_one]
  rw [abs_of_neg hs]
  field_simp

end Buckling
end
end ChunkedSource065
/- END SOURCE 065 -/

/- BEGIN SOURCE 066: RequestProject/Profiles/EndpointK.lean -/
section ChunkedSource066

/-!
# Expansions at the endpoint `r = k` (Lemma 4.11 of the paper)

With `δ = k - r`, we derive one-sided expansions of `p, u, φ` and `ψ(r) = J₁(αr)` by
integrating the radial equations, using `isBigO_pow_succ_of_deriv`.
-/

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace Buckling

/-- `(k - r)^n`. -/
noncomputable abbrev dk (n : ℕ) : ℝ → ℝ := fun r => (jk - r) ^ n

/-- `ψ(r) = J₁(α r)`, so that `φ' = -α ψ`. -/
noncomputable def rpsi (r : ℝ) : ℝ := besselJ 1 (pAlpha * r)

/-- `j = J₁(q)`. -/
noncomputable def jJ : ℝ := besselJ 1 jq

lemma isBigO_bdd_mul {f g : ℝ → ℝ} {n : ℕ} {L : ℝ} (hg : Tendsto g (𝓝[<] jk) (𝓝 L))
    (h : f =O[𝓝[<] jk] dk n) : (fun r => g r * f r) =O[𝓝[<] jk] dk n := by
  have := (hg.isBigO_one ℝ).mul h
  simpa using this

lemma isBigO_dk_mono {f : ℝ → ℝ} {m n : ℕ} (hmn : m ≤ n) (h : f =O[𝓝[<] jk] dk n) :
    f =O[𝓝[<] jk] dk m := h.trans (isBigO_pow_pow hmn)

lemma isBigO_const_dk (C : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (fun r => C * (jk - r) ^ n) =O[𝓝[<] jk] dk m :=
  ((isBigO_const_mul_self C (dk n) _)).trans (isBigO_pow_pow hmn)

lemma isBigO_dk_mul {f g : ℝ → ℝ} {m n : ℕ} (hf : f =O[𝓝[<] jk] dk m)
    (hg : g =O[𝓝[<] jk] dk n) : (fun r => f r * g r) =O[𝓝[<] jk] dk (m + n) := by
  exact (hf.mul hg).congr_right fun x => (pow_add _ _ _).symm

lemma isBigO_of_eventuallyEq {f g : ℝ → ℝ} {n : ℕ} (h : g =O[𝓝[<] jk] dk n)
    (heq : ∀ᶠ r in 𝓝[<] jk, f r = g r) : f =O[𝓝[<] jk] dk n :=
  h.congr' (heq.mono fun _ h => h.symm) EventuallyEq.rfl

lemma continuousAt_ne_zero {f : ℝ → ℝ} {k : ℝ} (hk : k ≠ 0) (hf : ContinuousAt f k) :
    ContinuousAt (fun r => f r / r) k := hf.div continuousAt_id hk

lemma ru_jk : ru jk = 0 := by simp [ru, pc]

lemma hasDerivAt_rPhi' (r : ℝ) : HasDerivAt rPhi (-pAlpha * rpsi r) r := hasDerivAt_rPhi r

section

variable (hZ : ExtZeros)
include hZ

lemma eventually_pos_nhds_jk : ∀ᶠ s in 𝓝 jk, 0 < s := lt_mem_nhds (jk_pos hZ)

lemma alpha_jk : pAlpha * jk = jq := by
  have := jk_pos hZ; unfold pAlpha; field_simp

lemma rPhi_jk : rPhi jk = 0 := by
  simp only [rPhi, alpha_jk hZ]; exact ((hZ 0 (by norm_num)).2.2.1 1 le_rfl).1

lemma rpsi_jk : rpsi jk = jJ := by simp only [rpsi, alpha_jk hZ, jJ]

lemma hasDerivAt_rpsi {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt rpsi (pAlpha * rPhi r - rpsi r / r) r := by
  have hα := (parameter_signs hZ).2.2.1
  have h := (hasDerivAt_besselJ_one (pAlpha * r) (mul_ne_zero hα.ne' hr)).comp r
    ((hasDerivAt_id r).const_mul pAlpha)
  unfold rpsi rPhi
  convert! h using 1 <;> norm_num <;> try field_simp <;> ring

/-! ### `O`-calculus helpers -/

lemma isBigO_div_r {f : ℝ → ℝ} {n : ℕ} (h : f =O[𝓝[<] jk] dk n) :
    (fun r => f r / r) =O[𝓝[<] jk] dk n := by
  have hinv : (fun r : ℝ => r⁻¹) =O[𝓝[<] jk] (fun _ => (1 : ℝ)) := by
    have := ((continuousAt_inv₀ (jk_pos hZ).ne').tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio jk)))
    exact this.isBigO_one ℝ
  have := hinv.mul h
  simpa [div_eq_inv_mul] using this

lemma eventually_pos_nhdsLT_jk : ∀ᶠ r in 𝓝[<] jk, 0 < r :=
  mem_nhdsWithin_of_mem_nhds (eventually_pos_nhds_jk hZ)

lemma tendsto_const_div_jk_mul (C : ℝ) :
    Tendsto (fun r => C / (jk * r)) (𝓝[<] jk) (𝓝 (C / (jk * jk))) := by
  have hk := jk_pos hZ
  have : ContinuousAt (fun r => C / (jk * r)) jk :=
    continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
  exact this.tendsto.mono_left nhdsWithin_le_nhds

/-! ### Expansions of `p` and `u` -/

/-- `p = O(δ)`. -/
lemma rp_O1 : rp =O[𝓝[<] jk] dk 1 := by
  apply isBigO_pow_succ_of_deriv (F' := fun r => ru r - pc - rp r / r)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs using hasDerivAt_rp s hs.ne'
  · exact rp_jk hZ
  · apply isBigO_one_of_continuousAt
    have h1 : Continuous ru := (continuous_besselJ 0).add continuous_const
    exact (h1.continuousAt.sub continuousAt_const).sub
      (continuousAt_ne_zero (jk_pos hZ).ne' (continuous_besselJ 1).continuousAt)

/-- `u = O(δ²)`. -/
lemma ru_O2 : ru =O[𝓝[<] jk] dk 2 := by
  apply isBigO_pow_succ_of_deriv (F' := fun r => -rp r)
  · exact Eventually.of_forall fun s => hasDerivAt_ru s
  · exact ru_jk
  · exact (rp_O1 hZ).neg_left

/-- `p - cδ = O(δ²)`. -/
lemma rp_O2 : (fun r => rp r - pc * (jk - r)) =O[𝓝[<] jk] dk 2 := by
  apply isBigO_pow_succ_of_deriv (F' := fun r => ru r - rp r / r)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    have := (hasDerivAt_rp s hs.ne').fun_sub (((hasDerivAt_id s).const_sub jk).const_mul pc)
    convert! this using 1 <;> norm_num <;> ring
  · simp [rp_jk hZ]
  · exact (isBigO_dk_mono (by norm_num) (ru_O2 hZ)).sub (isBigO_div_r hZ (rp_O1 hZ))

/-- `u - cδ²/2 = O(δ³)`. -/
lemma ru_O3 : (fun r => ru r - pc / 2 * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
  apply isBigO_pow_succ_of_deriv (F' := fun r => -(rp r - pc * (jk - r)))
  · refine Eventually.of_forall fun s => ?_
    have := (hasDerivAt_ru s).fun_sub ((((hasDerivAt_id s).const_sub jk).fun_pow 2).const_mul (pc / 2))
    convert! this using 1 <;> norm_num <;> ring
  · simp [ru_jk]
  · exact (rp_O2 hZ).neg_left

/-- `p - cδ - cδ²/(2k) = O(δ³)`. -/
lemma rp_O3 :
    (fun r => rp r - pc * (jk - r) - pc / (2 * jk) * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
  have hk := jk_pos hZ
  apply isBigO_pow_succ_of_deriv
    (F' := fun r => ru r - (rp r - pc * (jk - r)) / r - pc / (jk * r) * (jk - r) ^ 2)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    have := ((hasDerivAt_rp s hs.ne').fun_sub (((hasDerivAt_id s).const_sub jk).const_mul pc)).fun_sub
      ((((hasDerivAt_id s).const_sub jk).fun_pow 2).const_mul (pc / (2 * jk)))
    convert! this using 1 <;> norm_num <;> try field_simp <;> ring
  · simp [rp_jk hZ]
  · exact ((ru_O2 hZ).sub (isBigO_div_r hZ (rp_O2 hZ))).sub
      (isBigO_bdd_mul (tendsto_const_div_jk_mul hZ pc) (isBigO_refl (dk 2) _))

/-! ### Expansions of `φ` and `ψ` -/

/-- `ψ - j = O(δ)`. -/
lemma rpsi_O1 : (fun r => rpsi r - jJ) =O[𝓝[<] jk] dk 1 := by
  apply isBigO_pow_succ_of_deriv (F' := fun r => pAlpha * rPhi r - rpsi r / r)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    simpa using (hasDerivAt_rpsi hZ hs.ne').sub_const jJ
  · simp [rpsi_jk hZ]
  · apply isBigO_one_of_continuousAt
    have h1 : Continuous rPhi := (continuous_besselJ 0).comp (continuous_const.mul continuous_id)
    have h2 : Continuous rpsi := (continuous_besselJ 1).comp (continuous_const.mul continuous_id)
    exact (continuousAt_const.mul h1.continuousAt).sub
      (continuousAt_ne_zero (jk_pos hZ).ne' h2.continuousAt)

/-- `φ - αjδ = O(δ²)`. -/
lemma rPhi_O2 : (fun r => rPhi r - pAlpha * jJ * (jk - r)) =O[𝓝[<] jk] dk 2 := by
  apply isBigO_pow_succ_of_deriv (F' := fun r => -pAlpha * (rpsi r - jJ))
  · refine Eventually.of_forall fun s => ?_
    have := (hasDerivAt_rPhi' s).fun_sub (((hasDerivAt_id s).const_sub jk).const_mul (pAlpha * jJ))
    convert! this using 1 <;> norm_num <;> ring
  · simp [rPhi_jk hZ]
  · exact (rpsi_O1 hZ).const_mul_left _

lemma rPhi_O1 : rPhi =O[𝓝[<] jk] dk 1 := by
  exact ((isBigO_dk_mono (m := 1) (by norm_num) (rPhi_O2 hZ)).add
    (isBigO_const_dk (pAlpha * jJ) (le_refl 1))).congr_left fun r => by ring

/-- `ψ - j - jδ/k = O(δ²)`. -/
lemma rpsi_O2 : (fun r => rpsi r - jJ - jJ / jk * (jk - r)) =O[𝓝[<] jk] dk 2 := by
  have hk := jk_pos hZ
  apply isBigO_pow_succ_of_deriv
    (F' := fun r => pAlpha * rPhi r - (rpsi r - jJ) / r - jJ / (jk * r) * (jk - r) ^ 1)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    have := ((hasDerivAt_rpsi hZ hs.ne').sub_const jJ).fun_sub
      (((hasDerivAt_id s).const_sub jk).const_mul (jJ / jk))
    convert! this using 1 <;> norm_num <;> try field_simp <;> ring
  · simp [rpsi_jk hZ]
  · exact (((rPhi_O1 hZ).const_mul_left pAlpha).sub (isBigO_div_r hZ (rpsi_O1 hZ))).sub
      (isBigO_bdd_mul (tendsto_const_div_jk_mul hZ jJ) (isBigO_refl (dk 1) _))

/-- The `δ²` coefficient of `ψ`. -/
noncomputable def psi2 : ℝ := jJ / jk ^ 2 - pAlpha ^ 2 * jJ / 2

/-- `ψ - j - jδ/k - ψ₂δ² = O(δ³)`. -/
lemma rpsi_O3 :
    (fun r => rpsi r - jJ - jJ / jk * (jk - r) - psi2 * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
  have hk := jk_pos hZ
  apply isBigO_pow_succ_of_deriv
    (F' := fun r => pAlpha * (rPhi r - pAlpha * jJ * (jk - r)) -
      (rpsi r - jJ - jJ / jk * (jk - r)) / r - 2 * jJ / (jk ^ 2 * r) * (jk - r) ^ 2)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    have := (((hasDerivAt_rpsi hZ hs.ne').sub_const jJ).fun_sub
      (((hasDerivAt_id s).const_sub jk).const_mul (jJ / jk))).fun_sub
      ((((hasDerivAt_id s).const_sub jk).fun_pow 2).const_mul psi2)
    convert! this using 1 <;> norm_num [psi2] <;> try field_simp <;> ring
  · simp [rpsi_jk hZ]
  · have ht : Tendsto (fun r => 2 * jJ / (jk ^ 2 * r)) (𝓝[<] jk)
        (𝓝 (2 * jJ / (jk ^ 2 * jk))) := by
      have : ContinuousAt (fun r => 2 * jJ / (jk ^ 2 * r)) jk :=
        continuousAt_const.div (continuousAt_const.mul continuousAt_id) (by positivity)
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    exact (((rPhi_O2 hZ).const_mul_left pAlpha).sub (isBigO_div_r hZ (rpsi_O2 hZ))).sub
      (isBigO_bdd_mul ht (isBigO_refl (dk 2) _))

/-- `φ - αjδ - αjδ²/(2k) = O(δ³)`. -/
lemma rPhi_O3 : (fun r => rPhi r - pAlpha * jJ * (jk - r) - pAlpha * jJ / (2 * jk) * (jk - r) ^ 2)
    =O[𝓝[<] jk] dk 3 := by
  have hk := jk_pos hZ
  apply isBigO_pow_succ_of_deriv (F' := fun r => -pAlpha * (rpsi r - jJ - jJ / jk * (jk - r)))
  · refine Eventually.of_forall fun s => ?_
    have := ((hasDerivAt_rPhi' s).fun_sub (((hasDerivAt_id s).const_sub jk).const_mul
      (pAlpha * jJ))).fun_sub ((((hasDerivAt_id s).const_sub jk).fun_pow 2).const_mul
      (pAlpha * jJ / (2 * jk)))
    convert! this using 1 <;> norm_num <;> try field_simp <;> ring
  · simp [rPhi_jk hZ]
  · exact (rpsi_O2 hZ).const_mul_left _

/-- `p' + c + cδ/k = O(δ²)`, with `p' = u - c - p/r`. -/
lemma deriv_rp_O2 : (fun r => (ru r - pc - rp r / r) + pc + pc / jk * (jk - r))
    =O[𝓝[<] jk] dk 2 := by
  have hk := jk_pos hZ
  refine isBigO_of_eventuallyEq (((ru_O2 hZ).sub (isBigO_div_r hZ (rp_O2 hZ))).sub
    (isBigO_bdd_mul (tendsto_const_div_jk_mul hZ pc) (isBigO_refl (dk 2) _))) ?_
  filter_upwards [eventually_pos_nhdsLT_jk hZ] with r hr
  field_simp; ring

lemma pK_pc_sq : pK * pc ^ 2 = pAlpha ^ 2 * jJ ^ 2 := by
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  unfold pK jJ; field_simp

lemma jJ_pos : 0 < jJ := (parameter_signs hZ).2.2.2.2.2.2.2.1

lemma pBeta_eq : pBeta = pAlpha * jJ / pc := by
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hα := (parameter_signs hZ).2.2.1
  have hj := jJ_pos hZ
  unfold pBeta pK
  rw [Real.sqrt_sq (by positivity)]
  rfl

end

end Buckling
end
end ChunkedSource066
/- END SOURCE 066 -/

/- BEGIN SOURCE 067: RequestProject/Profiles/EndpointK2.lean -/
section ChunkedSource067

/-!
# The quantities `N` and `M` at the endpoint `r = k`

`N = φp' - pφ'` (numerator of `z`) and `M = Kp² + αrB(αr) - KrB(r) = Gp²` satisfy
`(rN)' = r(λ - 1 + r⁻²)pφ` and `(M/r)' = (Kpp' - φφ')/r - 2Kp²/r²`; integrating these gives
their leading behaviour at `k`.
-/

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace Buckling

/-- `p' = u - c - p/r`. -/
noncomputable def rpd (r : ℝ) : ℝ := ru r - pc - rp r / r
/-- `N = φ p' - p φ'`. -/
noncomputable def Nfun (r : ℝ) : ℝ := rPhi r * rpd r + pAlpha * rp r * rpsi r
/-- `N₂ = α r B(α r) - K r B(r)`. -/
noncomputable def N2fun (r : ℝ) : ℝ := pAlpha * r * besselB (pAlpha * r) - pK * r * besselB r
/-- `M = K p² + N₂ = G p²`. -/
noncomputable def Mfun (r : ℝ) : ℝ := pK * rp r ^ 2 + N2fun r
/-- `M'`. -/
noncomputable def Mdfun (r : ℝ) : ℝ :=
  pAlpha ^ 2 * r * (rPhi r ^ 2 + rpsi r ^ 2) - pK * r * (ru r - pc) ^ 2 +
    2 * pK * rp r * (ru r - pc) - pK * rp r ^ 2 * (r + 2 / r)
/-- `(M/r)'`. -/
noncomputable def Ifun (r : ℝ) : ℝ :=
  (pK * rp r * rpd r + pAlpha * rPhi r * rpsi r) / r - 2 * pK * rp r ^ 2 / r ^ 2

lemma isBigO_lin_quad (a b : ℝ) :
    (fun r => a * (jk - r) + b * (jk - r) ^ 2) =O[𝓝[<] jk] dk 1 :=
  ((isBigO_const_dk a (le_refl 1)).add (isBigO_const_dk b (by norm_num : 1 ≤ 2))).congr_left
    fun r => by ring

section

variable (hZ : ExtZeros)
include hZ

lemma hasDerivAt_Mfun {r : ℝ} (hr : r ≠ 0) : HasDerivAt Mfun (Mdfun r) r := by
  have hα := (parameter_signs hZ).2.2.1
  have h := ((hasDerivAt_rp r hr).pow 2).const_mul pK |>.add (hasDerivAt_N r hr hα.ne')
  unfold Mfun N2fun
  convert h using 1
  simp only [Mdfun, rPhi, rpsi, ru, rp]
  field_simp
  ring

lemma hasDerivAt_Mfun_div {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => Mfun r / r) (Ifun r) r := by
  have h := (hasDerivAt_Mfun hZ hr).fun_div (hasDerivAt_id r) hr
  convert! h using 1 <;>
    norm_num [Ifun, Mdfun, Mfun, N2fun, rpd, besselB, rPhi, rpsi, ru, rp, id_eq] <;>
    try field_simp <;> ring

lemma Mfun_jk : Mfun jk = 0 := by
  have h := (besselB_endpoints hZ).2.2
  simp only [Mfun, N2fun, rp_jk hZ, alpha_jk hZ]
  linear_combination (-jk) * h - (besselB jq) * alpha_jk hZ

lemma continuousAt_rpd : ContinuousAt rpd jk := by
  have h1 : Continuous ru := (continuous_besselJ 0).add continuous_const
  exact (h1.continuousAt.sub continuousAt_const).sub
    (continuousAt_ne_zero (jk_pos hZ).ne' (continuous_besselJ 1).continuousAt)

lemma rpd_jk : rpd jk = -pc := by simp [rpd, ru_jk, rp_jk hZ]

lemma tendsto_rpd : Tendsto rpd (𝓝[<] jk) (𝓝 (-pc)) := by
  have := (continuousAt_rpd hZ).tendsto
  rw [rpd_jk hZ] at this
  exact this.mono_left nhdsWithin_le_nhds

lemma tendsto_rpsi : Tendsto rpsi (𝓝[<] jk) (𝓝 jJ) := by
  have h2 : Continuous rpsi := (continuous_besselJ 1).comp (continuous_const.mul continuous_id)
  have := h2.continuousAt.tendsto (x := jk)
  rw [rpsi_jk hZ] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `(M/r)' + 2Kc²δ²/k² = O(δ³)`. -/
lemma Ifun_O3 : (fun r => Ifun r + 2 * pK * pc ^ 2 / jk ^ 2 * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
  have hk := jk_pos hZ
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hK : pK = pAlpha ^ 2 * jJ ^ 2 / pc ^ 2 := by
    rw [← pK_pc_sq hZ]; field_simp
  -- the four first-order products
  have hA1 : (fun r => pK * (rp r - pc * (jk - r) - pc / (2 * jk) * (jk - r) ^ 2) * rpd r +
      pK * (pc * (jk - r) + pc / (2 * jk) * (jk - r) ^ 2) * (rpd r + pc + pc / jk * (jk - r)) +
      pAlpha * (rPhi r - pAlpha * jJ * (jk - r) - pAlpha * jJ / (2 * jk) * (jk - r) ^ 2) * rpsi r +
      pAlpha * (pAlpha * jJ * (jk - r) + pAlpha * jJ / (2 * jk) * (jk - r) ^ 2) *
        (rpsi r - jJ - jJ / jk * (jk - r))) =O[𝓝[<] jk] dk 3 := by
    have t1 : (fun r => pK * (rp r - pc * (jk - r) - pc / (2 * jk) * (jk - r) ^ 2) * rpd r)
        =O[𝓝[<] jk] dk 3 := by
      have := isBigO_bdd_mul (tendsto_rpd hZ) ((rp_O3 hZ).const_mul_left pK)
      exact this.congr_left fun r => by ring
    have t2 : (fun r => pK * (pc * (jk - r) + pc / (2 * jk) * (jk - r) ^ 2) *
        (rpd r + pc + pc / jk * (jk - r))) =O[𝓝[<] jk] dk 3 := by
      have := isBigO_dk_mul ((isBigO_lin_quad pc (pc / (2 * jk))).const_mul_left pK)
        (show (fun r => rpd r + pc + pc / jk * (jk - r)) =O[𝓝[<] jk] dk 2 from deriv_rp_O2 hZ)
      exact this.congr_left fun r => by ring
    have t3 : (fun r => pAlpha * (rPhi r - pAlpha * jJ * (jk - r) -
        pAlpha * jJ / (2 * jk) * (jk - r) ^ 2) * rpsi r) =O[𝓝[<] jk] dk 3 := by
      have := isBigO_bdd_mul (tendsto_rpsi hZ) ((rPhi_O3 hZ).const_mul_left pAlpha)
      exact this.congr_left fun r => by ring
    have t4 : (fun r => pAlpha * (pAlpha * jJ * (jk - r) + pAlpha * jJ / (2 * jk) * (jk - r) ^ 2) *
        (rpsi r - jJ - jJ / jk * (jk - r))) =O[𝓝[<] jk] dk 3 :=
      (isBigO_dk_mul ((isBigO_lin_quad (pAlpha * jJ) (pAlpha * jJ / (2 * jk))).const_mul_left
        pAlpha) (rpsi_O2 hZ)).congr_left fun r => by ring
    exact ((t1.add t2).add t3).add t4
  have hsq : (fun r => rp r ^ 2 - pc ^ 2 * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
    have h1 : (fun r => rp r + pc * (jk - r)) =O[𝓝[<] jk] dk 1 :=
      ((rp_O1 hZ).add (isBigO_const_dk pc (le_refl 1))).congr_left fun r => by ring
    exact (isBigO_dk_mul (rp_O2 hZ) h1).congr_left fun r => by ring
  have hr2 : Tendsto (fun r => 2 * pK / r ^ 2) (𝓝[<] jk) (𝓝 (2 * pK / jk ^ 2)) := by
    have : ContinuousAt (fun r => 2 * pK / r ^ 2) jk :=
      continuousAt_const.div (continuousAt_id.pow 2) (by positivity)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have hr3 : Tendsto (fun r => 2 * pK * pc ^ 2 * (jk + r) / (jk ^ 2 * r ^ 2)) (𝓝[<] jk)
      (𝓝 (2 * pK * pc ^ 2 * (jk + jk) / (jk ^ 2 * jk ^ 2))) := by
    have : ContinuousAt (fun r => 2 * pK * pc ^ 2 * (jk + r) / (jk ^ 2 * r ^ 2)) jk :=
      (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
        (continuousAt_const.mul (continuousAt_id.pow 2)) (by positivity)
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have htot := ((isBigO_div_r hZ hA1).sub (isBigO_bdd_mul hr2 hsq)).sub
    (isBigO_bdd_mul hr3 (isBigO_refl (dk 3) _))
  refine isBigO_of_eventuallyEq htot ?_
  filter_upwards [eventually_pos_nhdsLT_jk hZ] with r hr
  simp only [Ifun]
  rw [hK]
  field_simp
  ring

/-- `M/r - 2Kc²δ³/(3k²) = O(δ⁴)`. -/
lemma Mdiv_O4 : (fun r => Mfun r / r - 2 * pK * pc ^ 2 / (3 * jk ^ 2) * (jk - r) ^ 3)
    =O[𝓝[<] jk] dk 4 := by
  have hk := jk_pos hZ
  apply isBigO_pow_succ_of_deriv (F' := fun r => Ifun r + 2 * pK * pc ^ 2 / jk ^ 2 * (jk - r) ^ 2)
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    have := (hasDerivAt_Mfun_div hZ hs.ne').fun_sub
      ((((hasDerivAt_id s).const_sub jk).fun_pow 3).const_mul (2 * pK * pc ^ 2 / (3 * jk ^ 2)))
    convert! this using 1 <;> norm_num <;> try field_simp <;> ring
  · simp [Mfun_jk hZ]
  · exact Ifun_O3 hZ

/-- `(rN)' = r(λ - 1 + r⁻²) p φ`. -/
lemma hasDerivAt_rN {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (fun r => r * Nfun r) (r * (pLam - 1 + 1 / r ^ 2) * rp r * rPhi r) r := by
  have h := (hasDerivAt_id r).fun_mul (((hasDerivAt_rPhi' r).fun_mul ((((hasDerivAt_ru r).sub_const pc).fun_sub
    ((hasDerivAt_rp r hr).fun_div (hasDerivAt_id r) hr)))).fun_add
    (((hasDerivAt_rp r hr).const_mul pAlpha).fun_mul (hasDerivAt_rpsi hZ hr)))
  convert! h using 1 <;> norm_num [id_eq, pLam_eq] <;> try field_simp <;> ring

lemma Nfun_jk : Nfun jk = 0 := by simp [Nfun, rPhi_jk hZ, rp_jk hZ]

/-- The leading coefficient of `rN` at `k`. -/
noncomputable def n3 : ℝ := -(jk * (pLam - 1 + 1 / jk ^ 2) * pc * (pAlpha * jJ)) / 3

/-- `rN - n₃δ³ = O(δ⁴)`. -/
lemma rN_O4 : (fun r => r * Nfun r - n3 * (jk - r) ^ 3) =O[𝓝[<] jk] dk 4 := by
  have hk := jk_pos hZ
  apply isBigO_pow_succ_of_deriv (F' := fun r =>
    (jk - r) ^ 1 * (1 - pLam + 1 / (r * jk)) * rp r * rPhi r +
      jk * (pLam - 1 + 1 / jk ^ 2) * ((rp r - pc * (jk - r)) * rPhi r +
        pc * (jk - r) ^ 1 * (rPhi r - pAlpha * jJ * (jk - r))))
  · filter_upwards [eventually_pos_nhds_jk hZ] with s hs
    have := (hasDerivAt_rN hZ hs.ne').fun_sub
      ((((hasDerivAt_id s).const_sub jk).fun_pow 3).const_mul n3)
    convert! this using 1 <;> norm_num [n3] <;> try field_simp <;> ring
  · simp [Nfun_jk hZ]
  · have hb : Tendsto (fun r => 1 - pLam + 1 / (r * jk)) (𝓝[<] jk)
        (𝓝 (1 - pLam + 1 / (jk * jk))) := by
      have : ContinuousAt (fun r => 1 - pLam + 1 / (r * jk)) jk :=
        continuousAt_const.add (continuousAt_const.div (continuousAt_id.mul continuousAt_const)
          (by positivity))
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    have t1 : (fun r => (jk - r) ^ 1 * (1 - pLam + 1 / (r * jk)) * rp r * rPhi r)
        =O[𝓝[<] jk] dk 3 := by
      have := isBigO_dk_mul (isBigO_dk_mul (isBigO_bdd_mul hb (isBigO_refl (dk 1) (𝓝[<] jk)))
        (rp_O1 hZ)) (rPhi_O1 hZ)
      exact this.congr_left fun r => by ring
    have t2 : (fun r => (rp r - pc * (jk - r)) * rPhi r) =O[𝓝[<] jk] dk 3 :=
      isBigO_dk_mul (rp_O2 hZ) (rPhi_O1 hZ)
    have t3 : (fun r => pc * (jk - r) ^ 1 * (rPhi r - pAlpha * jJ * (jk - r))) =O[𝓝[<] jk] dk 3 :=
      isBigO_dk_mul (isBigO_const_dk pc (le_refl 1)) (rPhi_O2 hZ)
    exact t1.add ((t2.add t3).const_mul_left _)

end

/-- From an expansion `F = a δⁿ + O(δⁿ⁺¹)` to the limit `F/δⁿ → a`. -/
lemma tendsto_div_of_expansion {F : ℝ → ℝ} {k a : ℝ} {n : ℕ}
    (h : (fun r => F r - a * (k - r) ^ n) =O[𝓝[<] k] fun r => (k - r) ^ (n + 1)) :
    Tendsto (fun r => F r / (k - r) ^ n) (𝓝[<] k) (𝓝 a) := by
  have := (tendsto_div_pow_of_isBigO h).add_const a
  rw [zero_add] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  have h0 : (k - r) ^ n ≠ 0 := pow_ne_zero _ (sub_pos.mpr (mem_Iio.mp hr)).ne'
  field_simp
  ring

end Buckling
end
end ChunkedSource067
/- END SOURCE 067 -/

/- BEGIN SOURCE 068: RequestProject/Profiles/EndpointK3.lean -/
section ChunkedSource068

/-!
# Limits of the profile quantities as `r → k⁻` (Lemma 4.11 / 9.1 at `t = 0`)
-/

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace Buckling

section

variable (hZ : ExtZeros)
include hZ

lemma tendsto_rp_div : Tendsto (fun r => rp r / (jk - r) ^ 1) (𝓝[<] jk) (𝓝 pc) :=
  tendsto_div_of_expansion ((rp_O2 hZ).congr_left fun r => by ring)

lemma tendsto_rPhi_div : Tendsto (fun r => rPhi r / (jk - r) ^ 1) (𝓝[<] jk) (𝓝 (pAlpha * jJ)) :=
  tendsto_div_of_expansion ((rPhi_O2 hZ).congr_left fun r => by ring)

omit hZ in
lemma rS_eq {r : ℝ} (hr : r ≠ 0) : rS r = rp r ^ 2 + ru r * rpd r := by
  simp only [rS, rpd, deriv_rp_eq r hr, ru, rp]; ring

/-- `S - c²δ²/2 = O(δ³)`. -/
lemma rS_O3 : (fun r => rS r - pc ^ 2 / 2 * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
  have hX : (fun r => ru r - rp r / r) =O[𝓝[<] jk] dk 1 :=
    (isBigO_dk_mono (by norm_num) (ru_O2 hZ)).sub (isBigO_div_r hZ (rp_O1 hZ))
  have t1 : (fun r => 2 * pc * (jk - r) ^ 1 * (rp r - pc * (jk - r))) =O[𝓝[<] jk] dk 3 :=
    isBigO_dk_mul (isBigO_const_dk (2 * pc) (le_refl 1)) (rp_O2 hZ)
  have t2 : (fun r => (rp r - pc * (jk - r)) * (rp r - pc * (jk - r))) =O[𝓝[<] jk] dk 3 :=
    isBigO_dk_mono (by norm_num) (isBigO_dk_mul (rp_O2 hZ) (rp_O2 hZ))
  have t3 : (fun r => pc / 2 * (jk - r) ^ 2 * (ru r - rp r / r)) =O[𝓝[<] jk] dk 3 :=
    isBigO_dk_mul (isBigO_const_dk (pc / 2) (le_refl 2)) hX
  have t4 : (fun r => rpd r * (ru r - pc / 2 * (jk - r) ^ 2)) =O[𝓝[<] jk] dk 3 :=
    isBigO_bdd_mul (tendsto_rpd hZ) (ru_O3 hZ)
  refine isBigO_of_eventuallyEq (((t1.add t2).add t3).add t4) ?_
  filter_upwards [eventually_pos_nhdsLT_jk hZ] with r hr
  rw [rS_eq hr.ne']
  simp only [rpd]
  ring

lemma tendsto_rS_div : Tendsto (fun r => rS r / (jk - r) ^ 2) (𝓝[<] jk) (𝓝 (pc ^ 2 / 2)) :=
  tendsto_div_of_expansion (rS_O3 hZ)

/-- `N - (n₃/k)δ³ = O(δ⁴)`. -/
lemma Nfun_O4 : (fun r => Nfun r - n3 / jk * (jk - r) ^ 3) =O[𝓝[<] jk] dk 4 := by
  have hk := jk_pos hZ
  have h1 := isBigO_div_r hZ (rN_O4 hZ)
  have h2 : (fun r => n3 / (r * jk) * (jk - r) ^ 4) =O[𝓝[<] jk] dk 4 := by
    have : Tendsto (fun r => n3 / (r * jk)) (𝓝[<] jk) (𝓝 (n3 / (jk * jk))) := by
      have : ContinuousAt (fun r => n3 / (r * jk)) jk :=
        continuousAt_const.div (continuousAt_id.mul continuousAt_const) (by positivity)
      exact this.tendsto.mono_left nhdsWithin_le_nhds
    exact isBigO_bdd_mul this (isBigO_refl _ _)
  refine isBigO_of_eventuallyEq (h1.add h2) ?_
  filter_upwards [eventually_pos_nhdsLT_jk hZ] with r hr
  field_simp
  ring

lemma tendsto_Nfun_div : Tendsto (fun r => Nfun r / (jk - r) ^ 3) (𝓝[<] jk) (𝓝 (n3 / jk)) :=
  tendsto_div_of_expansion (Nfun_O4 hZ)

/-- `M - 2Kc²δ³/(3k) = O(δ⁴)`. -/
lemma Mfun_O4 : (fun r => Mfun r - 2 * pK * pc ^ 2 / (3 * jk) * (jk - r) ^ 3) =O[𝓝[<] jk] dk 4 := by
  have hk := jk_pos hZ
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] jk) (𝓝 jk) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 := isBigO_bdd_mul hid (Mdiv_O4 hZ)
  have h2 := isBigO_const_dk (2 * pK * pc ^ 2 / (3 * jk ^ 2)) (le_refl 4)
  refine isBigO_of_eventuallyEq (h1.sub h2) ?_
  filter_upwards [eventually_pos_nhdsLT_jk hZ] with r hr
  field_simp
  ring

lemma tendsto_Mfun_div : Tendsto (fun r => Mfun r / (jk - r) ^ 3) (𝓝[<] jk)
    (𝓝 (2 * pK * pc ^ 2 / (3 * jk))) :=
  tendsto_div_of_expansion (Mfun_O4 hZ)

omit hZ in
lemma Mdfun_eq {r : ℝ} (hr : r ≠ 0) : Mdfun r = r * Ifun r + Mfun r / r := by
  simp only [Ifun, Mdfun, Mfun, N2fun, rpd, besselB, rPhi, rpsi, ru, rp]
  field_simp
  ring

/-- `M' + 2Kc²δ²/k = O(δ³)`. -/
lemma Mdfun_O3 : (fun r => Mdfun r + 2 * pK * pc ^ 2 / jk * (jk - r) ^ 2) =O[𝓝[<] jk] dk 3 := by
  have hk := jk_pos hZ
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] jk) (𝓝 jk) := tendsto_id.mono_left nhdsWithin_le_nhds
  have h1 := isBigO_bdd_mul hid (Ifun_O3 hZ)
  have h2 := isBigO_const_dk (2 * pK * pc ^ 2 / jk ^ 2) (le_refl 3)
  have h3 : (fun r => Mfun r / r) =O[𝓝[<] jk] dk 3 := by
    have := isBigO_dk_mono (m := 3) (by norm_num) (Mdiv_O4 hZ)
    exact (this.add (isBigO_const_dk (2 * pK * pc ^ 2 / (3 * jk ^ 2)) (le_refl 3))).congr_left
      fun r => by ring
  refine isBigO_of_eventuallyEq ((h1.add h2).add h3) ?_
  filter_upwards [eventually_pos_nhdsLT_jk hZ] with r hr
  rw [Mdfun_eq hr.ne']
  field_simp
  ring

lemma tendsto_Mdfun_div : Tendsto (fun r => Mdfun r / (jk - r) ^ 2) (𝓝[<] jk)
    (𝓝 (-(2 * pK * pc ^ 2 / jk))) :=
  tendsto_div_of_expansion ((Mdfun_O3 hZ).congr_left fun r => by ring)

end

end Buckling
end
end ChunkedSource068
/- END SOURCE 068 -/

/- BEGIN SOURCE 069: RequestProject/Profiles/EndpointK4.lean -/
section ChunkedSource069

/-!
# Limits of `f, z, g, G, G_t, b, b_t` as `r → k⁻` (i.e. `t → 0⁺`)
-/

@[expose] public section

open Real Set Filter Topology Asymptotics

namespace Buckling

/-- The explicit radial derivative of `G = M/p²`. -/
noncomputable def Grx (r : ℝ) : ℝ := (Mdfun r * rp r - 2 * Mfun r * rpd r) / rp r ^ 3

section

variable (hZ : ExtZeros)
include hZ

lemma eventually_Ioo_jk : ∀ᶠ r in 𝓝[<] jk, r ∈ Ioo 0 jk := Ioo_mem_nhdsLT (jk_pos hZ)

omit hZ in
lemma eventually_dk_ne : ∀ᶠ r in 𝓝[<] jk, jk - r ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with r hr using (sub_pos.mpr (mem_Iio.mp hr)).ne'

lemma pc_pos : 0 < pc := (parameter_signs hZ).2.2.2.2.2.2.1

/-- `f → β` as `r → k⁻`. -/
theorem tendsto_rf_jk : Tendsto rf (𝓝[<] jk) (𝓝 pBeta) := by
  have h := (tendsto_rPhi_div hZ).div (tendsto_rp_div hZ) (pc_pos hZ).ne'
  rw [← pBeta_eq hZ] at h
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne] with r hr
  simp only [Pi.div_apply, pow_one]
  simp only [rf]
  field_simp

/-- `T → -1/2` as `r → k⁻`. -/
theorem tendsto_rT_jk : Tendsto rT (𝓝[<] jk) (𝓝 (-1 / 2)) := by
  have hc := pc_pos hZ
  have h := ((tendsto_rS_div hZ).div ((tendsto_rp_div hZ).pow 2) (by positivity)).neg
  have hv : -(pc ^ 2 / 2 / pc ^ 2) = -1 / 2 := by field_simp
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne, eventually_Ioo_jk hZ] with r hr hr'
  simp only [Pi.div_apply, pow_one]
  have hp := (radial_equations hZ r hr'.1 hr'.2).1
  simp only [rT]
  field_simp

omit hZ in
lemma rz_eq {r : ℝ} (hr : r ≠ 0) : rz r = Nfun r / rS r := by
  simp only [rz, Nfun, deriv_rp_eq r hr, deriv_rPhi_eq, rpd, ru, rp, rpsi]; ring

/-- The limit of `z/δ`. -/
noncomputable def zc : ℝ := n3 / jk / (pc ^ 2 / 2)

theorem tendsto_rz_div : Tendsto (fun r => rz r / (jk - r) ^ 1) (𝓝[<] jk) (𝓝 zc) := by
  have hc := pc_pos hZ
  have h := (tendsto_Nfun_div hZ).div (tendsto_rS_div hZ) (by positivity)
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne, eventually_Ioo_jk hZ] with r hr hr'
  simp only [Pi.div_apply, pow_one]
  have hS := (rS_pos hZ hr'.1 hr'.2).ne'
  rw [rz_eq hr'.1.ne']
  field_simp

omit hZ in
lemma tendsto_dk1 : Tendsto (fun r => (jk - r) ^ 1) (𝓝[<] jk) (𝓝 0) := by
  have : Tendsto (fun r : ℝ => (jk - r) ^ 1) (𝓝 jk) (𝓝 ((jk - jk) ^ 1)) :=
    ((continuous_const.sub continuous_id).pow 1).tendsto jk
  rw [sub_self, zero_pow one_ne_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `z → 0` as `r → k⁻`. -/
theorem tendsto_rz_jk : Tendsto rz (𝓝[<] jk) (𝓝 0) := by
  have h := (tendsto_rz_div hZ).mul (tendsto_dk1)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne] with r hr
  simp only [pow_one]
  field_simp

/-- `w δ → -αj/c`. -/
theorem tendsto_rw_mul : Tendsto (fun r => rw r * (jk - r) ^ 1) (𝓝[<] jk)
    (𝓝 (-pAlpha * jJ / pc)) := by
  have h := ((tendsto_rpsi hZ).const_mul (-pAlpha)).div (tendsto_rp_div hZ) (pc_pos hZ).ne'
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne, eventually_Ioo_jk hZ] with r hr hr'
  simp only [Pi.div_apply, pow_one]
  have hp := (radial_equations hZ r hr'.1 hr'.2).1.ne'
  simp only [rw, deriv_rPhi_eq, rpsi]
  field_simp

theorem tendsto_rz_rw : Tendsto (fun r => rz r * rw r) (𝓝[<] jk)
    (𝓝 (zc * (-pAlpha * jJ / pc))) := by
  refine ((tendsto_rz_div hZ).mul (tendsto_rw_mul hZ)).congr' ?_
  filter_upwards [eventually_dk_ne] with r hr
  simp only [pow_one]
  field_simp

omit hZ in
lemma rG_eq_M {r : ℝ} (hp : rp r ≠ 0) : rG r = Mfun r / rp r ^ 2 := by
  simp only [rG, Mfun, N2fun]; field_simp

/-- `G/δ → 2K/(3k)`, hence `G → 0`. -/
theorem tendsto_rG_div : Tendsto (fun r => rG r / (jk - r) ^ 1) (𝓝[<] jk)
    (𝓝 (2 * pK * pc ^ 2 / (3 * jk) / pc ^ 2)) := by
  have hc := pc_pos hZ
  have h := (tendsto_Mfun_div hZ).div ((tendsto_rp_div hZ).pow 2) (by positivity)
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne, eventually_Ioo_jk hZ] with r hr hr'
  simp only [Pi.div_apply, pow_one]
  have hp := (radial_equations hZ r hr'.1 hr'.2).1.ne'
  rw [rG_eq_M hp]
  field_simp

theorem tendsto_rG_jk : Tendsto rG (𝓝[<] jk) (𝓝 0) := by
  have h := (tendsto_rG_div hZ).mul (tendsto_dk1)
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne] with r hr
  simp only [pow_one]
  field_simp

/-- The limit of `G_r` at `k`. -/
noncomputable def grk : ℝ :=
  (-(2 * pK * pc ^ 2 / jk) * pc - 2 * (2 * pK * pc ^ 2 / (3 * jk)) * (-pc)) / pc ^ 3

theorem tendsto_Grx : Tendsto Grx (𝓝[<] jk) (𝓝 grk) := by
  have hc := pc_pos hZ
  have h := (((tendsto_Mdfun_div hZ).mul (tendsto_rp_div hZ)).sub
    (((tendsto_Mfun_div hZ).const_mul 2).mul (tendsto_rpd hZ))).div
    ((tendsto_rp_div hZ).pow 3) (by positivity)
  refine h.congr' ?_
  filter_upwards [eventually_dk_ne, eventually_Ioo_jk hZ] with r hr hr'
  simp only [Pi.div_apply, pow_one]
  have hp := (radial_equations hZ r hr'.1 hr'.2).1.ne'
  simp only [Grx]
  field_simp

lemma hasDerivAt_rG_explicit {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rG (Grx r) r := by
  have hp := (radial_equations hZ r hr0 hrk).1
  have hpd : HasDerivAt rp (rpd r) r := hasDerivAt_rp r hr0.ne'
  have h := (hasDerivAt_Mfun hZ hr0.ne').div (hpd.pow 2) (pow_ne_zero 2 hp.ne')
  have heq : rG =ᶠ[𝓝 r] fun x => Mfun x / rp x ^ 2 := by
    have hcont : ContinuousAt rp r := (continuous_besselJ 1).continuousAt
    filter_upwards [hcont.eventually_ne hp.ne'] with x hx
    exact rG_eq_M hx
  refine (h.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [Grx, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  field_simp

lemma Grx_eq {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    Grx r = rb r + 2 * rA r * rG r + 2 * pK * rC r :=
  (hasDerivAt_rG_explicit hZ hr0 hrk).unique (hasDerivAt_rG hZ hr0 hrk)

theorem tendsto_rGt_jk : Tendsto rGt (𝓝[<] jk) (𝓝 (grk / (-1 / 2))) := by
  refine ((tendsto_Grx hZ).div (tendsto_rT_jk hZ) (by norm_num)).congr' ?_
  filter_upwards [eventually_Ioo_jk hZ] with r hr
  simp only [Pi.div_apply]
  simp only [rGt, Grx_eq hZ hr.1 hr.2]

/-- `b → 0` as `r → k⁻`. -/
theorem tendsto_rb_jk : Tendsto rb (𝓝[<] jk) (𝓝 0) := by
  have hc := pc_pos hZ
  have hk := jk_pos hZ
  have hAG : Tendsto (fun r => rA r * rG r) (𝓝[<] jk)
      (𝓝 (-(-pc) * (2 * pK * pc ^ 2 / (3 * jk)) / pc ^ 3)) := by
    have h := ((tendsto_rpd hZ).neg.mul (tendsto_Mfun_div hZ)).div ((tendsto_rp_div hZ).pow 3)
      (by positivity)
    refine h.congr' ?_
    filter_upwards [eventually_dk_ne, eventually_Ioo_jk hZ] with r hr hr'
    simp only [Pi.div_apply, pow_one]
    have hp := (radial_equations hZ r hr'.1 hr'.2).1.ne'
    rw [rG_eq_M hp]
    simp only [rA, deriv_rp_eq r hr'.1.ne', rpd, ru, rp]
    field_simp
    ring
  have hC : Tendsto rC (𝓝[<] jk) (𝓝 (-1 / jk)) := by
    have : ContinuousAt rC jk := continuousAt_const.div continuousAt_id hk.ne'
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have h := ((tendsto_Grx hZ).sub (hAG.const_mul 2)).sub (hC.const_mul (2 * pK))
  have hv : grk - 2 * (-(-pc) * (2 * pK * pc ^ 2 / (3 * jk)) / pc ^ 3) - 2 * pK * (-1 / jk) = 0 := by
    simp only [grk]; field_simp; ring
  rw [hv] at h
  refine h.congr' ?_
  filter_upwards [eventually_Ioo_jk hZ] with r hr
  rw [Grx_eq hZ hr.1 hr.2]
  ring

lemma rbt_eq {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    rbt r = -2 * rz r * rw r - rC r * rGt r := by
  have hT := (rT_neg hZ hr0 hrk).ne
  have hid := (profile_identities_alg hZ hr0 hrk).2.2.1
  have hT' : rT r ≠ 0 := hT
  simp only [rbt, rGt]
  rw [hid]
  field_simp

/-- `b_t` has a limit as `r → k⁻`. -/
theorem tendsto_rbt_jk : Tendsto rbt (𝓝[<] jk)
    (𝓝 (-2 * (zc * (-pAlpha * jJ / pc)) - (-1 / jk) * (grk / (-1 / 2)))) := by
  have hk := jk_pos hZ
  have hC : Tendsto rC (𝓝[<] jk) (𝓝 (-1 / jk)) := by
    have : ContinuousAt rC jk := continuousAt_const.div continuousAt_id hk.ne'
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  have h := ((tendsto_rz_rw hZ).const_mul (-2)).sub (hC.mul (tendsto_rGt_jk hZ))
  refine h.congr' ?_
  filter_upwards [eventually_Ioo_jk hZ] with r hr
  rw [rbt_eq hZ hr.1 hr.2]
  ring

/-- `g → β` as `r → k⁻`. -/
theorem tendsto_rg_jk : Tendsto rg (𝓝[<] jk) (𝓝 pBeta) := by
  have h := (tendsto_rf_jk hZ).sub ((tendsto_rt_jk hZ).mul (tendsto_rz_jk hZ))
  rw [zero_mul, sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_Ioo_jk hZ] with r hr
  rw [rg_eq hZ hr.1 hr.2]

end

end Buckling
end
end ChunkedSource069
/- END SOURCE 069 -/

/- BEGIN SOURCE 070: RequestProject/Concavity/RealSeries.lean -/
section ChunkedSource070

/-!
# The real power series of `G` (Proposition 8.9 of the paper, real form)

`G` is even, so its Taylor series at `0` only contains even powers.  Writing
`G(r) = ∑_m b_m r^{2m}` for `|r| < κ₂`, the function `H(y) = ∑_m b_m y^m` satisfies
`G(r) = H(r²)` on `(0, k)` and `H(k²) = 0`; moreover `b_m ≤ 0` for `m ≥ 2`.
-/

@[expose] public section

open Filter Topology Metric Set Real
open scoped Nat

namespace Buckling

lemma neg_mem_Gsing {z : ℂ} : -z ∈ Gsing ↔ z ∈ Gsing := by
  simp only [Gsing, Finset.mem_insert, Finset.mem_singleton, neg_eq_zero, neg_inj]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · right; right; rw [← h, neg_neg]
    · right; left; exact h
  · rintro (h | h | h)
    · exact Or.inl h
    · right; right; rw [h]
    · right; left; rw [h, neg_neg]

/-- `G` is even. -/
lemma Ghol_neg (z : ℂ) : Ghol (-z) = Ghol z := by
  by_cases hz : z ∈ Gsing
  · have hz' : -z ∈ Gsing := neg_mem_Gsing.mpr hz
    simp only [Ghol, fillSing, hz, hz', if_true]
    have hmap : Filter.map (fun w : ℂ => -w) (𝓝[≠] z) = 𝓝[≠] (-z) :=
      (Homeomorph.neg ℂ).map_punctured_nhds_eq z
    rw [← hmap, limUnder, limUnder, Filter.map_map]
    congr 2
    funext w
    exact Gfun_neg w
  · have hz' : -z ∉ Gsing := fun h => hz (neg_mem_Gsing.mp h)
    rw [Ghol_of_notMem hz, Ghol_of_notMem hz', Gfun_neg]

/-- The odd Taylor coefficients of `G` vanish. -/
lemma tcoef_Ghol_odd (m : ℕ) : tcoef Ghol (2 * m + 1) = 0 := by
  have h := iteratedDeriv_comp_neg (2 * m + 1) Ghol 0
  have he : (fun x => Ghol (-x)) = Ghol := funext Ghol_neg
  rw [he, neg_zero, pow_succ, pow_mul] at h
  simp only [neg_one_sq, one_pow, one_mul, neg_smul, one_smul] at h
  have : iteratedDeriv (2 * m + 1) Ghol 0 = 0 := by
    have := h; linear_combination (1 / 2 : ℂ) * this
  simp [tcoef, this]

/-- The real Taylor coefficients `b_m = Re [ζ^{2m}] G`. -/
noncomputable def bG (m : ℕ) : ℝ := (tcoef Ghol (2 * m)).re

lemma bG_nonpos {m : ℕ} (hm : 2 ≤ m) : bG m ≤ 0 :=
  tcoef_Ghol_re_nonpos hm

/-- `G(r) = ∑ b_m r^{2m}` for real `|r| < κ₂`. -/
lemma hasSum_bG (hZ : ExtZeros) (hP : ExtProduct) {r : ℝ} (hr : |r| < besselZero 1 2) :
    HasSum (fun m => bG m * (r ^ 2) ^ m) (Ghol r).re := by
  have hκ := besselZero_pos hZ 1 2 (by norm_num)
  have hmem : (r : ℂ) ∈ ball (0 : ℂ) (⟨besselZero 1 2, hκ.le⟩ : NNReal) := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; exact hr
  have hs := hasSum_tcoef (differentiableOn_Ghol_ball hZ hP) hmem
  have hs' := Complex.reCLM.hasSum hs
  have hodd : ∀ j ∉ Set.range (fun m : ℕ => 2 * m),
      Complex.reCLM (tcoef Ghol j * (r : ℂ) ^ j) = 0 := by
    intro j hj
    obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := by
      rcases Nat.even_or_odd j with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact absurd ⟨m, show 2 * m = j by omega⟩ hj
      · exact ⟨m, hm⟩
    simp [tcoef_Ghol_odd]
  have := ((Function.Injective.hasSum_iff (fun a b h => by simpa using h) hodd).mpr hs')
  convert this using 1
  · funext m
    simp only [Function.comp, Complex.reCLM_apply, bG]
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal, pow_mul]
  · simp only [Complex.reCLM_apply]

/-- `H(y) = ∑ b_m y^m`. -/
noncomputable def HG (y : ℝ) : ℝ := ∑' m, bG m * y ^ m

lemma hasSum_HG (hZ : ExtZeros) (hP : ExtProduct) {y : ℝ} (hy0 : 0 ≤ y)
    (hy : y < besselZero 1 2 ^ 2) : HasSum (fun m => bG m * y ^ m) (HG y) := by
  have hκ := besselZero_pos hZ 1 2 (by norm_num)
  have hr : |Real.sqrt y| < besselZero 1 2 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg y), Real.sqrt_lt' hκ]; exact hy
  have := hasSum_bG hZ hP hr
  rw [Real.sq_sqrt hy0] at this
  exact this.summable.hasSum

lemma HG_sq (hZ : ExtZeros) (hP : ExtProduct) {r : ℝ} (hr : |r| < besselZero 1 2) :
    HG (r ^ 2) = (Ghol r).re :=
  ((hasSum_HG hZ hP (sq_nonneg r) (by
    rw [← sq_abs]; exact pow_lt_pow_left₀ hr (abs_nonneg r) (by norm_num))).unique
    (hasSum_bG hZ hP hr))

lemma jk_lt_besselZero_two (hZ : ExtZeros) : jk < besselZero 1 2 := (hZ 1 (by norm_num)).1 (by norm_num)

/-- On `(0, k)`, `G(r) = H(r²)`. -/
lemma rG_eq_HG (hZ : ExtZeros) (hP : ExtProduct) {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rG r = HG (r ^ 2) := by
  have hk2 := jk_lt_besselZero_two hZ
  rw [HG_sq hZ hP (by rw [abs_of_pos hr.1]; linarith [hr.2])]
  have hS : (r : ℂ) ∉ Gsing := by
    simp only [Gsing, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨by exact_mod_cast hr.1.ne', fun h => ?_, fun h => ?_⟩
    · have := congrArg Complex.re h; simp at this; linarith [hr.2]
    · have := congrArg Complex.re h; simp at this; linarith [hr.1, jk_pos hZ]
  rw [Ghol_of_notMem hS, Gfun_ofReal, Complex.ofReal_re]

/-- `H(k²) = G(k) = 0`. -/
lemma HG_jk (hZ : ExtZeros) (hP : ExtProduct) : HG (jk ^ 2) = 0 := by
  have hk := jk_pos hZ
  have hk2 := jk_lt_besselZero_two hZ
  rw [HG_sq hZ hP (by rw [abs_of_pos hk]; exact hk2)]
  -- continuity of `Ghol` at `k` along the reals
  have hcont : ContinuousAt (fun r : ℝ => (Ghol r).re) jk := by
    have hd := differentiableOn_Ghol_ball hZ hP
    have hmem : (jk : ℂ) ∈ ball (0 : ℂ) (besselZero 1 2) := by
      rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
      exact hk2
    have := (hd.differentiableAt (isOpen_ball.mem_nhds hmem)).continuousAt
    exact Complex.continuous_re.continuousAt.comp (this.comp Complex.continuous_ofReal.continuousAt)
  have hlim := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio jk))
  have hlim2 : Tendsto (fun r : ℝ => (Ghol r).re) (𝓝[<] jk) (𝓝 0) := by
    refine (tendsto_rG_jk hZ).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT hk] with r hr
    rw [rG_eq_HG hZ hP hr, HG_sq hZ hP (by rw [abs_of_pos hr.1]; linarith [hr.2])]
  exact tendsto_nhds_unique hlim hlim2

end Buckling
end
end ChunkedSource070
/- END SOURCE 070 -/

/- BEGIN SOURCE 071: RequestProject/Profiles/Regularity.lean -/
section ChunkedSource071

/-!
# Regularity of the parity extensions (Lemma 9.3)

Continuity of the radial quantities on `(0, k)`, the behaviour of `r(t)` as `t → 0⁺`, and
the `C¹` regularity of the even extension of `f` and the odd extension of `b`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-! ### A generic `C¹` criterion -/

/-- A function which is differentiable away from `0`, continuous at `0`, and whose
derivative is continuous away from `0` with a limit at `0`, is `C¹`. -/
theorem contDiff_one_of_parts {F g : ℝ → ℝ} {L : ℝ} (hd : ∀ s ≠ 0, HasDerivAt F (g s) s)
    (hc : ∀ s ≠ 0, ContinuousAt g s) (hlim : Tendsto g (𝓝[≠] 0) (𝓝 L))
    (hF : ContinuousAt F 0) : ContDiff ℝ 1 F := by
  classical
  set g' := Function.update g 0 L with hg'
  have hcg : Continuous g' := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs; exact continuousAt_update_same.mpr hlim
    · have heq : g =ᶠ[𝓝 s] g' := by
        filter_upwards [isOpen_ne.mem_nhds hs] with y hy
        rw [hg', Function.update_of_ne hy]
      exact (hc s hs).congr heq
  have hd' : ∀ s, HasDerivAt F (g' s) s := by
    intro s
    by_cases hs : s = 0
    · subst hs
      refine hasDerivAt_of_hasDerivAt_of_ne (fun y hy => ?_) hF hcg.continuousAt
      rw [hg', Function.update_of_ne hy]; exact hd y hy
    · rw [hg', Function.update_of_ne hs]; exact hd s hs
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (hd' s).differentiableAt, ?_⟩
  have : deriv F = g' := funext fun s => (hd' s).deriv
  rw [this]; exact hcg

lemma tendsto_neg_nhdsLT_zero : Tendsto (fun x : ℝ => -x) (𝓝[<] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · simpa using ((continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with x hx using neg_pos.mpr (mem_Iio.mp hx)

/-- Combine one-sided limits at `0` of `h(s)` (for `s > 0`) and `h'(-s)` (for `s < 0`). -/
lemma tendsto_punctured_of_sides {g h₁ h₂ : ℝ → ℝ} {L : ℝ}
    (hpos : ∀ s, 0 < s → g s = h₁ s) (hneg : ∀ s, s < 0 → g s = h₂ (-s))
    (h1 : Tendsto h₁ (𝓝[>] 0) (𝓝 L)) (h2 : Tendsto h₂ (𝓝[>] 0) (𝓝 L)) :
    Tendsto g (𝓝[≠] 0) (𝓝 L) := by
  rw [← nhdsLT_sup_nhdsGT]
  refine Tendsto.sup ?_ ?_
  · refine (h2.comp tendsto_neg_nhdsLT_zero).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using (hneg s hs).symm
  · refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using (hpos s hs).symm

/-! ### Continuity of the radial quantities -/

lemma continuousAt_deriv_rp {r : ℝ} (hr : r ≠ 0) : ContinuousAt (deriv rp) r := by
  have h : ContinuousAt (fun x => besselJ 0 x - besselJ 1 x / x) r :=
    ((continuous_besselJ 0).continuousAt).sub
      (((continuous_besselJ 1).continuousAt).div continuousAt_id hr)
  refine h.congr ?_
  filter_upwards [isOpen_ne.mem_nhds hr] with x hx using (deriv_rp_eq x hx).symm

lemma continuous_deriv_rPhi : Continuous (deriv rPhi) := by
  have : deriv rPhi = fun r => -pAlpha * besselJ 1 (pAlpha * r) := funext deriv_rPhi_eq
  rw [this]
  exact continuous_const.mul ((continuous_besselJ 1).comp (continuous_const.mul continuous_id))

lemma continuous_rp : Continuous rp := continuous_besselJ 1
lemma continuous_ru : Continuous ru := (continuous_besselJ 0).add continuous_const
lemma continuous_rPhi : Continuous rPhi :=
  (continuous_besselJ 0).comp (continuous_const.mul continuous_id)
lemma continuous_besselB : Continuous besselB := by
  have h0 := continuous_besselJ 0
  have h1 := continuous_besselJ 1
  unfold besselB
  fun_prop

section

variable (hZ : ExtZeros)
include hZ

/-- All radial quantities are continuous on `(0, k)`. -/
theorem continuousAt_radial {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    ContinuousAt rS r ∧ ContinuousAt rT r ∧ ContinuousAt rf r ∧ ContinuousAt rw r ∧
    ContinuousAt rz r ∧ ContinuousAt rA r ∧ ContinuousAt rC r ∧ ContinuousAt rG r ∧
    ContinuousAt rb r ∧ ContinuousAt rGt r ∧ ContinuousAt rbt r ∧ ContinuousAt rt r ∧
    ContinuousAt rg r := by
  have hr : r ≠ 0 := hr0.ne'
  have hp : rp r ≠ 0 := (radial_equations hZ r hr0 hrk).1.ne'
  have hS : rS r ≠ 0 := (rS_pos hZ hr0 hrk).ne'
  have hT : rT r ≠ 0 := (rT_neg hZ hr0 hrk).ne
  have cp := continuous_rp.continuousAt (x := r)
  have cu := continuous_ru.continuousAt (x := r)
  have cφ := continuous_rPhi.continuousAt (x := r)
  have cdp := continuousAt_deriv_rp hr
  have cdφ := continuous_deriv_rPhi.continuousAt (x := r)
  have cB := continuous_besselB.continuousAt (x := r)
  have cBα : ContinuousAt (fun x => besselB (pAlpha * x)) r :=
    (continuous_besselB.comp (continuous_const.mul continuous_id)).continuousAt
  have cS : ContinuousAt rS r := (cp.pow 2).add (cu.mul cdp)
  have cT : ContinuousAt rT r := cS.neg.div (cp.pow 2) (pow_ne_zero 2 hp)
  have cf : ContinuousAt rf r := cφ.div cp hp
  have cw : ContinuousAt rw r := cdφ.div cp hp
  have cz : ContinuousAt rz r := ((cφ.mul cdp).sub (cp.mul cdφ)).div cS hS
  have cA : ContinuousAt rA r := cdp.neg.div cp hp
  have cC : ContinuousAt rC r := continuousAt_const.div continuousAt_id hr
  have cG : ContinuousAt rG r :=
    continuousAt_const.add ((((continuousAt_const.mul continuousAt_id).mul cBα).sub
      ((continuousAt_const.mul continuousAt_id).mul cB)).div (cp.pow 2) (pow_ne_zero 2 hp))
  have cb : ContinuousAt rb r :=
    ((continuousAt_const.mul (cdp.div cp hp)).add (cG.div continuousAt_id hr)).sub
      ((cφ.mul cdφ).div (cp.pow 2) (pow_ne_zero 2 hp))
  have cGt : ContinuousAt rGt r :=
    ((cb.add ((continuousAt_const.mul cA).mul cG)).add (continuousAt_const.mul cC)).div cT hT
  have cbt : ContinuousAt rbt r :=
    (((continuousAt_const.mul (cw.add (cA.mul cf))).mul cw).sub
      (cC.mul ((cb.add ((continuousAt_const.mul cA).mul cG)).add
        (continuousAt_const.mul cC)))).div cT hT
  have ct : ContinuousAt rt r := cu.div cp hp
  have cg : ContinuousAt rg r := ((cp.mul cφ).add (cu.mul cdφ)).div cS hS
  exact ⟨cS, cT, cf, cw, cz, cA, cC, cG, cb, cGt, cbt, ct, cg⟩

/-- `r(t) → k⁻` as `t → 0⁺`. -/
theorem tendsto_rOf_zero : Tendsto rOf (𝓝[>] 0) (𝓝[<] jk) := by
  have hk0 := jk_pos hZ
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · rw [Metric.tendsto_nhds]
    intro ε hε
    set e := max (jk - ε) (jk / 2)
    have he0 : 0 < e := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hek : e < jk := max_lt (by linarith) (by linarith)
    have hpos := rt_pos hZ he0 hek
    have hmem : Ioo (0 : ℝ) (rt e) ∈ 𝓝[>] 0 := Ioo_mem_nhdsGT hpos
    filter_upwards [hmem] with s hs
    have h1 := (rOf_spec hZ hs.1).1
    have h2 : rOf (rt e) < rOf s := rOf_strictAntiOn hZ (mem_Ioi.mpr hs.1) (mem_Ioi.mpr hpos) hs.2
    rw [rOf_rt hZ ⟨he0, hek⟩] at h2
    rw [Real.dist_eq, abs_of_neg (by linarith [h1.2])]
    have : jk - ε ≤ e := le_max_left _ _
    linarith
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (rOf_spec hZ hs).1.2

lemma continuousAt_comp_rOf {F : ℝ → ℝ} (hF : ∀ r, 0 < r → r < jk → ContinuousAt F r)
    {t : ℝ} (ht : 0 < t) : ContinuousAt (fun s => F (rOf s)) t := by
  obtain ⟨⟨h0, h1⟩, -⟩ := rOf_spec hZ ht
  exact (hF _ h0 h1).comp (continuousAt_rOf hZ ht)

lemma continuousAt_comp_rOf_abs {F : ℝ → ℝ} (hF : ∀ r, 0 < r → r < jk → ContinuousAt F r)
    {s : ℝ} (hs : s ≠ 0) : ContinuousAt (fun s => F (rOf |s|)) s :=
  (continuousAt_comp_rOf hZ hF (abs_pos.mpr hs)).comp continuous_abs.continuousAt

lemma continuousAt_comp_rOf_neg {F : ℝ → ℝ} (hF : ∀ r, 0 < r → r < jk → ContinuousAt F r)
    {s : ℝ} (hs : s < 0) : ContinuousAt (fun s => F (rOf (-s))) s :=
  (continuousAt_comp_rOf hZ hF (neg_pos.mpr hs)).comp continuous_neg.continuousAt

/-! ### Lemma 9.3: `C¹` regularity of `f` and `b` -/

/-- The even extension of `f` is continuous at `0`. -/
lemma continuousAt_fExt_zero : ContinuousAt fExt 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have h : Tendsto pf (𝓝[>] 0) (𝓝 pBeta) := (tendsto_rf_jk hZ).comp (tendsto_rOf_zero hZ)
  have : fExt 0 = pBeta := by simp [fExt]
  rw [this]
  refine tendsto_punctured_of_sides (h₁ := pf) (h₂ := pf) (fun s hs => ?_) (fun s hs => ?_) h h
  · simp [fExt, hs.ne', abs_of_pos hs]
  · simp [fExt, hs.ne, abs_of_neg hs]

/-- **Lemma 9.3**: the even extension of `f` is `C¹`. -/
theorem fExt_contDiff' : ContDiff ℝ 1 fExt := by
  set g : ℝ → ℝ := fun s => if 0 < s then rz (rOf s) else -rz (rOf (-s)) with hg
  have hcz : ∀ r, 0 < r → r < jk → ContinuousAt rz r :=
    fun r h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.1
  refine contDiff_one_of_parts (g := g) (L := 0) (fun s hs => ?_) (fun s hs => ?_) ?_
    (continuousAt_fExt_zero hZ)
  · rcases lt_or_gt_of_ne hs with h | h
    · simp only [hg, if_neg (not_lt.mpr h.le)]; exact hasDerivAt_fExt_neg hZ h
    · simp only [hg, if_pos h]; exact hasDerivAt_fExt_pos hZ h
  · rcases lt_or_gt_of_ne hs with h | h
    · refine (continuousAt_comp_rOf_neg hZ hcz h).neg.congr ?_
      filter_upwards [Iio_mem_nhds h] with y hy
      simp [hg, not_lt.mpr (le_of_lt (mem_Iio.mp hy))]
    · refine (continuousAt_comp_rOf hZ hcz h).congr ?_
      filter_upwards [Ioi_mem_nhds h] with y hy
      simp [hg, mem_Ioi.mp hy]
  · have h : Tendsto (fun s => rz (rOf s)) (𝓝[>] 0) (𝓝 0) :=
      (tendsto_rz_jk hZ).comp (tendsto_rOf_zero hZ)
    have h' : Tendsto (fun s => -rz (rOf s)) (𝓝[>] 0) (𝓝 0) := by simpa using h.neg
    refine tendsto_punctured_of_sides (fun s hs => ?_) (fun s hs => ?_) h h'
    · simp [hg, hs]
    · simp [hg, not_lt.mpr hs.le]

/-- The odd extension of `b` is continuous at `0`. -/
lemma continuousAt_bExt_zero : ContinuousAt bExt 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have h : Tendsto pb (𝓝[>] 0) (𝓝 0) := (tendsto_rb_jk hZ).comp (tendsto_rOf_zero hZ)
  have h' : Tendsto (fun s => -pb s) (𝓝[>] 0) (𝓝 0) := by simpa using h.neg
  have : bExt 0 = 0 := by simp [bExt]
  rw [this]
  refine tendsto_punctured_of_sides (fun s hs => ?_) (fun s hs => ?_) h h'
  · simp [bExt, hs.ne', abs_of_pos hs, hs]
  · simp [bExt, hs.ne, abs_of_neg hs, hs]

/-- **Lemma 9.3**: the odd extension of `b` is `C¹`. -/
theorem bExt_contDiff' : ContDiff ℝ 1 bExt := by
  have hcb : ∀ r, 0 < r → r < jk → ContinuousAt rbt r :=
    fun r h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.2.2.1
  refine contDiff_one_of_parts (g := fun s => rbt (rOf |s|))
    (L := -2 * (zc * (-pAlpha * jJ / pc)) - (-1 / jk) * (grk / (-1 / 2))) (fun s hs => ?_)
    (fun s hs => continuousAt_comp_rOf_abs hZ hcb hs) ?_ (continuousAt_bExt_zero hZ)
  · rcases lt_or_gt_of_ne hs with h | h
    · simp only [abs_of_neg h]; exact hasDerivAt_bExt_neg hZ h
    · simp only [abs_of_pos h]; exact hasDerivAt_bExt_pos hZ h
  · have h := (tendsto_rbt_jk hZ).comp (tendsto_rOf_zero hZ)
    refine tendsto_punctured_of_sides (h₁ := fun s => rbt (rOf s)) (h₂ := fun s => rbt (rOf s))
      (fun s hs => ?_) (fun s hs => ?_) h h
    · simp [abs_of_pos hs]
    · simp [abs_of_neg hs]

end

end Buckling
end
end ChunkedSource071
/- END SOURCE 071 -/

/- BEGIN SOURCE 072: RequestProject/Profiles/Origin.lean -/
section ChunkedSource072

/-!
# The profiles near the radial centre `r = 0` (Lemma 9.1 at `t = ∞`)

Writing `J_n(r) = (r/2)^n G_n(r²)` with `G_n` smooth, all radial quantities become smooth
functions of `y = r²` (up to explicit powers of `r`).  This yields the limits as `r → 0⁺` of
`z, g, b_t, b - t b_t, G_t, t G_t`.
-/

@[expose] public section

open Real Set Filter Topology
open scoped Nat

namespace Buckling

/-! ### Values at `0` and the representation in `y = r²` -/

lemma besselG_zero_arg (n : ℕ) : besselG n 0 = 1 / (n ! : ℝ) := by
  unfold besselG
  rw [tsum_eq_single 0]
  · simp [gterm]
  · intro m hm
    simp [gterm, zero_pow hm]

lemma besselG0_zero : besselG 0 0 = 1 := by simp [besselG_zero_arg]
lemma besselG1_zero : besselG 1 0 = 1 := by simp [besselG_zero_arg]

lemma continuous_besselG (n : ℕ) : Continuous (besselG n) :=
  (differentiable_besselG n).continuous

/-- `B(x) = x B̃(x²)`. -/
noncomputable def Bt (y : ℝ) : ℝ :=
  besselG 0 y ^ 2 + y / 4 * besselG 1 y ^ 2 - besselG 0 y * besselG 1 y / 2

/-- `G(r) = G̃(r²)`. -/
noncomputable def Gy (y : ℝ) : ℝ :=
  pK + 4 * (pLam * Bt (pLam * y) - pK * Bt y) / besselG 1 y ^ 2

/-- `b(r) = B̃_b(r²)/r`. -/
noncomputable def By (y : ℝ) : ℝ :=
  2 * pK * (besselG 0 y - besselG 1 y / 2) / besselG 1 y + Gy y +
    2 * pLam * besselG 0 (pLam * y) * besselG 1 (pLam * y) / besselG 1 y ^ 2

/-- `S(r) = S̃(r²)`. -/
noncomputable def Sy (y : ℝ) : ℝ :=
  y / 4 * besselG 1 y ^ 2 + (besselG 0 y + pc) * (besselG 0 y - besselG 1 y / 2)

/-- `b - t b_t = H(r²)/r`. -/
noncomputable def Hy (y : ℝ) : ℝ :=
  By y - (besselG 0 y + pc) * (By y - 2 * y * deriv By y) * besselG 1 y / (2 * Sy y)

lemma rp_eq_G (r : ℝ) : rp r = r / 2 * besselG 1 (r ^ 2) := by
  simp [rp, besselJ_eq_besselG]

lemma ru_eq_G (r : ℝ) : ru r = besselG 0 (r ^ 2) + pc := by
  simp [ru, besselJ_zero_eq_besselG]

lemma rPhi_eq_G (r : ℝ) : rPhi r = besselG 0 (pLam * r ^ 2) := by
  simp [rPhi, besselJ_zero_eq_besselG, pLam_eq, mul_pow]

lemma deriv_rp_eq_G {r : ℝ} (hr : r ≠ 0) :
    deriv rp r = besselG 0 (r ^ 2) - besselG 1 (r ^ 2) / 2 := by
  rw [deriv_rp_eq r hr, besselJ_zero_eq_besselG, besselJ_eq_besselG]
  field_simp

lemma deriv_rPhi_eq_G (r : ℝ) :
    deriv rPhi r = -(pLam * r / 2) * besselG 1 (pLam * r ^ 2) := by
  rw [deriv_rPhi_eq, besselJ_eq_besselG, pLam_eq, mul_pow]
  ring

lemma besselB_eq_G (x : ℝ) : besselB x = x * Bt (x ^ 2) := by
  simp only [besselB, Bt, besselJ_eq_besselG]
  ring_nf

lemma rS_eq_G {r : ℝ} (hr : r ≠ 0) : rS r = Sy (r ^ 2) := by
  rw [rS, deriv_rp_eq_G hr, rp_eq_G, ru_eq_G, Sy]
  ring

lemma rG_eq_G {r : ℝ} (hr : r ≠ 0) (hp : rp r ≠ 0) : rG r = Gy (r ^ 2) := by
  have hG : besselG 1 (r ^ 2) ≠ 0 := by
    intro h; apply hp; rw [rp_eq_G, h, mul_zero]
  rw [rG, Gy, rp_eq_G, besselB_eq_G, besselB_eq_G, mul_pow]
  simp only [pLam_eq]
  field_simp
  ring

lemma rb_eq_G {r : ℝ} (hr : r ≠ 0) (hp : rp r ≠ 0) : rb r = By (r ^ 2) / r := by
  have hG : besselG 1 (r ^ 2) ≠ 0 := by
    intro h; apply hp; rw [rp_eq_G, h, mul_zero]
  rw [rb, rG_eq_G hr hp, deriv_rp_eq_G hr, deriv_rPhi_eq_G, rPhi_eq_G, rp_eq_G, By]
  field_simp
  ring

/-! ### Smoothness near `y = 0` -/

/-- The open set where the denominators of `G̃, B̃_b, H` do not vanish. -/
def Uy : Set ℝ := {y | besselG 1 y ≠ 0 ∧ Sy y ≠ 0}

lemma contDiff_Bt : ContDiff ℝ (⊤ : ℕ∞) Bt := by
  have h0 := contDiff_besselG 0
  have h1 := contDiff_besselG 1
  unfold Bt
  exact ((h0.pow 2).add ((contDiff_id.div_const 4).mul (h1.pow 2))).sub
    ((h0.mul h1).div_const 2)

lemma contDiff_Sy : ContDiff ℝ (⊤ : ℕ∞) Sy := by
  have h0 := contDiff_besselG 0
  have h1 := contDiff_besselG 1
  unfold Sy
  exact ((contDiff_id.div_const 4).mul (h1.pow 2)).add
    ((h0.add contDiff_const).mul (h0.sub (h1.div_const 2)))

lemma isOpen_Uy : IsOpen Uy :=
  ((continuous_besselG 1).isOpen_preimage _ isOpen_ne).inter
    (contDiff_Sy.continuous.isOpen_preimage _ isOpen_ne)

lemma contDiffOn_Gy : ContDiffOn ℝ (⊤ : ℕ∞) Gy Uy := by
  have h1 := contDiff_besselG 1
  have hB := contDiff_Bt
  unfold Gy
  refine contDiffOn_const.add (ContDiffOn.div ?_ (h1.pow 2).contDiffOn fun y hy => pow_ne_zero 2 hy.1)
  exact (contDiff_const.mul ((contDiff_const.mul (hB.comp (contDiff_const.mul contDiff_id))).sub
    (contDiff_const.mul hB))).contDiffOn

lemma contDiffOn_By : ContDiffOn ℝ (⊤ : ℕ∞) By Uy := by
  have h0 := contDiff_besselG 0
  have h1 := contDiff_besselG 1
  have hl : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => pLam * y) := contDiff_const.mul contDiff_id
  unfold By
  refine ((ContDiffOn.div ?_ h1.contDiffOn fun y hy => hy.1).add contDiffOn_Gy).add
    (ContDiffOn.div ?_ (h1.pow 2).contDiffOn fun y hy => pow_ne_zero 2 hy.1)
  · exact (contDiff_const.mul (h0.sub (h1.div_const 2))).contDiffOn
  · exact ((contDiff_const.mul (h0.comp hl)).mul (h1.comp hl)).contDiffOn

lemma contDiffOn_Hy : ContDiffOn ℝ (⊤ : ℕ∞) Hy Uy := by
  have h0 := contDiff_besselG 0
  have h1 := contDiff_besselG 1
  have hdB : ContDiffOn ℝ (⊤ : ℕ∞) (deriv By) Uy :=
    contDiffOn_By.deriv_of_isOpen isOpen_Uy (by simp)
  unfold Hy
  refine contDiffOn_By.sub (ContDiffOn.div ?_ (contDiff_const.mul contDiff_Sy).contDiffOn
    fun y hy => mul_ne_zero two_ne_zero hy.2)
  exact (((h0.add contDiff_const).contDiffOn.mul (contDiffOn_By.sub
    ((contDiff_const.mul contDiff_id).contDiffOn.mul hdB))).mul h1.contDiffOn)

lemma Bt_zero : Bt 0 = 1 / 2 := by simp [Bt, besselG0_zero, besselG1_zero]; norm_num

lemma Sy_zero : Sy 0 = pSigma / 2 := by
  simp [Sy, besselG0_zero, besselG1_zero, pSigma]; ring

lemma Gy_zero : Gy 0 = 2 * pLam - pK := by
  simp [Gy, besselG1_zero, Bt_zero]; ring

lemma By_zero : By 0 = 4 * pLam := by
  simp [By, besselG0_zero, besselG1_zero, Gy_zero]; ring

lemma zero_mem_Uy (hZ : ExtZeros) : (0 : ℝ) ∈ Uy :=
  ⟨by rw [besselG1_zero]; norm_num, by rw [Sy_zero]; linarith [pSigma_pos hZ]⟩

lemma Hy_zero (hZ : ExtZeros) : Hy 0 = 0 := by
  have hσ := pSigma_pos hZ
  simp only [Hy, besselG0_zero, besselG1_zero, Sy_zero, mul_zero, zero_mul, sub_zero]
  rw [show (1 : ℝ) + pc = pSigma by rw [pSigma]]
  field_simp
  ring

/-! ### Explicit formulas on `(0, k)` -/

section

variable (hZ : ExtZeros)
include hZ

lemma sq_mem_Uy {r : ℝ} (hr : r ∈ Ioo 0 jk) : r ^ 2 ∈ Uy := by
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hS := rS_pos hZ hr.1 hr.2
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [rp_eq_G, h, mul_zero] at hp; exact lt_irrefl _ hp
  · rw [← rS_eq_G hr.1.ne', rS] at h; linarith

lemma G1_sq_ne {r : ℝ} (hr : r ∈ Ioo 0 jk) : besselG 1 (r ^ 2) ≠ 0 := (sq_mem_Uy hZ hr).1
lemma Sy_sq_ne {r : ℝ} (hr : r ∈ Ioo 0 jk) : Sy (r ^ 2) ≠ 0 := (sq_mem_Uy hZ hr).2

lemma hasDerivAt_sq_comp {F : ℝ → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Uy) {r : ℝ}
    (hr : r ∈ Ioo 0 jk) : HasDerivAt (fun x => F (x ^ 2)) (deriv F (r ^ 2) * (2 * r)) r := by
  have hd : DifferentiableAt ℝ F (r ^ 2) :=
    (hF.differentiableOn (by simp)).differentiableAt (isOpen_Uy.mem_nhds (sq_mem_Uy hZ hr))
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by simpa using hasDerivAt_pow 2 r
  exact hd.hasDerivAt.comp (h := fun x : ℝ => x ^ 2) r h2

omit hZ in
lemma rT_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rT r = -Sy (r ^ 2) / (r ^ 2 / 4 * besselG 1 (r ^ 2) ^ 2) := by
  rw [rT, rS_eq_G hr.1.ne', rp_eq_G]; ring

lemma rGt_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rGt r = -(deriv Gy (r ^ 2)) * r ^ 3 * besselG 1 (r ^ 2) ^ 2 / (2 * Sy (r ^ 2)) := by
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hev : rG =ᶠ[𝓝 r] fun x => Gy (x ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
    exact rG_eq_G hx.1.ne' (radial_equations hZ x hx.1 hx.2).1.ne'
  have h1 := (hasDerivAt_rG hZ hr.1 hr.2).deriv
  have h2 := ((hasDerivAt_sq_comp hZ contDiffOn_Gy hr).congr_of_eventuallyEq hev).deriv
  have hG := G1_sq_ne hZ hr
  have hS := Sy_sq_ne hZ hr
  have hr0 := hr.1.ne'
  rw [rGt, ← h1, h2, rT_eq_G hr]
  field_simp
  ring

omit hZ in
lemma rt_eq_G {r : ℝ} : rt r = (besselG 0 (r ^ 2) + pc) / (r / 2 * besselG 1 (r ^ 2)) := by
  rw [rt, ru_eq_G, rp_eq_G]

lemma rt_rGt_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rt r * rGt r = -(besselG 0 (r ^ 2) + pc) * deriv Gy (r ^ 2) * r ^ 2 * besselG 1 (r ^ 2) /
      Sy (r ^ 2) := by
  have hG := G1_sq_ne hZ hr
  have hS := Sy_sq_ne hZ hr
  have hr0 := hr.1.ne'
  rw [rt_eq_G, rGt_eq_G hZ hr]
  field_simp

lemma deriv_rb_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    deriv rb r = 2 * deriv By (r ^ 2) - By (r ^ 2) / r ^ 2 := by
  have hev : rb =ᶠ[𝓝 r] fun x => By (x ^ 2) / x := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
    exact rb_eq_G hx.1.ne' (radial_equations hZ x hx.1 hx.2).1.ne'
  have h := ((hasDerivAt_sq_comp hZ contDiffOn_By hr).div (hasDerivAt_id r) hr.1.ne')
  rw [(h.congr_of_eventuallyEq hev).deriv]
  have hr0 := hr.1.ne'
  simp only [id]
  field_simp

lemma rbt_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rbt r = (By (r ^ 2) - 2 * r ^ 2 * deriv By (r ^ 2)) * besselG 1 (r ^ 2) ^ 2 /
      (4 * Sy (r ^ 2)) := by
  have h1 := (hasDerivAt_rb hZ hr.1 hr.2).deriv
  have hG := G1_sq_ne hZ hr
  have hS := Sy_sq_ne hZ hr
  have hr0 := hr.1.ne'
  rw [rbt, ← h1, deriv_rb_eq_G hZ hr, rT_eq_G hr]
  field_simp
  ring

lemma rb_sub_rt_rbt_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rb r - rt r * rbt r = Hy (r ^ 2) / r := by
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hG := G1_sq_ne hZ hr
  have hS := Sy_sq_ne hZ hr
  have hr0 := hr.1.ne'
  rw [rb_eq_G hr0 hp.ne', rt_eq_G, rbt_eq_G hZ hr, Hy]
  field_simp
  ring

omit hZ in
lemma rz_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rz r = (besselG 0 (pLam * r ^ 2) * (besselG 0 (r ^ 2) - besselG 1 (r ^ 2) / 2) +
      pLam * r ^ 2 / 4 * besselG 1 (r ^ 2) * besselG 1 (pLam * r ^ 2)) / Sy (r ^ 2) := by
  have hr0 := hr.1.ne'
  rw [rz, ← rS_eq_G hr0, rPhi_eq_G, deriv_rp_eq_G hr0, rp_eq_G, deriv_rPhi_eq_G]
  ring

omit hZ in
lemma rg_eq_G {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rg r = r / 2 * (besselG 1 (r ^ 2) * besselG 0 (pLam * r ^ 2) -
      pLam * (besselG 0 (r ^ 2) + pc) * besselG 1 (pLam * r ^ 2)) / Sy (r ^ 2) := by
  have hr0 := hr.1.ne'
  rw [rg, ← rS_eq_G hr0, rPhi_eq_G, ru_eq_G, rp_eq_G, deriv_rPhi_eq_G]
  ring

end

/-! ### Limits as `r → 0⁺` -/

attribute [local fun_prop] continuous_besselG

lemma continuous_Sy : Continuous Sy := contDiff_Sy.continuous

attribute [local fun_prop] continuous_Sy

section

variable (hZ : ExtZeros)
include hZ

lemma tendsto_zero_of_eqOn {F E : ℝ → ℝ} (heq : ∀ r ∈ Ioo 0 jk, F r = E r)
    (hE : ContinuousAt E 0) : Tendsto F (𝓝[>] 0) (𝓝 (E 0)) := by
  refine (hE.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (jk_pos hZ)] with r hr using (heq r hr).symm

lemma continuousAt_deriv_sq {F : ℝ → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Uy) :
    ContinuousAt (fun r : ℝ => deriv F (r ^ 2)) 0 := by
  have h : ContinuousAt (deriv F) 0 :=
    (hF.continuousOn_deriv_of_isOpen isOpen_Uy (by simp)).continuousAt
      (isOpen_Uy.mem_nhds (zero_mem_Uy hZ))
  exact ContinuousAt.comp_of_eq h (continuous_pow 2).continuousAt (by simp)

lemma Sy_zero_ne : Sy 0 ≠ 0 := (zero_mem_Uy hZ).2

lemma Sy_sq_ne_zero : Sy ((0 : ℝ) ^ 2) ≠ 0 := by simpa using Sy_zero_ne hZ

theorem tendsto_rz_origin : Tendsto rz (𝓝[>] 0) (𝓝 pEll) := by
  have hS := Sy_sq_ne_zero hZ
  have h := tendsto_zero_of_eqOn hZ (fun r hr => rz_eq_G hr) (ContinuousAt.div (by fun_prop)
    (by fun_prop) hS)
  convert h using 2
  simp [besselG0_zero, besselG1_zero, Sy_zero, pEll]
  ring

theorem tendsto_rg_origin : Tendsto rg (𝓝[>] 0) (𝓝 0) := by
  have hS := Sy_sq_ne_zero hZ
  have h := tendsto_zero_of_eqOn hZ (fun r hr => rg_eq_G hr) (ContinuousAt.div (by fun_prop)
    (by fun_prop) hS)
  convert h using 2
  simp

theorem tendsto_rGt_origin : Tendsto rGt (𝓝[>] 0) (𝓝 0) := by
  have hS := Sy_sq_ne_zero hZ
  have hd := continuousAt_deriv_sq hZ contDiffOn_Gy
  have h := tendsto_zero_of_eqOn hZ (fun r hr => rGt_eq_G hZ hr) (ContinuousAt.div (by fun_prop)
    (by fun_prop) (mul_ne_zero two_ne_zero hS))
  convert h using 2
  simp

theorem tendsto_rt_rGt_origin : Tendsto (fun r => rt r * rGt r) (𝓝[>] 0) (𝓝 0) := by
  have hS := Sy_sq_ne_zero hZ
  have hd := continuousAt_deriv_sq hZ contDiffOn_Gy
  have h := tendsto_zero_of_eqOn hZ (fun r hr => rt_rGt_eq_G hZ hr) (ContinuousAt.div
    (by fun_prop) (by fun_prop) hS)
  convert h using 2
  simp

theorem tendsto_rbt_origin : Tendsto rbt (𝓝[>] 0) (𝓝 (2 * pLam * pEll)) := by
  have hS := Sy_sq_ne_zero hZ
  have hσ := pSigma_pos hZ
  have hd := continuousAt_deriv_sq hZ contDiffOn_By
  have hB : ContinuousAt (fun r : ℝ => By (r ^ 2)) 0 :=
    ContinuousAt.comp_of_eq ((contDiffOn_By.continuousOn).continuousAt
      (isOpen_Uy.mem_nhds (zero_mem_Uy hZ))) (continuous_pow 2).continuousAt (by simp)
  have h := tendsto_zero_of_eqOn hZ (fun r hr => rbt_eq_G hZ hr) (ContinuousAt.div
    (by fun_prop) (by fun_prop) (mul_ne_zero four_ne_zero hS))
  convert h using 2
  simp [besselG1_zero, Sy_zero, By_zero, pEll]
  field_simp

theorem tendsto_rb_sub_origin : Tendsto (fun r => rb r - rt r * rbt r) (𝓝[>] 0) (𝓝 0) := by
  have hH : HasDerivAt Hy (deriv Hy 0) 0 :=
    ((contDiffOn_Hy.differentiableOn (by simp)).differentiableAt
      (isOpen_Uy.mem_nhds (zero_mem_Uy hZ))).hasDerivAt
  have hsl := hasDerivAt_iff_tendsto_slope.mp hH
  have hsq : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have := ((continuous_pow 2).tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact pow_ne_zero 2 (ne_of_gt hr)
  have hid : Tendsto (fun r : ℝ => r) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have h := hid.mul (hsl.comp hsq)
  rw [zero_mul] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (jk_pos hZ)] with r hr
  rw [rb_sub_rt_rbt_eq_G hZ hr, Function.comp, slope_def_field, Hy_zero hZ]
  have hr0 := hr.1.ne'
  field_simp
  ring

end

end Buckling
end
end ChunkedSource072
/- END SOURCE 072 -/

/- BEGIN SOURCE 073: RequestProject/Concavity/SecondCoeff.lean -/
section ChunkedSource073

/-!
# The coefficient of `r²` in `G` (Proposition 8.9 of the paper, case `m = 1`)

`[r²] G = (2λ - λ² - K)/4 < 0`.  We compute it as the derivative at `0` of
`G̃(y) = G(√y)` (`Gy` from the analysis near the origin).
-/

@[expose] public section

open Filter Topology Metric Set Real
open scoped Nat

namespace Buckling

/-- The derivative of `B̃`. -/
noncomputable def dBt (y : ℝ) : ℝ :=
  2 * besselG 0 y * (-(1 / 4) * besselG 1 y) + (1 / 4 * besselG 1 y ^ 2 +
    y / 4 * (2 * besselG 1 y * (-(1 / 4) * besselG 2 y))) -
    ((-(1 / 4) * besselG 1 y) * besselG 1 y + besselG 0 y * (-(1 / 4) * besselG 2 y)) / 2

lemma hasDerivAt_Bt (y : ℝ) : HasDerivAt Bt (dBt y) y := by
  have h0 := hasDerivAt_besselG 0 y
  have h1 := hasDerivAt_besselG 1 y
  have := ((h0.fun_pow 2).fun_add (((hasDerivAt_id y).div_const 4).fun_mul (h1.fun_pow 2))).fun_sub
    ((h0.fun_mul h1).div_const 2)
  unfold Bt
  convert! this using 1 <;>
    simp only [dBt, id, Nat.cast_ofNat, Pi.pow_apply, Pi.mul_apply, zero_add, Nat.reduceAdd] <;>
    ring

lemma besselG2_zero : besselG 2 0 = 1 / 2 := by
  rw [besselG_zero_arg]; norm_num [Nat.factorial]

lemma dBt_zero : dBt 0 = -1 / 16 := by
  simp only [dBt, besselG0_zero, besselG1_zero, besselG2_zero]; norm_num

/-- `G̃'(0) = (2λ - λ² - K)/4`. -/
lemma hasDerivAt_Gy_zero : HasDerivAt Gy ((2 * pLam - pLam ^ 2 - pK) / 4) 0 := by
  have hB1 := (hasDerivAt_Bt (pLam * 0)).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul pLam)
  have hN : HasDerivAt (fun y => 4 * (pLam * Bt (pLam * y) - pK * Bt y))
      (4 * (pLam * (dBt (pLam * 0) * (pLam * 1)) - pK * dBt 0)) 0 :=
    ((hB1.const_mul pLam).sub ((hasDerivAt_Bt 0).const_mul pK)).const_mul 4
  have hD := (hasDerivAt_besselG 1 0).pow 2
  have hD0 : besselG 1 0 ^ 2 ≠ 0 := by rw [besselG1_zero]; norm_num
  have := (hN.div hD hD0).const_add pK
  unfold Gy
  convert this using 1
  simp only [mul_zero, dBt_zero, besselG1_zero, Bt_zero, Nat.cast_ofNat, Pi.pow_apply,
    Nat.reduceAdd, besselG2_zero]
  ring

/-- `[r²] G = (2λ - λ² - K)/4`. -/
theorem bG_one_eq (hZ : ExtZeros) (hP : ExtProduct) : bG 1 = (2 * pLam - pLam ^ 2 - pK) / 4 := by
  have hκ := besselZero_pos hZ 1 2 (by norm_num)
  have hk := jk_pos hZ
  have hk2 := jk_lt_besselZero_two hZ
  obtain ⟨C, hC⟩ := taylor_remainder (r := ⟨besselZero 1 2, hκ.le⟩) hκ
    (differentiableOn_Ghol_ball hZ hP) 2
  -- the Taylor expansion along the reals
  have hT : ∀ᶠ r in 𝓝[>] (0 : ℝ), |Gy (r ^ 2) - (bG 0 + bG 1 * r ^ 2)| ≤ C * r ^ 3 := by
    have hC' := (Complex.continuous_ofReal.continuousAt (x := 0)).tendsto.eventually
      (by simpa using hC)
    filter_upwards [nhdsWithin_le_nhds hC', Ioo_mem_nhdsGT hk] with r hr hr'
    have hrr : rG r = Gy (r ^ 2) := rG_eq_G hr'.1.ne' (radial_equations hZ r hr'.1 hr'.2).1.ne'
    rw [← hrr, rG_eq_HG hZ hP hr', HG_sq hZ hP (by rw [abs_of_pos hr'.1]; linarith [hr'.2])]
    have hsum : ∑ j ∈ Finset.range (2 + 1), tcoef Ghol j * (r : ℂ) ^ j =
        tcoef Ghol 0 + tcoef Ghol 1 * r + tcoef Ghol 2 * r ^ 2 := by
      simp [Finset.sum_range_succ]
    rw [hsum, show tcoef Ghol 1 = 0 from tcoef_Ghol_odd 0] at hr
    have hre : (Ghol r).re - (bG 0 + bG 1 * r ^ 2) =
        (Ghol r - (tcoef Ghol 0 + 0 * r + tcoef Ghol 2 * r ^ 2)).re := by
      simp only [bG, Complex.sub_re, Complex.add_re, zero_mul, add_zero]
      rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
    rw [hre]
    refine (Complex.abs_re_le_norm _).trans (hr.trans (le_of_eq ?_))
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr'.1]
  -- `G̃(0) = b₀`
  have hcont : ContinuousAt (fun r : ℝ => Gy (r ^ 2)) 0 := by
    exact hasDerivAt_Gy_zero.continuousAt.comp_of_eq ((continuous_pow 2).continuousAt)
      (by simp)
  have h0 : Gy 0 = bG 0 := by
    have hlim1 : Tendsto (fun r : ℝ => Gy (r ^ 2) - (bG 0 + bG 1 * r ^ 2)) (𝓝[>] 0)
        (𝓝 (Gy 0 - bG 0)) := by
      have hc2 : Continuous (fun r : ℝ => bG 0 + bG 1 * r ^ 2) := by fun_prop
      have := ((hcont.sub hc2.continuousAt).tendsto).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      simpa using! this
    have hlim2 : Tendsto (fun r : ℝ => Gy (r ^ 2) - (bG 0 + bG 1 * r ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hT ?_
      have : Tendsto (fun r : ℝ => C * r ^ 3) (𝓝 0) (𝓝 (C * 0 ^ 3)) :=
        (continuous_const.mul (continuous_pow 3)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    have := tendsto_nhds_unique hlim1 hlim2
    linarith
  -- the slope
  have hslope1 : Tendsto (fun r : ℝ => (Gy (r ^ 2) - Gy 0) / r ^ 2) (𝓝[>] 0)
      (𝓝 ((2 * pLam - pLam ^ 2 - pK) / 4)) := by
    have hs := hasDerivAt_Gy_zero.tendsto_slope_zero
    have hsq : Tendsto (fun r : ℝ => r ^ 2) (𝓝[>] 0) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Tendsto (fun r : ℝ => r ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) := (continuous_pow 2).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact pow_ne_zero 2 (ne_of_gt hr)
    refine (hs.comp hsq).congr' ?_
    filter_upwards with r
    simp only [Function.comp, zero_add, smul_eq_mul]
    field_simp
  have hslope2 : Tendsto (fun r : ℝ => (Gy (r ^ 2) - Gy 0) / r ^ 2) (𝓝[>] 0) (𝓝 (bG 1)) := by
    have hdiff : Tendsto (fun r : ℝ => (Gy (r ^ 2) - Gy 0) / r ^ 2 - bG 1) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_abs_tendsto_zero]
      have hb : ∀ᶠ r in 𝓝[>] (0 : ℝ), |(Gy (r ^ 2) - Gy 0) / r ^ 2 - bG 1| ≤ C * r := by
        filter_upwards [hT, self_mem_nhdsWithin] with r hr hr0
        have hr0' : (0 : ℝ) < r := hr0
        rw [h0]
        have : (Gy (r ^ 2) - bG 0) / r ^ 2 - bG 1 = (Gy (r ^ 2) - (bG 0 + bG 1 * r ^ 2)) / r ^ 2 := by
          field_simp; ring
        rw [this, abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2), div_le_iff₀ (by positivity)]
        calc _ ≤ C * r ^ 3 := hr
          _ = C * r * r ^ 2 := by ring
      refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) hb ?_
      have : Tendsto (fun r : ℝ => C * r) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using hdiff.add_const (bG 1)
  exact tendsto_nhds_unique hslope2 hslope1

/-- `[r²] G < 0`. -/
theorem bG_one_neg (hZ : ExtZeros) (hP : ExtProduct) (hI : ExtIntegral) : bG 1 < 0 := by
  rw [bG_one_eq hZ hP]
  obtain ⟨-, -, hl1, hl2, -, -, -, -, hK, -⟩ := coarse_bounds hZ hI
  nlinarith

end Buckling
end
end ChunkedSource073
/- END SOURCE 073 -/

/- BEGIN SOURCE 074: RequestProject/Concavity/DBounds.lean -/
section ChunkedSource074

/-!
# Bounds for `d = 2G - tG_t` (Corollaries 8.9 and 8.11 of the paper)

The series `H(y) = ∑ b_m y^m` has `b_m ≤ 0` for `m ≥ 1`, so it is concave and strictly
decreasing on `[0, κ₂²)`.  Since `G(r) = H(r²)` and `H(k²) = 0`, this gives the positivity
of `G`, the tangent bound `G ≤ (2K/3k)(k - r)`, and, together with the tail ratio bound
`up/S < (k² - r²)/r`, the bounds `0 < d ≤ (4K/3k)(k - r)`.
-/

@[expose] public section

open Filter Topology Set Real

namespace Buckling

/-- Convexity of `t ↦ t^m` on `[0, ∞)` in three-point form. -/
lemma pow_three_point {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) (m : ℕ) :
    (z - x) * y ^ m ≤ (z - y) * x ^ m + (y - x) * z ^ m := by
  rcases eq_or_lt_of_le (hxy.trans hyz) with h | h
  · have h1 : x = y := le_antisymm hxy (h ▸ hyz)
    subst h1; subst h; simp
  have hzx : 0 < z - x := sub_pos.mpr h
  have hc := (convexOn_pow m).2 (Set.mem_Ici.mpr hx) (Set.mem_Ici.mpr (hx.trans (hxy.trans hyz)))
    (div_nonneg (by linarith : (0:ℝ) ≤ z - y) hzx.le)
    (div_nonneg (by linarith : (0:ℝ) ≤ y - x) hzx.le) (by rw [← add_div, div_eq_one_iff_eq hzx.ne']; ring)
  have he : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp; ring
  simp only [smul_eq_mul] at hc
  rw [he] at hc
  have := mul_le_mul_of_nonneg_left hc hzx.le
  calc (z - x) * y ^ m ≤ (z - x) * ((z - y) / (z - x) * x ^ m + (y - x) / (z - x) * z ^ m) :=
        this
    _ = _ := by field_simp

section


/-- `b_m ≤ 0` for all `m ≥ 1`. -/
lemma bG_nonpos' {m : ℕ} (hm : 1 ≤ m) : bG m ≤ 0 := by
  rcases eq_or_lt_of_le hm with h | h
  · subst h; exact (bG_one_neg extZeros_holds extProduct_holds extIntegral_holds).le
  · exact bG_nonpos h

/-- Concavity of `H` on `[0, κ₂²)`, in three-point form. -/
lemma HG_three_point {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : z < besselZero 1 2 ^ 2) :
    (z - y) * HG x + (y - x) * HG z ≤ (z - x) * HG y := by
  have hy0 : 0 ≤ y := hx.trans hxy
  have hz0 : 0 ≤ z := hy0.trans hyz
  have hX := hasSum_HG extZeros_holds extProduct_holds hx (by linarith)
  have hY := hasSum_HG extZeros_holds extProduct_holds hy0 (by linarith)
  have hZ := hasSum_HG extZeros_holds extProduct_holds hz0 hz
  have hS := (hY.mul_left (z - x)).sub ((hX.mul_left (z - y)).add (hZ.mul_left (y - x)))
  have hnn : 0 ≤ (z - x) * HG y - ((z - y) * HG x + (y - x) * HG z) := by
    refine hS.nonneg fun m => ?_
    have heq : (z - x) * (bG m * y ^ m) - ((z - y) * (bG m * x ^ m) + (y - x) * (bG m * z ^ m))
        = bG m * ((z - x) * y ^ m - ((z - y) * x ^ m + (y - x) * z ^ m)) := by ring
    rw [heq]
    rcases Nat.lt_or_ge m 1 with hm | hm
    · interval_cases m; simp
    · exact mul_nonneg_of_nonpos_of_nonpos (bG_nonpos' hm)
        (by linarith [pow_three_point hx hxy hyz m])
  linarith

/-- `H` is strictly decreasing: `H(y) - H(z) ≥ -b₁ (z - y)`. -/
lemma HG_sub_ge {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (hz : z < besselZero 1 2 ^ 2) :
    bG 1 * (y - z) ≤ HG y - HG z := by
  have hY := hasSum_HG extZeros_holds extProduct_holds hy (by linarith)
  have hZ := hasSum_HG extZeros_holds extProduct_holds (hy.trans hyz) hz
  have hS := hY.sub hZ
  have := le_hasSum hS 1 (fun m hm => by
    rw [← mul_sub]
    rcases Nat.lt_or_ge m 1 with h | h
    · interval_cases m; simp
    · exact mul_nonneg_of_nonpos_of_nonpos (bG_nonpos' h)
        (sub_nonpos.mpr (pow_le_pow_left₀ hy hyz m)))
  simpa [mul_sub] using this

/-- `G > 0` on `(0, k)`. -/
lemma rG_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < rG r := by
  have hZ := extZeros_holds
  have hk2 := jk_lt_besselZero_two hZ
  have hk := jk_pos hZ
  have h := HG_sub_ge (sq_nonneg r) (pow_le_pow_left₀ hr.1.le hr.2.le 2)
    (pow_lt_pow_left₀ hk2 hk.le (by norm_num))
  rw [HG_jk hZ extProduct_holds, ← rG_eq_HG hZ extProduct_holds hr] at h
  have hb := bG_one_neg hZ extProduct_holds extIntegral_holds
  have : r ^ 2 - jk ^ 2 < 0 := by nlinarith [hr.1, hr.2]
  nlinarith

/-- For `0 < r < s < k`: `G(s)(k² - r²) ≥ G(r)(k² - s²)`. -/
lemma rG_chord {r s : ℝ} (hr : r ∈ Ioo 0 jk) (hs : s ∈ Ioo 0 jk) (hrs : r ≤ s) :
    rG r * (jk ^ 2 - s ^ 2) ≤ rG s * (jk ^ 2 - r ^ 2) := by
  have hZ := extZeros_holds
  have hk2 := jk_lt_besselZero_two hZ
  have hk := jk_pos hZ
  have h := HG_three_point (sq_nonneg r) (pow_le_pow_left₀ hr.1.le hrs 2)
    (pow_le_pow_left₀ hs.1.le hs.2.le 2) (pow_lt_pow_left₀ hk2 hk.le (by norm_num))
  rw [HG_jk hZ extProduct_holds, ← rG_eq_HG hZ extProduct_holds hr, ← rG_eq_HG hZ extProduct_holds hs] at h
  linarith

/-- `G` is decreasing on `(0, k)`. -/
lemma rG_anti {r s : ℝ} (hr : r ∈ Ioo 0 jk) (hs : s ∈ Ioo 0 jk) (hrs : r ≤ s) :
    rG s ≤ rG r := by
  have hZ := extZeros_holds
  have hk2 := jk_lt_besselZero_two hZ
  have hk := jk_pos hZ
  have h := HG_sub_ge (sq_nonneg r) (pow_le_pow_left₀ hr.1.le hrs 2)
    (by nlinarith [hs.1, hs.2] : s ^ 2 < besselZero 1 2 ^ 2)
  rw [← rG_eq_HG hZ extProduct_holds hr, ← rG_eq_HG hZ extProduct_holds hs] at h
  have hb := bG_one_neg hZ extProduct_holds extIntegral_holds
  have : r ^ 2 - s ^ 2 ≤ 0 := by nlinarith [hr.1]
  nlinarith

/-- **Corollary 8.9 (endpoint tangent bound)**: `G(r) ≤ (2K/3k)(k - r)` on `(0, k)`. -/
theorem rG_le_tangent {r : ℝ} (hr : r ∈ Ioo 0 jk) : rG r ≤ 2 * pK / (3 * jk) * (jk - r) := by
  have hZ := extZeros_holds
  have hk := jk_pos hZ
  have hc := pc_pos hZ
  have hK := (parameter_signs hZ).2.2.2.2.2.2.2.2
  set L := 2 * pK / (3 * jk)
  have hL : 2 * pK * pc ^ 2 / (3 * jk) / pc ^ 2 = L := by
    simp only [L]; field_simp
  have hlim := tendsto_rG_div hZ
  rw [hL] at hlim
  -- `G(r) ≤ (G(s)/(k - s)) (k² - r²)/(k + s)` for `s ∈ (r, k)`
  have hev : ∀ᶠ s in 𝓝[<] jk, rG r ≤ rG s / (jk - s) ^ 1 * ((jk ^ 2 - r ^ 2) / (jk + s)) := by
    filter_upwards [Ioo_mem_nhdsLT hr.2] with s hs
    have hs' : s ∈ Ioo 0 jk := ⟨hr.1.trans hs.1, hs.2⟩
    have h := rG_chord hr hs' hs.1.le
    have h1 : 0 < jk - s := sub_pos.mpr hs.2
    have h2 : 0 < jk + s := by linarith [hs'.1]
    have h3 : 0 < jk ^ 2 - s ^ 2 := by nlinarith
    rw [pow_one, div_mul_div_comm, le_div_iff₀ (by positivity)]
    have : (jk - s) * (jk + s) = jk ^ 2 - s ^ 2 := by ring
    rw [this]; linarith
  have hlim2 : Tendsto (fun s => rG s / (jk - s) ^ 1 * ((jk ^ 2 - r ^ 2) / (jk + s))) (𝓝[<] jk)
      (𝓝 (L * ((jk ^ 2 - r ^ 2) / (jk + jk)))) := by
    refine hlim.mul (Tendsto.div tendsto_const_nhds ?_ (by linarith))
    exact (tendsto_const_nhds.add tendsto_id).mono_left nhdsWithin_le_nhds
  have hle := ge_of_tendsto hlim2 hev
  have hL0 : 0 ≤ L := by positivity
  calc rG r ≤ L * ((jk ^ 2 - r ^ 2) / (jk + jk)) := hle
    _ = L * (jk - r) * ((jk + r) / (2 * jk)) := by field_simp; ring
    _ ≤ L * (jk - r) * 1 := by
        gcongr
        · exact mul_nonneg hL0 (by linarith [hr.2])
        · rw [div_le_one (by positivity)]; linarith [hr.2]
    _ = _ := by ring

/-- The radial derivative `D = G_r` satisfies `-2rG/(k² - r²) ≤ D ≤ 0`. -/
lemma rG_deriv_bounds {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    -(2 * r * rG r / (jk ^ 2 - r ^ 2)) ≤ rb r + 2 * rA r * rG r + 2 * pK * rC r ∧
      rb r + 2 * rA r * rG r + 2 * pK * rC r ≤ 0 := by
  have hZ := extZeros_holds
  have hD := hasDerivAt_rG hZ hr.1 hr.2
  set D := rb r + 2 * rA r * rG r + 2 * pK * rC r
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hD).mono_left
    (nhdsWithin_mono r (s := Ioi r) (fun x hx => (ne_of_gt (Set.mem_Ioi.mp hx) : x ≠ r)))
  have hk2 : 0 < jk ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
  constructor
  · have hev : ∀ᶠ s in 𝓝[>] r, -(rG r * (s + r) / (jk ^ 2 - r ^ 2)) ≤ slope rG r s := by
      filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
      have hs' : s ∈ Ioo 0 jk := ⟨hr.1.trans hs.1, hs.2⟩
      have h := rG_chord hr hs' hs.1.le
      have h1 : 0 < s - r := sub_pos.mpr hs.1
      rw [slope_def_field, le_div_iff₀ h1, neg_mul, div_mul_eq_mul_div, neg_le,
        le_div_iff₀ hk2]
      nlinarith
    have hlim : Tendsto (fun s => -(rG r * (s + r) / (jk ^ 2 - r ^ 2))) (𝓝[>] r)
        (𝓝 (-(rG r * (r + r) / (jk ^ 2 - r ^ 2)))) := by
      refine (Tendsto.neg (Tendsto.div_const (tendsto_const_nhds.mul
        (tendsto_id.add tendsto_const_nhds)) _)).mono_left nhdsWithin_le_nhds
    have := le_of_tendsto_of_tendsto hlim hsl hev
    convert this using 2; ring
  · have hev : ∀ᶠ s in 𝓝[>] r, slope rG r s ≤ 0 := by
      filter_upwards [Ioo_mem_nhdsGT hr.2] with s hs
      have hs' : s ∈ Ioo 0 jk := ⟨hr.1.trans hs.1, hs.2⟩
      have h := rG_anti hr hs' hs.1.le
      rw [slope_def_field]
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith [hs.1])
    exact le_of_tendsto hsl hev

/-- **Corollaries 8.9 and 8.11**, assuming the tail ratio bound (Lemma 8.10). -/
theorem d_bounds_of_tail
    (htail : ∀ r ∈ Ioo 0 jk, ru r * rp r / rS r < (jk ^ 2 - r ^ 2) / r) :
    ∀ r ∈ Ioo 0 jk, 0 < 2 * rG r - rt r * rGt r ∧
      2 * rG r - rt r * rGt r ≤ 4 * pK / (3 * jk) * (jk - r) := by
  intro r hr
  have hZ := extZeros_holds
  obtain ⟨hp, hu, -⟩ := radial_equations hZ r hr.1 hr.2
  have hS : 0 < rS r := rS_pos hZ hr.1 hr.2
  have hG := rG_pos hr
  have hGt := rG_le_tangent hr
  obtain ⟨hD1, hD2⟩ := rG_deriv_bounds hr
  have ht := htail r hr
  set D := rb r + 2 * rA r * rG r + 2 * pK * rC r
  set C := ru r * rp r / rS r with hC
  have hC0 : 0 < C := by positivity
  have hd : 2 * rG r - rt r * rGt r = 2 * rG r + C * D := by
    simp only [rGt, rT, rt, C, D]
    field_simp
    ring
  rw [hd]
  have hk2 : 0 < jk ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
  refine ⟨?_, ?_⟩
  · rcases le_or_gt 0 D with h | h
    · nlinarith
    · have h1 : (jk ^ 2 - r ^ 2) / r * D < C * D := mul_lt_mul_of_neg_right ht h
      have h2 : -(2 * rG r) ≤ (jk ^ 2 - r ^ 2) / r * D := by
        have : (jk ^ 2 - r ^ 2) / r * (-(2 * r * rG r / (jk ^ 2 - r ^ 2))) = -(2 * rG r) := by
          have hr0 := hr.1.ne'
          field_simp
        rw [← this]
        exact mul_le_mul_of_nonneg_left hD1 (div_nonneg hk2.le hr.1.le)
      linarith
  · have : C * D ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hC0.le hD2
    have h4 : 2 * rG r ≤ 4 * pK / (3 * jk) * (jk - r) := by
      have : 4 * pK / (3 * jk) * (jk - r) = 2 * (2 * pK / (3 * jk) * (jk - r)) := by ring
      rw [this]; linarith
    linarith

end

end Buckling
end
end ChunkedSource074
/- END SOURCE 074 -/

/- BEGIN SOURCE 075: RequestProject/Concavity/TailRatio.lean -/
section ChunkedSource075

/-!
# A bound for the radial tail ratio (Lemma 8.10 of the paper)

For `0 < r < k`: `up/S < (k² - r²)/r`.

Write `Q(r) = p(r)/(r(k² - r²))`.  By the canonical product (External theorem E2),
`2k² Q(r) = ∏_{n ≥ 2} (1 - r²/κ_n²)`, so `Q` is decreasing and `log Q` is concave in `r²`.
The concavity, together with the endpoint expansion at `r = k`, gives
`p'/p - 1/r + 2r/(k² - r²) ≥ -2r/k²`, while monotonicity gives `u ≤ p(k² - r²)/(4r)`.
-/

@[expose] public section

open Filter Topology Set Real

namespace Buckling

/-- Concave functions in three-point form. -/
lemma ConcaveOn.three_point' {s : Set ℝ} {f : ℝ → ℝ} (hf : ConcaveOn ℝ s f) {x y z : ℝ}
    (hx : x ∈ s) (hz : z ∈ s) (hxy : x ≤ y) (hyz : y ≤ z) :
    (z - y) * f x + (y - x) * f z ≤ (z - x) * f y := by
  rcases eq_or_lt_of_le (hxy.trans hyz) with h | h
  · have h1 : x = y := le_antisymm hxy (h ▸ hyz)
    subst h1; subst h; simp
  have hzx : 0 < z - x := sub_pos.mpr h
  have hc := hf.2 hx hz (div_nonneg (by linarith : (0:ℝ) ≤ z - y) hzx.le)
    (div_nonneg (by linarith : (0:ℝ) ≤ y - x) hzx.le)
    (by rw [← add_div, div_eq_one_iff_eq hzx.ne']; ring)
  have he : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by
    field_simp; ring
  simp only [smul_eq_mul] at hc
  rw [he] at hc
  have := mul_le_mul_of_nonneg_left hc hzx.le
  calc (z - y) * f x + (y - x) * f z
      = (z - x) * ((z - y) / (z - x) * f x + (y - x) / (z - x) * f z) := by field_simp
    _ ≤ (z - x) * f y := this

/-- Three-point concavity of `x ↦ log (1 - a x)`. -/
lemma log_one_sub_three_point {a x y z : ℝ} (ha : 0 < a) (hxy : x ≤ y) (hyz : y ≤ z)
    (hz : a * z < 1) :
    (z - y) * Real.log (1 - a * x) + (y - x) * Real.log (1 - a * z) ≤
      (z - x) * Real.log (1 - a * y) := by
  have hZ : (1 - a * z) ∈ Ioi (0 : ℝ) := by simp; linarith
  have hX : (1 - a * x) ∈ Ioi (0 : ℝ) := by simp; nlinarith
  have h := ConcaveOn.three_point' strictConcaveOn_log_Ioi.concaveOn hZ hX
    (by nlinarith : 1 - a * z ≤ 1 - a * y) (by nlinarith : 1 - a * y ≤ 1 - a * x)
  have e1 : (1 - a * x) - (1 - a * y) = a * (y - x) := by ring
  have e2 : (1 - a * y) - (1 - a * z) = a * (z - y) := by ring
  have e3 : (1 - a * x) - (1 - a * z) = a * (z - x) := by ring
  rw [e1, e2, e3] at h
  have : a * ((z - y) * Real.log (1 - a * x) + (y - x) * Real.log (1 - a * z)) ≤
      a * ((z - x) * Real.log (1 - a * y)) := by linarith
  exact le_of_mul_le_mul_left this ha

/-- Derivative bounds from three-point concavity in the variable `r²`. -/
lemma deriv_ge_of_sq_three_point {F : ℝ → ℝ} {a b r s d : ℝ} (ha : 0 ≤ a)
    (h3 : ∀ x y z, a < x → x ≤ y → y ≤ z → z < b →
      (z ^ 2 - y ^ 2) * F x + (y ^ 2 - x ^ 2) * F z ≤ (z ^ 2 - x ^ 2) * F y)
    (hr : a < r) (hrs : r < s) (hs : s < b) (hd : HasDerivAt F d r) :
    (F s - F r) / (s ^ 2 - r ^ 2) ≤ d / (2 * r) := by
  have hr0 : 0 < r := ha.trans_lt hr
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono r (s := Ioi r) (fun x hx => (ne_of_gt (Set.mem_Ioi.mp hx) : x ≠ r)))
  set m := (F s - F r) / (s ^ 2 - r ^ 2)
  have hsr : 0 < s ^ 2 - r ^ 2 := by nlinarith
  have hm : m * (s ^ 2 - r ^ 2) = F s - F r := div_mul_cancel₀ _ hsr.ne'
  have hev : ∀ᶠ t in 𝓝[>] r, (t + r) * m ≤ slope F r t := by
    filter_upwards [Ioo_mem_nhdsGT hrs] with t ht
    have h := h3 r t s hr ht.1.le ht.2.le hs
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr ht.1)]
    have key : (s ^ 2 - r ^ 2) * ((t + r) * m * (t - r)) ≤ (s ^ 2 - r ^ 2) * (F t - F r) := by
      have : (s ^ 2 - r ^ 2) * ((t + r) * m * (t - r)) = (t ^ 2 - r ^ 2) * (m * (s ^ 2 - r ^ 2)) := by
        ring
      rw [this, hm]; linarith
    exact le_of_mul_le_mul_left key hsr
  have hlim : Tendsto (fun t => (t + r) * m) (𝓝[>] r) (𝓝 ((r + r) * m)) :=
    ((tendsto_id.add tendsto_const_nhds).mul tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto hlim hsl hev
  rw [le_div_iff₀ (by positivity)]
  linarith

lemma deriv_le_of_sq_three_point {F : ℝ → ℝ} {a b r s d : ℝ} (ha : 0 ≤ a)
    (h3 : ∀ x y z, a < x → x ≤ y → y ≤ z → z < b →
      (z ^ 2 - y ^ 2) * F x + (y ^ 2 - x ^ 2) * F z ≤ (z ^ 2 - x ^ 2) * F y)
    (hr : a < r) (hrs : r < s) (hs : s < b) (hd : HasDerivAt F d s) :
    d / (2 * s) ≤ (F s - F r) / (s ^ 2 - r ^ 2) := by
  have hr0 : 0 < r := ha.trans_lt hr
  have hs0 : 0 < s := hr0.trans hrs
  have hsl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono s (s := Iio s) (fun x hx => (ne_of_lt (Set.mem_Iio.mp hx) : x ≠ s)))
  set m := (F s - F r) / (s ^ 2 - r ^ 2)
  have hsr : 0 < s ^ 2 - r ^ 2 := by nlinarith
  have hm : m * (s ^ 2 - r ^ 2) = F s - F r := div_mul_cancel₀ _ hsr.ne'
  have hev : ∀ᶠ t in 𝓝[<] s, slope F s t ≤ (s + t) * m := by
    filter_upwards [Ioo_mem_nhdsLT hrs] with t ht
    have h := h3 r t s hr ht.1.le ht.2.le hs
    rw [slope_def_field, div_le_iff_of_neg (sub_neg.mpr ht.2)]
    have key : (s ^ 2 - r ^ 2) * (F s - F t) ≤ (s ^ 2 - r ^ 2) * ((s ^ 2 - t ^ 2) * m) := by
      have : (s ^ 2 - r ^ 2) * ((s ^ 2 - t ^ 2) * m) = (s ^ 2 - t ^ 2) * (m * (s ^ 2 - r ^ 2)) := by
        ring
      rw [this, hm]; linarith
    have := le_of_mul_le_mul_left key hsr
    nlinarith
  have hlim : Tendsto (fun t => (s + t) * m) (𝓝[<] s) (𝓝 ((s + s) * m)) :=
    ((tendsto_const_nhds.add tendsto_id).mul tendsto_const_nhds).mono_left nhdsWithin_le_nhds
  have := le_of_tendsto_of_tendsto hsl hlim hev
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- `Q(r) = p(r)/(r(k² - r²))`. -/
noncomputable def rQ (r : ℝ) : ℝ := rp r / (r * (jk ^ 2 - r ^ 2))

/-- The partial products `∏_{n < N} (1 - x/κ_{n+2}²)`. -/
noncomputable def tailProd (N : ℕ) (x : ℝ) : ℝ :=
  ∏ n ∈ Finset.range N, (1 - x / besselZero 1 (n + 2) ^ 2)

/-- `log Q` (up to the constant `log 2k²`). -/
noncomputable def rLQ (r : ℝ) : ℝ := Real.log (2 * jk ^ 2 * rQ r)

/-- Its derivative `p'/p - 1/r + 2r/(k² - r²)`. -/
noncomputable def rLQd (r : ℝ) : ℝ := deriv rp r / rp r - 1 / r + 2 * r / (jk ^ 2 - r ^ 2)

section

variable (hZ : ExtZeros)
include hZ

lemma rQ_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < rQ r := by
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have : 0 < jk ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
  exact div_pos hp (mul_pos hr.1 this)

lemma hasDerivAt_rLQ {r : ℝ} (hr : r ∈ Ioo 0 jk) : HasDerivAt rLQ (rLQd r) r := by
  have hr0 : r ≠ 0 := hr.1.ne'
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hk2 : 0 < jk ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hk := jk_pos hZ
  have hden : HasDerivAt (fun x => x * (jk ^ 2 - x ^ 2)) (1 * (jk ^ 2 - r ^ 2) + r * (-(2 * r)))
      r := by
    simpa only [id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat] using!
      (hasDerivAt_id r).fun_mul ((hasDerivAt_pow 2 r).const_sub (jk ^ 2))
  have hQ := ((hasDerivAt_rp r hr0).fun_div hden (mul_pos hr.1 hk2).ne').const_mul (2 * jk ^ 2)
  have hpos : 2 * jk ^ 2 * rQ r ≠ 0 := by have := rQ_pos hZ hr; positivity
  have h := hQ.log hpos
  unfold rLQ
  convert! h using 1
  simp only [rLQd, rQ, (hasDerivAt_rp r hr0).deriv, Pi.div_apply]
  field_simp
  ring

/-- The endpoint limit `(p'/p - 1/r + 2r/(k² - r²))/(2r) → -1/k²` as `r → k⁻`. -/
lemma tendsto_rLQd : Tendsto (fun r => rLQd r / (2 * r)) (𝓝[<] jk) (𝓝 (-1 / jk ^ 2)) := by
  have hk := jk_pos hZ
  have hc := pc_pos hZ
  have hid : Tendsto (fun r : ℝ => r) (𝓝[<] jk) (𝓝 jk) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hkr : Tendsto (fun r : ℝ => jk + r) (𝓝[<] jk) (𝓝 (jk + jk)) := tendsto_const_nhds.add hid
  -- numerator `Num = p'(k - r)(k + r) + 2rp`
  have hE1 : (fun r => rpd r + pc + pc / jk * (jk - r)) =O[𝓝[<] jk] dk 2 := deriv_rp_O2 hZ
  have hδ1 : (fun r => (jk + r) * (jk - r) ^ 1) =O[𝓝[<] jk] dk 1 :=
    isBigO_bdd_mul hkr (Asymptotics.isBigO_refl _ _)
  have hN : (fun r => (rpd r * ((jk - r) * (jk + r)) + 2 * r * rp r) - (-2 * pc) * (jk - r) ^ 2)
      =O[𝓝[<] jk] fun r => (jk - r) ^ (2 + 1) := by
    have t1 := isBigO_dk_mul hE1 hδ1
    have t2 := isBigO_bdd_mul (hid.const_mul 2) (rp_O3 hZ)
    refine isBigO_of_eventuallyEq (t1.add t2) (Eventually.of_forall fun r => ?_)
    field_simp
    ring
  have hD : (fun r => rp r * ((jk - r) * (jk + r)) - (2 * jk * pc) * (jk - r) ^ 2)
      =O[𝓝[<] jk] fun r => (jk - r) ^ (2 + 1) := by
    have t1 := isBigO_dk_mul (rp_O2 hZ) hδ1
    have t2 := isBigO_const_dk (-pc) (le_refl 3)
    refine isBigO_of_eventuallyEq (t1.add t2) (Eventually.of_forall fun r => ?_)
    ring
  have hlim := ((tendsto_div_of_expansion hN).div (tendsto_div_of_expansion hD)
    (by positivity)).sub (hid.inv₀ hk.ne')
  have hlim2 := hlim.div (hid.const_mul 2) (by positivity)
  have hval : (-2 * pc / (2 * jk * pc) - jk⁻¹) / (2 * jk) = -1 / jk ^ 2 := by
    field_simp; ring
  rw [hval] at hlim2
  refine hlim2.congr' ?_
  filter_upwards [eventually_Ioo_jk hZ] with r hr
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hδ : 0 < jk - r := sub_pos.mpr hr.2
  have hr0 := hr.1.ne'
  have hd : deriv rp r = rpd r := (hasDerivAt_rp r hr0).deriv
  simp only [Pi.div_apply, rLQd, hd]
  have hkr' : 0 < jk + r := by linarith [hr.1]
  have : jk ^ 2 - r ^ 2 = (jk - r) * (jk + r) := by ring
  rw [this]
  field_simp
  ring

variable (hP : ExtProduct)
include hP

/-- `∏_{n<N} (1 - r²/κ_{n+2}²) → 2k² Q(r)` on `(0, k)`. -/
lemma tendsto_tailProd {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    Tendsto (fun N => tailProd N (r ^ 2)) atTop (𝓝 (2 * jk ^ 2 * rQ r)) := by
  have hk := jk_pos hZ
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hc := (TendstoLocallyUniformly.tendstoLocallyUniformlyOn (s := Set.univ) hP).tendsto_at
    (Set.mem_univ (r : ℂ))
  rw [besselJC_ofReal] at hc
  have h_eq : ∀ N : ℕ, (((r / 2 * ∏ n ∈ Finset.range N, (1 - r ^ 2 / besselZero 1 (n + 1) ^ 2) : ℝ))
      : ℂ) = (r : ℂ) / 2 * ∏ n ∈ Finset.range N,
        (1 - (r : ℂ) ^ 2 / ((besselZero 1 (n + 1) : ℝ) : ℂ) ^ 2) := by
    intro N; push_cast; rfl
  have hc' := hc.congr (fun N => (h_eq N).symm)
  have hre : Tendsto (fun N => r / 2 * ∏ n ∈ Finset.range N, (1 - r ^ 2 / besselZero 1 (n + 1) ^ 2))
      atTop (𝓝 (rp r)) := by
    have := (Complex.continuous_re.tendsto _).comp hc'
    simpa only [Function.comp_def, Complex.ofReal_re] using! this
  have hshift := (tendsto_add_atTop_iff_nat 1).mpr hre
  have hform : ∀ N, r / 2 * ∏ n ∈ Finset.range (N + 1), (1 - r ^ 2 / besselZero 1 (n + 1) ^ 2) =
      (r / 2 * (1 - r ^ 2 / jk ^ 2)) * tailProd N (r ^ 2) := by
    intro N
    rw [Finset.prod_range_succ']
    have : tailProd N (r ^ 2) =
        ∏ n ∈ Finset.range N, (1 - r ^ 2 / besselZero 1 (n + 1 + 1) ^ 2) := rfl
    rw [this, jk, zero_add]
    ring
  have hne : r / 2 * (1 - r ^ 2 / jk ^ 2) ≠ 0 := by
    have : 0 < 1 - r ^ 2 / jk ^ 2 := by
      rw [sub_pos, div_lt_one (by positivity)]; nlinarith [hr.1, hr.2]
    have := hr.1
    positivity
  have hlim2 : Tendsto (fun N => tailProd N (r ^ 2)) atTop
      (𝓝 (rp r / (r / 2 * (1 - r ^ 2 / jk ^ 2)))) := by
    refine (hshift.div_const (r / 2 * (1 - r ^ 2 / jk ^ 2))).congr fun N => ?_
    rw [hform, mul_div_cancel_left₀ _ hne]
  convert hlim2 using 2
  have hk2 : jk ^ 2 - r ^ 2 ≠ 0 := by nlinarith [hr.1, hr.2]
  have hr0 := hr.1.ne'
  simp only [rQ]
  field_simp

/-- `Q` is decreasing on `(0, k)`. -/
lemma rQ_anti {r s : ℝ} (hr : r ∈ Ioo 0 jk) (hs : s ∈ Ioo 0 jk) (hrs : r ≤ s) : rQ s ≤ rQ r := by
  have hk := jk_pos hZ
  have hmono := (hZ 1 (by norm_num)).1.monotone
  have h2 : ∀ N, tailProd N (s ^ 2) ≤ tailProd N (r ^ 2) := by
    intro N
    apply Finset.prod_le_prod₀
    · intro n _
      have hκ : jk < besselZero 1 (n + 2) :=
        lt_of_lt_of_le (jk_lt_besselZero_two hZ) (hmono (by omega))
      have : s ^ 2 < besselZero 1 (n + 2) ^ 2 := by nlinarith [hs.1, hs.2]
      rw [sub_nonneg, div_le_one (by nlinarith)]; linarith
    · intro n _
      have : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.1.le hrs 2
      gcongr
  have := le_of_tendsto_of_tendsto' (tendsto_tailProd hZ hP hs) (tendsto_tailProd hZ hP hr) h2
  exact le_of_mul_le_mul_left this (by positivity)

/-- `log Q` is concave in `r²` on `(0, k)`. -/
lemma rLQ_three_point : ∀ x y z, 0 < x → x ≤ y → y ≤ z → z < jk →
    (z ^ 2 - y ^ 2) * rLQ x + (y ^ 2 - x ^ 2) * rLQ z ≤ (z ^ 2 - x ^ 2) * rLQ y := by
  intro x y z hx hxy hyz hz
  have hk := jk_pos hZ
  have hmono := (hZ 1 (by norm_num)).1.monotone
  have hκ : ∀ n : ℕ, jk < besselZero 1 (n + 2) := fun n =>
    lt_of_lt_of_le (jk_lt_besselZero_two hZ) (hmono (by omega))
  have hfac : ∀ (n : ℕ) (w : ℝ), w < jk ^ 2 → 0 < 1 - w / besselZero 1 (n + 2) ^ 2 := by
    intro n w hw
    have := hκ n
    rw [sub_pos, div_lt_one (by nlinarith)]; nlinarith
  have hlog : ∀ N w, w < jk ^ 2 → Real.log (tailProd N w) =
      ∑ n ∈ Finset.range N, Real.log (1 - w / besselZero 1 (n + 2) ^ 2) :=
    fun N w hw => Real.log_prod (fun n _ => (hfac n w hw).ne')
  have hx2 : x ^ 2 < jk ^ 2 := by nlinarith
  have hy2 : y ^ 2 < jk ^ 2 := by nlinarith
  have hz2 : z ^ 2 < jk ^ 2 := by nlinarith
  have hN : ∀ N, (z ^ 2 - y ^ 2) * Real.log (tailProd N (x ^ 2)) +
      (y ^ 2 - x ^ 2) * Real.log (tailProd N (z ^ 2)) ≤
      (z ^ 2 - x ^ 2) * Real.log (tailProd N (y ^ 2)) := by
    intro N
    rw [hlog N _ hx2, hlog N _ hy2, hlog N _ hz2, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro n _
    have h0 : 0 < besselZero 1 (n + 2) := hk.trans (hκ n)
    simp only [div_eq_inv_mul]
    refine log_one_sub_three_point (inv_pos.mpr (by positivity))
      (pow_le_pow_left₀ (by linarith) hxy 2) (pow_le_pow_left₀ (by linarith) hyz 2) ?_
    have := hfac n (z ^ 2) hz2
    rw [div_eq_inv_mul] at this
    linarith
  have hT : ∀ w, w ∈ Ioo 0 jk → Tendsto (fun N => Real.log (tailProd N (w ^ 2))) atTop
      (𝓝 (rLQ w)) := fun w hw =>
    (tendsto_tailProd hZ hP hw).log (by have := rQ_pos hZ hw; positivity)
  have hxm : x ∈ Ioo 0 jk := ⟨hx, by linarith⟩
  have hym : y ∈ Ioo 0 jk := ⟨by linarith, by linarith⟩
  have hzm : z ∈ Ioo 0 jk := ⟨by linarith, hz⟩
  exact le_of_tendsto_of_tendsto' (((hT x hxm).const_mul _).add ((hT z hzm).const_mul _))
    ((hT y hym).const_mul _) hN

/-- `p'/p - 1/r + 2r/(k² - r²) ≥ -2r/k²` on `(0, k)`. -/
lemma rLQd_ge {r : ℝ} (hr : r ∈ Ioo 0 jk) : -1 / jk ^ 2 ≤ rLQd r / (2 * r) := by
  have h3 := rLQ_three_point hZ hP
  have hev : ∀ᶠ s in 𝓝[<] jk, rLQd s / (2 * s) ≤ rLQd r / (2 * r) := by
    filter_upwards [Ioo_mem_nhdsLT hr.2] with s hs
    have hs' : s ∈ Ioo 0 jk := ⟨hr.1.trans hs.1, hs.2⟩
    exact (deriv_le_of_sq_three_point le_rfl h3 hr.1 hs.1 hs.2 (hasDerivAt_rLQ hZ hs')).trans
      (deriv_ge_of_sq_three_point le_rfl h3 hr.1 hs.1 hs.2 (hasDerivAt_rLQ hZ hr))
  exact le_of_tendsto (tendsto_rLQd hZ) hev

/-- `u ≤ p(k² - r²)/(4r)` on `(0, k)`. -/
lemma ru_le {r : ℝ} (hr : r ∈ Ioo 0 jk) : ru r ≤ rp r * (jk ^ 2 - r ^ 2) / (4 * r) := by
  have hk := jk_pos hZ
  obtain ⟨hp, hu, -, -, -, -, -, hint⟩ := radial_equations hZ r hr.1 hr.2
  have hk2 : 0 < jk ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hcont : Continuous rp := continuous_besselJ 1
  have hpoly : Continuous (fun s : ℝ => rQ r * (s * (jk ^ 2 - s ^ 2))) := by fun_prop
  have hle : ∫ s in r..jk, rp s ≤ ∫ s in r..jk, rQ r * (s * (jk ^ 2 - s ^ 2)) := by
    apply intervalIntegral.integral_mono_on hr.2.le (hcont.intervalIntegrable _ _)
      (hpoly.intervalIntegrable _ _)
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h, rp_jk hZ]; simp
    · have hs' : s ∈ Ioo 0 jk := ⟨hr.1.trans_le hs.1, h⟩
      have hks : 0 < jk ^ 2 - s ^ 2 := by nlinarith [hs'.1]
      have hQ := rQ_anti hZ hP hr hs' hs.1
      have hs0 := hs'.1
      have : rp s = rQ s * (s * (jk ^ 2 - s ^ 2)) := by unfold rQ; field_simp
      rw [this]; exact mul_le_mul_of_nonneg_right hQ (by positivity)
  have hcalc : ∫ s in r..jk, rQ r * (s * (jk ^ 2 - s ^ 2)) = rQ r * ((jk ^ 2 - r ^ 2) ^ 2 / 4) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := r) (b := jk)
      (f := fun s => -(jk ^ 2 - s ^ 2) ^ 2 / 4) (f' := fun s => s * (jk ^ 2 - s ^ 2))
      (fun s _ => by
        have := (((hasDerivAt_pow 2 s).const_sub (jk ^ 2)).pow 2).neg.div_const 4
        convert this using 1
        simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
        ring)
      ((by fun_prop : Continuous fun s : ℝ => s * (jk ^ 2 - s ^ 2)).intervalIntegrable _ _)
    rw [this]; ring
  rw [hint]
  calc _ ≤ _ := hle
    _ = _ := by
      rw [hcalc]
      have hr0 := hr.1.ne'
      have hk2' := hk2.ne'
      unfold rQ; field_simp

/-- **Lemma 8.10 (the radial tail ratio).** -/
theorem tail_ratio {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    ru r * rp r / rS r < (jk ^ 2 - r ^ 2) / r := by
  have hk := jk_pos hZ
  obtain ⟨hp, hu, -⟩ := radial_equations hZ r hr.1 hr.2
  have hS : 0 < rS r := rS_pos hZ hr.1 hr.2
  have hk2 : 0 < jk ^ 2 - r ^ 2 := by nlinarith [hr.1, hr.2]
  have hr0 := hr.1
  have hU := ru_le hZ hP hr
  have hF := rLQd_ge hZ hP hr
  rw [le_div_iff₀ (by positivity)] at hF
  have hX : rLQd r = deriv rp r / rp r - 1 / r + 2 * r / (jk ^ 2 - r ^ 2) := rfl
  have hSdef : rS r = rp r ^ 2 + ru r * deriv rp r := rfl
  generalize rLQd r = X at hF hX
  generalize rp r = P at *
  generalize ru r = U at *
  generalize deriv rp r = D at *
  have hDform : D = P * (X + 1 / r - 2 * r / (jk ^ 2 - r ^ 2)) := by
    rw [hX]; field_simp; ring
  have hW : 0 < (jk ^ 2 - r ^ 2) * X + (jk ^ 2 - r ^ 2) / r + r := by
    have h1 : (jk ^ 2 - r ^ 2) * (-1 / jk ^ 2 * (2 * r)) ≤ (jk ^ 2 - r ^ 2) * X :=
      mul_le_mul_of_nonneg_left hF hk2.le
    have h2 : 0 < (jk ^ 2 - r ^ 2) * (-1 / jk ^ 2 * (2 * r)) + (jk ^ 2 - r ^ 2) / r + r := by
      have : (jk ^ 2 - r ^ 2) * (-1 / jk ^ 2 * (2 * r)) + (jk ^ 2 - r ^ 2) / r + r =
          ((jk ^ 2 - r ^ 2) ^ 2 + r ^ 4) / (r * jk ^ 2) := by
        field_simp; ring
      rw [this]; positivity
    linarith
  have hE : (jk ^ 2 - r ^ 2) * D + 3 * r * P = P * ((jk ^ 2 - r ^ 2) * X + (jk ^ 2 - r ^ 2) / r + r) := by
    rw [hDform]; field_simp; ring
  have hpos : 0 < (jk ^ 2 - r ^ 2) * D + 3 * r * P := by rw [hE]; exact mul_pos hp hW
  rw [div_lt_div_iff₀ hS hr0, hSdef]
  rcases le_or_gt 0 ((jk ^ 2 - r ^ 2) * D - r * P) with h | h
  · nlinarith [mul_nonneg hu.le h, mul_pos hk2 (mul_pos hp hp)]
  · have h7 : P * (jk ^ 2 - r ^ 2) / (4 * r) * ((jk ^ 2 - r ^ 2) * D - r * P) ≤
        U * ((jk ^ 2 - r ^ 2) * D - r * P) := mul_le_mul_of_nonpos_right hU h.le
    have h5 : 0 < P * (jk ^ 2 - r ^ 2) / (4 * r) * ((jk ^ 2 - r ^ 2) * D + 3 * r * P) :=
      mul_pos (by positivity) hpos
    have h6 : P * (jk ^ 2 - r ^ 2) / (4 * r) * ((jk ^ 2 - r ^ 2) * D + 3 * r * P) =
        (jk ^ 2 - r ^ 2) * P ^ 2 + P * (jk ^ 2 - r ^ 2) / (4 * r) * ((jk ^ 2 - r ^ 2) * D - r * P) := by
      field_simp; ring
    nlinarith

end

end Buckling
end
end ChunkedSource075
/- END SOURCE 075 -/

/- BEGIN SOURCE 076: RequestProject/Profiles/Bounds.lean -/
section ChunkedSource076

/-!
# Global bounds for the parity-extended profiles (Lemmas 9.1 and 9.3)

The quantities `f_s, f - s f_s, b_s, b - s b_s, G, s G_s, G_s` are bounded on `ℝ`
(wherever the derivatives are defined), and the even extension of `G` is globally Lipschitz.
-/

@[expose] public section

open Real Set Filter Topology NNReal

namespace Buckling

/-- A function continuous on `(0, ∞)` with finite limits at `0⁺` and at `∞` is bounded
there. -/
theorem bdd_of_tendsto_Ioi {h : ℝ → ℝ} {a b : ℝ} (hc : ∀ t, 0 < t → ContinuousAt h t)
    (h0 : Tendsto h (𝓝[>] 0) (𝓝 a)) (hinf : Tendsto h atTop (𝓝 b)) :
    ∃ C, ∀ t, 0 < t → |h t| ≤ C := by
  have e0 : ∀ᶠ t in 𝓝[>] 0, |h t| < |a| + 1 :=
    ((continuous_abs.tendsto a).comp h0).eventually (gt_mem_nhds (by linarith))
  have e1 : ∀ᶠ t in atTop, |h t| < |b| + 1 :=
    ((continuous_abs.tendsto b).comp hinf).eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp e0
  obtain ⟨M, hM⟩ := eventually_atTop.mp e1
  have hδ0 : (0 : ℝ) < δ := hδ
  have hcont : ContinuousOn h (Icc δ M) := fun t ht =>
    (hc t (lt_of_lt_of_le hδ0 ht.1)).continuousWithinAt
  obtain ⟨C3, hC3⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max (max (|a| + 1) (|b| + 1)) C3, fun t ht => ?_⟩
  rcases lt_or_ge t δ with h1 | h1
  · have : |h t| < |a| + 1 := hsub ⟨ht, h1⟩
    exact le_trans this.le (le_trans (le_max_left _ _) (le_max_left _ _))
  rcases le_or_gt M t with h2 | h2
  · exact le_trans (hM t h2).le (le_trans (le_max_right _ _) (le_max_left _ _))
  · have := hC3 t ⟨h1, h2.le⟩
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_right _ _)

/-- A continuous function on `ℝ` which is differentiable off `0` with derivative bounded by
`C` there is `C`-Lipschitz. -/
theorem lipschitzWith_of_deriv_bound_off_zero {F : ℝ → ℝ} {C : ℝ≥0} (hc : Continuous F)
    (hd : ∀ s, s ≠ 0 → DifferentiableAt ℝ F s) (hb : ∀ s, s ≠ 0 → |deriv F s| ≤ C) :
    LipschitzWith C F := by
  have key : ∀ a b, a ≤ b → (0 : ℝ) ∉ Ioo a b → |F b - F a| ≤ C * (b - a) := by
    intro a b hab h0
    rcases hab.lt_or_eq with hlt | heq
    · obtain ⟨c, hc', hcd⟩ := exists_hasDerivAt_eq_slope F (deriv F) hlt hc.continuousOn
        (fun x hx => (hd x (fun h => h0 (h ▸ hx))).hasDerivAt)
      have hc0 : c ≠ 0 := fun h => h0 (h ▸ hc')
      have hpos : 0 < b - a := sub_pos.mpr hlt
      rw [eq_div_iff hpos.ne'] at hcd
      rw [← hcd, abs_mul, abs_of_pos hpos]
      exact mul_le_mul_of_nonneg_right (hb c hc0) hpos.le
    · subst heq; simp
  have key2 : ∀ a b, a ≤ b → |F b - F a| ≤ C * (b - a) := by
    intro a b hab
    by_cases h0 : (0 : ℝ) ∈ Ioo a b
    · have h1 := key a 0 h0.1.le (fun h => lt_irrefl _ h.2)
      have h2 := key 0 b h0.2.le (fun h => lt_irrefl _ h.1)
      calc |F b - F a| = |(F b - F 0) + (F 0 - F a)| := by ring_nf
        _ ≤ |F b - F 0| + |F 0 - F a| := abs_add_le _ _
        _ ≤ C * (b - 0) + C * (0 - a) := add_le_add h2 h1
        _ = C * (b - a) := by ring
    · exact key a b hab h0
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq]
  rcases le_total x y with h | h
  · rw [abs_sub_comm (F x), abs_sub_comm x, abs_of_nonneg (sub_nonneg.mpr h)]
    exact key2 x y h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact key2 y x h

section

variable (hZ : ExtZeros)
include hZ

omit hZ in
lemma tendsto_id_nhdsGT : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds

lemma eventually_rt_rOf : ∀ᶠ t in atTop, rt (rOf t) = t := by
  filter_upwards [eventually_gt_atTop 0] with t ht using (rOf_spec hZ ht).2

/-- `f - t f_t = g` in the variable `t`. -/
lemma pf_sub_eq {t : ℝ} (ht : 0 < t) : pf t - t * rz (rOf t) = rg (rOf t) := by
  obtain ⟨hr, hrt⟩ := rOf_spec hZ ht
  have hid := (profile_identities_alg hZ hr.1 hr.2).2.1
  have hp := (radial_equations hZ _ hr.1 hr.2).1
  set r := rOf t with hr_def
  show rPhi r / rp r - t * rz r = rg r
  rw [← hrt]
  unfold rt
  rw [hid]
  field_simp
  ring

lemma bdd_rz : ∃ C, ∀ t, 0 < t → |rz (rOf t)| ≤ C :=
  bdd_of_tendsto_Ioi
    (fun _ ht => continuousAt_comp_rOf hZ
      (fun _ h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.1) ht)
    ((tendsto_rz_jk hZ).comp (tendsto_rOf_zero hZ))
    ((tendsto_rz_origin hZ).comp (tendsto_rOf_atTop hZ))

lemma bdd_rg : ∃ C, ∀ t, 0 < t → |rg (rOf t)| ≤ C :=
  bdd_of_tendsto_Ioi
    (fun _ ht => continuousAt_comp_rOf hZ
      (fun _ h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.2.2.2.2) ht)
    ((tendsto_rg_jk hZ).comp (tendsto_rOf_zero hZ))
    ((tendsto_rg_origin hZ).comp (tendsto_rOf_atTop hZ))

lemma bdd_rbt : ∃ C, ∀ t, 0 < t → |rbt (rOf t)| ≤ C :=
  bdd_of_tendsto_Ioi
    (fun _ ht => continuousAt_comp_rOf hZ
      (fun _ h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.2.2.1) ht)
    ((tendsto_rbt_jk hZ).comp (tendsto_rOf_zero hZ))
    ((tendsto_rbt_origin hZ).comp (tendsto_rOf_atTop hZ))

lemma bdd_rGt : ∃ C, ∀ t, 0 < t → |rGt (rOf t)| ≤ C :=
  bdd_of_tendsto_Ioi
    (fun _ ht => continuousAt_comp_rOf hZ
      (fun _ h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.2.1) ht)
    ((tendsto_rGt_jk hZ).comp (tendsto_rOf_zero hZ))
    ((tendsto_rGt_origin hZ).comp (tendsto_rOf_atTop hZ))

lemma bdd_rG : ∃ C, ∀ t, 0 < t → |rG (rOf t)| ≤ C :=
  bdd_of_tendsto_Ioi
    (fun _ ht => continuousAt_comp_rOf hZ
      (fun _ h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.1) ht)
    ((tendsto_rG_jk hZ).comp (tendsto_rOf_zero hZ))
    ((tendsto_rG_zero hZ).comp (tendsto_rOf_atTop hZ))

lemma bdd_b_sub : ∃ C, ∀ t, 0 < t → |rb (rOf t) - t * rbt (rOf t)| ≤ C := by
  refine bdd_of_tendsto_Ioi (a := 0 - 0 * (-2 * (zc * (-pAlpha * jJ / pc)) - (-1 / jk) *
    (grk / (-1 / 2)))) (b := 0) (fun t ht => ?_) ?_ ?_
  · exact (continuousAt_comp_rOf hZ
      (fun r h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.1) ht).sub
      (continuousAt_id.mul (continuousAt_comp_rOf hZ
      (fun r h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.2.2.1) ht))
  · have := ((tendsto_rb_jk hZ).comp (tendsto_rOf_zero hZ)).sub
      ((tendsto_id_nhdsGT).mul ((tendsto_rbt_jk hZ).comp (tendsto_rOf_zero hZ)))
    exact this
  · refine ((tendsto_rb_sub_origin hZ).comp (tendsto_rOf_atTop hZ)).congr' ?_
    filter_upwards [eventually_rt_rOf hZ] with t ht
    simp only [Function.comp, ht]

lemma bdd_tGt : ∃ C, ∀ t, 0 < t → |t * rGt (rOf t)| ≤ C := by
  refine bdd_of_tendsto_Ioi (a := 0 * (grk / (-1 / 2))) (b := 0) (fun t ht => ?_) ?_ ?_
  · exact continuousAt_id.mul (continuousAt_comp_rOf hZ
      (fun r h0 h1 => (continuousAt_radial hZ h0 h1).2.2.2.2.2.2.2.2.2.1) ht)
  · exact (tendsto_id_nhdsGT).mul ((tendsto_rGt_jk hZ).comp (tendsto_rOf_zero hZ))
  · refine ((tendsto_rt_rGt_origin hZ).comp (tendsto_rOf_atTop hZ)).congr' ?_
    filter_upwards [eventually_rt_rOf hZ] with t ht
    simp only [Function.comp, ht]

/-! ### The bounds on the real line -/

theorem fExt_bounds' :
    ∃ C, ∀ s, |deriv fExt s| ≤ C ∧ |fExt s - s * deriv fExt s| ≤ C := by
  obtain ⟨C1, h1⟩ := bdd_rz hZ
  obtain ⟨C2, h2⟩ := bdd_rg hZ
  refine ⟨max (max C1 C2) (max |deriv fExt 0| |fExt 0|), fun s => ?_⟩
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hs' : 0 < -s := neg_pos.mpr hs
    rw [(hasDerivAt_fExt_neg hZ hs).deriv, (fExt_eventually_neg hs).eq_of_nhds]
    refine ⟨?_, ?_⟩
    · rw [abs_neg]; exact le_trans (h1 _ hs') (le_trans (le_max_left _ _) (le_max_left _ _))
    · have := pf_sub_eq hZ hs'
      rw [show pf (-s) - s * -rz (rOf (-s)) = pf (-s) - -s * rz (rOf (-s)) by ring, this]
      exact le_trans (h2 _ hs') (le_trans (le_max_right _ _) (le_max_left _ _))
  · simp only [zero_mul, sub_zero]
    exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  · rw [(hasDerivAt_fExt_pos hZ hs).deriv, (fExt_eventually_pos hs).eq_of_nhds, pf_sub_eq hZ hs]
    exact ⟨le_trans (h1 _ hs) (le_trans (le_max_left _ _) (le_max_left _ _)),
      le_trans (h2 _ hs) (le_trans (le_max_right _ _) (le_max_left _ _))⟩

theorem bExt_bounds' :
    ∃ C, ∀ s, |deriv bExt s| ≤ C ∧ |bExt s - s * deriv bExt s| ≤ C := by
  obtain ⟨C1, h1⟩ := bdd_rbt hZ
  obtain ⟨C2, h2⟩ := bdd_b_sub hZ
  refine ⟨max (max C1 C2) (max |deriv bExt 0| |bExt 0|), fun s => ?_⟩
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hs' : 0 < -s := neg_pos.mpr hs
    rw [(hasDerivAt_bExt_neg hZ hs).deriv, (bExt_eventually_neg hs).eq_of_nhds]
    refine ⟨le_trans (h1 _ hs') (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
    have := h2 _ hs'
    rw [show -pb (-s) - s * rbt (rOf (-s)) = -(rb (rOf (-s)) - -s * rbt (rOf (-s))) by
      unfold pb; ring, abs_neg]
    exact le_trans this (le_trans (le_max_right _ _) (le_max_left _ _))
  · simp only [zero_mul, sub_zero]
    exact ⟨le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  · rw [(hasDerivAt_bExt_pos hZ hs).deriv, (bExt_eventually_pos hs).eq_of_nhds]
    exact ⟨le_trans (h1 _ hs) (le_trans (le_max_left _ _) (le_max_left _ _)),
      le_trans (h2 _ hs) (le_trans (le_max_right _ _) (le_max_left _ _))⟩

theorem GExt_bounds' :
    ∃ C, ∀ s, |GExt s| ≤ C ∧ |s * deriv GExt s| ≤ C := by
  obtain ⟨C1, h1⟩ := bdd_rG hZ
  obtain ⟨C2, h2⟩ := bdd_tGt hZ
  refine ⟨max (max C1 C2) 0, fun s => ?_⟩
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hs' : 0 < -s := neg_pos.mpr hs
    rw [(hasDerivAt_GExt_neg hZ hs).deriv, (GExt_eventually_neg hs).eq_of_nhds]
    refine ⟨le_trans (h1 _ hs') (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
    rw [show s * -rGt (rOf (-s)) = -s * rGt (rOf (-s)) by ring]
    exact le_trans (h2 _ hs') (le_trans (le_max_right _ _) (le_max_left _ _))
  · simp [GExt]
  · rw [(hasDerivAt_GExt_pos hZ hs).deriv, (GExt_eventually_pos hs).eq_of_nhds]
    exact ⟨le_trans (h1 _ hs) (le_trans (le_max_left _ _) (le_max_left _ _)),
      le_trans (h2 _ hs) (le_trans (le_max_right _ _) (le_max_left _ _))⟩

/-- The even extension of `G` is continuous at `0`. -/
lemma continuousAt_GExt_zero : ContinuousAt GExt 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  have h : Tendsto pG (𝓝[>] 0) (𝓝 0) := (tendsto_rG_jk hZ).comp (tendsto_rOf_zero hZ)
  have : GExt 0 = 0 := by simp [GExt]
  rw [this]
  refine tendsto_punctured_of_sides (h₁ := pG) (h₂ := pG) (fun s hs => ?_) (fun s hs => ?_) h h
  · simp [GExt, hs.ne', abs_of_pos hs]
  · simp [GExt, hs.ne, abs_of_neg hs]

theorem GExt_lipschitz' : ∃ L, LipschitzWith L GExt := by
  obtain ⟨C, hC⟩ := bdd_rGt hZ
  have hd : ∀ s, s ≠ 0 → HasDerivAt GExt (deriv GExt s) s := fun s hs => by
    rcases lt_or_gt_of_ne hs with h | h
    · exact (hasDerivAt_GExt_neg hZ h).differentiableAt.hasDerivAt
    · exact (hasDerivAt_GExt_pos hZ h).differentiableAt.hasDerivAt
  have hcont : Continuous GExt := by
    rw [continuous_iff_continuousAt]
    intro s
    by_cases hs : s = 0
    · subst hs; exact continuousAt_GExt_zero hZ
    · exact (hd s hs).continuousAt
  refine ⟨⟨max C 0, le_max_right _ _⟩, lipschitzWith_of_deriv_bound_off_zero hcont
    (fun s hs => (hd s hs).differentiableAt) fun s hs => ?_⟩
  rcases lt_or_gt_of_ne hs with h | h
  · rw [(hasDerivAt_GExt_neg hZ h).deriv, abs_neg]
    exact le_trans (hC _ (neg_pos.mpr h)) (le_max_left _ _)
  · rw [(hasDerivAt_GExt_pos hZ h).deriv]
    exact le_trans (hC _ h) (le_max_left _ _)

end

end Buckling
end
end ChunkedSource076
/- END SOURCE 076 -/

/- BEGIN SOURCE 077: RequestProject/Positivity/Phase.lean -/
section ChunkedSource077

/-!
# The phase estimate (Section 6 of the paper)

With `ρ² = u² + p²`, `η = S/ρ²`, the auxiliary potential
`𝒱 = 1 - cu/ρ² - p²/(r²ρ²) - S²/ρ⁴` is strictly decreasing on `(0, k)` (Proposition 6.5),
from `𝒱(0⁺) > λ` to `𝒱(k⁻) < λ`.  A Sturm-type argument then gives `z - t g < 0`
(the key step of Proposition 6.6).
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- Lemma 2.1 with a forcing `w φ`, `w > 0`, `φ` continuous and strictly decreasing from
positive to negative values. -/
theorem pos_of_hasDerivAt_mul_strictAnti {H w φ : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, HasDerivAt H (w x * φ x) x) (hw : ∀ x ∈ Ioo a b, 0 < w x)
    (hφc : ContinuousOn φ (Ioo a b)) (hφ : StrictAntiOn φ (Ioo a b))
    (hφa : ∀ᶠ x in 𝓝[>] a, 0 < φ x) (hφb : ∀ᶠ x in 𝓝[<] b, φ x < 0)
    (ha : Tendsto H (𝓝[>] a) (𝓝 0)) (hb : Tendsto H (𝓝[<] b) (𝓝 0)) :
    ∀ x ∈ Ioo a b, 0 < H x := by
  intro x hx
  have hab : a < b := hx.1.trans hx.2
  obtain ⟨x1, hx1, hx1'⟩ := (hφa.and (Ioo_mem_nhdsGT hab)).exists
  obtain ⟨x2, hx2, hx2'⟩ := (hφb.and (Ioo_mem_nhdsLT hab)).exists
  have h12 : x1 < x2 := by
    by_contra h
    push_neg at h
    rcases h.lt_or_eq with h | h
    · have := hφ hx2' hx1' h; linarith
    · subst h; linarith
  have hsub : Icc x1 x2 ⊆ Ioo a b := fun y hy => ⟨hx1'.1.trans_le hy.1, hy.2.trans_lt hx2'.2⟩
  obtain ⟨ξ, hξ, hξ0⟩ := intermediate_value_Icc' h12.le (hφc.mono hsub) ⟨hx2.le, hx1.le⟩
  have hξ' : ξ ∈ Ioo a b := hsub hξ
  refine pos_of_deriv_one_change hξ' (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    ha hb (fun y hy => ?_) (fun y hy => ?_) x hx
  · have hy' : y ∈ Ioo a b := ⟨hy.1, hy.2.trans hξ'.2⟩
    rw [(hd y hy').deriv]
    have := hφ hy' hξ' hy.2
    exact mul_pos (hw y hy') (by linarith)
  · have hy' : y ∈ Ioo a b := ⟨hξ'.1.trans hy.1, hy.2⟩
    rw [(hd y hy').deriv]
    have := hφ hξ' hy' hy.1
    exact mul_neg_of_pos_of_neg (hw y hy') (by linarith)

/-! ### Positivity of `J₂` and `J₃` on `(0, 4)` -/

lemma besselJ_two_pos_small (r : ℝ) (hr0 : 0 < r) (hr : r < 4) : 0 < besselJ 2 r := by
  have h := besselJ_tail_general 2 3 r hr0 (by push_cast; nlinarith)
  simp [besselPartialR, Finset.sum_range_succ, Nat.factorial] at h
  have hx0 : 0 < r ^ 2 := by positivity
  have hx : r ^ 2 < 16 := by nlinarith
  have hP : 0 < 1 / 8 - r ^ 2 / 96 + (r ^ 2) ^ 2 / 3072 - (r ^ 2) ^ 3 / 184320 := by
    nlinarith [mul_pos hx0 hx0, mul_pos (sub_pos.mpr hx) hx0, mul_pos (mul_pos (sub_pos.mpr hx) hx0) hx0]
  nlinarith [h.1]

lemma besselJ_three_pos_small (r : ℝ) (hr0 : 0 < r) (hr : r < 4) : 0 < besselJ 3 r := by
  have h := besselJ_tail_general 3 1 r hr0 (by push_cast; nlinarith)
  simp [besselPartialR, Finset.sum_range_succ, Nat.factorial] at h
  have hx0 : 0 < r ^ 3 := by positivity
  have hx : r ^ 2 < 16 := by nlinarith
  nlinarith [h.1, mul_pos hx0 (sub_pos.mpr hx)]

/-! ### The three phase inequalities (Lemma 6.3) -/

lemma deriv_rp_eq_all : deriv rp = fun x => (besselJ 0 x - besselJ 2 x) / 2 :=
  funext fun x => (hasDerivAt_besselJ_succ 0 x).deriv

lemma continuous_deriv_rp : Continuous (deriv rp) := by
  rw [deriv_rp_eq_all]; exact ((continuous_besselJ 0).sub (continuous_besselJ 2)).div_const 2

lemma besselJ_two_eq_rp {r : ℝ} (hr : r ≠ 0) : besselJ 2 r = rp r / r - deriv rp r := by
  rw [besselJ_two_eq r hr, deriv_rp_eq r hr, rp]; ring

section
variable (hZ : ExtZeros)
include hZ

lemma jk_lt_four : jk < 4 := by
  obtain ⟨-, -, -, h, -⟩ := root_boxes hZ; linarith

/-- `J₂ > 0` on `(0, k)`. -/
lemma J2_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < rp r / r - deriv rp r := by
  rw [← besselJ_two_eq_rp hr.1.ne']
  exact besselJ_two_pos_small r hr.1 (hr.2.trans (jk_lt_four hZ))

/-- **(P3)** `ρ² - 2cu = J₀² + J₁² - c² > 0` on `(0, k)`. -/
lemma R2_sub_two_c_u_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    0 < ru r ^ 2 + rp r ^ 2 - 2 * pc * ru r := by
  set E : ℝ → ℝ := fun x => besselJ 0 x ^ 2 + besselJ 1 x ^ 2 with hE
  have hk := jk_pos hZ
  have hanti : StrictAntiOn E (Icc r jk) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
    · exact (((continuous_besselJ 0).pow 2).add ((continuous_besselJ 1).pow 2)).continuousOn
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hr.1.trans hx.1
      have hd : HasDerivAt E (-2 * besselJ 1 x ^ 2 / x) x := by
        have := ((hasDerivAt_besselJ_zero x).pow 2).add ((hasDerivAt_besselJ_one x hx0.ne').pow 2)
        refine this.congr_deriv ?_
        field_simp; ring
      rw [hd.deriv]
      have : 0 < besselJ 1 x := (radial_equations hZ x hx0 hx.2).1
      have : 0 < besselJ 1 x ^ 2 := by positivity
      apply div_neg_of_neg_of_pos (by linarith) hx0
  have h := hanti ⟨le_rfl, hr.2.le⟩ ⟨hr.2.le, le_rfl⟩ hr.2
  have hEk : E jk = pc ^ 2 := by
    simp only [hE, pc, besselJ_one_jk hZ]; ring
  rw [hEk] at h
  simp only [hE] at h
  have : ru r ^ 2 + rp r ^ 2 - 2 * pc * ru r = besselJ 0 r ^ 2 + besselJ 1 r ^ 2 - pc ^ 2 := by
    simp only [ru, rp]; ring
  rw [this]; linarith

/-- **(P2)** `pρ² - r u S = p(p - ru/2)² + (r²u²/4) J₃ > 0` on `(0, k)`. -/
lemma pR2_sub_ruS_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    0 < rp r * (ru r ^ 2 + rp r ^ 2) - r * ru r * rS r := by
  have hr0 := hr.1.ne'
  have hJ3 := besselJ_three_pos_small r hr.1 (hr.2.trans (jk_lt_four hZ))
  rw [besselJ_three_eq r hr0, besselJ_two_eq_rp hr0] at hJ3
  obtain ⟨hp, hu, -⟩ := radial_equations hZ r hr.1 hr.2
  have hid : rp r * (ru r ^ 2 + rp r ^ 2) - r * ru r * rS r =
      rp r * (rp r - r * ru r / 2) ^ 2 + r ^ 2 * ru r ^ 2 / 4 *
        (4 * (rp r / r - deriv rp r) / r - besselJ 1 r) := by
    simp only [rS, rp] at *; field_simp; ring
  rw [hid]
  have : 0 < r ^ 2 * ru r ^ 2 / 4 * (4 * (rp r / r - deriv rp r) / r - besselJ 1 r) := by
    positivity
  nlinarith [sq_nonneg (rp r - r * ru r / 2)]

end

section
variable (hZ : ExtZeros)
include hZ

/-- **(P1)** `F = p² - u J₂ > 0` on `(0, k)`, i.e. `S > up/r`. -/
lemma rS_gt_up_div_r (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    ru r * rp r / r < rS r := by
  have hk := jk_pos hZ
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hc1 := (coarse_c hZ hI).2
  set H : ℝ → ℝ := fun x => x ^ 2 * rp x ^ 2 - x * ru x * rp x + x ^ 2 * ru x * deriv rp x
    with hH
  have hHc : Continuous H := by
    have := continuous_deriv_rp
    have h1 : Continuous rp := continuous_besselJ 1
    have h2 : Continuous ru := (continuous_besselJ 0).add continuous_const
    simp only [hH]; fun_prop
  have hd : ∀ x ∈ Ioo 0 jk, HasDerivAt H (x ^ 2 * rp x * (2 * rp x / x - pc)) x := by
    intro x hx
    obtain ⟨hp, hu, -, hu', hp', hp'', -⟩ := radial_equations hZ x hx.1 hx.2
    have hdp : deriv rp x = ru x - pc - rp x / x := hp'.deriv
    have hx0 := hx.1.ne'
    have h := ((((hasDerivAt_pow 2 x).mul (hp'.pow 2)).sub
      (((hasDerivAt_id x).mul hu').mul hp')).add (((hasDerivAt_pow 2 x).mul hu').mul hp''))
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, Pi.pow_apply, id, Nat.cast_ofNat, hdp]
    field_simp
    ring
  have hφc : ∀ x : ℝ, x ≠ 0 → ContinuousAt (fun x => 2 * rp x / x - pc) x := by
    intro x hx
    have : Continuous rp := continuous_besselJ 1
    fun_prop (disch := exact hx)
  have hpos := pos_of_hasDerivAt_mul_strictAnti (H := H) (w := fun x => x ^ 2 * rp x)
    (φ := fun x => 2 * rp x / x - pc) (a := 0) (b := jk) hd
    (fun x hx => mul_pos (pow_pos hx.1 2) (radial_equations hZ x hx.1 hx.2).1) ?_ ?_ ?_ ?_ ?_ ?_ r hr
  · obtain ⟨hp, hu, -, -, hp', -⟩ := radial_equations hZ r hr.1 hr.2
    have hr0 := hr.1.ne'
    have : H r = r ^ 2 * (rS r - ru r * rp r / r) := by
      simp only [hH, rS]; field_simp; ring
    rw [this] at hpos
    have := pos_of_mul_pos_right hpos (by positivity)
    linarith
  · intro x hx
    exact (hφc x hx.1.ne').continuousWithinAt
  · apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro x hx
      exact (hφc x hx.1.ne').continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      obtain ⟨-, -, -, -, hp', -⟩ := radial_equations hZ x hx.1 hx.2
      have hx0 := hx.1.ne'
      have h := ((hp'.div (hasDerivAt_id x) hx0).const_mul 2).sub_const pc
      have hJ := J2_pos hZ hx
      rw [hp'.deriv] at hJ
      have h' : HasDerivAt (fun x => 2 * (rp x / x) - pc)
          (2 * (((ru x - pc - rp x / x) * x - rp x * 1) / x ^ 2)) x := h
      change deriv (fun x => 2 * rp x / x - pc) x < 0
      have e : (fun x => 2 * rp x / x - pc) = fun x => 2 * (rp x / x) - pc := by
        ext y; ring
      rw [e, h'.deriv]
      have : (ru x - pc - rp x / x) * x - rp x * 1 = x * ((ru x - pc - rp x / x) - rp x / x) := by
        field_simp
      rw [this]
      have : 0 < x ^ 2 := by positivity
      have : (ru x - pc - rp x / x) - rp x / x < 0 := by linarith
      have : x * ((ru x - pc - rp x / x) - rp x / x) / x ^ 2 < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hx.1 this) (by positivity)
      linarith
  · have h := (tendsto_besselJ_one_div_pos.const_mul 2).sub_const pc
    have : (0 : ℝ) < 2 * (1 / 2) - pc := by linarith
    filter_upwards [h.eventually (lt_mem_nhds this)] with x hx
    simpa [rp, mul_div_assoc] using! hx
  · have h : Tendsto (fun x => 2 * rp x / x - pc) (𝓝[<] jk) (𝓝 (2 * rp jk / jk - pc)) :=
      (hφc jk hk.ne').tendsto.mono_left nhdsWithin_le_nhds
    rw [rp_jk hZ] at h
    have : 2 * 0 / jk - pc < 0 := by simp; linarith
    exact h.eventually (gt_mem_nhds this)
  · have := hHc.continuousAt (x := 0) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hH] using this
  · have := hHc.continuousAt (x := jk) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio jk))
    simpa [hH, rp_jk hZ, ru_jk] using this

end

/-! ### The auxiliary potential and its derivative (Proposition 6.5) -/

/-- `ρ² = u² + p²`. -/
noncomputable def R2f (r : ℝ) : ℝ := ru r ^ 2 + rp r ^ 2

/-- The auxiliary potential `𝒱 = 1 - cu/ρ² - p²/(r²ρ²) - S²/ρ⁴`. -/
noncomputable def Vf (r : ℝ) : ℝ :=
  1 - pc * ru r / R2f r - rp r ^ 2 / (r ^ 2 * R2f r) - rS r ^ 2 / R2f r ^ 2

/-- The explicit derivative of `𝒱` (equation (6.4) of the paper), with `η = S/ρ²`. -/
noncomputable def Vd (r : ℝ) : ℝ :=
  -(pc * rp r / R2f r) * (1 - 2 * (rS r / R2f r)) ^ 2 +
    2 / r * (1 / R2f r) * ((rS r / R2f r * ru r - rp r / r) ^ 2 - (rS r / R2f r) ^ 2 * rp r ^ 2)

section
variable (hZ : ExtZeros)
include hZ

lemma R2f_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < R2f r := by
  have := (radial_equations hZ r hr.1 hr.2).1
  unfold R2f; positivity

lemma hasDerivAt_rS {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt rS (rp r * deriv rp r - ru r * deriv rp r / r - ru r * rp r * (1 - 1 / r ^ 2)) r := by
  obtain ⟨hp, hu, -, hu', hp', hp'', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have h := (hp'.pow 2).add (hu'.mul hp'')
  refine h.congr_deriv ?_
  rw [hdp]; ring

lemma hasDerivAt_R2f {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt R2f (-2 * rp r * (pc + rp r / r)) r := by
  obtain ⟨hp, hu, -, hu', hp', -⟩ := radial_equations hZ r hr.1 hr.2
  have h := (hu'.pow 2).add (hp'.pow 2)
  refine h.congr_deriv ?_
  ring

lemma hasDerivAt_Vf {r : ℝ} (hr : r ∈ Ioo 0 jk) : HasDerivAt Vf (Vd r) r := by
  obtain ⟨hp, hu, -, hu', hp', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have hR := R2f_pos hZ hr
  have hr0 := hr.1.ne'
  have hS := hasDerivAt_rS hZ hr
  have hR' := hasDerivAt_R2f hZ hr
  have h := (((hasDerivAt_const r (1 : ℝ)).sub ((hu'.const_mul pc).div hR' hR.ne')).sub
    ((hp'.pow 2).div ((hasDerivAt_pow 2 r).mul hR') (mul_ne_zero (pow_ne_zero 2 hr0) hR.ne'))).sub
    ((hS.pow 2).div (hR'.pow 2) (pow_ne_zero 2 hR.ne'))
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, Vd, rS, hdp, Nat.cast_ofNat]
  norm_num
  unfold R2f at *
  have hR0 : ru r ^ 2 + rp r ^ 2 ≠ 0 := hR.ne'
  generalize ru r = u at *
  generalize rp r = p at *
  field_simp
  ring

end

/-! ### The radius bound (Lemma 6.4) -/

section
variable (hZ : ExtZeros)
include hZ

/-- `Y = p²/(r²ρ²) = (sin θ / r)²`. -/
lemma hasDerivAt_Yphase {x : ℝ} (hx : x ∈ Ioo 0 jk) :
    HasDerivAt (fun x => rp x ^ 2 / (x ^ 2 * R2f x))
      (2 * rp x * (x * ru x * rS x - rp x * R2f x) / (x ^ 3 * R2f x ^ 2)) x := by
  obtain ⟨hp, hu, -, hu', hp', -⟩ := radial_equations hZ x hx.1 hx.2
  have hdp : deriv rp x = ru x - pc - rp x / x := hp'.deriv
  have hR := R2f_pos hZ hx
  have hx0 := hx.1.ne'
  have h := (hp'.pow 2).div ((hasDerivAt_pow 2 x).mul (hasDerivAt_R2f hZ hx))
    (mul_ne_zero (pow_ne_zero 2 hx0) hR.ne')
  refine h.congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply, Nat.cast_ofNat, rS, hdp]
  norm_num
  unfold R2f at *
  have hR0 : ru x ^ 2 + rp x ^ 2 ≠ 0 := hR.ne'
  generalize ru x = u at *
  generalize rp x = p at *
  field_simp
  ring

lemma Yphase_strictAnti : StrictAntiOn (fun x => rp x ^ 2 / (x ^ 2 * R2f x)) (Ioo 0 jk) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro x hx; exact (hasDerivAt_Yphase hZ hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_Yphase hZ hx).deriv]
    have hp := (radial_equations hZ x hx.1 hx.2).1
    have hR := R2f_pos hZ hx
    have h2 := pR2_sub_ruS_pos hZ hx
    have hx0 := hx.1
    unfold R2f at *
    apply div_neg_of_neg_of_pos _ (by positivity)
    have : x * ru x * rS x - rp x * (ru x ^ 2 + rp x ^ 2) < 0 := by linarith
    nlinarith

lemma two_lt_jk : 2 < jk := by
  obtain ⟨-, -, h, -⟩ := root_boxes hZ; linarith

/-- `p(2) < u(2)`. -/
lemma rp_two_lt_ru_two (hI : ExtIntegral) : rp 2 < ru 2 := by
  obtain ⟨-, -, -, h1, h2⟩ := small_bessel_bounds
  have hc := (coarse_c hZ hI).1
  simp only [rp, ru]; linarith

/-- **Lemma 6.4**: if `θ ≥ π/4`, i.e. `p ≥ u`, then `r > 2√2 sin θ`, i.e. `8p² < r²ρ²`. -/
lemma radius_bound (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) (hpu : ru r ≤ rp r) :
    8 * rp r ^ 2 < r ^ 2 * R2f r := by
  have h2 : (2 : ℝ) ∈ Ioo 0 jk := ⟨by norm_num, two_lt_jk hZ⟩
  have hp2 := (radial_equations hZ 2 h2.1 h2.2).1
  have hpu2 := rp_two_lt_ru_two hZ hI
  -- `r > 2`
  have hr2 : 2 < r := by
    by_contra hcon
    push_neg at hcon
    have ht2 : 1 < rt 2 := by rw [rt, one_lt_div hp2]; exact hpu2
    have htr : rt 2 ≤ rt r := (rt_strictAntiOn hZ).antitoneOn hr h2 hcon
    have hp := (radial_equations hZ r hr.1 hr.2).1
    have : rt r ≤ 1 := by rw [rt, div_le_one hp]; exact hpu
    linarith
  have hY := Yphase_strictAnti hZ h2 hr hr2
  have hY2 : rp 2 ^ 2 / (2 ^ 2 * R2f 2) < 1 / 8 := by
    have hR := R2f_pos hZ h2
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    unfold R2f
    nlinarith
  have hR := R2f_pos hZ hr
  have := hY.trans hY2
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)] at this
  linarith

end

/-- The algebraic step of Proposition 6.5 on the second angular range:
`c_θ + 1/(s_θ + c_θ) ≤ √2` combined with `r > 2√2 s_θ`. -/
lemma phase_alg {r p u : ℝ} (hr : 0 < r) (hu : 0 < u) (hpu : u ≤ p)
    (h8 : 8 * p ^ 2 < r ^ 2 * (u ^ 2 + p ^ 2)) :
    p / (r * (u + p)) ≤ 1 / 2 - p * u / (r * (u ^ 2 + p ^ 2)) := by
  have hp : 0 < p := hu.trans_le hpu
  set R := u ^ 2 + p ^ 2 with hR
  have hR0 : 0 < R := by positivity
  set X := p * u / R + p / (u + p) with hX
  have hX0 : 0 < X := by positivity
  have hkey : (u * (u + p) + R) ^ 2 ≤ 2 * R * (u + p) ^ 2 := by
    have : 2 * R * (u + p) ^ 2 - (u * (u + p) + R) ^ 2 =
        (p - u) * (p ^ 3 + 3 * u * p ^ 2 + 2 * u ^ 2 * p + 2 * u ^ 3) := by
      rw [hR]; ring
    nlinarith [mul_nonneg (sub_nonneg.mpr hpu)
      (by positivity : (0 : ℝ) ≤ p ^ 3 + 3 * u * p ^ 2 + 2 * u ^ 2 * p + 2 * u ^ 3)]
  have hX2 : X ^ 2 ≤ 2 * p ^ 2 / R := by
    have : X = p * (u * (u + p) + R) / (R * (u + p)) := by
      rw [hX]; field_simp
    rw [this, div_pow, div_le_div_iff₀ (by positivity) hR0]
    have : (p * (u * (u + p) + R)) ^ 2 * R = p ^ 2 * R * (u * (u + p) + R) ^ 2 := by ring
    rw [this]
    have : 2 * p ^ 2 * (R * (u + p)) ^ 2 = p ^ 2 * R * (2 * R * (u + p) ^ 2) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  have hr2 : 2 * p ^ 2 / R < (r / 2) ^ 2 := by
    rw [div_lt_iff₀ hR0]; nlinarith
  have hXr : X < r / 2 := by
    have := lt_of_le_of_lt hX2 hr2
    nlinarith
  rw [hX] at hXr
  have e1 : p / (r * (u + p)) = (p / (u + p)) / r := by field_simp
  have e2 : 1 / 2 - p * u / (r * R) = (r / 2 - p * u / R) / r := by field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ hr.le
  linarith

/-! ### Monotonicity of the potential (Proposition 6.5) -/

lemma bracket_neg_alg {η u p r : ℝ} (hA : p / r < η * (u + p)) (hB : η * (u - p) < p / r) :
    (η * u - p / r) ^ 2 - η ^ 2 * p ^ 2 < 0 := by
  have : (η * u - p / r) ^ 2 - η ^ 2 * p ^ 2 = (η * (u - p) - p / r) * (η * (u + p) - p / r) := by
    ring
  rw [this]
  exact mul_neg_of_neg_of_pos (by linarith) (by linarith)

section
variable (hZ : ExtZeros)
include hZ

/-- The square bracket in (6.4) is strictly negative (proof of Proposition 6.5). -/
lemma phase_bracket_neg (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    (rS r / R2f r * ru r - rp r / r) ^ 2 - (rS r / R2f r) ^ 2 * rp r ^ 2 < 0 := by
  obtain ⟨hp, hu, -, -, hp', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have hR := R2f_pos hZ hr
  have hr0 := hr.1
  have hS := rS_pos hZ hr.1 hr.2
  have hS' : 0 < rS r := by simpa [rS] using hS
  have hη : 0 < rS r / R2f r := div_pos hS' hR
  set η := rS r / R2f r with hη_def
  apply bracket_neg_alg
  · -- `η (u + p) > p/r`
    rcases le_or_gt (ru r) (rp r) with hpu | hpu
    · have h3 := R2_sub_two_c_u_pos hZ hr
      have h8 := radius_bound hZ hI hr hpu
      have halg := phase_alg hr0 hu hpu h8
      have hSeq : rS r = R2f r - pc * ru r - rp r * ru r / r := by
        simp only [rS, R2f, hdp]; ring
      have hη1 : 1 / 2 - rp r * ru r / (r * R2f r) < η := by
        rw [hη_def, hSeq]
        unfold R2f at *
        rw [lt_div_iff₀ hR]
        field_simp
        nlinarith
      have : rp r / (r * (ru r + rp r)) < η := lt_of_le_of_lt (by unfold R2f at *; exact halg) hη1
      rw [div_lt_iff₀ (by positivity)] at this
      rw [div_lt_iff₀ hr0]; nlinarith
    · have h1 := rS_gt_up_div_r hZ hI hr
      have hη1 : ru r * rp r / (r * R2f r) < η := by
        rw [hη_def, div_lt_div_iff₀ (by positivity) hR]
        rw [div_lt_iff₀ hr0] at h1
        nlinarith
      have hge : rp r / r ≤ ru r * rp r / (r * R2f r) * (ru r + rp r) := by
        unfold R2f at *
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hr0 (by positivity)]
        nlinarith [mul_pos (mul_pos (mul_pos hp hp) hr0) (sub_pos.mpr hpu)]
      calc rp r / r ≤ _ := hge
        _ < η * (ru r + rp r) := by gcongr
  · -- `η (u - p) < p/r`
    rcases le_or_gt (ru r) (rp r) with hpu | hpu
    · have : η * (ru r - rp r) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hη.le (by linarith)
      have : 0 < rp r / r := div_pos hp hr0
      linarith
    · have h2 := pR2_sub_ruS_pos hZ hr
      have hη2 : η * ru r < rp r / r := by
        rw [hη_def, div_mul_eq_mul_div, div_lt_div_iff₀ hR hr0]
        unfold R2f at *; nlinarith
      nlinarith

lemma Vd_neg (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) : Vd r < 0 := by
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hR := R2f_pos hZ hr
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hB := phase_bracket_neg hZ hI hr
  have hr0 := hr.1
  unfold Vd
  have h1 : 0 ≤ pc * rp r / R2f r * (1 - 2 * (rS r / R2f r)) ^ 2 := by positivity
  have h2 : 2 / r * (1 / R2f r) * ((rS r / R2f r * ru r - rp r / r) ^ 2 -
      (rS r / R2f r) ^ 2 * rp r ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (by positivity) hB
  linarith

/-- **Proposition 6.5**: `𝒱` is strictly decreasing on `(0, k)`. -/
theorem Vf_strictAnti (hI : ExtIntegral) : StrictAntiOn Vf (Ioo 0 jk) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro x hx; exact (hasDerivAt_Vf hZ hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioo] at hx
    rw [(hasDerivAt_Vf hZ hx).deriv]
    exact Vd_neg hZ hI hx

end

/-! ### Endpoint values of the potential -/

section
variable (hZ : ExtZeros)
include hZ

lemma tendsto_ru_div_sq : Tendsto (fun r => ru r / (jk - r) ^ 2) (𝓝[<] jk) (𝓝 (pc / 2)) :=
  tendsto_div_of_expansion (ru_O3 hZ)

omit hZ in
lemma tendsto_dk_zero : Tendsto (fun r => jk - r) (𝓝[<] jk) (𝓝 0) := by
  have : Tendsto (fun r => jk - r) (𝓝 jk) (𝓝 (jk - jk)) :=
    (continuous_const.sub continuous_id).tendsto jk
  rw [sub_self] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- `𝒱(k⁻) = 1/4 - 1/k²`. -/
theorem tendsto_Vf_jk : Tendsto Vf (𝓝[<] jk) (𝓝 (1 / 4 - 1 / jk ^ 2)) := by
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hk := jk_pos hZ
  have ha := tendsto_ru_div_sq hZ
  have hb : Tendsto (fun r => rp r / (jk - r)) (𝓝[<] jk) (𝓝 pc) := by
    simpa using tendsto_rp_div hZ
  have hs := tendsto_rS_div hZ
  have hδ := tendsto_dk_zero
  have hr : Tendsto (fun r : ℝ => r) (𝓝[<] jk) (𝓝 jk) := nhdsWithin_le_nhds
  -- `X = (u/p)² + 1 → 1`
  have hX : Tendsto (fun r => (ru r / (jk - r) ^ 2 * (jk - r) / (rp r / (jk - r))) ^ 2 + 1)
      (𝓝[<] jk) (𝓝 ((pc / 2 * 0 / pc) ^ 2 + 1)) :=
    (((ha.mul hδ).div hb hc.ne').pow 2).add_const 1
  have hA : Tendsto (fun r => pc * (ru r / (jk - r) ^ 2 / (rp r / (jk - r)) ^ 2)) (𝓝[<] jk)
      (𝓝 (pc * (pc / 2 / pc ^ 2))) :=
    (ha.div (hb.pow 2) (pow_ne_zero 2 hc.ne')).const_mul pc
  have hB : Tendsto (fun r => rS r / (jk - r) ^ 2 / (rp r / (jk - r)) ^ 2) (𝓝[<] jk)
      (𝓝 (pc ^ 2 / 2 / pc ^ 2)) := hs.div (hb.pow 2) (pow_ne_zero 2 hc.ne')
  simp only [mul_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_add] at hX
  have hlim := ((((tendsto_const_nhds (x := (1 : ℝ))).sub (hA.div hX one_ne_zero)).sub
    ((tendsto_const_nhds (x := (1 : ℝ))).div ((hr.pow 2).mul hX) (by positivity))).sub
    ((hB.pow 2).div (hX.pow 2) (by norm_num)))
  have hval : 1 - pc * (pc / 2 / pc ^ 2) / 1 - 1 / (jk ^ 2 * 1) - (pc ^ 2 / 2 / pc ^ 2) ^ 2 / 1 ^ 2
      = 1 / 4 - 1 / jk ^ 2 := by field_simp; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hk] with r hr'
  have hp := (radial_equations hZ r hr'.1 hr'.2).1
  have hδ0 : jk - r ≠ 0 := (sub_pos.mpr hr'.2).ne'
  have hr0 := hr'.1.ne'
  have hR := R2f_pos hZ hr'
  simp only [Pi.div_apply]
  unfold Vf
  unfold R2f at *
  have hR0 : ru r ^ 2 + rp r ^ 2 ≠ 0 := hR.ne'
  have hp0 : rp r ≠ 0 := hp.ne'
  generalize ru r = u at *
  generalize rp r = p at *
  generalize jk - r = δ at *
  field_simp

/-- `𝒱(0⁺) = 1 - c/σ - 1/(2σ²)`. -/
theorem tendsto_Vf_zero :
    Tendsto Vf (𝓝[>] 0) (𝓝 (1 - pc / pSigma - 1 / (2 * pSigma ^ 2))) := by
  have hσ := pSigma_pos hZ
  have hk := jk_pos hZ
  have hu := tendsto_ru_zero
  have hp0 : Tendsto rp (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_besselJ 1).tendsto 0
    simp only [besselJ_zero_arg] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpr := tendsto_besselJ_one_div_pos
  have hdp := tendsto_deriv_rp_zero
  have hR : Tendsto R2f (𝓝[>] 0) (𝓝 (pSigma ^ 2 + 0 ^ 2)) := (hu.pow 2).add (hp0.pow 2)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hR
  have hS : Tendsto rS (𝓝[>] 0) (𝓝 (0 ^ 2 + pSigma * (1 / 2))) := (hp0.pow 2).add (hu.mul hdp)
  have hσ2 : pSigma ^ 2 ≠ 0 := by positivity
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).sub (((tendsto_const_nhds (x := pc)).mul hu).div
    hR hσ2)).sub ((hpr.pow 2).div hR hσ2)).sub ((hS.pow 2).div (hR.pow 2) (pow_ne_zero 2 hσ2))
  have hval : 1 - pc * pSigma / pSigma ^ 2 - (1 / 2) ^ 2 / pSigma ^ 2 -
      ((0 : ℝ) ^ 2 + pSigma * (1 / 2)) ^ 2 / (pSigma ^ 2) ^ 2 =
      1 - pc / pSigma - 1 / (2 * pSigma ^ 2) := by field_simp; ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hk] with r hr'
  have hr0 := hr'.1.ne'
  simp only [Vf, rp, Pi.div_apply]
  field_simp

end

end Buckling
end
end ChunkedSource077
/- END SOURCE 077 -/

/- BEGIN SOURCE 078: RequestProject/Positivity/PhaseW.lean -/
section ChunkedSource078

/-!
# The phase estimate `z - t g < 0` (proof of Proposition 6.6)

With `ρ = √(u² + p²)` and `W = ρ φ' - φ ρ'`, one has `(rW)' = rρφ(𝒱 - λ)`.  Since `𝒱 - λ`
changes sign once (from positive to negative) and `rW → 0` at both endpoints, `W > 0`;
and `z - t g = -ρ W / (p S)`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `ρ = √(u² + p²)`. -/
noncomputable def rhoF (r : ℝ) : ℝ := Real.sqrt (R2f r)

/-- `M = p(c + p/r)`, so that `ρ' = -M/ρ`. -/
noncomputable def Mf (r : ℝ) : ℝ := pc * rp r + rp r ^ 2 / r

/-- `W = ρφ' - φρ' = ρφ' + φM/ρ`. -/
noncomputable def Wf (r : ℝ) : ℝ := rhoF r * deriv rPhi r + rPhi r * Mf r / rhoF r

section
variable (hZ : ExtZeros)
include hZ

lemma rhoF_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < rhoF r := Real.sqrt_pos.mpr (R2f_pos hZ hr)

lemma rhoF_sq {r : ℝ} (hr : r ∈ Ioo 0 jk) : rhoF r ^ 2 = R2f r :=
  Real.sq_sqrt (R2f_pos hZ hr).le

lemma hasDerivAt_rhoF {r : ℝ} (hr : r ∈ Ioo 0 jk) : HasDerivAt rhoF (-Mf r / rhoF r) r := by
  have h := (hasDerivAt_R2f hZ hr).sqrt (R2f_pos hZ hr).ne'
  refine h.congr_deriv ?_
  have hρ := rhoF_pos hZ hr
  simp only [rhoF] at hρ ⊢
  unfold Mf
  field_simp

lemma hasDerivAt_Mf {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt Mf (pc * deriv rp r + (2 * rp r * deriv rp r * r - rp r ^ 2) / r ^ 2) r := by
  obtain ⟨-, -, -, -, hp', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have h := (hp'.const_mul pc).add ((hp'.pow 2).div (hasDerivAt_id r) hr.1.ne')
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply, id, hdp, Nat.cast_ofNat]
  ring

/-- `(rW)' = rρφ(𝒱 - λ)`. -/
lemma hasDerivAt_rWf {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt (fun x => x * Wf x) (r * rhoF r * rPhi r * (Vf r - pLam)) r := by
  obtain ⟨hp, hu, -, hu', hp', -, hφ'', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have hφ' : HasDerivAt rPhi (deriv rPhi r) r := (hasDerivAt_rPhi r).differentiableAt.hasDerivAt
  have hρ := hasDerivAt_rhoF hZ hr
  have hM := hasDerivAt_Mf hZ hr
  have hρ0 := rhoF_pos hZ hr
  have hρ2 := rhoF_sq hZ hr
  have hr0 := hr.1.ne'
  have h := (hasDerivAt_id r).mul ((hρ.mul hφ'').add ((hφ'.mul hM).div hρ hρ0.ne'))
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply, id, Vf, ← hρ2, Mf, hdp, rS]
  unfold R2f at hρ2
  field_simp
  have h4 : rhoF r ^ 4 = (ru r ^ 2 + rp r ^ 2) ^ 2 := by rw [← hρ2]; ring
  simp only [h4, hρ2]
  ring

lemma tendsto_rWf_zero : Tendsto (fun x => x * Wf x) (𝓝[>] 0) (𝓝 0) := by
  have hσ := pSigma_pos hZ
  have hu := tendsto_ru_zero
  have hp0 : Tendsto rp (𝓝[>] 0) (𝓝 0) := by
    have := (continuous_besselJ 1).tendsto 0
    simp only [besselJ_zero_arg] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpr := tendsto_besselJ_one_div_pos
  have hR : Tendsto R2f (𝓝[>] 0) (𝓝 (pSigma ^ 2 + 0 ^ 2)) := (hu.pow 2).add (hp0.pow 2)
  have hρ : Tendsto rhoF (𝓝[>] 0) (𝓝 (Real.sqrt (pSigma ^ 2 + 0 ^ 2))) :=
    (Real.continuous_sqrt.tendsto _).comp hR
  rw [show Real.sqrt (pSigma ^ 2 + 0 ^ 2) = pSigma by
    rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hσ.le]] at hρ
  have hdφ : Tendsto (deriv rPhi) (𝓝[>] 0) (𝓝 (deriv rPhi 0)) :=
    (continuous_deriv_rPhi.tendsto 0).mono_left nhdsWithin_le_nhds
  rw [deriv_rPhi_eq, mul_zero, besselJ_zero_arg] at hdφ
  simp only [one_ne_zero, if_false, mul_zero] at hdφ
  have hM : Tendsto Mf (𝓝[>] 0) (𝓝 (pc * 0 + 1 / 2 * 0)) := by
    refine ((tendsto_const_nhds.mul hp0).add (hpr.mul hp0)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Mf, rp]; field_simp
  have hW : Tendsto Wf (𝓝[>] 0) (𝓝 (pSigma * 0 + 1 * (pc * 0 + 1 / 2 * 0) / pSigma)) :=
    (hρ.mul hdφ).add (((tendsto_rPhi_zero hZ).mul hM).div hρ hσ.ne')
  have hid : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have := hid.mul hW
  simpa using this

lemma tendsto_rWf_jk : Tendsto (fun x => x * Wf x) (𝓝[<] jk) (𝓝 0) := by
  have hk := jk_pos hZ
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hR : Tendsto R2f (𝓝[<] jk) (𝓝 (ru jk ^ 2 + rp jk ^ 2)) :=
    ((((continuous_besselJ 0).add continuous_const).pow 2).add
      ((continuous_besselJ 1).pow 2)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [ru_jk, rp_jk hZ] at hR
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hR
  have hρ : Tendsto rhoF (𝓝[<] jk) (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto _).comp hR
  rw [Real.sqrt_zero] at hρ
  have hdφ : Tendsto (deriv rPhi) (𝓝[<] jk) (𝓝 (deriv rPhi jk)) :=
    (continuous_deriv_rPhi.tendsto jk).mono_left nhdsWithin_le_nhds
  have hφ : Tendsto rPhi (𝓝[<] jk) (𝓝 0) := by
    have := continuous_rPhi.tendsto jk
    rw [rPhi_jk hZ] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hp0 : Tendsto rp (𝓝[<] jk) (𝓝 0) := by
    have := (continuous_besselJ 1).tendsto jk
    rw [← rp, rp_jk hZ] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hA : Tendsto (fun x => rPhi x * (pc + rp x / x)) (𝓝[<] jk) (𝓝 (0 * (pc + 0 / jk))) :=
    hφ.mul (tendsto_const_nhds.add (hp0.div nhdsWithin_le_nhds hk.ne'))
  rw [zero_mul] at hA
  have hB : IsBoundedUnder (· ≤ ·) (𝓝[<] jk) (fun x => ‖rp x / rhoF x‖) := by
    refine isBoundedUnder_of_eventually_le (a := 1) ?_
    filter_upwards [Ioo_mem_nhdsLT hk] with x hx
    have hp := (radial_equations hZ x hx.1 hx.2).1
    have hρ0 := rhoF_pos hZ hx
    have hρ2 := rhoF_sq hZ hx
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hp hρ0), div_le_one hρ0]
    unfold R2f at hρ2
    nlinarith [sq_nonneg (ru x)]
  have hC := hA.zero_mul_isBoundedUnder_le hB
  have hW : Tendsto Wf (𝓝[<] jk) (𝓝 (0 * deriv rPhi jk + 0)) := by
    refine (hρ.mul hdφ).add (hC.congr' ?_)
    filter_upwards [Ioo_mem_nhdsLT hk] with x hx
    have hρ0 := rhoF_pos hZ hx
    simp only [Mf]
    field_simp
  have hid : Tendsto (fun x : ℝ => x) (𝓝[<] jk) (𝓝 jk) := nhdsWithin_le_nhds
  have := hid.mul hW
  simpa using this

/-- `𝒱(0⁺) > λ`. -/
lemma Vf_zero_gt (hI : ExtIntegral) : pLam < 1 - pc / pSigma - 1 / (2 * pSigma ^ 2) := by
  obtain ⟨hc1, hc2⟩ := coarse_c hZ hI
  have hlam := (coarse_lam hZ).2
  have hσ : pSigma = 1 + pc := rfl
  have hσ0 : 0 < pSigma := by rw [hσ]; linarith
  suffices h : (2 : ℝ) / 5 < 1 - pc / pSigma - 1 / (2 * pSigma ^ 2) by linarith
  have : 1 - pc / pSigma - 1 / (2 * pSigma ^ 2) = (pc + 1 / 2) / pSigma ^ 2 := by
    rw [hσ]; field_simp; ring
  rw [this, lt_div_iff₀ (by positivity), hσ]
  nlinarith

/-- `𝒱(k⁻) < λ`. -/
lemma Vf_jk_lt : 1 / 4 - 1 / jk ^ 2 < pLam := by
  have hlam := (coarse_lam hZ).1
  have hk := jk_pos hZ
  have : 0 < 1 / jk ^ 2 := by positivity
  linarith

/-- `W > 0` on `(0, k)`. -/
theorem Wf_pos (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < Wf r := by
  have h := pos_of_hasDerivAt_mul_strictAnti (H := fun x => x * Wf x)
    (w := fun x => x * rhoF x * rPhi x) (φ := fun x => Vf x - pLam) (a := 0) (b := jk)
    (fun x hx => by simpa [mul_assoc] using hasDerivAt_rWf hZ hx)
    (fun x hx => mul_pos (mul_pos hx.1 (rhoF_pos hZ hx)) (radial_equations hZ x hx.1 hx.2).2.2.1)
    (fun x hx => ((hasDerivAt_Vf hZ hx).continuousAt.sub continuousAt_const).continuousWithinAt)
    (fun x hx y hy hxy => by have := Vf_strictAnti hZ hI hx hy hxy; linarith)
    ?_ ?_ (tendsto_rWf_zero hZ) (tendsto_rWf_jk hZ) r hr
  · exact pos_of_mul_pos_right h hr.1.le
  · have := (tendsto_Vf_zero hZ).sub_const pLam
    exact this.eventually (lt_mem_nhds (by linarith [Vf_zero_gt hZ hI]))
  · have := (tendsto_Vf_jk hZ).sub_const pLam
    exact this.eventually (gt_mem_nhds (by linarith [Vf_jk_lt hZ]))

/-- **The phase estimate** (proof of Proposition 6.6): `z - t g < 0` on `(0, k)`. -/
theorem phase_estimate (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rz r - rt r * rg r < 0 := by
  obtain ⟨hp, hu, -, -, hp', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have hW := Wf_pos hZ hI hr
  have hρ0 := rhoF_pos hZ hr
  have hρ2 := rhoF_sq hZ hr
  have hS := rS_pos hZ hr.1 hr.2
  have hr0 := hr.1.ne'
  have hS' : 0 < rS r := by simpa [rS] using hS
  have hid : rz r - rt r * rg r = -(rhoF r * Wf r) / (rp r * rS r) := by
    have hS'' : rp r ^ 2 + ru r * (ru r - pc - rp r / r) ≠ 0 := by
      have := hS'.ne'; simpa [rS, hdp] using this
    simp only [rz, rg, rt, Wf, Mf, rS, hdp]
    unfold R2f at hρ2
    field_simp
    simp only [hρ2]
    ring
  rw [hid]
  apply div_neg_of_neg_of_pos (by nlinarith) (mul_pos hp hS')

end

end Buckling
end
end ChunkedSource078
/- END SOURCE 078 -/

/- BEGIN SOURCE 079: RequestProject/Positivity/Quadratic.lean -/
section ChunkedSource079

/-!
# The quadratic profile estimate (Proposition 6.6 of the paper)

`g² + z² < K` on `(0, k)`.  In the radial variable, `g_r = -t z_r`, so
`(g² + z²)_r = 2 z_r (z - t g)`.  Strict convexity (Proposition 5.7: `z_r < 0`) and the
phase estimate `z - t g < 0` (from Proposition 6.5) make `g² + z²` strictly increasing,
and its limit at `r = k` is `β² = K`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

section

variable (hZ : ExtZeros)
include hZ

lemma hasDerivAt_rt' {r : ℝ} (hr : r ∈ Ioo 0 jk) : HasDerivAt rt (rT r) r := by
  have := (hasDerivAt_rt hZ r hr.1 hr.2).1
  simpa [rT, rS] using this

/-- `g = f - t z`, hence `g_r = -t z_r` (using `f_r = T z`). -/
lemma hasDerivAt_rg_of_rz {r z' : ℝ} (hr : r ∈ Ioo 0 jk) (hz : HasDerivAt rz z' r) :
    HasDerivAt rg (-(rt r) * z') r := by
  have hev : rg =ᶠ[𝓝 r] fun x => rf x - rt x * rz x := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx using rg_eq hZ hx.1 hx.2
  have h := (hasDerivAt_rf hZ hr.1 hr.2).sub ((hasDerivAt_rt' hZ hr).mul hz)
  have hid := (profile_identities_alg hZ hr.1 hr.2).2.2.1
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [hid]; ring

/-- `g² + z² → K` as `r → k⁻`. -/
lemma tendsto_energy_jk : Tendsto (fun r => rg r ^ 2 + rz r ^ 2) (𝓝[<] jk) (𝓝 pK) := by
  have hK := (parameter_signs hZ).2.2.2.2.2.2.2.2
  have h := ((tendsto_rg_jk hZ).pow 2).add ((tendsto_rz_jk hZ).pow 2)
  have : pBeta ^ 2 + (0 : ℝ) ^ 2 = pK := by
    rw [pBeta, Real.sq_sqrt hK.le]; ring
  rwa [this] at h

/-- If `z_r < 0` and `z - t g < 0` on `(0, k)`, then `g² + z² < K` there. -/
theorem quadratic_estimate_of (hconv : ∀ r ∈ Ioo 0 jk, ∃ z', HasDerivAt rz z' r ∧ z' < 0)
    (hphase : ∀ r ∈ Ioo 0 jk, rz r - rt r * rg r < 0) :
    ∀ r ∈ Ioo 0 jk, rg r ^ 2 + rz r ^ 2 < pK := by
  set E : ℝ → ℝ := fun r => rg r ^ 2 + rz r ^ 2 with hE
  have hderiv : ∀ r ∈ Ioo 0 jk, ∃ e, HasDerivAt E e r ∧ 0 < e := by
    intro r hr
    obtain ⟨z', hz, hz'⟩ := hconv r hr
    have hg := hasDerivAt_rg_of_rz hZ hr hz
    refine ⟨2 * z' * (rz r - rt r * rg r), ?_, ?_⟩
    · have := (hg.pow 2).add (hz.pow 2)
      refine this.congr_deriv ?_
      simp; ring
    · have := hphase r hr
      nlinarith
  have hmono : StrictMonoOn E (Ioo 0 jk) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro r hr
      obtain ⟨e, he, -⟩ := hderiv r hr
      exact he.continuousAt.continuousWithinAt
    · intro r hr
      rw [interior_Ioo] at hr
      obtain ⟨e, he, he'⟩ := hderiv r hr
      rw [he.deriv]; exact he'
  intro r hr
  have hlim := tendsto_energy_jk hZ
  -- `E` is bounded above on `(r, k)` by its limit, and strictly larger than `E r` there
  obtain ⟨s, hs⟩ : ∃ s, s ∈ Ioo r jk := ⟨(r + jk) / 2, by constructor <;> linarith [hr.2]⟩
  have hrs : E r < E s := hmono hr ⟨hr.1.trans hs.1, hs.2⟩ hs.1
  have hle : E s ≤ pK := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsLT hs.2] with x hx
    exact (hmono ⟨hr.1.trans hs.1, hs.2⟩ ⟨hr.1.trans (hs.1.trans hx.1), hx.2⟩ hx.1).le
  exact lt_of_lt_of_le hrs hle

end

end Buckling
end
end ChunkedSource079
/- END SOURCE 079 -/

/- BEGIN SOURCE 080: RequestProject/Positivity/Convexity.lean -/
section ChunkedSource080

/-!
# Strict convexity of the profile (Section 5 of the paper)

With `m = a₀ - r⁻²` and `Q = a₀ u - c`, the radial derivative of `g` is
`g_r = (u/S)(p m g + Q z)` (Lemma 5.4).  We show `X = p m g + Q z > 0` on `(0, k)`
(Proposition 5.7), whence `g_r > 0` and `z_r < 0`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `m = a₀ - r⁻²`. -/
noncomputable def mF (r : ℝ) : ℝ := pa0 - 1 / r ^ 2
/-- `Q = a₀ u - c`. -/
noncomputable def QF (r : ℝ) : ℝ := pa0 * ru r - pc
/-- `X = p m g + Q z`, so that `g_r = (u/S) X`. -/
noncomputable def Xf (r : ℝ) : ℝ := rp r * mF r * rg r + QF r * rz r

section
variable (hZ : ExtZeros)
include hZ

lemma deriv_rPhi_neg {r : ℝ} (hr : r ∈ Ioo 0 jk) : deriv rPhi r < 0 := by
  have hα := (parameter_signs hZ).2.2.1
  have hα1 := (parameter_signs hZ).2.2.2.1
  rw [deriv_rPhi_eq]
  have : 0 < besselJ 1 (pAlpha * r) :=
    besselJ_one_pos_of_lt_jk hZ _ (mul_pos hα hr.1) (by nlinarith [hr.2, hr.1])
  nlinarith

omit hZ in
lemma hasDerivAt_rPhi_deriv (r : ℝ) : HasDerivAt rPhi (deriv rPhi r) r :=
  (hasDerivAt_rPhi r).differentiableAt.hasDerivAt

/-- **Lemma 5.4**: `g_r = (u/S)(p m g + Q z)`. -/
theorem hasDerivAt_rg_explicit {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt rg (ru r / rS r * Xf r) r := by
  obtain ⟨hp, hu, -, hu', hp', -, hφ'', -⟩ := radial_equations hZ r hr.1 hr.2
  have hdp : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  have hS := rS_pos hZ hr.1 hr.2
  have hS' : rS r ≠ 0 := by simpa [rS] using hS.ne'
  have hr0 := hr.1.ne'
  have h := ((hp'.mul (hasDerivAt_rPhi_deriv r)).add (hu'.mul hφ'')).div (hasDerivAt_rS hZ hr) hS'
  have heq : rg = fun x => (rp x * rPhi x + ru x * deriv rPhi x) / rS x := by
    ext x; rfl
  rw [heq]
  refine h.congr_deriv ?_
  have hS'' : rp r ^ 2 + ru r * (ru r - pc - rp r / r) ≠ 0 := by simpa [rS, hdp] using hS'
  simp only [Pi.add_apply, Pi.mul_apply, Xf, mF, QF, rg, rz, rS, pa0, hdp]
  clear h heq hS hS' hp' hu' hφ'' hdp
  generalize rp r = p at *
  generalize ru r = u at *
  generalize rPhi r = φ at *
  generalize deriv rPhi r = ψ at *
  field_simp
  ring

/-- `z` is differentiable on `(0, k)`, with `z_r = -g_r / t`. -/
theorem hasDerivAt_rz_explicit {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt rz (-(ru r / rS r * Xf r) / rt r) r := by
  have ht := rt_pos hZ hr.1 hr.2
  have hev : rz =ᶠ[𝓝 r] fun x => (rf x - rg x) / rt x := by
    filter_upwards [isOpen_Ioo.mem_nhds hr] with x hx
    have := rg_eq hZ hx.1 hx.2
    have htx := rt_pos hZ hx.1 hx.2
    field_simp
    linarith
  have h := ((hasDerivAt_rf hZ hr.1 hr.2).sub (hasDerivAt_rg_explicit hZ hr)).div
    (hasDerivAt_rt' hZ hr) ht.ne'
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  have hid := (profile_identities_alg hZ hr.1 hr.2).2.2.1
  have hg := rg_eq hZ hr.1 hr.2
  rw [hid]
  simp only [Pi.sub_apply]
  rw [hg]
  field_simp
  ring

/-- **Lemma 5.2**: `z > 0` on `(0, k)`. -/
theorem rz_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < rz r := by
  have hk := jk_pos hZ
  have ha0 : 1 / jk ^ 2 < pa0 := by
    have hlam := (coarse_lam hZ).2
    have h4 := jk_lt_four hZ
    have h2 := two_lt_jk hZ
    unfold pa0
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set W : ℝ → ℝ := fun x => -(x * (rp x * deriv rPhi x - rPhi x * deriv rp x)) with hW
  have hWc : Continuous W := by
    have h1 : Continuous rp := continuous_besselJ 1
    have h2 := continuous_deriv_rPhi
    have h3 := continuous_deriv_rp
    have h4 := continuous_rPhi
    simp only [hW]; fun_prop
  have hd : ∀ x ∈ Ioo 0 jk, HasDerivAt W (x * rp x * rPhi x * (1 / x ^ 2 - pa0)) x := by
    intro x hx
    obtain ⟨hp, hu, -, hu', hp', hp'', hφ'', -⟩ := radial_equations hZ x hx.1 hx.2
    have hx0 := hx.1.ne'
    have h := ((hasDerivAt_id x).mul ((hp'.mul hφ'').sub ((hasDerivAt_rPhi_deriv x).mul hp''))).neg
    refine h.congr_deriv ?_
    simp only [Pi.sub_apply, Pi.mul_apply, id, pa0, hp'.deriv]
    field_simp
    ring
  have hpos := pos_of_hasDerivAt_mul_strictAnti (H := W) (w := fun x => x * rp x * rPhi x)
    (φ := fun x => 1 / x ^ 2 - pa0) (a := 0) (b := jk) hd
    (fun x hx => by
      obtain ⟨hp, -, hφ, -⟩ := radial_equations hZ x hx.1 hx.2
      exact mul_pos (mul_pos hx.1 hp) hφ)
    (fun x hx => ((continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hx.1.ne')).sub continuousAt_const).continuousWithinAt)
    (fun x hx y hy hxy => by
      have : 1 / y ^ 2 < 1 / x ^ 2 := one_div_lt_one_div_of_lt (pow_pos hx.1 2) (by gcongr; exact hx.1.le)
      linarith) ?_ ?_ ?_ ?_ r hr
  · obtain ⟨hp, hu, -, -, hp', -⟩ := radial_equations hZ r hr.1 hr.2
    have hS := rS_pos hZ hr.1 hr.2
    have hS' : 0 < rS r := by simpa [rS] using hS
    have : rp r * deriv rPhi r - rPhi r * deriv rp r < 0 := by
      simp only [hW] at hpos
      nlinarith [hr.1]
    unfold rz
    apply div_pos _ hS'
    linarith
  · have h : Tendsto (fun x : ℝ => 1 / x ^ 2) (𝓝[>] 0) atTop := by
      have h2 : Tendsto (fun x : ℝ => x ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have := ((continuous_pow 2).tendsto (0:ℝ))
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with x hx
          exact Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp hx) 2)
      have hi := h2.inv_tendsto_nhdsGT_zero
      have hfun : (fun x : ℝ => x ^ 2)⁻¹ = (fun x : ℝ => (x ^ 2)⁻¹) := by
        funext x
        simp only [Pi.inv_apply]
      rw [hfun] at hi
      simpa only [one_div] using! hi
    filter_upwards [h.eventually (eventually_gt_atTop (pa0))] with x hx
    linarith
  · have h : Tendsto (fun x : ℝ => 1 / x ^ 2 - pa0) (𝓝[<] jk) (𝓝 (1 / jk ^ 2 - pa0)) :=
      ((continuousAt_const.div (continuousAt_id.pow 2) (pow_ne_zero 2 hk.ne')).sub
        continuousAt_const).tendsto.mono_left nhdsWithin_le_nhds
    exact h.eventually (gt_mem_nhds (by linarith))
  · have := hWc.continuousAt (x := 0) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa [hW] using this
  · have := hWc.continuousAt (x := jk) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio jk))
    simpa [hW, rp_jk hZ, rPhi_jk hZ] using this

/-- **Lemma 5.3**: `g > 0` on `(0, k)`. -/
theorem rg_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < rg r := by
  have hk := jk_pos hZ
  have ha0 : 0 < pa0 := by have := (coarse_lam hZ).2; unfold pa0; linarith
  -- `K = r(pψ' - ψp')` with `ψ = -φ'`
  set K : ℝ → ℝ := fun x => rp x * deriv rPhi x + pLam * x * rp x * rPhi x +
    x * deriv rPhi x * deriv rp x with hK
  have hKc : Continuous K := by
    have h1 : Continuous rp := continuous_besselJ 1
    have h2 := continuous_deriv_rPhi
    have h3 := continuous_deriv_rp
    have h4 := continuous_rPhi
    simp only [hK]; fun_prop
  have hKd : ∀ x ∈ Ioo 0 jk, HasDerivAt K (-pa0 * x * rp x * deriv rPhi x) x := by
    intro x hx
    obtain ⟨hp, hu, -, hu', hp', hp'', hφ'', -⟩ := radial_equations hZ x hx.1 hx.2
    have hx0 := hx.1.ne'
    have h := ((hp'.mul hφ'').add ((((hasDerivAt_id x).const_mul pLam).mul hp').mul
      (hasDerivAt_rPhi_deriv x))).add (((hasDerivAt_id x).mul hφ'').mul hp'')
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, id, pa0, hp'.deriv]
    field_simp
    ring
  have hKpos : ∀ x ∈ Ioo 0 jk, 0 < K x := by
    intro x hx
    have hmono : StrictMonoOn K (Icc 0 x) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hKc.continuousOn
      intro y hy
      rw [interior_Icc] at hy
      have hy' : y ∈ Ioo 0 jk := ⟨hy.1, hy.2.trans hx.2⟩
      rw [(hKd y hy').deriv]
      have := deriv_rPhi_neg hZ hy'
      have hp := (radial_equations hZ y hy'.1 hy'.2).1
      have : 0 < pa0 * y * rp y := by have := hy'.1; positivity
      nlinarith
    have := hmono ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1
    have hK0 : K 0 = 0 := by simp [hK, rp, besselJ_zero_arg]
    linarith
  -- `h = ψ/p` is strictly increasing
  set hf : ℝ → ℝ := fun x => -deriv rPhi x / rp x with hhf
  have hhd : ∀ x ∈ Ioo 0 jk, HasDerivAt hf (K x / (x * rp x ^ 2)) x := by
    intro x hx
    obtain ⟨hp, hu, -, hu', hp', hp'', hφ'', -⟩ := radial_equations hZ x hx.1 hx.2
    have hx0 := hx.1.ne'
    have h := hφ''.neg.div hp' hp.ne'
    refine h.congr_deriv ?_
    simp only [hK, Pi.neg_apply, hp'.deriv]
    field_simp
    ring
  have hhmono : StrictMonoOn hf (Ioo 0 jk) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro x hx; exact (hhd x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hhd x hx).deriv]
      have := hKpos x hx
      have hp := (radial_equations hZ x hx.1 hx.2).1
      have := hx.1
      positivity
  -- `F(s) = p(r) φ(s) - ψ(r) u(s)` is decreasing on `[r, k]` and vanishes at `k`
  obtain ⟨hp, hu, -, -, hp', -⟩ := radial_equations hZ r hr.1 hr.2
  set F : ℝ → ℝ := fun s => rp r * rPhi s + deriv rPhi r * ru s with hF
  have hFc : Continuous F := by
    have := continuous_rPhi
    have h2 : Continuous ru := (continuous_besselJ 0).add continuous_const
    simp only [hF]; fun_prop
  have hFanti : StrictAntiOn F (Icc r jk) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hFc.continuousOn
    intro s hs
    rw [interior_Icc] at hs
    have hs' : s ∈ Ioo 0 jk := ⟨hr.1.trans hs.1, hs.2⟩
    obtain ⟨hps, -, -, hus, -⟩ := radial_equations hZ s hs'.1 hs'.2
    have hd : HasDerivAt F (rp r * deriv rPhi s + deriv rPhi r * (-rp s)) s :=
      ((hasDerivAt_rPhi_deriv s).const_mul (rp r)).add (hus.const_mul (deriv rPhi r))
    rw [hd.deriv]
    have hlt := hhmono hr hs' hs.1
    simp only [hhf] at hlt
    rw [div_lt_div_iff₀ hp hps] at hlt
    linarith
  have hFk : F jk = 0 := by simp [hF, rPhi_jk hZ, ru_jk]
  have hFr := hFanti ⟨le_rfl, hr.2.le⟩ ⟨hr.2.le, le_rfl⟩ hr.2
  rw [hFk] at hFr
  have hS := rS_pos hZ hr.1 hr.2
  have hS' : 0 < rS r := by simpa [rS] using hS
  unfold rg
  apply div_pos _ hS'
  simp only [hF] at hFr
  linarith

end

end Buckling
end
end ChunkedSource080
/- END SOURCE 080 -/

/- BEGIN SOURCE 081: RequestProject/Positivity/ConvexityX.lean -/
section ChunkedSource081

/-!
# Positivity of `X = p m g + Q z` (Lemmas 5.5, 5.6 and Proposition 5.7 of the paper)
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `D = (pm)' Q - Q' p m`, so that `(pm/Q)' = D/Q²`. -/
noncomputable def Dfun (r : ℝ) : ℝ :=
  (deriv rp r * mF r + 2 * rp r / r ^ 3) * QF r + pa0 * rp r ^ 2 * mF r

lemma hasDerivAt_mF {r : ℝ} (hr : r ≠ 0) : HasDerivAt mF (2 / r ^ 3) r := by
  have h := ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr)).const_sub pa0
  have heq : mF = fun x => pa0 - (x ^ 2)⁻¹ := by ext x; simp [mF]
  rw [heq]
  refine h.congr_deriv ?_
  field_simp
  ring

lemma hasDerivAt_QF (r : ℝ) : HasDerivAt QF (-pa0 * rp r) r := by
  have h := ((hasDerivAt_ru r).const_mul pa0).sub_const pc
  have heq : QF = fun x => pa0 * ru x - pc := rfl
  rw [heq]
  refine h.congr_deriv ?_
  ring

lemma D_left_alg {r p p' Q a0 Q0 : ℝ} (hr : 0 < r) (hp : 0 < p) (hp2 : p ≤ r / 2)
    (hp' : p' ≤ p / r) (ha0 : 0 < a0) (hx : a0 * r ^ 2 < 1) (hQ : Q0 - a0 * r ^ 2 / 4 ≤ Q)
    (hQ0 : 2 / 5 < Q0) :
    0 < (p' * (a0 - 1 / r ^ 2) + 2 * p / r ^ 3) * Q + a0 * p ^ 2 * (a0 - 1 / r ^ 2) := by
  set x := a0 * r ^ 2 with hxdef
  have hx0 : 0 < x := by positivity
  have hm : a0 - 1 / r ^ 2 = (x - 1) / r ^ 2 := by rw [hxdef]; field_simp
  have hmn : a0 - 1 / r ^ 2 < 0 := by rw [hm]; exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  have hQp : 0 < Q := by linarith
  have h1 : (p / r) * (a0 - 1 / r ^ 2) * Q ≤ p' * (a0 - 1 / r ^ 2) * Q := by
    have := mul_nonneg (sub_nonneg.mpr hp') (mul_nonneg (neg_nonneg.mpr hmn.le) hQp.le)
    nlinarith
  have h2 : a0 * p * (r / 2) * (a0 - 1 / r ^ 2) ≤ a0 * p ^ 2 * (a0 - 1 / r ^ 2) := by
    have := mul_nonneg (sub_nonneg.mpr hp2) (mul_nonneg (mul_nonneg ha0.le hp.le) (neg_nonneg.mpr hmn.le))
    nlinarith
  have h3 : (p / r) * (a0 - 1 / r ^ 2) * Q + 2 * p / r ^ 3 * Q + a0 * p * (r / 2) * (a0 - 1 / r ^ 2)
      = p / r ^ 3 * ((x + 1) * Q + x * (x - 1) / 2) := by
    rw [hm, hxdef]; field_simp; ring
  have h4 : 0 < (x + 1) * Q + x * (x - 1) / 2 := by nlinarith
  have h5 : 0 < p / r ^ 3 * ((x + 1) * Q + x * (x - 1) / 2) := by positivity
  nlinarith
lemma D_right_alg {r p p' W a0 mm A E l : ℝ} (hr : 0 < r) (hp : 0 < p) (hA : p' = -A * p)
    (hA0 : 0 < A) (ha0 : 0 < a0) (hW0 : 0 < W) (hW : W * A < a0 * p * (E - 1)) (hE : E * (1 - A * l) < 1)
    (hl : 0 < l) (hcub : 2 * l < mm * r ^ 3) :
    0 < (p' * mm + 2 * p / r ^ 3) * (-W) + a0 * p ^ 2 * mm := by
  have hWA : 0 < W * A := mul_pos hW0 hA0
  have hE1 : 1 < E := by
    have := pos_of_mul_pos_right (hWA.trans hW) (mul_pos ha0 hp).le
    linarith
  have k0 : A * W * E < (A * W + a0 * p) * (E - 1) := by nlinarith
  have k0' : W * (E - 1) < A * W * E * l := by nlinarith
  have k1 : W < (A * W + a0 * p) * l := by
    have : W * (E - 1) < (A * W + a0 * p) * l * (E - 1) := by nlinarith
    nlinarith
  have hS : 0 < A * W + a0 * p := by
    by_contra h; push_neg at h; nlinarith
  have k2 : 2 * W < mm * r ^ 3 * (A * W + a0 * p) := by nlinarith
  have key : (p' * mm + 2 * p / r ^ 3) * (-W) + a0 * p ^ 2 * mm
      = p / r ^ 3 * (mm * r ^ 3 * (A * W + a0 * p) - 2 * W) := by
    rw [hA]; field_simp; ring
  rw [key]
  apply mul_pos (by positivity); linarith

section
variable (hZ : ExtZeros)
include hZ

lemma hasDerivAt_Xf {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt Xf ((deriv rp r * mF r + rp r * (2 / r ^ 3)) * rg r +
      rp r * mF r * (ru r / rS r * Xf r) + (-pa0 * rp r) * rz r +
      QF r * (-(ru r / rS r * Xf r) / rt r)) r := by
  have hp' := (radial_equations hZ r hr.1 hr.2).2.2.2.2.1
  have hp : HasDerivAt rp (deriv rp r) r := hp'.differentiableAt.hasDerivAt
  have h := ((hp.mul (hasDerivAt_mF hr.1.ne')).mul (hasDerivAt_rg_explicit hZ hr)).add
    ((hasDerivAt_QF r).mul (hasDerivAt_rz_explicit hZ hr))
  refine HasDerivAt.congr_deriv (f := Xf) h ?_
  simp only [Pi.mul_apply]
  ring

lemma deriv_Xf_mul_QF {r : ℝ} (hr : r ∈ Ioo 0 jk) (hX : Xf r = 0) :
    deriv Xf r * QF r = rg r * Dfun r := by
  rw [(hasDerivAt_Xf hZ hr).deriv, hX]
  have hX' : QF r * rz r = -(rp r * mF r * rg r) := by
    unfold Xf at hX; linarith
  simp only [Dfun, mul_zero, zero_div, neg_zero, add_zero]
  linear_combination (-pa0 * rp r) * hX'

lemma pa0_gt : 3 / 5 < pa0 := by have := (coarse_lam hZ).2; unfold pa0; linarith

/-- **Lemma 5.5, first range**: on `(0, r₀)` (where `a₀ r² < 1`), `Q > 0` and `D > 0`. -/
lemma Dfun_pos_left (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) (hx : pa0 * r ^ 2 < 1) :
    0 < Dfun r ∧ 0 < QF r := by
  have ha := pa0_gt hZ
  have hlam := coarse_lam hZ
  obtain ⟨-, hc2⟩ := coarse_c hZ hI
  have hc0 := pc_pos hZ
  have hr2 : r ^ 2 < 5 / 3 := by nlinarith
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hp2 : rp r < r / 2 := besselJ_one_lt_small r hr.1 (by linarith)
  have hJ2 := besselJ_two_pos_small r hr.1 (by nlinarith)
  rw [besselJ_two_eq_rp hr.1.ne'] at hJ2
  have hJ0 := besselJ_zero_gt_small r hr.1 (by linarith)
  have hQ0 : 2 / 5 < pa0 * (1 + pc) - pc := by unfold pa0; nlinarith
  have hQ : pa0 * (1 + pc) - pc - pa0 * r ^ 2 / 4 ≤ QF r := by
    unfold QF ru; nlinarith
  refine ⟨D_left_alg hr.1 hp hp2.le (by linarith) (by linarith) hx hQ hQ0, ?_⟩
  nlinarith

/-- Tangent-line bound for the concave function `log p`, tangency at the right point. -/
lemma rp_lt_tangent_left {r s : ℝ} (hs : Real.sqrt 5 / 2 < s) (hsr : s < r) (hrk : r < jk) :
    rp s < rp r * Real.exp (deriv rp r / rp r * (s - r)) := by
  have h52 : 0 < Real.sqrt 5 / 2 := by positivity
  have hs0 : 0 < s := h52.trans hs
  have hpos : ∀ x ∈ Icc s r, 0 < rp x := fun x hx =>
    (radial_equations hZ x (hs0.trans_le hx.1) (hx.2.trans_lt hrk)).1
  have hcont : ContinuousOn (fun x => Real.log (rp x)) (Icc s r) :=
    fun x hx => ((continuous_besselJ 1).continuousAt.log (hpos x hx).ne').continuousWithinAt
  have hdiff : ∀ x ∈ Ioo s r, HasDerivAt (fun x => Real.log (rp x)) (deriv rp x / rp x) x := by
    intro x hx
    have hx0 : 0 < x := hs0.trans hx.1
    have hp' := (radial_equations hZ x hx0 (hx.2.trans hrk)).2.2.2.2.1
    have := hp'.log (hpos x ⟨hx.1.le, hx.2.le⟩).ne'
    rwa [← hp'.deriv] at this
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun x => Real.log (rp x))
    (fun x => deriv rp x / rp x) hsr hcont hdiff
  have hlt : deriv rp r / rp r < deriv rp ξ / rp ξ :=
    logderiv_rp_strictAnti hZ ⟨hs.trans hξ.1, hξ.2.trans hrk⟩ ⟨hs.trans hsr, hrk⟩ hξ.2
  have hlog : Real.log (rp s) - Real.log (rp r) < deriv rp r / rp r * (s - r) := by
    rw [hξeq] at hlt
    rw [lt_div_iff₀ (sub_pos.mpr hsr)] at hlt
    linarith
  have hps := hpos s ⟨le_rfl, hsr.le⟩
  have hpr := hpos r ⟨hsr.le, le_rfl⟩
  calc rp s = Real.exp (Real.log (rp s)) := (Real.exp_log hps).symm
    _ < Real.exp (Real.log (rp r) + deriv rp r / rp r * (s - r)) := by
        apply Real.exp_lt_exp.mpr; linarith
    _ = rp r * Real.exp (deriv rp r / rp r * (s - r)) := by
        rw [Real.exp_add, Real.exp_log hpr]

omit hZ in
lemma QF_sub_eq (a b : ℝ) : QF b - QF a = -pa0 * ∫ s in a..b, rp s := by
  have hcont : Continuous rp := continuous_besselJ 1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) (f := ru)
    (f' := fun s => -rp s) (fun s _ => hasDerivAt_ru s) (hcont.neg.intervalIntegrable _ _)
  rw [intervalIntegral.integral_neg] at this
  simp only [QF]
  linear_combination (-pa0) * this

lemma logderiv_rp_neg {r : ℝ} (hr : 19 / 10 < r) (hrk : r < jk) : deriv rp r / rp r < 0 := by
  have h5 : Real.sqrt 5 / 2 < 19 / 10 := by
    rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  obtain ⟨-, h1, h2, -, -⟩ := small_bessel_bounds
  have hp19 := (radial_equations hZ (19 / 10) (by norm_num) ((hr.trans hrk))).1
  have hd19 : deriv rp (19 / 10) < 0 := by
    rw [deriv_rp_eq _ (by norm_num)]; linarith
  have hL19 : deriv rp (19 / 10) / rp (19 / 10) < 0 := div_neg_of_neg_of_pos hd19 hp19
  have := logderiv_rp_strictAnti hZ ⟨h5, hr.trans hrk⟩ ⟨h5.trans hr, hrk⟩ hr
  linarith

/-- **Lemma 5.5, second range**: if `Q(r_Q) = 0` with `19/10 < r_Q < k`, then on `(r_Q, k)`,
`Q < 0` and `D > 0`. -/
lemma Dfun_pos_right {rQ : ℝ} (hrQ : 19 / 10 < rQ) (hQ : QF rQ = 0) {r : ℝ}
    (hr : r ∈ Ioo rQ jk) : 0 < Dfun r ∧ QF r < 0 := by
  have ha := pa0_gt hZ
  have h5 : Real.sqrt 5 / 2 < 19 / 10 := by
    rw [div_lt_iff₀ (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  have hr0 : 0 < r := by linarith [hr.1]
  have hp := (radial_equations hZ r hr0 hr.2).1
  have hcont : Continuous rp := continuous_besselJ 1
  set W := -QF r with hWdef
  set L := deriv rp r / rp r with hLdef
  set A := -L with hAdef
  set l := r - rQ with hldef
  have hl : 0 < l := by linarith [hr.1]
  have hA0 : 0 < A := by have := logderiv_rp_neg hZ (hrQ.trans hr.1) hr.2; linarith
  have hWint : W = pa0 * ∫ s in rQ..r, rp s := by
    have := QF_sub_eq rQ r; rw [hQ] at this; rw [hWdef]; linarith
  have hint_pos : 0 < ∫ s in rQ..r, rp s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) _ hr.1
    intro s hs
    exact (radial_equations hZ s (by linarith [hs.1]) (hs.2.trans hr.2)).1
  have hW0 : 0 < W := by rw [hWint]; positivity
  -- the tangent-line integral bound
  have hlt : ∫ s in rQ..r, rp s < ∫ s in rQ..r, rp r * Real.exp (L * (s - r)) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hr.1
      hcont.continuousOn (by fun_prop)
    · intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h, sub_self, mul_zero, Real.exp_zero, mul_one]
      · exact (rp_lt_tangent_left hZ (h5.trans (hrQ.trans hs.1)) h hr.2).le
    · refine ⟨(rQ + r) / 2, ⟨by linarith [hr.1], by linarith [hr.1]⟩, ?_⟩
      exact rp_lt_tangent_left hZ (h5.trans (by linarith [hr.1])) (by linarith [hr.1]) hr.2
  have hexp : ∫ s in rQ..r, Real.exp (L * (s - r)) = (Real.exp (A * l) - 1) / A := by
    rw [intervalIntegral.integral_symm, integral_exp_tangent L r rQ (by linarith)]
    rw [hAdef, hldef]
    field_simp
    ring_nf
  rw [intervalIntegral.integral_const_mul, hexp] at hlt
  have hW : W * A < pa0 * rp r * (Real.exp (A * l) - 1) := by
    rw [hWint]
    have : (∫ s in rQ..r, rp s) * A < rp r * (Real.exp (A * l) - 1) := by
      rw [mul_div_assoc'] at hlt
      rwa [lt_div_iff₀ hA0] at hlt
    nlinarith
  have hE : Real.exp (A * l) * (1 - A * l) < 1 := by
    have h1 := Real.add_one_lt_exp (x := -(A * l)) (by have := mul_pos hA0 hl; linarith)
    have h2 : Real.exp (A * l) * Real.exp (-(A * l)) = 1 := by
      rw [← Real.exp_add]; simp
    have h3 := Real.exp_pos (A * l)
    nlinarith
  have hrQ2 : 1 < pa0 * rQ ^ 2 := by nlinarith
  have hcub : 2 * l < mF r * r ^ 3 := by
    have : mF r * r ^ 3 = pa0 * r ^ 3 - r := by unfold mF; field_simp
    rw [this, hldef]
    have h1 : 1 < pa0 * r ^ 2 := by nlinarith [hr.1]
    have h2 : 1 < pa0 * (r * rQ) := by nlinarith [hr.1]
    nlinarith [mul_pos hl (show 0 < pa0 * (r ^ 2 + r * rQ + rQ ^ 2) - 3 by nlinarith)]
  refine ⟨?_, by linarith⟩
  have hD := D_right_alg (p' := deriv rp r) hr0 hp (by rw [hAdef, hLdef]; field_simp)
    hA0 (by linarith) hW0 hW hE hl hcub
  unfold Dfun
  rw [show QF r = -W by rw [hWdef]; ring]
  exact hD

attribute [local fun_prop] continuous_besselG continuous_Sy

/-- Near `0`, `X → Q₀/(2σ) > 0`. -/
lemma Xf_pos_near_zero (hI : ExtIntegral) : ∀ᶠ r in 𝓝[>] 0, 0 < Xf r := by
  have hS := Sy_sq_ne_zero hZ
  have hσ := pSigma_pos hZ
  have hlam := coarse_lam hZ
  obtain ⟨-, hc2⟩ := coarse_c hZ hI
  set E : ℝ → ℝ := fun r => besselG 1 (r ^ 2) * (pa0 * r ^ 2 - 1) *
    (besselG 1 (r ^ 2) * besselG 0 (pLam * r ^ 2) -
      pLam * (besselG 0 (r ^ 2) + pc) * besselG 1 (pLam * r ^ 2)) / (4 * Sy (r ^ 2)) with hE
  have h1 : Tendsto (fun r => rp r * mF r * rg r) (𝓝[>] 0) (𝓝 (E 0)) := by
    apply tendsto_zero_of_eqOn hZ
    · intro r hr
      have hr0 := hr.1.ne'
      have hSr : Sy (r ^ 2) ≠ 0 := by
        rw [← rS_eq_G hr0]; exact (rS_pos hZ hr.1 hr.2).ne'
      rw [rg_eq_G hr, rp_eq_G, hE]
      simp only [mF]
      field_simp
      ring
    · exact ContinuousAt.div (by fun_prop) (by fun_prop) (mul_ne_zero four_ne_zero hS)
  have hQc : Continuous QF := by
    have : Continuous ru := (continuous_besselJ 0).add continuous_const
    unfold QF; fun_prop
  have h2 := (hQc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds |>.mul
    (tendsto_rz_origin hZ)
  have h := h1.add h2
  have hval : E 0 + QF 0 * pEll = (1 - pLam * pSigma) / (2 * pSigma) := by
    simp only [hE, QF, ru, pEll, besselJ_zero_arg]
    simp [besselG0_zero, besselG1_zero, Sy_zero, pa0, pSigma]
    field_simp
    ring
  rw [hval] at h
  have hpos : 0 < (1 - pLam * pSigma) / (2 * pSigma) := by
    apply div_pos _ (by positivity)
    unfold pSigma; nlinarith
  exact h.eventually (lt_mem_nhds hpos)

/-- Near `k`, `X/(k - r) → (a₀ - k⁻²) α J₁(q)/3 > 0`. -/
lemma Xf_pos_near_jk : ∀ᶠ r in 𝓝[<] jk, 0 < Xf r := by
  have hk := jk_pos hZ
  have hc := pc_pos hZ
  have hα := (parameter_signs hZ).2.2.1
  have hj := jJ_pos hZ
  have hmk : 1 / jk ^ 2 < pa0 := by
    have hlam := (coarse_lam hZ).2
    have h2 := two_lt_jk hZ
    unfold pa0
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hmc : ContinuousAt mF jk := by
    unfold mF
    exact continuousAt_const.sub (continuousAt_const.div (continuousAt_id.pow 2)
      (pow_ne_zero 2 hk.ne'))
  have hQc : Continuous QF := by
    have : Continuous ru := (continuous_besselJ 0).add continuous_const
    unfold QF; fun_prop
  have h := (((tendsto_rp_div hZ).mul (hmc.tendsto.mono_left nhdsWithin_le_nhds)).mul
    (tendsto_rg_jk hZ)).add (((hQc.continuousAt (x := jk)).tendsto.mono_left
      nhdsWithin_le_nhds).mul (tendsto_rz_div hZ))
  have hval : pc * mF jk * pBeta + QF jk * zc = (pa0 - 1 / jk ^ 2) * (pAlpha * jJ) / 3 := by
    rw [pBeta_eq hZ]
    simp only [mF, QF, ru_jk, zc, n3, pa0]
    field_simp
    ring
  rw [hval] at h
  have hpos : 0 < (pa0 - 1 / jk ^ 2) * (pAlpha * jJ) / 3 := by
    have : 0 < pa0 - 1 / jk ^ 2 := by linarith
    positivity
  filter_upwards [h.eventually (lt_mem_nhds hpos), eventually_Ioo_jk hZ] with r hr hr'
  have hd : 0 < (jk - r) ^ 1 := by simpa using hr'.2
  have := mul_pos hr hd
  have hd0 : jk - r ≠ 0 := by simpa using hd.ne'
  have e : (rp r / (jk - r) ^ 1 * mF r * rg r + QF r * (rz r / (jk - r) ^ 1)) * (jk - r) ^ 1
      = Xf r := by
    unfold Xf; field_simp
  linarith

lemma QF_strictAntiOn : StrictAntiOn QF (Icc 0 jk) := by
  intro a ha b hb hab
  have h := QF_sub_eq a b
  have hcont : Continuous rp := continuous_besselJ 1
  have hpos : 0 < ∫ s in a..b, rp s := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _) _ hab
    intro s hs
    exact (radial_equations hZ s (ha.1.trans_lt hs.1) (hs.2.trans_le hb.2)).1
  have := pa0_gt hZ
  nlinarith

/-- The unique zero `r_Q ∈ (19/10, k)` of `Q` (Lemma 5.5). -/
lemma exists_rQ (hI : ExtIntegral) : ∃ rQ, 19 / 10 < rQ ∧ rQ < jk ∧ QF rQ = 0 := by
  have ha := pa0_gt hZ
  have hlam := coarse_lam hZ
  obtain ⟨-, hc2⟩ := coarse_c hZ hI
  have hc := pc_pos hZ
  obtain ⟨h1, -⟩ := small_bessel_bounds
  have hQ19 : 0 < QF (19 / 10) := by
    unfold QF ru
    have : pa0 - 1 = -pLam := by unfold pa0; ring
    nlinarith
  have hQk : QF jk < 0 := by simp [QF, ru_jk]; linarith
  have hQc : Continuous QF := by
    have : Continuous ru := (continuous_besselJ 0).add continuous_const
    unfold QF; fun_prop
  obtain ⟨rQ, hrQ, h⟩ := intermediate_value_Ioo' (by linarith [two_lt_jk hZ])
    hQc.continuousOn ⟨hQk, hQ19⟩
  exact ⟨rQ, hrQ.1, hrQ.2, h⟩

/-- **Proposition 5.7 (core)**: `X = p m g + Q z > 0` on `(0, k)`. -/
theorem Xf_pos (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < Xf r := by
  obtain ⟨rQ, hrQ1, hrQ2, hQ⟩ := exists_rQ hZ hI
  have ha := pa0_gt hZ
  have hk2 := two_lt_jk hZ
  set r0 := Real.sqrt (1 / pa0) with hr0def
  have hr0 : 0 < r0 := Real.sqrt_pos.mpr (by positivity)
  have hr0sq : pa0 * r0 ^ 2 = 1 := by
    rw [hr0def, Real.sq_sqrt (by positivity)]; field_simp
  have hr0lt : r0 < 19 / 10 := by nlinarith
  have hdiff : ∀ a b, 0 ≤ a → b ≤ jk → DifferentiableOn ℝ Xf (Ioo a b) := by
    intro a b ha0 hb x hx
    exact (hasDerivAt_Xf hZ ⟨ha0.trans_lt hx.1, hx.2.trans_le hb⟩).differentiableAt
      |>.differentiableWithinAt
  rcases lt_or_ge r r0 with h1 | h1
  · -- first range: oriented zeros from the left
    refine pos_of_oriented_zeros (hdiff 0 r0 le_rfl (by linarith)) (Xf_pos_near_zero hZ hI)
      ?_ r ⟨hr.1, h1⟩
    intro x hx hX
    have hx' : x ∈ Ioo 0 jk := ⟨hx.1, by linarith [hx.2]⟩
    have hx2 : pa0 * x ^ 2 < 1 := by
      rw [← hr0sq]; have := hx.1; gcongr; exact hx.2
    obtain ⟨hD, hQp⟩ := Dfun_pos_left hZ hI hx' hx2
    have h := deriv_Xf_mul_QF hZ hx' hX
    have hg := rg_pos hZ hx'
    have : 0 < deriv Xf x * QF x := by rw [h]; positivity
    exact pos_of_mul_pos_left this hQp.le
  rcases le_or_gt r rQ with h2 | h2
  · -- middle range: both terms nonnegative
    have hp := (radial_equations hZ r hr.1 hr.2).1
    have hg := rg_pos hZ hr
    have hz := rz_pos hZ hr
    have hm : 0 ≤ mF r := by
      unfold mF
      have : 1 ≤ pa0 * r ^ 2 := by rw [← hr0sq]; gcongr
      rw [sub_nonneg, div_le_iff₀ (pow_pos hr.1 2)]; linarith
    rcases lt_or_eq_of_le h2 with h3 | h3
    · have hQp : 0 < QF r := by
        rw [← hQ]
        exact QF_strictAntiOn hZ ⟨hr.1.le, hr.2.le⟩ ⟨by linarith, hrQ2.le⟩ h3
      unfold Xf
      have := mul_nonneg (mul_nonneg hp.le hm) hg.le
      have := mul_pos hQp hz
      linarith
    · have hm' : 0 < mF r := by
        unfold mF
        have : 1 < pa0 * r ^ 2 := by rw [h3]; nlinarith
        rw [sub_pos, div_lt_iff₀ (pow_pos hr.1 2)]; linarith
      unfold Xf
      rw [h3] at hp hg hm' ⊢
      rw [hQ, zero_mul, add_zero]
      positivity
  · -- last range: oriented zeros from the right
    refine pos_of_oriented_zeros' (hdiff rQ jk (by linarith) le_rfl) (Xf_pos_near_jk hZ)
      ?_ r ⟨h2, hr.2⟩
    intro x hx hX
    have hx' : x ∈ Ioo 0 jk := ⟨by linarith [hx.1], hx.2⟩
    obtain ⟨hD, hQn⟩ := Dfun_pos_right hZ hrQ1 hQ hx
    have h := deriv_Xf_mul_QF hZ hx' hX
    have hg := rg_pos hZ hx'
    have : 0 < deriv Xf x * QF x := by rw [h]; positivity
    by_contra hc
    push_neg at hc
    nlinarith

/-- **Proposition 5.7**: `z_r < 0` on `(0, k)` (equivalently `g_r > 0`, `f_tt > 0`). -/
theorem rz_hasDerivAt_neg (hI : ExtIntegral) :
    ∀ r ∈ Ioo 0 jk, ∃ z', HasDerivAt rz z' r ∧ z' < 0 := by
  intro r hr
  refine ⟨_, hasDerivAt_rz_explicit hZ hr, ?_⟩
  have hu := (radial_equations hZ r hr.1 hr.2).2.1
  have hS : 0 < rS r := by simpa [rS] using rS_pos hZ hr.1 hr.2
  have ht := rt_pos hZ hr.1 hr.2
  have hX := Xf_pos hZ hI hr
  have : 0 < ru r / rS r * Xf r := mul_pos (div_pos hu hS) hX
  exact div_neg_of_neg_of_pos (by linarith) ht

/-- **Proposition 5.7**: `g_r > 0` on `(0, k)`. -/
theorem rg_hasDerivAt_pos (hI : ExtIntegral) :
    ∀ r ∈ Ioo 0 jk, ∃ g', HasDerivAt rg g' r ∧ 0 < g' := by
  intro r hr
  refine ⟨_, hasDerivAt_rg_explicit hZ hr, ?_⟩
  have hu := (radial_equations hZ r hr.1 hr.2).2.1
  have hS : 0 < rS r := by simpa [rS] using rS_pos hZ hr.1 hr.2
  have hX := Xf_pos hZ hI hr
  exact mul_pos (div_pos hu hS) hX

end

end Buckling
end
end ChunkedSource081
/- END SOURCE 081 -/

/- BEGIN SOURCE 082: RequestProject/Positivity/Chord.lean -/
section ChunkedSource082

/-!
# The chord inequality for `J₀` (Lemmas 7.4–7.6 of the paper)

`J₀(r) > 1 - r/q` on `(0, q)`; hence `φ(r) > (k - r)/k` on `(0, k)`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

lemma besselJ_zero_gt_S3 (r : ℝ) (hr0 : 0 < r) (hr : r < 10) :
    1 - r ^ 2 / 4 + r ^ 4 / 64 - r ^ 6 / 2304 < besselJ 0 r := by
  have h := besselJ_tail_general 0 3 r hr0 (by push_cast; nlinarith)
  simp [besselPartialR, Finset.sum_range_succ, Nat.factorial] at h
  nlinarith [h]

section
variable (hZ : ExtZeros)
include hZ

/-- **Lemma 7.5**: `q J₁(q) > 1`. -/
lemma jq_mul_J1q (hI : ExtIntegral) : 1 < jq * besselJ 1 jq := by
  obtain ⟨hq1, -⟩ := root_boxes hZ
  have := coarse_J1q hZ hI
  nlinarith

lemma besselJ_zero_jq : besselJ 0 jq = 0 := ((hZ 0 (by norm_num)).2.2.1 1 le_rfl).1

lemma jq_lt_jk : jq < jk := by
  obtain ⟨-, hq2, hk1, -⟩ := root_boxes hZ
  linarith

lemma deriv_rp_neg_of_gt {r : ℝ} (hr : 19 / 10 < r) (hrk : r < jk) : deriv rp r < 0 := by
  have h := logderiv_rp_neg hZ hr hrk
  have hp := (radial_equations hZ r (by linarith) hrk).1
  rw [div_neg_iff, or_iff_right (by intro h'; linarith [h'.2])] at h
  exact h.1

/-- **Lemma 7.6 (chord inequality)**: `J₀(r) > 1 - r/q` for `0 < r < q`. -/
theorem besselJ_zero_gt_chord (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jq) :
    1 - r / jq < besselJ 0 r := by
  obtain ⟨hq1, hq2, -⟩ := root_boxes hZ
  have hq0 : 0 < jq := by linarith
  rcases le_or_gt r (19 / 10) with h | h
  · have hS := besselJ_zero_gt_S3 r hr.1 (by linarith)
    have hinv : 41582 / 100000 < 1 / jq := by
      rw [lt_div_iff₀ hq0]; nlinarith
    have hr0 := hr.1
    have key : 0 < 41582 / 100000 - r / 4 + r ^ 3 / 64 - r ^ 5 / 2304 := by
      have h1 : 0 ≤ 19 / 10 - r := by linarith
      have hr2 : r ^ 2 ≤ 361 / 100 := by nlinarith
      nlinarith [mul_nonneg h1 (sq_nonneg r), mul_nonneg h1 hr0.le,
        mul_nonneg (mul_nonneg h1 hr0.le) (sq_nonneg r), pow_pos hr0 3, pow_pos hr0 4,
        mul_nonneg (pow_pos hr0 3).le h1]
    have : r / jq = r * (1 / jq) := by ring
    rw [this]
    nlinarith
  · -- mean value theorem on `[r, q]`, with `J₁` decreasing there
    have hk := jq_lt_jk hZ
    have hanti : StrictAntiOn (besselJ 1) (Icc (19 / 10) jq) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_besselJ 1).continuousOn
      intro x hx
      rw [interior_Icc] at hx
      exact deriv_rp_neg_of_gt hZ hx.1 (hx.2.trans hk)
    obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (besselJ 0) (fun x => -besselJ 1 x) hr.2
      (continuous_besselJ 0).continuousOn (fun x _ => hasDerivAt_besselJ_zero x)
    rw [besselJ_zero_jq hZ] at hξeq
    have hJ : besselJ 1 jq < besselJ 1 ξ :=
      hanti ⟨h.le.trans hξ.1.le, hξ.2.le⟩ ⟨by linarith, le_rfl⟩ hξ.2
    have hqr : 0 < jq - r := by linarith [hr.2]
    have e : besselJ 0 r = besselJ 1 ξ * (jq - r) := by
      field_simp at hξeq; linarith
    rw [e]
    have hqJ := jq_mul_J1q hZ hI
    have : 1 - r / jq = (jq - r) / jq := by field_simp
    rw [this, div_lt_iff₀ hq0]
    have h1 : 1 < besselJ 1 ξ * jq := by nlinarith [mul_lt_mul_of_pos_right hJ hq0]
    nlinarith [mul_pos hqr (sub_pos.mpr h1)]

/-- **Lemma 7.6**: `φ(r) > (k - r)/k` for `0 < r < k`. -/
theorem rPhi_gt_chord (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    (jk - r) / jk < rPhi r := by
  have hk := jk_pos hZ
  have hα := (parameter_signs hZ).2.2.1
  have hαk := alpha_jk hZ
  have h := besselJ_zero_gt_chord hZ hI (r := pAlpha * r)
    ⟨mul_pos hα hr.1, by rw [← hαk]; exact mul_lt_mul_of_pos_left hr.2 hα⟩
  have hq : 0 < jq := by rw [← hαk]; positivity
  have e : 1 - pAlpha * r / jq = (jk - r) / jk := by
    rw [← hαk]; field_simp
  rw [e] at h
  exact h
end

end Buckling
end
end ChunkedSource082
/- END SOURCE 082 -/

/- BEGIN SOURCE 083: RequestProject/Positivity/Ratio.lean -/
section ChunkedSource083

/-!
# The ratio inequality for the disk profile (Lemma 7.2 of the paper)

With `v = 1 - J₀`, we show `(u - v) p² - 2 u v p' > 0` on `(0, k)`, i.e. `2vS/p² < σ`.
The monotonicity of `J₂/(rJ₁)` is obtained from the identity
`(r (r(J₁² + J₂²) - 4J₁J₂))' = 2 r J₂²` instead of the product formula.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `v = 1 - J₀`. -/
noncomputable def vF (r : ℝ) : ℝ := 1 - besselJ 0 r

lemma hasDerivAt_besselJ_two {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (besselJ 2) (besselJ 1 r - 2 * besselJ 2 r / r) r := by
  have h := hasDerivAt_besselJ_succ 1 r
  have hrec := besselJ_recurrence 1 r
  refine h.congr_deriv ?_
  field_simp
  push_cast at hrec
  linarith

lemma hasDerivAt_besselJ_one' (r : ℝ) :
    HasDerivAt (besselJ 1) ((besselJ 0 r - besselJ 2 r) / 2) r :=
  hasDerivAt_besselJ_succ 0 r

/-- `N₂ = r(J₁² + J₂²) - 4J₁J₂`. -/
noncomputable def N2f (r : ℝ) : ℝ :=
  r * (besselJ 1 r ^ 2 + besselJ 2 r ^ 2) - 4 * besselJ 1 r * besselJ 2 r

lemma N2f_pos {r : ℝ} (hr0 : 0 < r) (hr : r < 4) : 0 < N2f r := by
  set M : ℝ → ℝ := fun y => y * N2f y with hM
  have hMc : Continuous M := by
    have h1 := continuous_besselJ 1
    have h2 := continuous_besselJ 2
    simp only [hM, N2f]; fun_prop
  have hMd : ∀ y, y ≠ 0 → HasDerivAt M (2 * y * besselJ 2 y ^ 2) y := by
    intro y hy
    have h1 := hasDerivAt_besselJ_one' y
    have h2 := hasDerivAt_besselJ_two hy
    have hrec := besselJ_recurrence 0 y
    have h := (hasDerivAt_id y).mul ((((hasDerivAt_id y).mul ((h1.pow 2).add (h2.pow 2))).sub
      ((h1.const_mul 4).mul h2)))
    refine HasDerivAt.congr_deriv (f := M) h ?_
    simp only [id, Nat.cast_ofNat, Nat.cast_zero] at hrec ⊢
    have e : besselJ 0 y = 2 * besselJ 1 y / y - besselJ 2 y := by
      field_simp; linarith
    rw [e]
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id]
    field_simp
    ring
  have hmono : StrictMonoOn M (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hMc.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hMd y hy.1.ne').deriv]
    have := besselJ_two_pos_small y hy.1 (hy.2.trans hr)
    have := hy.1
    positivity
  have h := hmono ⟨le_rfl, hr0.le⟩ ⟨hr0.le, le_rfl⟩ hr0
  have hM0 : M 0 = 0 := by simp [hM]
  rw [hM0] at h
  simp only [hM] at h
  exact pos_of_mul_pos_right h hr0.le

section
variable (hZ : ExtZeros)
include hZ

/-- **Lemma 7.2**: `(u - v) p² - 2 u v p' > 0` on `(0, k)`. -/
theorem ratio_ineq {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    2 * ru r * vF r * deriv rp r < (ru r - vF r) * rp r ^ 2 := by
  have hk := jk_pos hZ
  have hk4 := jk_lt_four hZ
  have hJ1 : ∀ y ∈ Ioo 0 jk, 0 < besselJ 1 y := fun y hy => (radial_equations hZ y hy.1 hy.2).1
  have h := cubic_interpolation_param (X := besselJ 0) (dX := fun y => -besselJ 1 y)
    (E := fun y => besselJ 1 y ^ 2) (E1 := fun y => -(besselJ 0 y - besselJ 2 y))
    (E2 := fun y => 2 * (besselJ 2 y / (y * besselJ 1 y)) - 2)
    (E3 := fun y => -2 * N2f y / (y ^ 2 * besselJ 1 y ^ 3)) (a := 0) (b := jk)
    (continuous_besselJ 0).continuousOn ((continuous_besselJ 1).pow 2).continuousOn
    (fun y _ => hasDerivAt_besselJ_zero y) (fun y hy => by simpa using hJ1 y hy)
    (fun y _ => by
      have := (hasDerivAt_besselJ_one' y).pow 2
      refine this.congr_deriv ?_
      simp only [Nat.cast_ofNat]; ring)
    (fun y hy => by
      have hy0 := hy.1.ne'
      have := ((hasDerivAt_besselJ_zero y).sub (hasDerivAt_besselJ_two hy0)).neg
      refine this.congr_deriv ?_
      have hp := hJ1 y hy
      field_simp
      ring)
    (fun y hy => by
      have hy0 := hy.1.ne'
      have hp := hJ1 y hy
      have := (((hasDerivAt_besselJ_two hy0).div ((hasDerivAt_id y).mul
        (hasDerivAt_besselJ_one' y)) (mul_ne_zero hy0 hp.ne')).const_mul 2).sub_const 2
      refine this.congr_deriv ?_
      have hrec := besselJ_recurrence 0 y
      simp only [id, Nat.cast_zero] at hrec ⊢
      have e : besselJ 0 y = 2 * besselJ 1 y / y - besselJ 2 y := by
        field_simp; linarith
      rw [e]
      simp only [N2f, Pi.mul_apply, id]
      field_simp
      ring)
    (by simp [besselJ_zero_arg]) (by simp [besselJ_one_jk hZ])
    (fun y hy => by
      have := N2f_pos hy.1 (hy.2.trans hk4)
      have hp := hJ1 y hy
      have : 0 < y ^ 2 * besselJ 1 y ^ 3 := by have := hy.1; positivity
      apply div_neg_of_neg_of_pos (by linarith) this) hr
  have hX0 : besselJ 0 0 = 1 := by simp [besselJ_zero_arg]
  have hXk : besselJ 0 jk = -pc := by have := ru_jk; unfold ru at this; linarith
  rw [hX0, hXk] at h
  have hd := deriv_rp_eq_all
  have : deriv rp r = (besselJ 0 r - besselJ 2 r) / 2 := by rw [hd]
  rw [this]
  simp only [ru, vF, rp]
  nlinarith [h]
end

end Buckling
end
end ChunkedSource083
/- END SOURCE 083 -/

/- BEGIN SOURCE 084: RequestProject/Positivity/LowerZ.lean -/
section ChunkedSource084

/-!
# The comparison residual (Lemma 7.3 of the paper)

With `h₀ = (p + vA)/σ`, the residual `R = λ - h₀/r + h₀² - h₀'` is strictly decreasing on
`(0, k)`.  The positivity of `A' ` is obtained from the identity
`(r²(p'² + p²) - p²)' = 2rp²` instead of the product formula.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- The explicit derivative `A' = A² - A/r + 1 - r⁻²` of `A = -p'/p`. -/
noncomputable def Ad (r : ℝ) : ℝ := rA r ^ 2 - rA r / r + 1 - 1 / r ^ 2
/-- `h₀ = (p + vA)/σ`. -/
noncomputable def h0 (r : ℝ) : ℝ := (rp r + vF r * rA r) / pSigma
/-- The comparison residual `R = λ - h₀/r + h₀² - h₀'`, with `h₀' = vA'/σ`. -/
noncomputable def Rres (r : ℝ) : ℝ := pLam - h0 r / r + h0 r ^ 2 - vF r * Ad r / pSigma

lemma hasDerivAt_vF (r : ℝ) : HasDerivAt vF (rp r) r := by
  have := (hasDerivAt_besselJ_zero r).const_sub 1
  simpa [vF, rp] using! this

lemma vF_add_ru (r : ℝ) : vF r + ru r = pSigma := by simp [vF, ru, pSigma]; ring

section
variable (hZ : ExtZeros)
include hZ

lemma hasDerivAt_rA' {r : ℝ} (hr : r ∈ Ioo 0 jk) : HasDerivAt rA (Ad r) r := by
  refine (hasDerivAt_rA hZ hr.1 hr.2).congr_deriv ?_
  simp only [Ad, rC]; field_simp; ring

/-- `p² < r²(p'² + p²)` on `(0, k)`. -/
lemma rp_sq_lt {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rp r ^ 2 < r ^ 2 * (deriv rp r ^ 2 + rp r ^ 2) := by
  set K : ℝ → ℝ := fun y => y ^ 2 * (deriv rp y ^ 2 + rp y ^ 2) - rp y ^ 2 with hK
  have hKc : Continuous K := by
    have h1 : Continuous rp := continuous_besselJ 1
    have h2 := continuous_deriv_rp
    simp only [hK]; fun_prop
  have hKd : ∀ y ∈ Ioo 0 jk, HasDerivAt K (2 * y * rp y ^ 2) y := by
    intro y hy
    obtain ⟨-, -, -, -, hp', hp'', -⟩ := radial_equations hZ y hy.1 hy.2
    have hp : HasDerivAt rp (deriv rp y) y := hp'.differentiableAt.hasDerivAt
    have h := (((hasDerivAt_id y).pow 2).mul ((hp''.pow 2).add (hp.pow 2))).sub (hp.pow 2)
    refine HasDerivAt.congr_deriv (f := K) h ?_
    have hy0 := hy.1.ne'
    simp only [id, Nat.cast_ofNat, Pi.pow_apply, Pi.add_apply]
    field_simp
    ring
  have hmono : StrictMonoOn K (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hKc.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    have hy' : y ∈ Ioo 0 jk := ⟨hy.1, hy.2.trans hr.2⟩
    rw [(hKd y hy').deriv]
    have := (radial_equations hZ y hy'.1 hy'.2).1
    have := hy.1
    positivity
  have h := hmono ⟨le_rfl, hr.1.le⟩ ⟨hr.1.le, le_rfl⟩ hr.1
  have hK0 : K 0 = 0 := by simp [hK, rp, besselJ_zero_arg]
  rw [hK0] at h
  simp only [hK] at h
  linarith

/-- `A' > 0` on `(0, k)`. -/
lemma Ad_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < Ad r := by
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hr0 := hr.1.ne'
  have key : r ^ 2 * rp r ^ 2 * Ad r =
      r ^ 2 * deriv rp r ^ 2 + r * rp r * deriv rp r + (r ^ 2 - 1) * rp r ^ 2 := by
    simp only [Ad, rA]; field_simp; ring
  have hpos : 0 < r ^ 2 * deriv rp r ^ 2 + r * rp r * deriv rp r + (r ^ 2 - 1) * rp r ^ 2 := by
    rcases le_or_gt 0 (deriv rp r) with h | h
    · have := rp_sq_lt hZ hr
      have : 0 ≤ r * rp r * deriv rp r := by have := hr.1; positivity
      nlinarith
    · have hr2 : 2 < r ^ 2 := by
        by_contra hc; push_neg at hc
        linarith [deriv_rp_pos_small r hr.1 hc]
      nlinarith [sq_nonneg (r * deriv rp r + rp r / 2), sq_pos_of_pos hp]
  have : 0 < r ^ 2 * rp r ^ 2 := by positivity
  rw [← key] at hpos
  exact pos_of_mul_pos_right hpos this.le

/-- `r p < 2v` on `(0, k)`. -/
lemma r_rp_lt_two_vF {r : ℝ} (hr : r ∈ Ioo 0 jk) : r * rp r < 2 * vF r := by
  set G : ℝ → ℝ := fun y => 2 * vF y - y * rp y with hG
  have hGc : Continuous G := by
    have h1 : Continuous rp := continuous_besselJ 1
    have h2 : Continuous vF := (continuous_const.sub (continuous_besselJ 0))
    simp only [hG]; fun_prop
  have hmono : StrictMonoOn G (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hGc.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    have hy' : y ∈ Ioo 0 jk := ⟨hy.1, hy.2.trans hr.2⟩
    have hp' := (radial_equations hZ y hy'.1 hy'.2).2.2.2.2.1
    have hp : HasDerivAt rp (deriv rp y) y := hp'.differentiableAt.hasDerivAt
    have h := ((hasDerivAt_vF y).const_mul 2).sub ((hasDerivAt_id y).mul hp)
    have h' : HasDerivAt G (2 * rp y - (1 * rp y + id y * deriv rp y)) y := h
    rw [h'.deriv]
    have := J2_pos hZ hy'
    have h0 := hy'.1
    have : 0 < y * (rp y / y - deriv rp y) := mul_pos h0 this
    have e : y * (rp y / y - deriv rp y) = rp y - y * deriv rp y := by field_simp
    simp only [id]
    linarith
  have h := hmono ⟨le_rfl, hr.1.le⟩ ⟨hr.1.le, le_rfl⟩ hr.1
  have hG0 : G 0 = 0 := by simp [hG, vF, besselJ_zero_arg]
  rw [hG0] at h
  simp only [hG] at h
  linarith

lemma hasDerivAt_h0 {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt h0 (vF r * Ad r / pSigma) r := by
  have hp' := (radial_equations hZ r hr.1 hr.2).2.2.2.2.1
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hp1 : HasDerivAt rp (deriv rp r) r := hp'.differentiableAt.hasDerivAt
  have h := (hp1.add ((hasDerivAt_vF r).mul (hasDerivAt_rA' hZ hr))).div_const pSigma
  refine HasDerivAt.congr_deriv (f := h0) h ?_
  simp only [rA]
  field_simp
  ring

lemma hasDerivAt_Ad {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt Ad (2 * rA r * Ad r - Ad r / r + rA r / r ^ 2 + 2 / r ^ 3) r := by
  have hr0 := hr.1.ne'
  have hA := hasDerivAt_rA' hZ hr
  have h := ((((hA.pow 2).sub (hA.div (hasDerivAt_id r) hr0)).add_const 1).sub
    ((hasDerivAt_pow 2 r).inv (pow_ne_zero 2 hr0)))
  have heq : Ad = fun y => rA y ^ 2 - rA y / id y + 1 - (y ^ 2)⁻¹ := by
    ext y; simp [Ad]
  refine (h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq)).congr_deriv ?_
  simp only [id, Nat.cast_ofNat]
  field_simp
  ring

/-- The derivative of the residual (Lemma 7.3). -/
noncomputable def Rd (r : ℝ) : ℝ :=
  Ad r / pSigma * (2 * vF r * (rp r - ru r * rA r) / pSigma - rp r) +
    (r * rp r - 2 * vF r) / (pSigma * r ^ 3)

lemma hasDerivAt_Rres {r : ℝ} (hr : r ∈ Ioo 0 jk) : HasDerivAt Rres (Rd r) r := by
  have hr0 := hr.1.ne'
  have hσ := pSigma_pos hZ
  have hh := hasDerivAt_h0 hZ hr
  have h := ((((hh.div (hasDerivAt_id r) hr0).const_sub pLam).add (hh.pow 2)).sub
    (((hasDerivAt_vF r).mul (hasDerivAt_Ad hZ hr)).div_const pSigma))
  have heq : Rres = fun y => pLam - h0 y / id y + h0 y ^ 2 - vF y * Ad y / pSigma := by
    ext y; simp [Rres]
  refine (h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq heq)).congr_deriv ?_
  have hu : ru r = pSigma - vF r := by linarith [vF_add_ru r]
  have hσ' : pSigma ≠ 0 := hσ.ne'
  simp only [Rd, id, Nat.cast_ofNat, h0, hu]
  field_simp
  have := mul_inv_cancel₀ hσ'
  linear_combination (2 * r ^ 3 * vF r * Ad r * rp r + 2 * r ^ 3 * vF r ^ 2 * Ad r * rA r) * this

/-- **Lemma 7.3**: `R' < 0` on `(0, k)`. -/
lemma Rd_neg {r : ℝ} (hr : r ∈ Ioo 0 jk) : Rd r < 0 := by
  have hσ := pSigma_pos hZ
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hA := Ad_pos hZ hr
  have hrat := ratio_ineq hZ hr
  have hrv := r_rp_lt_two_vF hZ hr
  have h1 : 2 * vF r * (rp r - ru r * rA r) / pSigma - rp r < 0 := by
    rw [sub_neg, div_lt_iff₀ hσ]
    have e : rp r - ru r * rA r = (rp r ^ 2 + ru r * deriv rp r) / rp r := by
      simp only [rA]; field_simp; ring
    rw [e]
    have hu : pSigma = ru r + vF r := by linarith [vF_add_ru r]
    rw [hu, mul_div_assoc', div_lt_iff₀ hp]
    nlinarith
  have h2 : (r * rp r - 2 * vF r) / (pSigma * r ^ 3) < 0 :=
    div_neg_of_neg_of_pos (by linarith) (by have := hr.1; positivity)
  have h3 : Ad r / pSigma * (2 * vF r * (rp r - ru r * rA r) / pSigma - rp r) < 0 :=
    mul_neg_of_pos_of_neg (div_pos hA hσ) h1
  unfold Rd
  linarith

end

end Buckling
end
end ChunkedSource084
/- END SOURCE 084 -/

/- BEGIN SOURCE 085: RequestProject/Positivity/LowerZ2.lean -/
section ChunkedSource085

/-!
# A lower bound for `z` (Proposition 7.7 of the paper)
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `ψ = exp(-∫₁^r h₀)` (normalised at `r = 1` instead of `r = 0`). -/
noncomputable def psiF (r : ℝ) : ℝ := Real.exp (-∫ s in (1 : ℝ)..r, h0 s)

/-- `r W = r(ψ φ' - φ ψ') = r ψ (φ' + h₀ φ)`. -/
noncomputable def Wz (r : ℝ) : ℝ := r * psiF r * (deriv rPhi r + h0 r * rPhi r)

lemma false_of_strictAntiOn_tendsto {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : StrictAntiOn f (Ioo a b)) (ha : Tendsto f (𝓝[>] a) (𝓝 0))
    (hb : Tendsto f (𝓝[<] b) (𝓝 0)) : False := by
  set x := (2 * a + b) / 3
  set y := (a + 2 * b) / 3
  have hx : x ∈ Ioo a b := ⟨by simp only [x]; linarith, by simp only [x]; linarith⟩
  have hy : y ∈ Ioo a b := ⟨by simp only [y]; linarith, by simp only [y]; linarith⟩
  have hxy : x < y := by simp only [x, y]; linarith
  have h1 : f x ≤ 0 := by
    apply ge_of_tendsto ha
    filter_upwards [Ioo_mem_nhdsGT hx.1] with s hs
    exact (hf ⟨hs.1, hs.2.trans hx.2⟩ hx hs.2).le
  have h2 : 0 ≤ f y := by
    apply le_of_tendsto hb
    filter_upwards [Ioo_mem_nhdsLT hy.2] with s hs
    exact (hf hy ⟨hy.1.trans hs.1, hs.2⟩ hs.1).le
  linarith [hf hx hy hxy]

section
variable (hZ : ExtZeros)
include hZ

lemma vF_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < vF r := by
  have hmono : StrictMonoOn vF (Icc 0 r) := by
    have hc : Continuous vF := continuous_const.sub (continuous_besselJ 0)
    apply strictMonoOn_of_deriv_pos (f := vF) (convex_Icc _ _) hc.continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(hasDerivAt_vF y).deriv]
    exact (radial_equations hZ y hy.1 (hy.2.trans hr.2)).1
  have := hmono ⟨le_rfl, hr.1.le⟩ ⟨hr.1.le, le_rfl⟩ hr.1
  simpa [vF, besselJ_zero_arg] using this

lemma one_lt_jk : 1 < jk := by linarith [two_lt_jk hZ]

lemma continuousOn_h0 : ContinuousOn h0 (Ioo 0 jk) := by
  intro x hx
  have hp := (radial_equations hZ x hx.1 hx.2).1
  have h1 : Continuous rp := continuous_besselJ 1
  have h2 : Continuous vF := continuous_const.sub (continuous_besselJ 0)
  have h3 := continuous_deriv_rp
  apply ContinuousAt.continuousWithinAt
  unfold h0 rA
  exact ((h1.continuousAt.add (h2.continuousAt.mul
    (h3.continuousAt.neg.div h1.continuousAt hp.ne'))).div_const _)

/-- `h₀ > 0` on `(0, k)`. -/
lemma h0_pos {r : ℝ} (hr : r ∈ Ioo 0 jk) : 0 < h0 r := by
  have hσ := pSigma_pos hZ
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hv := vF_pos hZ hr
  have key : 0 < rp r ^ 2 - vF r * deriv rp r := by
    rcases le_or_gt (deriv rp r) 0 with h | h
    · nlinarith
    · have hr19 : r ≤ 19 / 10 := by
        by_contra hc; push_neg at hc
        linarith [deriv_rp_neg_of_gt hZ hc hr.2]
      have hr0 := hr.1
      have hJ0 := besselJ_zero_gt_small r hr.1 (by nlinarith)
      have hJ2 := J2_pos hZ hr
      have hJ1 := besselJ_tail_general 1 1 r hr.1 (by push_cast; nlinarith)
      rw [besselPartialR_one_one] at hJ1
      norm_num at hJ1
      have hp4 : r / 4 < rp r := by
        have : r ^ 2 < 4 := by nlinarith
        simp only [rp]; nlinarith
      have hv4 : vF r < r ^ 2 / 4 := by simp only [vF]; linarith
      have hd : deriv rp r < rp r / r := by linarith
      have h1 : vF r * deriv rp r < r ^ 2 / 4 * (rp r / r) := by
        apply mul_lt_mul'' hv4 hd hv.le h.le
      have h2 : r ^ 2 / 4 * (rp r / r) = r * rp r / 4 := by field_simp
      nlinarith
  unfold h0 rA
  have : rp r + vF r * (-deriv rp r / rp r) = (rp r ^ 2 - vF r * deriv rp r) / rp r := by
    field_simp; ring
  rw [this]
  positivity

lemma hasDerivAt_psiF {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt psiF (-h0 r * psiF r) r := by
  have h1 := one_lt_jk hZ
  have hsub : uIcc 1 r ⊆ Ioo 0 jk := by
    intro x hx
    rcases le_total 1 r with h | h
    · rw [uIcc_of_le h] at hx; exact ⟨by linarith [hx.1], hx.2.trans_lt hr.2⟩
    · rw [uIcc_of_ge h] at hx; exact ⟨hr.1.trans_le hx.1, by linarith [hx.2]⟩
  have hint : IntervalIntegrable h0 MeasureTheory.volume 1 r :=
    ((continuousOn_h0 hZ).mono hsub).intervalIntegrable
  have hmeas : StronglyMeasurableAtFilter h0 (𝓝 r) :=
    (continuousOn_h0 hZ).stronglyMeasurableAtFilter isOpen_Ioo r hr
  have hca : ContinuousAt h0 r := (continuousOn_h0 hZ).continuousAt (isOpen_Ioo.mem_nhds hr)
  have hI := intervalIntegral.integral_hasDerivAt_right hint hmeas hca
  have h := hI.neg.exp
  refine h.congr_deriv ?_
  simp only [psiF, Pi.neg_apply]
  ring

omit hZ in
lemma psiF_pos (r : ℝ) : 0 < psiF r := Real.exp_pos _

/-- `ψ ≤ 1` on `[1, k)`. -/
lemma psiF_le_one {r : ℝ} (h1 : 1 ≤ r) (hrk : r < jk) : psiF r ≤ 1 := by
  unfold psiF
  rw [Real.exp_le_one_iff, neg_nonpos]
  apply intervalIntegral.integral_nonneg h1
  intro x hx
  exact (h0_pos hZ ⟨by linarith [hx.1], hx.2.trans_lt hrk⟩).le

/-- `h₀ ≤ 1/2` on `(0, 1]`. -/
lemma h0_le_half {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : h0 r ≤ 1 / 2 := by
  have hk1 := one_lt_jk hZ
  have hr : r ∈ Ioo 0 jk := ⟨hr0, by linarith⟩
  have hσ : 1 < pSigma := by have := pc_pos hZ; unfold pSigma; linarith
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hv := vF_pos hZ hr
  have hd := deriv_rp_pos_small r hr0 (by nlinarith)
  have hp2 : rp r < r / 2 := besselJ_one_lt_small r hr0 (by nlinarith)
  unfold h0 rA
  rw [div_le_iff₀ (by linarith)]
  have : vF r * (-deriv rp r / rp r) ≤ 0 := by
    have : 0 < deriv rp r / rp r := div_pos hd hp
    rw [neg_div]; nlinarith
  nlinarith

/-- `ψ ≤ 2` on `(0, 1]`. -/
lemma psiF_le_two {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) : psiF r ≤ 2 := by
  unfold psiF
  have hb : ∫ s in (1 : ℝ)..r, h0 s ≥ -(1 / 2) := by
    rw [intervalIntegral.integral_symm, ge_iff_le, neg_le_neg_iff]
    have hle : ∫ s in r..1, h0 s ≤ ∫ s in r..1, (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_mono_on hr1
      · apply ContinuousOn.intervalIntegrable_of_Icc hr1
        exact (continuousOn_h0 hZ).mono fun x hx =>
          ⟨hr0.trans_le hx.1, hx.2.trans_lt (one_lt_jk hZ)⟩
      · exact intervalIntegrable_const
      · intro x hx; exact h0_le_half hZ (hr0.trans_le hx.1) hx.2
    simp at hle
    linarith
  calc Real.exp (-∫ s in (1 : ℝ)..r, h0 s) ≤ Real.exp (1 / 2) := by
        apply Real.exp_le_exp.mpr; linarith
    _ ≤ 2 := by
        have := Real.exp_one_lt_d9
        have h2 : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
          rw [← Real.exp_add]; norm_num
        have h3 := Real.exp_pos (1 / 2)
        nlinarith

lemma hasDerivAt_Wz {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    HasDerivAt Wz (-(r * psiF r * rPhi r * Rres r)) r := by
  have hr0 := hr.1.ne'
  have hφ'' := (radial_equations hZ r hr.1 hr.2).2.2.2.2.2.2.1
  have h := (((hasDerivAt_id r).mul (hasDerivAt_psiF hZ hr)).mul (hφ''.add
    ((hasDerivAt_h0 hZ hr).mul (hasDerivAt_rPhi_deriv r))))
  refine HasDerivAt.congr_deriv (f := Wz) h ?_
  simp only [Rres, id, Pi.mul_apply, Pi.add_apply]
  field_simp
  ring

/-- `φ' + h₀ φ → 0` as `r → k⁻`. -/
lemma tendsto_phi_h0_jk :
    Tendsto (fun r => deriv rPhi r + h0 r * rPhi r) (𝓝[<] jk) (𝓝 0) := by
  have hk := jk_pos hZ
  have hc := pc_pos hZ
  have hσ := pSigma_pos hZ
  have h1 : Tendsto (deriv rPhi) (𝓝[<] jk) (𝓝 (-pAlpha * jJ)) := by
    have := (continuous_deriv_rPhi.tendsto jk).mono_left (nhdsWithin_le_nhds (s := Iio jk))
    rwa [deriv_rPhi_eq, alpha_jk hZ] at this
  have hratio : Tendsto (fun r => rPhi r / rp r) (𝓝[<] jk) (𝓝 (pAlpha * jJ / pc)) := by
    refine ((tendsto_rPhi_div hZ).div (tendsto_rp_div hZ) hc.ne').congr' ?_
    filter_upwards [eventually_dk_ne] with r hr
    simp only [pow_one, Pi.div_apply]
    field_simp
  have hpd : Tendsto (deriv rp) (𝓝[<] jk) (𝓝 (-pc)) := by
    have := (continuous_deriv_rp.tendsto jk).mono_left (nhdsWithin_le_nhds (s := Iio jk))
    rwa [deriv_rp_eq jk hk.ne', besselJ_one_jk hZ, zero_div, sub_zero,
      show besselJ 0 jk = -pc by have := ru_jk; unfold ru at this; linarith] at this
  have hv : Tendsto vF (𝓝[<] jk) (𝓝 pSigma) := by
    have hc' : Continuous vF := continuous_const.sub (continuous_besselJ 0)
    have := (hc'.tendsto jk).mono_left (nhdsWithin_le_nhds (s := Iio jk))
    have e : vF jk = pSigma := by
      have := vF_add_ru jk; rw [ru_jk] at this; linarith
    rwa [e] at this
  have hp0 : Tendsto rp (𝓝[<] jk) (𝓝 0) := by
    have := ((continuous_besselJ 1).tendsto jk).mono_left (nhdsWithin_le_nhds (s := Iio jk))
    simpa [rp, besselJ_one_jk hZ] using! this
  have hφ0 : Tendsto rPhi (𝓝[<] jk) (𝓝 0) := by
    have := (continuous_rPhi.tendsto jk).mono_left (nhdsWithin_le_nhds (s := Iio jk))
    rwa [rPhi_jk hZ] at this
  have h2 : Tendsto (fun r => (rp r * rPhi r + vF r * (-deriv rp r) * (rPhi r / rp r)) / pSigma)
      (𝓝[<] jk) (𝓝 ((0 * 0 + pSigma * (-(-pc)) * (pAlpha * jJ / pc)) / pSigma)) :=
    (((hp0.mul hφ0).add ((hv.mul hpd.neg).mul hratio)).div_const pSigma)
  have hval : (0 * 0 + pSigma * (-(-pc)) * (pAlpha * jJ / pc)) / pSigma = pAlpha * jJ := by
    field_simp; ring
  rw [hval] at h2
  have h := h1.add h2
  rw [show -pAlpha * jJ + pAlpha * jJ = 0 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_Ioo_jk hZ] with r hr
  have hp := (radial_equations hZ r hr.1 hr.2).1
  simp only [h0, rA]
  field_simp

lemma tendsto_Wz_jk : Tendsto Wz (𝓝[<] jk) (𝓝 0) := by
  have hk := jk_pos hZ
  have h := (tendsto_phi_h0_jk hZ).const_mul jk
  rw [mul_zero] at h
  refine squeeze_zero_norm' ?_ (h.norm.trans (by simp))
  filter_upwards [Ioo_mem_nhdsLT (one_lt_jk hZ)] with r hr
  have hψ := psiF_le_one hZ hr.1.le hr.2
  have hψ0 := psiF_pos r
  have hr0 : 0 < r := by linarith [hr.1]
  rw [Wz, norm_mul, norm_mul, Real.norm_of_nonneg hr0.le, Real.norm_of_nonneg hψ0.le, norm_mul,
    Real.norm_of_nonneg hk.le]
  have := norm_nonneg (deriv rPhi r + h0 r * rPhi r)
  have : r * psiF r ≤ jk := by nlinarith [hr.2]
  nlinarith

lemma tendsto_Wz_zero (hI : ExtIntegral) : Tendsto Wz (𝓝[>] 0) (𝓝 0) := by
  have hα := (parameter_signs hZ).2.2.1
  obtain ⟨-, hα2⟩ := coarse_alpha hZ
  have h : Tendsto (fun r : ℝ => 3 * r) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_const_mul (3 : ℝ)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using! this
  refine squeeze_zero_norm' ?_ h
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with r hr
  have hψ := psiF_le_two hZ hr.1 hr.2.le
  have hψ0 := psiF_pos r
  have hh := h0_le_half hZ hr.1 hr.2.le
  have hh0 := h0_pos hZ ⟨hr.1, hr.2.trans (one_lt_jk hZ)⟩
  have hd : |deriv rPhi r| ≤ 1 := by
    rw [deriv_rPhi_eq, abs_mul, abs_neg, abs_of_pos hα]
    have := abs_besselJ_le_one hI 1 (pAlpha * r)
    nlinarith [abs_nonneg (besselJ 1 (pAlpha * r))]
  have hφ : |rPhi r| ≤ 1 := abs_besselJ_le_one hI 0 _
  have hT : |deriv rPhi r + h0 r * rPhi r| ≤ 3 / 2 := by
    calc _ ≤ |deriv rPhi r| + |h0 r * rPhi r| := abs_add_le _ _
      _ ≤ 1 + 1 / 2 * 1 := by
          rw [abs_mul, abs_of_pos hh0]
          gcongr
      _ = 3 / 2 := by norm_num
  rw [Wz, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hr.1, abs_of_pos hψ0]
  have : r * psiF r ≤ 2 * r := by nlinarith [hr.1]
  calc r * psiF r * |deriv rPhi r + h0 r * rPhi r| ≤ 2 * r * (3 / 2) := by
        apply mul_le_mul this hT (abs_nonneg _) (by linarith [hr.1])
    _ = 3 * r := by ring

/-- `W < 0` on `(0, k)` (proof of Proposition 7.7). -/
theorem Wz_neg (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) : Wz r < 0 := by
  have hk := jk_pos hZ
  have hRc : ContinuousOn Rres (Ioo 0 jk) := fun x hx =>
    (hasDerivAt_Rres hZ hx).continuousAt.continuousWithinAt
  have hR : StrictAntiOn Rres (Ioo 0 jk) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) hRc
    intro x hx; rw [interior_Ioo] at hx
    rw [(hasDerivAt_Rres hZ hx).deriv]; exact Rd_neg hZ hx
  have hWd : DifferentiableOn ℝ Wz (Ioo 0 jk) := fun x hx =>
    (hasDerivAt_Wz hZ hx).differentiableAt.differentiableWithinAt
  have hw : ∀ x ∈ Ioo 0 jk, 0 < x * psiF x * rPhi x := fun x hx => by
    have := psiF_pos x
    have := (radial_equations hZ x hx.1 hx.2).2.2.1
    have := hx.1
    positivity
  have hderiv : ∀ x ∈ Ioo 0 jk, deriv Wz x = -(x * psiF x * rPhi x * Rres x) :=
    fun x hx => (hasDerivAt_Wz hZ hx).deriv
  have h0 := tendsto_Wz_zero hZ hI
  have hkl := tendsto_Wz_jk hZ
  -- existence of the sign change of `R`
  have hξ : ∃ ξ ∈ Ioo 0 jk, Rres ξ = 0 := by
    by_contra hno
    push_neg at hno
    by_cases hpos : ∀ x ∈ Ioo 0 jk, 0 < Rres x
    · apply false_of_strictAntiOn_tendsto hk _ h0 hkl
      apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) hWd.continuousOn
      intro x hx; rw [interior_Ioo] at hx
      rw [hderiv x hx]
      have := mul_pos (hw x hx) (hpos x hx)
      linarith
    by_cases hneg : ∀ x ∈ Ioo 0 jk, Rres x < 0
    · apply false_of_strictAntiOn_tendsto (f := fun x => -Wz x) hk _
        (by simpa using h0.neg) (by simpa using hkl.neg)
      apply strictAntiOn_of_deriv_neg (convex_Ioo _ _) hWd.continuousOn.neg
      intro x hx; rw [interior_Ioo] at hx
      rw [deriv.neg, hderiv x hx]
      have := mul_neg_of_pos_of_neg (hw x hx) (hneg x hx)
      linarith
    push_neg at hpos hneg
    obtain ⟨a, ha, ha'⟩ := hpos
    obtain ⟨b, hb, hb'⟩ := hneg
    have ha'' : Rres a < 0 := lt_of_le_of_ne ha' (hno a ha)
    have hb'' : 0 < Rres b := lt_of_le_of_ne hb' (Ne.symm (hno b hb))
    have hba : b < a := by
      by_contra hc; push_neg at hc
      rcases eq_or_lt_of_le hc with h | h
      · rw [h] at ha''; linarith
      · linarith [hR ha hb h]
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo' hba.le
      (hRc.mono (Icc_subset_Ioo hb.1 ha.2)) ⟨ha'', hb''⟩
    exact hno c ⟨hb.1.trans hc.1, hc.2.trans ha.2⟩ hc0
  obtain ⟨ξ, hξ, hRξ⟩ := hξ
  refine neg_of_deriv_one_change hξ hWd h0 hkl ?_ ?_ r hr
  · intro x hx
    have hx' : x ∈ Ioo 0 jk := ⟨hx.1, hx.2.trans hξ.2⟩
    rw [hderiv x hx']
    have := hR hx' hξ hx.2
    have := mul_pos (hw x hx') (by linarith : 0 < Rres x)
    linarith
  · intro x hx
    have hx' : x ∈ Ioo 0 jk := ⟨hξ.1.trans hx.1, hx.2⟩
    rw [hderiv x hx']
    have := hR hξ hx' hx.1
    have := mul_neg_of_pos_of_neg (hw x hx') (by linarith : Rres x < 0)
    linarith

/-- `z > φ/σ` on `(0, k)`. -/
theorem rz_gt_rPhi_div (hI : ExtIntegral) {r : ℝ} (hr : r ∈ Ioo 0 jk) :
    rPhi r / pSigma < rz r := by
  have hσ := pSigma_pos hZ
  have hW := Wz_neg hZ hI hr
  have hp := (radial_equations hZ r hr.1 hr.2).1
  have hS : 0 < rS r := by simpa [rS] using rS_pos hZ hr.1 hr.2
  have hT : deriv rPhi r + h0 r * rPhi r < 0 := by
    unfold Wz at hW
    have : 0 < r * psiF r := mul_pos hr.1 (psiF_pos r)
    by_contra hc; push_neg at hc
    nlinarith
  have hid : rz r - rPhi r / pSigma = -(rp r / rS r) * (deriv rPhi r + h0 r * rPhi r) := by
    have hu : ru r = pSigma - vF r := by linarith [vF_add_ru r]
    have hS' := hS.ne'
    simp only [rz, h0, rA]
    field_simp
    simp only [rS, hu]
    ring
  have : 0 < -(rp r / rS r) * (deriv rPhi r + h0 r * rPhi r) :=
    mul_pos_of_neg_of_neg (by have := div_pos hp hS; linarith) hT
  linarith

/-- **Proposition 7.7**: `z > (k - r)/(k(1 + c))` on `(0, k)`. -/
theorem z_lower_bound_of (hI : ExtIntegral) :
    ∀ r ∈ Ioo 0 jk, (jk - r) / (jk * (1 + pc)) < rz r := by
  intro r hr
  have hσ := pSigma_pos hZ
  have hk := jk_pos hZ
  have h1 := rz_gt_rPhi_div hZ hI hr
  have h2 := rPhi_gt_chord hZ hI hr
  have : (jk - r) / (jk * (1 + pc)) = (jk - r) / jk / pSigma := by
    unfold pSigma; field_simp
  rw [this]
  calc (jk - r) / jk / pSigma < rPhi r / pSigma := div_lt_div_of_pos_right h2 hσ
    _ < rz r := h1

end

end Buckling
end
end ChunkedSource085
/- END SOURCE 085 -/

/- BEGIN SOURCE 086: RequestProject/Positivity/Coupling.lean -/
section ChunkedSource086

/-!
# The strict coupling estimate (Proposition 8.13 of the paper)

The inequality `d² + 4Kg² ≤ 4K²` (`RemainingPositivity`) follows from three one-variable
estimates on `(0, k)`:

* the quadratic estimate `g² + z² < K` (Proposition 6.6),
* the lower bound `z > (k - r)/(k(1 + c))` (Proposition 7.7),
* the bounds `0 < d ≤ (4K/3k)(k - r)` for `d = 2G - tG_t` (Corollaries 8.9 and 8.11),

together with the numerical inequality `2√K (1 + c) < 3`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `J₁(q) < 0.5192`. -/
lemma coarse_J1q_upper (hZ : ExtZeros) (hI : ExtIntegral) : besselJ 1 jq < 5192 / 10000 := by
  obtain ⟨hq1, hq2, -⟩ := root_boxes hZ
  have := abs_besselJ_one_sub hI jq (240482 / 100000)
  have hr := besselJ_bounds_row11.2
  rw [abs_of_pos (by linarith : (0 : ℝ) < jq - 240482 / 100000), abs_le] at this
  linarith [this.2]

/-- `K < 0.66`. -/
lemma coarse_K_upper (hZ : ExtZeros) (hI : ExtIntegral) : pK < 66 / 100 := by
  obtain ⟨hα1, hα2⟩ := coarse_alpha hZ
  have hJ := coarse_J1q_upper hZ hI
  have hJ0 := (parameter_signs hZ).2.2.2.2.2.2.2.1
  obtain ⟨hc1, -⟩ := coarse_c hZ hI
  have hc0 : 0 < pc := by linarith
  have hα0 : 0 < pAlpha := by linarith
  have hX0 : 0 < pAlpha * besselJ 1 jq / pc := by positivity
  have hX : pAlpha * besselJ 1 jq / pc < 8124 / 10000 := by
    rw [div_lt_iff₀ hc0]
    have : pAlpha * besselJ 1 jq < 628 / 1000 * (5192 / 10000) :=
      mul_lt_mul hα2 hJ.le hJ0 (by norm_num)
    nlinarith
  unfold pK
  nlinarith

/-- The numerical inequality `2√K (1 + c) < 3`. -/
lemma coupling_constant (hZ : ExtZeros) (hI : ExtIntegral) : 2 * Real.sqrt pK * (1 + pc) < 3 := by
  have hK := coarse_K_upper hZ hI
  obtain ⟨-, hc2⟩ := coarse_c hZ hI
  have hs : Real.sqrt pK < 82 / 100 := by
    rw [Real.sqrt_lt' (by norm_num)]; linarith
  have hs0 := Real.sqrt_nonneg pK
  nlinarith

/-- **Proposition 8.13 (the strict coupling estimate)**: from the three estimates,
`d² < 4Kz² < 4K(K - g²)` on `(0, k)`; in particular `d² + 4Kg² ≤ 4K²`. -/
theorem remaining_positivity_of (hZ : ExtZeros) (hI : ExtIntegral)
    (hQ : ∀ r ∈ Ioo 0 jk, rg r ^ 2 + rz r ^ 2 < pK)
    (hZl : ∀ r ∈ Ioo 0 jk, (jk - r) / (jk * (1 + pc)) < rz r)
    (hD : ∀ r ∈ Ioo 0 jk, 0 < 2 * rG r - rt r * rGt r ∧
      2 * rG r - rt r * rGt r ≤ 4 * pK / (3 * jk) * (jk - r)) : RemainingPositivity := by
  intro r hr
  have hk := jk_pos hZ
  have hK := (parameter_signs hZ).2.2.2.2.2.2.2.2
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hq := hQ r hr
  have hz := hZl r hr
  obtain ⟨hd0, hd1⟩ := hD r hr
  have hcc := coupling_constant hZ hI
  set d := 2 * rG r - rt r * rGt r
  set s := Real.sqrt pK with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hK
  have hss : s * s = pK := Real.mul_self_sqrt hK.le
  have hδ : 0 < jk - r := sub_pos.mpr hr.2
  -- `d < 2√K z`
  have h1 : 4 * pK / (3 * jk) * (jk - r) < 2 * s * ((jk - r) / (jk * (1 + pc))) := by
    rw [← hss]
    have : 4 * (s * s) / (3 * jk) * (jk - r) = 2 * s * ((jk - r) / (jk * (1 + pc))) *
        (2 * s * (1 + pc) / 3) := by field_simp; ring
    rw [this]
    have hpos : 0 < 2 * s * ((jk - r) / (jk * (1 + pc))) := by positivity
    have : 2 * s * (1 + pc) / 3 < 1 := by rw [div_lt_one (by norm_num)]; linarith
    nlinarith
  have h2 : d < 2 * s * rz r := by
    calc d ≤ _ := hd1
      _ < _ := h1
      _ < 2 * s * rz r := by gcongr
  have h3 : d ^ 2 < 4 * pK * rz r ^ 2 := by
    rw [← hss]; nlinarith
  nlinarith


section


/-- **Proposition 6.6 (the quadratic profile estimate)**: `g² + z² < K` on `(0, k)`. -/
theorem quadratic_estimate : ∀ r ∈ Ioo 0 jk, rg r ^ 2 + rz r ^ 2 < pK :=
  quadratic_estimate_of extZeros_holds (rz_hasDerivAt_neg extZeros_holds extIntegral_holds)
    (fun _ hr => phase_estimate extZeros_holds extIntegral_holds hr)

/-- **Proposition 7.7 (a lower bound for `z`)**: `z > (k - r)/(k(1 + c))` on `(0, k)`. -/
theorem z_lower_bound : ∀ r ∈ Ioo 0 jk, (jk - r) / (jk * (1 + pc)) < rz r :=
  z_lower_bound_of extZeros_holds extIntegral_holds

/-- **Corollaries 8.9 and 8.11 (bounds for `d`)**: `0 < d ≤ (4K/3k)(k - r)` on `(0, k)`, where
`d = 2G - tG_t`. -/
theorem d_bounds : ∀ r ∈ Ioo 0 jk, 0 < 2 * rG r - rt r * rGt r ∧
    2 * rG r - rt r * rGt r ≤ 4 * pK / (3 * jk) * (jk - r) :=
  d_bounds_of_tail fun _ hr => tail_ratio extZeros_holds extProduct_holds hr

/-- **Proposition 8.13**: the coupling estimate `d² + 4Kg² ≤ 4K²` on `(0, k)`. -/
theorem remaining_positivity_of_estimates : RemainingPositivity :=
  remaining_positivity_of extZeros_holds extIntegral_holds quadratic_estimate z_lower_bound
    d_bounds

end

end Buckling
end
end ChunkedSource086
/- END SOURCE 086 -/

/- BEGIN SOURCE 087: RequestProject/Sobolev/Embedding.lean -/
section ChunkedSource087

/-!
# The planar Sobolev embedding on test functions (External theorem E9, proved)

For every `φ ∈ C_c^∞(ℝ²)` and every point `p`,
`φ(p)² ≤ ∫ φ² + ∫ (∂₁φ)² + ∫ (∂₂φ)² + ∫ (∂₂∂₁φ)²`,
hence `sup |φ| ≤ ‖φ‖_{H²}`.  This proves the hypothesis `ExtEmbedding` (with `C = 1`),
which is therefore no longer assumed.

Proof: write `p = (a, b)` in coordinates.  By the fundamental theorem of calculus in the
first variable, `φ(a,b)² ≤ ∫_ℝ |∂_s(φ²)(s,b)| ds`, and, in the second variable,
`|∂_s(φ²)(s,b)| ≤ ∫_ℝ |∂_t∂_s(φ²)(s,t)| dt`.  By Fubini, the result is bounded by
`∫_{ℝ²} |2(∂₂φ ∂₁φ + φ ∂₂∂₁φ)|`, and `2|xy| ≤ x² + y²` finishes the proof.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology

namespace Buckling

/-- One-dimensional estimate: a `C¹` function vanishing for `|t| > ρ` satisfies
`|g(b)| ≤ ∫ |g'|`. -/
lemma abs_le_integral_abs_deriv {g g' : ℝ → ℝ} (hg : ∀ t, HasDerivAt g (g' t) t)
    (hg'c : Continuous g') (ρ : ℝ) (hz : ∀ t, ρ < |t| → g t = 0)
    (hz' : ∀ t, ρ < |t| → g' t = 0) (b : ℝ) : |g b| ≤ ∫ t, |g' t| := by
  set c : ℝ := -(|b| + |ρ| + 1) with hc
  have hcb : c ≤ b := by
    have := neg_abs_le b; have := abs_nonneg ρ; rw [hc]; linarith
  have hgc : g c = 0 := hz c (by
    rw [hc, abs_neg, abs_of_pos (by positivity)]; have := le_abs_self ρ
    have := abs_nonneg b; linarith)
  have hint : IntervalIntegrable g' volume c b := hg'c.intervalIntegrable c b
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hg t) hint
  rw [hgc, sub_zero] at hftc
  have hcs : HasCompactSupport (fun t => |g' t|) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -|ρ|) (b := |ρ|)) fun t ht => ?_
    have : ρ < |t| := by
      by_contra h
      push_neg at h
      exact ht ⟨by linarith [abs_le.mp (h.trans (le_abs_self ρ))],
        (le_abs_self t).trans (h.trans (le_abs_self ρ))⟩
    simp [hz' t this]
  have hI : Integrable (fun t => |g' t|) := hg'c.abs.integrable_of_hasCompactSupport hcs
  calc |g b| = |∫ t in c..b, g' t| := by rw [hftc]
    _ ≤ ∫ t in c..b, |g' t| := intervalIntegral.abs_integral_le_integral_abs hcb
    _ = ∫ t in Ioc c b, |g' t| := intervalIntegral.integral_of_le hcb
    _ ≤ ∫ t, |g' t| := setIntegral_le_integral hI (Eventually.of_forall fun t => abs_nonneg _)

/-- Derivative along a line. -/
lemma hasDerivAt_comp_line {ψ : Plane → ℝ} (hψ : Differentiable ℝ ψ) (p v : Plane) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ψ (p + t • v)) (fderiv ℝ ψ (p + t • v) v) t := by
  have h1 : HasDerivAt (fun t : ℝ => p + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  exact (hψ (p + t • v)).hasFDerivAt.comp_hasDerivAt t h1

/-- The coordinate map `(s, t) ↦ s e₁ + t e₂`. -/
lemma prodToPlane_eq (s t : ℝ) :
    prodToPlane (s, t) = s • EuclideanSpace.single 0 1 + t • EuclideanSpace.single 1 1 :=
  prodToPlane_apply (s, t)

lemma abs_le_norm_prodToPlane_fst (s t : ℝ) : |s| ≤ ‖prodToPlane (s, t)‖ := by
  have h := PiLp.norm_apply_le (p := 2) (prodToPlane (s, t)) 0
  rw [prodToPlane_eq] at h ⊢
  simpa using h

lemma abs_le_norm_prodToPlane_snd (s t : ℝ) : |t| ≤ ‖prodToPlane (s, t)‖ := by
  have h := PiLp.norm_apply_le (p := 2) (prodToPlane (s, t)) 1
  rw [prodToPlane_eq] at h ⊢
  simpa using h

/-- **The pointwise `H²` bound** for test functions on the plane. -/
theorem sq_le_of_isTestFn {φ : Plane → ℝ} (hφ : IsTestFn Set.univ φ) (p : Plane) :
    φ p ^ 2 ≤ (∫ x, φ x ^ 2) + (∫ x, pderiv 0 φ x ^ 2) + (∫ x, pderiv 1 φ x ^ 2)
      + ∫ x, pderiv 1 (pderiv 0 φ) x ^ 2 := by
  -- a ball containing the support
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, tsupport φ ⊆ Metric.closedBall 0 ρ :=
    hφ.2.1.isCompact.isBounded.subset_closedBall 0
  have hB : IsTestFn (Metric.closedBall 0 ρ) φ := ⟨hφ.1, hφ.2.1, hρ⟩
  have h0 := hB.pderiv 0
  have h1 := hB.pderiv 1
  have h10 := h0.pderiv 1
  have hdiff : ∀ {ψ : Plane → ℝ}, IsTestFn (Metric.closedBall 0 ρ) ψ → Differentiable ℝ ψ :=
    fun h => h.1.differentiable (by simp)
  have hcont : ∀ {ψ : Plane → ℝ}, IsTestFn (Metric.closedBall 0 ρ) ψ → Continuous ψ :=
    fun h => h.1.continuous
  have hvan : ∀ {ψ : Plane → ℝ}, IsTestFn (Metric.closedBall 0 ρ) ψ → ∀ s t : ℝ,
      (ρ < |s| ∨ ρ < |t|) → ψ (prodToPlane (s, t)) = 0 := by
    intro ψ h s t hst
    apply h.eq_zero_of_notMem
    rw [Metric.mem_closedBall, dist_zero_right, not_le]
    rcases hst with hs | ht
    · exact hs.trans_le (abs_le_norm_prodToPlane_fst s t)
    · exact ht.trans_le (abs_le_norm_prodToPlane_snd s t)
  -- the integrand
  set H : Plane → ℝ := fun x =>
    2 * (pderiv 1 φ x * pderiv 0 φ x + φ x * pderiv 1 (pderiv 0 φ) x) with hH
  have hHc : Continuous H := by
    simp only [hH]
    exact continuous_const.mul (((hcont h1).mul (hcont h0)).add ((hcont hB).mul (hcont h10)))
  have hHvan : ∀ s t : ℝ, (ρ < |s| ∨ ρ < |t|) → H (prodToPlane (s, t)) = 0 := by
    intro s t hst
    simp only [hH, hvan hB s t hst, hvan h0 s t hst, hvan h1 s t hst, hvan h10 s t hst]
    ring
  have hHcs : HasCompactSupport H := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Plane) ρ) fun x hx => ?_
    simp only [hH, h1.eq_zero_of_notMem hx, h0.eq_zero_of_notMem hx, hB.eq_zero_of_notMem hx]
    ring
  have hHI : Integrable (fun x => |H x|) := hHc.abs.integrable_of_hasCompactSupport hHcs.abs
  have hPeq : (fun q : ℝ × ℝ => prodToPlane q) =
      fun q => q.1 • EuclideanSpace.single 0 1 + q.2 • EuclideanSpace.single 1 1 :=
    funext prodToPlane_apply
  have hPc : Continuous (fun q : ℝ × ℝ => prodToPlane q) := by rw [hPeq]; fun_prop
  have hlineS : ∀ s t : ℝ, prodToPlane (s, t) =
      t • EuclideanSpace.single 1 1 + s • EuclideanSpace.single 0 1 := by
    intro s t; rw [prodToPlane_eq, add_comm]
  have hlineT : ∀ s t : ℝ, prodToPlane (s, t) =
      s • EuclideanSpace.single 0 1 + t • EuclideanSpace.single 1 1 := prodToPlane_eq
  -- derivatives along coordinate lines
  have hdS : ∀ {ψ : Plane → ℝ}, IsTestFn (Metric.closedBall 0 ρ) ψ → ∀ s t : ℝ,
      HasDerivAt (fun s => ψ (prodToPlane (s, t))) (pderiv 0 ψ (prodToPlane (s, t))) s := by
    intro ψ h s t
    have := hasDerivAt_comp_line (hdiff h) (t • EuclideanSpace.single 1 1)
      (EuclideanSpace.single 0 1) s
    simp only [← hlineS] at this
    exact this
  have hdT : ∀ {ψ : Plane → ℝ}, IsTestFn (Metric.closedBall 0 ρ) ψ → ∀ s t : ℝ,
      HasDerivAt (fun t => ψ (prodToPlane (s, t))) (pderiv 1 ψ (prodToPlane (s, t))) t := by
    intro ψ h s t
    have := hasDerivAt_comp_line (hdiff h) (s • EuclideanSpace.single 0 1)
      (EuclideanSpace.single 1 1) t
    simp only [← hlineT] at this
    exact this
  -- step B: the inner estimate in the second variable
  have hstepB : ∀ s b : ℝ,
      |2 * (φ (prodToPlane (s, b)) * pderiv 0 φ (prodToPlane (s, b)))| ≤
        ∫ t, |H (prodToPlane (s, t))| := by
    intro s b
    refine abs_le_integral_abs_deriv (g := fun t =>
        2 * (φ (prodToPlane (s, t)) * pderiv 0 φ (prodToPlane (s, t))))
      (g' := fun t => H (prodToPlane (s, t))) (fun t => ?_)
      (hHc.comp (hPc.comp (Continuous.prodMk_right s))) ρ
      (fun t ht => by simp [hvan hB s t (Or.inr ht)])
      (fun t ht => hHvan s t (Or.inr ht)) b
    have := ((hdT hB s t).mul (hdT h0 s t)).const_mul 2
    convert this using 1
  -- step A: the outer estimate in the first variable
  obtain ⟨⟨a, b⟩, rfl⟩ : ∃ q, prodToPlane q = p := ⟨prodToPlane.symm p, by simp⟩
  have hstepA : |φ (prodToPlane (a, b)) * φ (prodToPlane (a, b))| ≤
      ∫ s, |2 * (φ (prodToPlane (s, b)) * pderiv 0 φ (prodToPlane (s, b)))| := by
    refine abs_le_integral_abs_deriv (g := fun s => φ (prodToPlane (s, b)) * φ (prodToPlane (s, b)))
      (g' := fun s => 2 * (φ (prodToPlane (s, b)) * pderiv 0 φ (prodToPlane (s, b))))
      (fun s => ?_) ?_ ρ
      (fun s hs => by simp [hvan hB s b (Or.inl hs)])
      (fun s hs => by simp [hvan hB s b (Or.inl hs)]) a
    · have := (hdS hB s b).mul (hdS hB s b)
      convert this using 1; ring
    · exact continuous_const.mul (((hcont hB).comp (hPc.comp (Continuous.prodMk_left b))).mul
        ((hcont h0).comp (hPc.comp (Continuous.prodMk_left b))))
  -- Fubini
  have hHP : Integrable (fun q : ℝ × ℝ => |H (prodToPlane q)|) := by
    have := (prodToPlane_mp.integrable_comp_emb prodToPlane.measurableEmbedding).mpr hHI
    exact this
  have hfub : ∫ s, ∫ t, |H (prodToPlane (s, t))| = ∫ x, |H x| := by
    rw [← prodToPlane_mp.integral_comp' (fun x => |H x|)]
    exact (integral_prod _ hHP).symm
  have hAB : |φ (prodToPlane (a, b)) * φ (prodToPlane (a, b))| ≤ ∫ x, |H x| := by
    refine hstepA.trans ?_
    rw [← hfub]
    refine integral_mono ?_ hHP.integral_prod_left fun s => hstepB s b
    have hcs : HasCompactSupport (fun s =>
        |2 * (φ (prodToPlane (s, b)) * pderiv 0 φ (prodToPlane (s, b)))|) := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -|ρ|) (b := |ρ|)) fun s hs => ?_
      have : ρ < |s| := by
        by_contra h
        push_neg at h
        exact hs ⟨by linarith [abs_le.mp (h.trans (le_abs_self ρ))],
          (le_abs_self s).trans (h.trans (le_abs_self ρ))⟩
      simp [hvan hB s b (Or.inl this)]
    refine Continuous.integrable_of_hasCompactSupport ?_ hcs
    exact (continuous_const.mul (((hcont hB).comp (hPc.comp (Continuous.prodMk_left b))).mul
        ((hcont h0).comp (hPc.comp (Continuous.prodMk_left b))))).abs
  -- step C: pointwise AM-GM and integration
  have hpt : ∀ x, |H x| ≤ φ x ^ 2 + pderiv 0 φ x ^ 2 + pderiv 1 φ x ^ 2
      + pderiv 1 (pderiv 0 φ) x ^ 2 := by
    intro x
    simp only [hH]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (pderiv 1 φ x + pderiv 0 φ x),
      sq_nonneg (pderiv 1 φ x - pderiv 0 φ x), sq_nonneg (φ x + pderiv 1 (pderiv 0 φ) x),
      sq_nonneg (φ x - pderiv 1 (pderiv 0 φ) x)]
  have iB := hB.integrable_sq
  have i0 := h0.integrable_sq
  have i1 := h1.integrable_sq
  have i10 := h10.integrable_sq
  have hC : ∫ x, |H x| ≤ (∫ x, φ x ^ 2) + (∫ x, pderiv 0 φ x ^ 2) + (∫ x, pderiv 1 φ x ^ 2)
      + ∫ x, pderiv 1 (pderiv 0 φ) x ^ 2 := by
    have hsum : Integrable (fun x => φ x ^ 2 + pderiv 0 φ x ^ 2 + pderiv 1 φ x ^ 2
        + pderiv 1 (pderiv 0 φ) x ^ 2) := ((iB.add i0).add i1).add i10
    refine (integral_mono hHI hsum hpt).trans_eq ?_
    have j2 : Integrable (fun x => φ x ^ 2 + pderiv 0 φ x ^ 2) := iB.add i0
    have j3 : Integrable (fun x => φ x ^ 2 + pderiv 0 φ x ^ 2 + pderiv 1 φ x ^ 2) := j2.add i1
    rw [integral_add j3 i10, integral_add j2 i1, integral_add iB i0]
  have : φ (prodToPlane (a, b)) ^ 2 = |φ (prodToPlane (a, b)) * φ (prodToPlane (a, b))| := by
    rw [abs_mul_self, sq]
  rw [this]
  exact hAB.trans hC

/-- **External theorem E9, proved** (with constant `C = 1`): for every `φ ∈ C_c^∞(ℝ²)`,
`sup |φ| ≤ ‖φ‖_{H²}`.  Hence `ExtEmbedding` holds. -/
theorem extEmbedding_holds : ExtEmbedding := by
  refine ⟨1, fun φ hφ x => ?_⟩
  rw [one_mul]
  have h := sq_le_of_isTestFn hφ x
  have e0 := hφ.integral_sq
  have e1 := (hφ.pderiv 0).integral_sq
  have e2 := (hφ.pderiv 1).integral_sq
  have e3 := ((hφ.pderiv 0).pderiv 1).integral_sq
  have hle : φ x ^ 2 ≤ ‖hφ.toL2‖ ^ 2 + ∑ i, ‖(hφ.pderiv i).toL2‖ ^ 2
      + ∑ i, ∑ j, ‖((hφ.pderiv j).pderiv i).toL2‖ ^ 2 := by
    simp only [Fin.sum_univ_two]
    rw [e0, e1, e2, e3] at *
    nlinarith [sq_nonneg ‖((hφ.pderiv 0).pderiv 0).toL2‖, sq_nonneg ‖((hφ.pderiv 1).pderiv 0).toL2‖,
      sq_nonneg ‖((hφ.pderiv 1).pderiv 1).toL2‖]
  calc |φ x| = Real.sqrt (φ x ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt hle

end Buckling
end
end ChunkedSource087
/- END SOURCE 087 -/

