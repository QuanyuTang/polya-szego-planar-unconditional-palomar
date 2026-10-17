module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/
public import RequestProject.Core1

/- CONDITIONAL, UNCOMPILED structural experiment. See README.md. -/

/- BEGIN SOURCE 031: RequestProject/Bessel/ZerosE1.lean -/
section ChunkedSource031

/-!
# Positive zeros of `J₀` and `J₁` (External theorem E1, in the form used)

We prove, for `n ∈ {0, 1}`, that the positive zeros of `J_n` form an unbounded strictly
increasing sequence of simple zeros enumerated by `besselZero n`, and that the zeros of
`J₀` and `J₁` interlace: `j_{0,k} < j_{1,k} < j_{0,k+1}`.

* `J_n` is real analytic (it is the restriction of the entire function `besselJC n`), so its
  zeros are isolated;
* `E = J₀² + J₁²` satisfies `E' = -2 J₁²/x ≤ 0`, so `J₀` and `J₁` have no common positive
  zero; hence all positive zeros of `J₀` and `J₁` are simple;
* `u = √x J₀` solves `u'' = -(1 + 1/(4x²)) u`, so by Sturm comparison with `sin (x - a)`
  every interval `[a, a + π]` (`a > 0`) contains a zero of `J₀`;
* Rolle's theorem with `J₀' = -J₁` and `(x J₁)' = x J₀` gives the interlacing.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-! ### Analyticity and isolated zeros -/

lemma analyticAt_besselJ (n : ℕ) (x : ℝ) : AnalyticAt ℝ (besselJ n) x := by
  have h1 : AnalyticAt ℝ (besselJC n) (Complex.ofRealCLM x) :=
    ((differentiable_besselJC n).analyticAt (x : ℂ)).restrictScalars
  have h2 : AnalyticAt ℝ (fun y : ℝ => Complex.reCLM (besselJC n (Complex.ofRealCLM y))) x :=
    (Complex.reCLM.analyticAt _).comp (h1.comp (Complex.ofRealCLM.analyticAt x))
  convert h2 using 1
  ext y; simp [besselJC_ofReal]

lemma besselJ_one_one_pos : 0 < besselJ 1 1 := besselJ_one_pos_small 1 one_pos (by norm_num)

lemma besselJ_not_eqOn_zero (n : ℕ) (hn : n ≤ 1) : ¬ ∀ x, besselJ n x = 0 := by
  intro h
  interval_cases n
  · have := h 0; rw [besselJ_zero_at_zero] at this; norm_num at this
  · have := h 1; linarith [besselJ_one_one_pos]

/-- Zeros of `J_n` (`n ≤ 1`) are isolated. -/
lemma besselJ_eventually_ne_zero (n : ℕ) (hn : n ≤ 1) (x₀ : ℝ) :
    ∀ᶠ x in 𝓝[≠] x₀, besselJ n x ≠ 0 := by
  have hA : AnalyticOnNhd ℝ (besselJ n) univ := fun x _ => analyticAt_besselJ n x
  by_contra h
  rw [not_eventually] at h
  simp only [ne_eq, not_not] at h
  have := hA.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (mem_univ x₀) h
  exact besselJ_not_eqOn_zero n hn fun x => this (mem_univ x)

/-- No zeros of `J_n` (`n ≤ 1`) immediately to the right of `0`. -/
lemma besselJ_eventually_ne_zero_right (n : ℕ) (hn : n ≤ 1) :
    ∀ᶠ x in 𝓝[>] (0 : ℝ), besselJ n x ≠ 0 := by
  interval_cases n
  · exact nhdsWithin_le_nhds ((continuous_besselJ 0).continuousAt.eventually_ne
      (by rw [besselJ_zero_at_zero]; norm_num))
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 28 / 10 by norm_num)] with x hx
    exact (besselJ_one_pos_small x hx.1 hx.2.le).ne'

/-! ### No common positive zeros -/

lemma besselJ_zero_one_no_common_zero (x : ℝ) (hx : 0 < x) :
    ¬ (besselJ 0 x = 0 ∧ besselJ 1 x = 0) := by
  rintro ⟨h0, h1⟩
  set E : ℝ → ℝ := fun y => besselJ 0 y ^ 2 + besselJ 1 y ^ 2 with hE
  have hEd : ∀ y, 0 < y → HasDerivAt E (-(2 * besselJ 1 y ^ 2 / y)) y := by
    intro y hy
    have := ((hasDerivAt_besselJ_zero y).pow 2).add ((hasDerivAt_besselJ_one y hy.ne').pow 2)
    convert this using 1
    field_simp
    ring
  have hanti : AntitoneOn E (Ici x) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici x)
    · exact fun y hy => (hEd y (hx.trans_le hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      exact (hEd y (hx.trans hy)).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hEd y (hx.trans hy)).deriv]
      have : 0 < y := hx.trans hy
      have : 0 ≤ 2 * besselJ 1 y ^ 2 / y := by positivity
      linarith
  have hzero : ∀ y, x < y → besselJ 0 y = 0 := by
    intro y hy
    have h1' := hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hy.le) hy.le
    have hEx : E x = 0 := by simp [hE, h0, h1]
    rw [hEx] at h1'
    have : besselJ 0 y ^ 2 ≤ 0 := by
      have := sq_nonneg (besselJ 1 y)
      simp only [hE] at h1'
      linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm this (sq_nonneg _))
  obtain ⟨y, hy1, hy2⟩ := ((besselJ_eventually_ne_zero 0 (by norm_num) (x + 1)).and
    (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show x < x + 1 by linarith)))).exists
  exact hy1 (hzero y hy2)

/-! ### Infinitely many zeros of `J₀` -/

/-- `u(r) = √r J₀(r)` satisfies `u'' + (1 + 1/(4r²)) u = 0` for `r > 0`. -/
lemma sqrt_besselJ_zero_ode (r : ℝ) (hr : 0 < r) :
    HasDerivAt (fun s => Real.sqrt s * besselJ 0 s)
        (besselJ 0 r / (2 * Real.sqrt r) - Real.sqrt r * besselJ 1 r) r ∧
    HasDerivAt (fun s => besselJ 0 s / (2 * Real.sqrt s) - Real.sqrt s * besselJ 1 s)
        (-(1 + 1 / (4 * r ^ 2)) * (Real.sqrt r * besselJ 0 r)) r := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hsd : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt r)) r := Real.hasDerivAt_sqrt hr.ne'
  have hJ1 := hasDerivAt_besselJ_one r hr.ne'
  have hJ0 := hasDerivAt_besselJ_zero r
  constructor
  · convert hsd.mul hJ0 using 1; ring
  · have e1 := hJ0.div ((hsd.const_mul 2)) (by positivity)
    have e2 := hsd.mul hJ1
    convert e1.sub e2 using 1
    field_simp
    rw [show Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 by ring, hsq]
    ring

/-- Sturm comparison with `sin (r - a)`, positive case. -/
lemma sturm_zero_aux {u u' Q : ℝ → ℝ} {a : ℝ}
    (hu : ∀ r ∈ Icc a (a + π), HasDerivAt u (u' r) r)
    (hu' : ∀ r ∈ Icc a (a + π), HasDerivAt u' (-(Q r) * u r) r)
    (hQ : ∀ r ∈ Ioo a (a + π), 1 < Q r) (hpos : ∀ r ∈ Icc a (a + π), 0 < u r) : False := by
  set W : ℝ → ℝ := fun r => u' r * Real.sin (r - a) - u r * Real.cos (r - a) with hW
  have hWd : ∀ r ∈ Icc a (a + π), HasDerivAt W ((1 - Q r) * u r * Real.sin (r - a)) r := by
    intro r hr
    have hs : HasDerivAt (fun r => Real.sin (r - a)) (Real.cos (r - a)) r := by
      simpa using ((hasDerivAt_id r).sub_const a).sin
    have hc : HasDerivAt (fun r => Real.cos (r - a)) (-Real.sin (r - a)) r := by
      simpa using ((hasDerivAt_id r).sub_const a).cos
    have := ((hu' r hr).mul hs).sub ((hu r hr).mul hc)
    convert this using 1; ring
  have hab : a < a + π := by linarith [pi_pos]
  have hmono : StrictAntiOn W (Icc a (a + π)) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
      (fun r hr => (hWd r hr).continuousAt.continuousWithinAt)
    intro r hr
    rw [interior_Icc] at hr
    rw [(hWd r (Ioo_subset_Icc_self hr)).deriv]
    have h1 := hQ r hr
    have h2 := hpos r (Ioo_subset_Icc_self hr)
    have h3 : 0 < Real.sin (r - a) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hr.1]) (by linarith [hr.2])
    have : (1 - Q r) * u r < 0 := mul_neg_of_neg_of_pos (by linarith) h2
    exact mul_neg_of_neg_of_pos this h3
  have h := hmono (left_mem_Icc.2 hab.le) (right_mem_Icc.2 hab.le) hab
  have hWa : W a = -u a := by simp [hW]
  have hWb : W (a + π) = u (a + π) := by simp [hW]
  rw [hWa, hWb] at h
  linarith [hpos a (left_mem_Icc.2 hab.le), hpos (a + π) (right_mem_Icc.2 hab.le)]

/-- Sturm comparison: a solution of `u'' = -Q u` with `Q > 1` vanishes in every
interval of length `π`. -/
lemma sturm_zero {u u' Q : ℝ → ℝ} {a : ℝ}
    (hu : ∀ r ∈ Icc a (a + π), HasDerivAt u (u' r) r)
    (hu' : ∀ r ∈ Icc a (a + π), HasDerivAt u' (-(Q r) * u r) r)
    (hQ : ∀ r ∈ Ioo a (a + π), 1 < Q r) : ∃ r ∈ Icc a (a + π), u r = 0 := by
  by_contra hne
  push_neg at hne
  have hab : a ≤ a + π := by linarith [pi_pos]
  have hcont : ContinuousOn u (Icc a (a + π)) :=
    fun r hr => (hu r hr).continuousAt.continuousWithinAt
  rcases lt_or_gt_of_ne (hne a (left_mem_Icc.2 hab)) with ha | ha
  · have hneg : ∀ r ∈ Icc a (a + π), u r < 0 := by
      intro r hr
      by_contra h
      push_neg at h
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hr.1
        (hcont.mono (Icc_subset_Icc le_rfl hr.2)) ⟨ha.le, h⟩
      exact hne c ⟨hc.1, hc.2.trans hr.2⟩ hc0
    exact sturm_zero_aux (u := fun r => -u r) (u' := fun r => -u' r) (Q := Q)
      (fun r hr => (hu r hr).fun_neg)
      (fun r hr => by simpa using! (hu' r hr).fun_neg) hQ
      (fun r hr => neg_pos.2 (hneg r hr))
  · have hpos : ∀ r ∈ Icc a (a + π), 0 < u r := by
      intro r hr
      by_contra h
      push_neg at h
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hr.1
        (hcont.mono (Icc_subset_Icc le_rfl hr.2)) ⟨h, ha.le⟩
      exact hne c ⟨hc.1, hc.2.trans hr.2⟩ hc0
    exact sturm_zero_aux hu hu' hQ hpos

lemma exists_besselJ_zero_zero_gt (a : ℝ) : ∃ x, a < x ∧ besselJ 0 x = 0 := by
  set b := max a 0 + 1 with hb
  have hb0 : 0 < b := by positivity
  have hpos : ∀ r ∈ Icc b (b + π), 0 < r := fun r hr => hb0.trans_le hr.1
  obtain ⟨r, hr, hr0⟩ := sturm_zero (u := fun s => Real.sqrt s * besselJ 0 s)
    (u' := fun s => besselJ 0 s / (2 * Real.sqrt s) - Real.sqrt s * besselJ 1 s)
    (Q := fun s => 1 + 1 / (4 * s ^ 2)) (a := b)
    (fun r hr => (sqrt_besselJ_zero_ode r (hpos r hr)).1)
    (fun r hr => (sqrt_besselJ_zero_ode r (hpos r hr)).2)
    (fun r hr => by
      have : 0 < r := hpos r (Ioo_subset_Icc_self hr)
      have : 0 < 1 / (4 * r ^ 2) := by positivity
      linarith)
  refine ⟨r, ?_, ?_⟩
  · have : a < b := by rw [hb]; linarith [le_max_left a 0]
    linarith [hr.1]
  · rcases mul_eq_zero.1 hr0 with h | h
    · exact absurd h (Real.sqrt_pos.2 (hpos r hr)).ne'
    · exact h

/-! ### Rolle -/

/-- `(x J₁(x))' = x J₀(x)`. -/
lemma hasDerivAt_mul_besselJ_one (x : ℝ) :
    HasDerivAt (fun y => y * besselJ 1 y) (x * besselJ 0 x) x := by
  have h := (hasDerivAt_id x).fun_mul (hasDerivAt_besselJ_succ 0 x)
  have hr := besselJ_recurrence 0 x
  push_cast at hr
  have hD :
      (1 : ℝ) * besselJ (0 + 1) x +
          x * ((besselJ 0 x - besselJ (0 + 2) x) / 2) =
        x * besselJ 0 x := by
    nlinarith [hr]
  simpa only [id_eq] using! (h.congr_deriv hD)

lemma exists_besselJ_one_zero_between {a b : ℝ} (hab : a < b) (ha : besselJ 0 a = 0)
    (hb : besselJ 0 b = 0) : ∃ c ∈ Ioo a b, besselJ 1 c = 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_zero hab (continuous_besselJ 0).continuousOn
    (ha.trans hb.symm) (fun x _ => hasDerivAt_besselJ_zero x)
  exact ⟨c, hc, neg_eq_zero.1 h⟩

lemma exists_besselJ_zero_zero_between {a b : ℝ} (ha0 : 0 ≤ a) (hab : a < b)
    (ha : a * besselJ 1 a = 0) (hb : besselJ 1 b = 0) : ∃ c ∈ Ioo a b, besselJ 0 c = 0 := by
  obtain ⟨c, hc, h⟩ := exists_hasDerivAt_eq_zero hab
    ((continuous_id.mul (continuous_besselJ 1)).continuousOn)
    (show a * besselJ 1 a = b * besselJ 1 b by rw [ha, hb, mul_zero])
    (fun x _ => hasDerivAt_mul_besselJ_one x)
  refine ⟨c, hc, ?_⟩
  rcases mul_eq_zero.1 h with h | h
  · exact absurd h (ha0.trans_lt hc.1).ne'
  · exact h

lemma exists_besselJ_one_zero_gt (a : ℝ) : ∃ x, a < x ∧ besselJ 1 x = 0 := by
  obtain ⟨x, hx, hx0⟩ := exists_besselJ_zero_zero_gt a
  obtain ⟨y, hy, hy0⟩ := exists_besselJ_zero_zero_gt x
  obtain ⟨c, hc, hc0⟩ := exists_besselJ_one_zero_between hy hx0 hy0
  exact ⟨c, hx.trans hc.1, hc0⟩

/-! ### Enumeration of the zeros -/

/-- The infimum of the zeros of `f` beyond `c` is itself such a zero, and there are no zeros
strictly in between, provided zeros do not accumulate at `c` from the right. -/
lemma sInf_zeros_spec {f : ℝ → ℝ} (hf : Continuous f) {c : ℝ}
    (hiso : ∀ᶠ x in 𝓝[>] c, f x ≠ 0) (hunb : ∃ x, c < x ∧ f x = 0) :
    sInf {x | c < x ∧ f x = 0} ∈ {x | c < x ∧ f x = 0} ∧
    ∀ y ∈ Ioo c (sInf {x | c < x ∧ f x = 0}), f y ≠ 0 := by
  set S := {x | c < x ∧ f x = 0} with hS
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hiso
  have hT : S = Ici u ∩ f ⁻¹' {0} := by
    ext x
    simp only [hS, mem_setOf_eq, mem_inter_iff, mem_Ici, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hcx, hfx⟩
      refine ⟨?_, hfx⟩
      by_contra h
      push_neg at h
      exact hsub ⟨hcx, h⟩ hfx
    · rintro ⟨hux, hfx⟩
      exact ⟨hu.trans_le hux, hfx⟩
  have hclosed : IsClosed S := by
    rw [hT]; exact isClosed_Ici.inter (isClosed_singleton.preimage hf)
  have hmem : sInf S ∈ S := hclosed.csInf_mem hunb ⟨c, fun x hx => hx.1.le⟩
  refine ⟨hmem, fun y hy hfy => ?_⟩
  have := csInf_le ⟨c, fun x hx => hx.1.le⟩ (show y ∈ S from ⟨hy.1, hfy⟩)
  linarith [hy.2]

/-- Enumeration properties of `besselZero n`, from isolation and unboundedness of the zeros. -/
lemma besselZero_props (n : ℕ)
    (hiso : ∀ x₀ : ℝ, 0 < x₀ → ∀ᶠ x in 𝓝[≠] x₀, besselJ n x ≠ 0)
    (hiso0 : ∀ᶠ x in 𝓝[>] (0 : ℝ), besselJ n x ≠ 0)
    (hunb : ∀ a, ∃ x, a < x ∧ besselJ n x = 0) :
    StrictMono (besselZero n) ∧ Tendsto (besselZero n) atTop atTop ∧
    (∀ k, 1 ≤ k → besselJ n (besselZero n k) = 0) ∧
    (∀ x, 0 < x → besselJ n x = 0 → ∃ k, 1 ≤ k ∧ besselZero n k = x) := by
  have hisoR : ∀ c : ℝ, 0 ≤ c → ∀ᶠ x in 𝓝[>] c, besselJ n x ≠ 0 := by
    intro c hc
    rcases hc.eq_or_lt with rfl | hc
    · exact hiso0
    · exact nhdsWithin_mono _ (fun y hy => ne_of_gt hy) (hiso c hc)
  have hstep : ∀ k, 0 ≤ besselZero n k →
      besselZero n k < besselZero n (k + 1) ∧ besselJ n (besselZero n (k + 1)) = 0 ∧
      ∀ y ∈ Ioo (besselZero n k) (besselZero n (k + 1)), besselJ n y ≠ 0 := by
    intro k hk
    obtain ⟨⟨h1, h2⟩, h3⟩ := sInf_zeros_spec (continuous_besselJ n) (hisoR _ hk) (hunb _)
    exact ⟨h1, h2, h3⟩
  have hnn : ∀ k, 0 ≤ besselZero n k := by
    intro k
    induction k with
    | zero => simp [besselZero]
    | succ k ih => exact ih.trans (hstep k ih).1.le
  have hmono : StrictMono (besselZero n) :=
    strictMono_nat_of_lt_succ fun k => (hstep k (hnn k)).1
  have hzero : ∀ k, 1 ≤ k → besselJ n (besselZero n k) = 0 := by
    intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    exact (hstep j (hnn j)).2.1
  have htend : Tendsto (besselZero n) atTop atTop := by
    refine hmono.monotone.tendsto_atTop_atTop fun b => ?_
    by_contra hb
    push_neg at hb
    have hbdd : BddAbove (range (besselZero n)) := ⟨b, by rintro _ ⟨a, rfl⟩; exact (hb a).le⟩
    set L := ⨆ k, besselZero n k
    have hL := tendsto_atTop_ciSup hmono.monotone hbdd
    have hlt : ∀ k, besselZero n k < L := fun k =>
      (hmono (Nat.lt_succ_self k)).trans_le (le_ciSup hbdd (k + 1))
    have hL0 : 0 < L := (hnn 0).trans_lt (hlt 0)
    have hL' : Tendsto (besselZero n) atTop (𝓝[≠] L) :=
      tendsto_nhdsWithin_iff.2 ⟨hL, Eventually.of_forall fun k => (hlt k).ne⟩
    obtain ⟨k, hk1, hk2⟩ := ((hL'.eventually (hiso L hL0)).and (eventually_ge_atTop 1)).exists
    exact hk1 (hzero k hk2)
  refine ⟨hmono, htend, hzero, fun x hx hfx => ?_⟩
  have hex : ∃ k, x ≤ besselZero n k := (htend.eventually (eventually_ge_atTop x)).exists
  classical
  set k := Nat.find hex with hkdef
  have hk : x ≤ besselZero n k := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hk
    simp [besselZero] at hk
    linarith
  obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjx : besselZero n j < x := by
    have := Nat.find_min hex (show j < k by omega)
    push_neg at this
    exact this
  refine ⟨k, by omega, ?_⟩
  rcases hk.eq_or_lt with h | h
  · exact h.symm
  · exfalso
    rw [hj] at h
    exact (hstep j (hnn j)).2.2 x ⟨hjx, h⟩ hfx

/-- **E1 for `n ∈ {0,1}`.** -/
theorem besselZero_spec (n : ℕ) (hn : n ≤ 1) :
    StrictMono (besselZero n) ∧
    Tendsto (besselZero n) atTop atTop ∧
    (∀ k, 1 ≤ k → besselJ n (besselZero n k) = 0 ∧ deriv (besselJ n) (besselZero n k) ≠ 0) ∧
    (∀ x, 0 < x → besselJ n x = 0 → ∃ k, 1 ≤ k ∧ besselZero n k = x) := by
  have hunb : ∀ a, ∃ x, a < x ∧ besselJ n x = 0 := by
    interval_cases n
    · exact exists_besselJ_zero_zero_gt
    · exact exists_besselJ_one_zero_gt
  obtain ⟨hmono, htend, hzero, hall⟩ := besselZero_props n
    (fun x₀ _ => besselJ_eventually_ne_zero n hn x₀) (besselJ_eventually_ne_zero_right n hn) hunb
  have hpos : ∀ k, 1 ≤ k → 0 < besselZero n k := fun k hk => by
    have := hmono (show 0 < k by omega); simpa [besselZero] using this
  refine ⟨hmono, htend, fun k hk => ⟨hzero k hk, ?_⟩, hall⟩
  have hz := hzero k hk
  have hx := hpos k hk
  have hnc := besselJ_zero_one_no_common_zero _ hx
  interval_cases n
  · rw [deriv_besselJ_zero]
    intro h
    exact hnc ⟨hz, neg_eq_zero.1 h⟩
  · rw [(hasDerivAt_besselJ_one _ hx.ne').deriv, hz, zero_div, sub_zero]
    intro h
    exact hnc ⟨h, hz⟩

/-- **Interlacing** `j_{0,k} < j_{1,k} < j_{0,k+1}`. -/
theorem besselZero_interlace (k : ℕ) (hk : 1 ≤ k) :
    besselZero 0 k < besselZero 1 k ∧ besselZero 1 k < besselZero 0 (k + 1) := by
  have hnn : ∀ n, n ≤ 1 → ∀ j, 0 ≤ besselZero n j := fun n hn j => by
    have := (besselZero_spec n hn).1.monotone (Nat.zero_le j); simpa [besselZero] using this
  have hnext : ∀ n, n ≤ 1 → ∀ j z, besselZero n j < z → besselJ n z = 0 →
      besselZero n (j + 1) ≤ z := by
    intro n hn j z hz hJ
    obtain ⟨hmono, -, -, hall⟩ := besselZero_spec n hn
    obtain ⟨m, -, rfl⟩ := hall z ((hnn n hn j).trans_lt hz) hJ
    exact hmono.monotone (Nat.succ_le_of_lt (hmono.lt_iff_lt.1 hz))
  have hz0 : ∀ j, 1 ≤ j → besselJ 0 (besselZero 0 j) = 0 :=
    fun j hj => ((besselZero_spec 0 (by norm_num)).2.2.1 j hj).1
  have hz1 : ∀ j, besselZero 1 j * besselJ 1 (besselZero 1 j) = 0 := by
    intro j
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [besselZero]
    · rw [((besselZero_spec 1 (by norm_num)).2.2.1 j hj).1, mul_zero]
  have hm0 := (besselZero_spec 0 (by norm_num)).1
  have hm1 := (besselZero_spec 1 (by norm_num)).1
  have key : ∀ j, (besselZero 0 j ≤ besselZero 1 j ∧ besselZero 1 j < besselZero 0 (j + 1)) →
      besselZero 0 (j + 1) < besselZero 1 (j + 1) ∧
      besselZero 1 (j + 1) < besselZero 0 (j + 2) := by
    rintro j ⟨h1, h2⟩
    obtain ⟨c, hc, hc0⟩ := exists_besselJ_zero_zero_between (hnn 1 (by norm_num) j)
      (hm1 (Nat.lt_succ_self j)) (hz1 j)
      (by have := hz1 (j + 1); rcases mul_eq_zero.1 this with h | h
          · exact absurd h (((hnn 1 (by norm_num) j).trans_lt (hm1 (Nat.lt_succ_self j))).ne')
          · exact h)
    have hA := hnext 0 (by norm_num) j c (h1.trans_lt hc.1) hc0
    obtain ⟨d, hd, hd0⟩ := exists_besselJ_one_zero_between (hm0 (Nat.lt_succ_self (j + 1)))
      (hz0 (j + 1) (by omega)) (hz0 (j + 2) (by omega))
    have hB := hnext 1 (by norm_num) j d (h2.trans hd.1) hd0
    exact ⟨hA.trans_lt hc.2, hB.trans_lt hd.2⟩
  have hR : ∀ j, besselZero 0 j ≤ besselZero 1 j ∧ besselZero 1 j < besselZero 0 (j + 1) := by
    intro j
    induction j with
    | zero => exact ⟨by simp [besselZero], by simpa [besselZero] using hm0 (Nat.lt_succ_self 0)⟩
    | succ j ih => exact ⟨(key j ih).1.le, (key j ih).2⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  exact ⟨(key j (hR j)).1, (hR (j + 1)).2⟩

/-- **E1** (in the form used, orders `0` and `1`) holds. -/
theorem extZeros_holds : ExtZeros := fun n hn =>
  ⟨(besselZero_spec n hn).1, (besselZero_spec n hn).2.1, (besselZero_spec n hn).2.2.1,
    (besselZero_spec n hn).2.2.2, besselZero_interlace⟩

end Buckling
end
end ChunkedSource031
/- END SOURCE 031 -/

/- BEGIN SOURCE 032: RequestProject/Concavity/J1Zeros.lean -/
section ChunkedSource032

/-!
# The complex zeros of `J₁` (Lemma 8.3 of the paper)

Every zero of `J₁` in `ℂ` is `0` or `±κ_n`.  The paper proves that nonzero zeros are real by
an integral identity; we derive the statement from the canonical product (External theorem
E2), using the growth `κ_n > nπ` of the zeros (from Lemma 3.3).
-/

@[expose] public section

open Real Filter Topology

namespace Buckling

/-- `κ_n > n π` for `n ≥ 1`. -/
lemma besselZero_one_gt (hZ : ExtZeros) (n : ℕ) : ((n + 1 : ℕ) : ℝ) * π < besselZero 1 (n + 1) := by
  induction n with
  | zero =>
    obtain ⟨-, -, hk1, -⟩ := root_boxes hZ
    have := Real.pi_lt_d2
    simp only [zero_add, Nat.cast_one, one_mul]
    change π < jk
    linarith
  | succ n ih =>
    have hgap := besselZero_one_gap hZ (n + 1) (by omega)
    push_cast at ih ⊢
    linarith

lemma besselZero_one_pos (hZ : ExtZeros) (n : ℕ) : 0 < besselZero 1 (n + 1) :=
  lt_of_le_of_lt (by positivity) (besselZero_one_gt hZ n)

/-- `∑ 1/κ_{n+1}²` converges. -/
lemma summable_inv_besselZero_sq (hZ : ExtZeros) :
    Summable fun n : ℕ => 1 / besselZero 1 (n + 1) ^ 2 := by
  have hs : Summable fun n : ℕ => 1 / (π ^ 2 * ((n + 1 : ℕ) : ℝ) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      (add_left_injective 1)
    refine (this.mul_left (1 / π ^ 2)).congr fun n => ?_
    simp only [Function.comp]
    field_simp
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  have h := besselZero_one_gt hZ n
  have h0 : 0 < ((n + 1 : ℕ) : ℝ) * π := by positivity
  have hk := besselZero_one_pos hZ n
  rw [one_div_le_one_div (by positivity) (by positivity)]
  nlinarith

/-- `e^{-2x} ≤ 1 - x` for `0 ≤ x ≤ 1/2`. -/
lemma exp_neg_two_mul_le (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : Real.exp (-2 * x) ≤ 1 - x := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have h2 : Real.exp (-2 * x) * Real.exp (2 * x) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : 0 < Real.exp (-2 * x) := Real.exp_pos _
  have h4 : Real.exp (-2 * x) * (1 + 2 * x) ≤ 1 := by nlinarith
  nlinarith

/-- A lower bound for a finite product of factors close to `1`. -/
lemma norm_prod_ge_exp {ι : Type*} (s : Finset ι) (a : ι → ℂ) (ha : ∀ i ∈ s, ‖a i‖ ≤ 1 / 2) :
    Real.exp (-2 * ∑ i ∈ s, ‖a i‖) ≤ ‖∏ i ∈ s, (1 - a i)‖ := by
  rw [norm_prod, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le)
  intro i hi
  calc Real.exp (-2 * ‖a i‖) ≤ 1 - ‖a i‖ := exp_neg_two_mul_le _ (norm_nonneg _) (ha i hi)
    _ ≤ ‖1 - a i‖ := by
      have := norm_sub_norm_le (1 : ℂ) (a i)
      simpa using this

/-- **Lemma 8.3**: the zeros of `J₁` in `ℂ` are `0` and `±κ_n`, `n ≥ 1`. -/
theorem besselJC_one_eq_zero (hZ : ExtZeros) (hP : ExtProduct) {ζ : ℂ}
    (hζ : besselJC 1 ζ = 0) :
    ζ = 0 ∨ ∃ n : ℕ, ζ = (besselZero 1 (n + 1) : ℂ) ∨ ζ = -(besselZero 1 (n + 1) : ℂ) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hζ0, hne⟩ := hcon
  set κ : ℕ → ℝ := fun n => besselZero 1 (n + 1)
  set a : ℕ → ℂ := fun n => ζ ^ 2 / ((κ n : ℝ) : ℂ) ^ 2
  have hκ0 : ∀ n, 0 < κ n := besselZero_one_pos hZ
  have ha_norm : ∀ n, ‖a n‖ = ‖ζ‖ ^ 2 * (1 / κ n ^ 2) := by
    intro n
    simp only [a, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hκ0 n)]
    ring
  have hsum : Summable fun n => ‖a n‖ := by
    simp only [ha_norm]; exact (summable_inv_besselZero_sq hZ).mul_left _
  -- eventually `‖a n‖ ≤ 1/2`
  obtain ⟨n0, hn0⟩ : ∃ n0, ∀ n ≥ n0, ‖a n‖ ≤ 1 / 2 := by
    have := hsum.tendsto_atTop_zero
    have h := (this.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
    obtain ⟨n0, hn0⟩ := eventually_atTop.mp h
    exact ⟨n0, fun n hn => (hn0 n hn).le⟩
  -- the factors are nonzero
  have hfac : ∀ n, 1 - a n ≠ 0 := by
    intro n h
    have h1 : ζ ^ 2 = ((κ n : ℝ) : ℂ) ^ 2 := by
      have hk : ((κ n : ℝ) : ℂ) ^ 2 ≠ 0 := by
        have : ((κ n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hκ0 n).ne'
        exact pow_ne_zero 2 this
      have : a n = 1 := by linear_combination -h
      simp only [a] at this
      rwa [div_eq_one_iff_eq hk] at this
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
    · exact (hne n).1 h2
    · exact (hne n).2 h2
  set A := ‖∏ n ∈ Finset.range n0, (1 - a n)‖
  have hA : 0 < A := norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun n _ => hfac n)
  set S := ∑' n, ‖a n‖
  -- lower bound on the partial products
  have hlow : ∀ N ≥ n0, ‖ζ‖ / 2 * (A * Real.exp (-2 * S)) ≤
      ‖ζ / 2 * ∏ n ∈ Finset.range N, (1 - ζ ^ 2 / ((besselZero 1 (n + 1) : ℝ) : ℂ) ^ 2)‖ := by
    intro N hN
    change _ ≤ ‖ζ / 2 * ∏ n ∈ Finset.range N, (1 - a n)‖
    rw [← Finset.prod_range_mul_prod_Ico _ hN, norm_mul, norm_mul, norm_div, Complex.norm_two]
    gcongr
    calc Real.exp (-2 * S) ≤ Real.exp (-2 * ∑ n ∈ Finset.Ico n0 N, ‖a n‖) := by
          apply Real.exp_le_exp.mpr
          have := hsum.sum_le_tsum (Finset.Ico n0 N) (fun n _ => norm_nonneg _)
          linarith
      _ ≤ _ := norm_prod_ge_exp _ _ fun n hn => hn0 n (Finset.mem_Ico.mp hn).1
  have hlim := (TendstoLocallyUniformly.tendstoLocallyUniformlyOn (s := Set.univ) hP).tendsto_at (Set.mem_univ ζ)
  rw [hζ] at hlim
  have hpos : 0 < ‖ζ‖ / 2 * (A * Real.exp (-2 * S)) := by
    have := norm_pos_iff.mpr hζ0
    positivity
  have := (hlim.norm).eventually (gt_mem_nhds (by rw [norm_zero]; exact hpos))
  obtain ⟨N, hN⟩ := eventually_atTop.mp this
  have h1 := hN (max N n0) (le_max_left _ _)
  have h2 := hlow (max N n0) (le_max_right _ _)
  linarith

end Buckling
end
end ChunkedSource032
/- END SOURCE 032 -/

/- BEGIN SOURCE 033: RequestProject/Bessel/Product/RealZeros.lean -/
section ChunkedSource033

/-!
# The complex zeros of `J₁` are real (Lemma 8.3 of the paper, via Lommel's identity)

For `a, b ∈ ℂ` put `W(t) = t (a J₀(at) J₁(bt) - b J₁(at) J₀(bt))`.  Then
`W'(t) = (b² - a²) t J₁(at) J₁(bt)`.  If `J₁(a) = 0` then also `J₁(ā) = 0`, and integrating
over `[0,1]` with `b = ā` gives `(ā² - a²) ∫₀¹ t |J₁(at)|² dt = 0`, so `a² ∈ ℝ`.  Purely
imaginary nonzero `a` are excluded by the positivity of the series of `-i J₁(iy)`; real zeros
are the `±κ_n` by E1.  This proof does not use the canonical product.
-/

@[expose] public section

open Complex Real MeasureTheory Filter Topology Set
open scoped Nat

namespace Buckling

/-- `ζ J₁'(ζ) = ζ J₀(ζ) - J₁(ζ)`. -/
lemma mul_deriv_besselJC_one (ζ : ℂ) :
    ζ * ((besselJC 0 ζ - besselJC 2 ζ) / 2) = ζ * besselJC 0 ζ - besselJC 1 ζ := by
  have h := besselJC_two_mul ζ
  linear_combination (-1 / 2 : ℂ) * h

/-- Lommel's function. -/
noncomputable def lommelW (a b : ℂ) (t : ℂ) : ℂ :=
  t * (a * besselJC 0 (a * t) * besselJC 1 (b * t) - b * besselJC 1 (a * t) * besselJC 0 (b * t))

/-- `d/dt [t J₁(ct)] = c t J₀(ct)`. -/
lemma hasDerivAt_mul_besselJC_one_comp (c t : ℂ) :
    HasDerivAt (fun s => s * besselJC 1 (c * s)) (c * t * besselJC 0 (c * t)) t := by
  have h1 : HasDerivAt (fun s => besselJC 1 (c * s))
      ((besselJC 0 (c * t) - besselJC 2 (c * t)) / 2 * c) t := by
    have := hasDerivAt_besselJC_succ 0 (c * t)
    exact this.comp t ((hasDerivAt_id t).const_mul c |>.congr_deriv (by simp))
  have h2 := (hasDerivAt_id t).fun_mul h1
  have hr := mul_deriv_besselJC_one (c * t)
  have hD :
      (1 : ℂ) * besselJC 1 (c * t) +
          t * (((besselJC 0 (c * t) - besselJC 2 (c * t)) / 2) * c) =
        c * t * besselJC 0 (c * t) := by
    calc
      _ = besselJC 1 (c * t) +
          (c * t) * ((besselJC 0 (c * t) - besselJC 2 (c * t)) / 2) := by ring
      _ = c * t * besselJC 0 (c * t) := by rw [hr]; ring
  simpa only [id_eq] using! (h2.congr_deriv hD)

lemma hasDerivAt_besselJC_zero_comp (c t : ℂ) :
    HasDerivAt (fun s => besselJC 0 (c * s)) (-besselJC 1 (c * t) * c) t :=
  (hasDerivAt_besselJC_zero (c * t)).comp t
    ((hasDerivAt_id t).const_mul c |>.congr_deriv (by simp))

/-- **Lommel's identity.** -/
lemma hasDerivAt_lommelW (a b t : ℂ) :
    HasDerivAt (lommelW a b) ((b ^ 2 - a ^ 2) * t * besselJC 1 (a * t) * besselJC 1 (b * t)) t := by
  have hA := ((hasDerivAt_besselJC_zero_comp a t).const_mul a).mul
    (hasDerivAt_mul_besselJC_one_comp b t)
  have hB := ((hasDerivAt_besselJC_zero_comp b t).const_mul b).mul
    (hasDerivAt_mul_besselJC_one_comp a t)
  have h := hA.sub hB
  have heq : lommelW a b = fun s => a * besselJC 0 (a * s) * (s * besselJC 1 (b * s)) -
      b * besselJC 0 (b * s) * (s * besselJC 1 (a * s)) := by
    funext s; unfold lommelW; ring
  rw [heq]
  convert h using 1
  ring

/-- The integral form of Lommel's identity on `[0, 1]`. -/
lemma lommel_integral (a b : ℂ) :
    ∫ x in (0 : ℝ)..1, (b ^ 2 - a ^ 2) * (x : ℂ) * besselJC 1 (a * x) * besselJC 1 (b * x) =
      a * besselJC 0 a * besselJC 1 b - b * besselJC 1 a * besselJC 0 b := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun y : ℝ => lommelW a b y)
      ((b ^ 2 - a ^ 2) * (x : ℂ) * besselJC 1 (a * x) * besselJC 1 (b * x)) x :=
    fun x _ => (hasDerivAt_lommelW a b x).comp_ofReal
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp [lommelW]
  · apply Continuous.intervalIntegrable
    have := continuous_besselJC 1
    fun_prop

/-- Near `0`, `J₁(a x) ≠ 0` for small `x > 0` (`a ≠ 0`). -/
lemma exists_besselJC_one_ne_zero {a : ℂ} (ha : a ≠ 0) :
    ∃ x ∈ Ioo (0 : ℝ) 1, besselJC 1 (a * x) ≠ 0 := by
  have hd : HasDerivAt (fun y : ℝ => besselJC 1 (a * y)) (1 / 2 * a) 0 := by
    have h := hasDerivAt_besselJC_succ 0 (a * ((0 : ℝ) : ℂ))
    have h2 := (h.comp ((0 : ℝ) : ℂ) ((hasDerivAt_id ((0 : ℝ) : ℂ)).const_mul a)).comp_ofReal
    have hD :
        ((besselJC 0 (a * ((0 : ℝ) : ℂ)) -
            besselJC (0 + 2) (a * ((0 : ℝ) : ℂ))) / 2) * (a * 1) =
          (1 / 2 : ℂ) * a := by
      norm_num [besselJC_zero_arg]
    simpa only [Function.comp_apply, Nat.zero_add] using! (h2.congr_deriv hD)
  have hne := hd.eventually_ne (c := 0) (by simpa using ha)
  have hmem : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
  have := (hmem.and (nhdsGT_le_nhdsNE 0 hne)).exists
  obtain ⟨x, hx, hx'⟩ := this
  exact ⟨x, hx, hx'⟩

/-- `∫₀¹ x |J₁(a x)|² dx > 0` for `a ≠ 0`. -/
lemma integral_besselJC_one_sq_pos {a : ℂ} (ha : a ≠ 0) :
    0 < ∫ x in (0 : ℝ)..1, x * ‖besselJC 1 (a * x)‖ ^ 2 := by
  have hc : Continuous fun x : ℝ => x * ‖besselJC 1 (a * x)‖ ^ 2 := by
    have := continuous_besselJC 1
    fun_prop
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae' _ (hc.intervalIntegrable _ _)]
  · refine ⟨by norm_num, ?_⟩
    obtain ⟨x0, hx0, hne⟩ := exists_besselJC_one_ne_zero ha
    set U := {x : ℝ | x * ‖besselJC 1 (a * x)‖ ^ 2 ≠ 0} ∩ Ioo 0 1
    have hU : IsOpen U := (isOpen_ne_fun hc continuous_const).inter isOpen_Ioo
    have hx0U : x0 ∈ U := by
      refine ⟨?_, hx0⟩
      simp only [mem_setOf_eq]
      have : 0 < ‖besselJC 1 (a * x0)‖ := norm_pos_iff.mpr hne
      have := hx0.1
      positivity
    have hsub : U ⊆ Function.support (fun x : ℝ => x * ‖besselJC 1 (a * x)‖ ^ 2) ∩ Ioc 0 1 :=
      fun x hx => ⟨hx.1, Ioo_subset_Ioc_self hx.2⟩
    exact lt_of_lt_of_le (hU.measure_pos volume ⟨x0, hx0U⟩) (measure_mono hsub)
  · rw [uIoc_of_le zero_le_one]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun x hx => ?_)
    have := hx.1.le
    simp only [Pi.zero_apply]
    positivity

/-- `J₁(iy) = i ∑ (y/2)^{2m+1}/(m!(m+1)!)`. -/
lemma cterm_one_I_mul (m : ℕ) (y : ℝ) :
    cterm 1 m (I * y) = I * (((y / 2) ^ (2 * m + 1) / ((m ! : ℝ) * ((m + 1) ! : ℝ)) : ℝ) : ℂ) := by
  unfold cterm
  have hI : (I * (y : ℂ) / 2) ^ (2 * m + 1) = I * (-1) ^ m * ((y : ℂ) / 2) ^ (2 * m + 1) := by
    rw [mul_div_assoc, mul_pow, pow_succ, pow_mul, I_sq]; ring
  rw [hI]
  push_cast
  have h1 : ((-1 : ℂ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (I * ((y : ℂ) / 2) ^ (2 * m + 1) / ((m ! : ℂ) * ((m + 1) ! : ℂ))) * h1

/-- Purely imaginary nonzero numbers are not zeros of `J₁`. -/
lemma besselJC_one_I_mul_ne_zero {y : ℝ} (hy : y ≠ 0) : besselJC 1 (I * y) ≠ 0 := by
  set t : ℕ → ℝ := fun m => (y / 2) ^ (2 * m + 1) / ((m ! : ℝ) * ((m + 1) ! : ℝ))
  have hst : Summable t := by
    refine Summable.of_norm ((summable_abs_bterm 1 y).congr fun m => ?_)
    simp only [t, bterm, Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul]
  have hJ : besselJC 1 (I * y) = I * ((∑' m, t m : ℝ) : ℂ) := by
    rw [besselJC_eq_tsum, Complex.ofReal_tsum, ← tsum_mul_left]
    simp only [cterm_one_I_mul, t]
  set s : ℕ → ℝ := fun m => ((y / 2) ^ 2) ^ m / ((m ! : ℝ) * ((m + 1) ! : ℝ))
  have hts : ∀ m, t m = y / 2 * s m := by
    intro m; simp only [t, s]; rw [← pow_mul, pow_succ]; ring
  have hy2 : y / 2 ≠ 0 := by positivity
  have hss : Summable s := by
    refine (hst.mul_left (y / 2)⁻¹).congr fun m => ?_
    rw [hts]; field_simp
  have hs1 : 1 ≤ ∑' m, s m := by
    have := hss.le_tsum 0 (fun j _ => by simp only [s]; positivity)
    simpa [s] using this
  rw [hJ, tsum_congr hts, tsum_mul_left]
  have : y / 2 * ∑' m, s m ≠ 0 := mul_ne_zero hy2 (by linarith)
  exact mul_ne_zero I_ne_zero (by exact_mod_cast this)

/-- Nonzero zeros of `J₁` are real. -/
lemma besselJC_one_zero_im {a : ℂ} (ha : besselJC 1 a = 0) : a.im = 0 := by
  rcases eq_or_ne a 0 with rfl | ha0
  · simp
  set b := (starRingEnd ℂ) a
  have hb : besselJC 1 b = 0 := by rw [besselJC_conj, ha, map_zero]
  have hL := lommel_integral a b
  rw [ha, hb] at hL
  simp only [mul_zero, zero_mul, sub_zero] at hL
  have hconj : ∀ x : ℝ, (b ^ 2 - a ^ 2) * (x : ℂ) * besselJC 1 (a * x) * besselJC 1 (b * x) =
      (b ^ 2 - a ^ 2) * ((x * ‖besselJC 1 (a * x)‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    have : b * (x : ℂ) = (starRingEnd ℂ) (a * x) := by simp [b]
    rw [this, besselJC_conj]
    push_cast
    rw [mul_assoc _ (besselJC 1 (a * x)), Complex.mul_conj']
    ring
  simp_rw [hconj] at hL
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal] at hL
  have hpos := integral_besselJC_one_sq_pos ha0
  have hI0 : ((∫ x in (0 : ℝ)..1, x * ‖besselJC 1 (a * x)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hpos.ne'
  have hsq : b ^ 2 = a ^ 2 := by
    have := (mul_eq_zero.mp hL).resolve_right hI0
    linear_combination this
  have hre : a.re * a.im = 0 := by
    have := congrArg Complex.im hsq
    simp only [b, sq, Complex.mul_im, Complex.conj_re, Complex.conj_im] at this
    linarith
  rcases mul_eq_zero.mp hre with h | h
  · by_contra him
    have hai : a = I * (a.im : ℂ) := by
      apply Complex.ext <;> simp [h]
    exact besselJC_one_I_mul_ne_zero him (hai ▸ ha)
  · exact h

/-- **Lemma 8.3** (without the canonical product): the zeros of `J₁` in `ℂ` are `0` and
`±κ_n`, `n ≥ 1`. -/
theorem besselJC_one_eq_zero' {ζ : ℂ} (hζ : besselJC 1 ζ = 0) :
    ζ = 0 ∨ ∃ n : ℕ, ζ = (besselZero 1 (n + 1) : ℂ) ∨ ζ = -(besselZero 1 (n + 1) : ℂ) := by
  have him := besselJC_one_zero_im hζ
  have hζx : ζ = (ζ.re : ℂ) := Complex.ext (by simp) (by simp [him])
  set x := ζ.re
  have hx : besselJ 1 x = 0 := by
    have := besselJC_ofReal 1 x
    rw [← hζx, hζ] at this
    exact_mod_cast this.symm
  have hZ := (extZeros_holds 1 le_rfl).2.2.2.1
  rcases lt_trichotomy x 0 with hneg | h0 | hpos
  · have hx' : besselJ 1 (-x) = 0 := by
      have := besselJC_ofReal 1 (-x)
      rw [Complex.ofReal_neg, besselJC_neg, besselJC_ofReal, hx] at this
      simp at this
      exact_mod_cast this.symm
    obtain ⟨k, hk, hkx⟩ := hZ (-x) (by linarith) hx'
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    refine Or.inr ⟨n, Or.inr ?_⟩
    rw [hζx, hkx]; push_cast; ring
  · left; rw [hζx, h0]; simp
  · obtain ⟨k, hk, hkx⟩ := hZ x hpos hx
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    exact Or.inr ⟨n, Or.inl (by rw [hζx, hkx])⟩

end Buckling
end
end ChunkedSource033
/- END SOURCE 033 -/

/- BEGIN SOURCE 034: RequestProject/Concavity/Removable.lean -/
section ChunkedSource034

/-!
# Removable singularities and principal parts

Generic complex-analytic tools used in Section 8:

* filling finitely many removable singularities (`fillSing`),
* the residue theorem (External theorem E6, proved here from Mathlib) in the form "if `h` minus explicit principal
  parts is bounded near each singular point, then `∮ h = 2πi ∑ residues`",
* the principal part of `Φ(z)/(z-a)²` for holomorphic `Φ`.
-/

@[expose] public section

open Filter Topology Metric Set

namespace Buckling

/-- Redefine `f` at the points of `T` by its limits there. -/
noncomputable def fillSing (T : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ T then limUnder (𝓝[≠] z) f else f z

lemma fillSing_of_notMem {T : Finset ℂ} {f : ℂ → ℂ} {z : ℂ} (hz : z ∉ T) :
    fillSing T f z = f z := by simp [fillSing, hz]

/-- Filling finitely many bounded isolated singularities gives a holomorphic function. -/
theorem differentiableOn_fillSing {U : Set ℂ} (hU : IsOpen U) (T : Finset ℂ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U \ T))
    (hb : ∀ a ∈ T, a ∈ U → ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖f z‖ ≤ C) :
    DifferentiableOn ℂ (fillSing T f) U := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  by_cases hzT : z ∈ T
  · obtain ⟨C, hC⟩ := hb z hzT hz
    set T' := T.erase z
    have hT'c : IsClosed (T' : Set ℂ) := T'.finite_toSet.isClosed
    have hzT' : z ∉ T' := Finset.notMem_erase z T
    rw [eventually_nhdsWithin_iff] at hC
    set s : Set ℂ := U ∩ (T' : Set ℂ)ᶜ ∩ {w | w ∈ ({z}ᶜ : Set ℂ) → ‖f w‖ ≤ C}
    have hs : s ∈ 𝓝 z :=
      inter_mem (inter_mem (hU.mem_nhds hz) (hT'c.isOpen_compl.mem_nhds hzT')) hC
    have hsub : s \ {z} ⊆ U \ T := by
      rintro w ⟨⟨⟨hwU, hwT'⟩, -⟩, hwz⟩
      refine ⟨hwU, fun hwT => hwT' ?_⟩
      exact Finset.mem_erase.mpr ⟨hwz, hwT⟩
    have hbdd : BddAbove (norm ∘ f '' (s \ {z})) := by
      refine ⟨C, ?_⟩
      rintro _ ⟨w, ⟨hws, hwz⟩, rfl⟩
      exact hws.2 hwz
    have H := Complex.differentiableOn_update_limUnder_of_bddAbove hs (hf.mono hsub) hbdd
    refine (H.differentiableAt hs).congr_of_eventuallyEq ?_
    filter_upwards [hs] with w hw
    by_cases hwz : w = z
    · subst hwz; simp [fillSing, hzT]
    · have hwT : w ∉ T := fun hwT => hw.1.2 (Finset.mem_erase.mpr ⟨hwz, hwT⟩)
      simp [fillSing, hwT, Function.update_of_ne hwz]
  · have hTc : IsOpen ((T : Set ℂ)ᶜ) := T.finite_toSet.isClosed.isOpen_compl
    have hV : U \ T ∈ 𝓝 z := (hU.inter hTc).mem_nhds ⟨hz, hzT⟩
    refine ((hf z ⟨hz, hzT⟩).differentiableAt hV).congr_of_eventuallyEq ?_
    filter_upwards [hTc.mem_nhds hzT] with w hw
    exact fillSing_of_notMem hw

/-- A function continuous at `a` is bounded on a punctured neighbourhood of `a`. -/
lemma bdd_of_continuousAt {f : ℂ → ℂ} {a : ℂ} (hf : ContinuousAt f a) :
    ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖f z‖ ≤ C := by
  refine ⟨‖f a‖ + 1, ?_⟩
  have := hf.norm.eventually (gt_mem_nhds (lt_add_one ‖f a‖))
  exact (this.filter_mono nhdsWithin_le_nhds).mono fun z hz => hz.le

/-- The principal part `∑_{j<N} P(a,j)/(z-a)^{j+1}`. -/
noncomputable def princPart (N : ℕ) (P : ℂ → ℕ → ℂ) (a z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range N, P a j / (z - a) ^ (j + 1)

lemma continuousAt_princPart (N : ℕ) (P : ℂ → ℕ → ℂ) {a z : ℂ} (hz : z ≠ a) :
    ContinuousAt (princPart N P a) z := by
  unfold princPart
  refine tendsto_finset_sum _ fun j _ => ?_
  exact continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

lemma differentiableAt_princPart (N : ℕ) (P : ℂ → ℕ → ℂ) {a z : ℂ} (hz : z ≠ a) :
    DifferentiableAt ℂ (princPart N P a) z := by
  unfold princPart
  have : (fun w => ∑ j ∈ Finset.range N, P a j / (w - a) ^ (j + 1)) =
      ∑ j ∈ Finset.range N, fun w => P a j / (w - a) ^ (j + 1) := by
    ext w; simp
  rw [this]
  refine DifferentiableAt.sum fun j _ => ?_
  exact (differentiableAt_const _).div ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

/-- The circle integral of a single principal-part term `c/(z-a)^{j+1}` with `|a| < R`. -/
lemma circleIntegral_princ_term {R : ℝ} {a : ℂ} (ha : a ∈ ball (0:ℂ) R) (c : ℂ) (j : ℕ) :
    (∮ z in C(0, R), c / (z - a) ^ (j + 1)) =
      if j = 0 then 2 * Real.pi * Complex.I * c else 0 := by
  have : (fun z : ℂ => c / (z - a) ^ (j + 1)) = fun z => c * (z - a) ^ (-((j:ℤ) + 1)) := by
    ext z; rw [zpow_neg, div_eq_mul_inv]; norm_cast
  rw [this, circleIntegral.integral_const_mul]
  split_ifs with hj
  · subst hj
    simp only [Nat.cast_zero, zero_add, Int.reduceNeg, zpow_neg, zpow_one]
    rw [circleIntegral.integral_sub_inv_of_mem_ball ha]; ring
  · rw [circleIntegral.integral_sub_zpow_of_ne, mul_zero]
    omega

/-- **Residue theorem for explicit principal parts** (the part of External theorem E6
used in the paper, Rudin, *Real and Complex Analysis*, Thm 10.42), proved here from
Mathlib's Cauchy integral theorem and the integrals `∮ (z-a)^n`.  If, off the finite set
`S ⊆ {|ζ| < R}`, `h = g + ∑_{a ∈ S} ∑_{j < N} P(a,j)(ζ-a)^{-(j+1)}` with `g` holomorphic on
a neighbourhood `U` of the closed disk and `N ≥ 1`, then `∮_{|ζ|=R} h = 2πi ∑_a P(a,0)`.

(The hypothesis `0 < N` is necessary: for `N = 0` the principal parts vanish, so the
left side is `0` while the right side need not be.) -/
theorem circleIntegral_eq_explicit_residues (R : ℝ) (h g : ℂ → ℂ) (S : Finset ℂ) (N : ℕ)
    (P : ℂ → ℕ → ℂ) (U : Set ℂ) (hN : 0 < N) (hR : 0 < R) (hU : IsOpen U)
    (hRU : closedBall 0 R ⊆ U) (hS : (↑S : Set ℂ) ⊆ ball 0 R) (hg : DifferentiableOn ℂ g U)
    (hh : ∀ ζ ∈ U \ ↑S, h ζ = g ζ + ∑ a ∈ S, ∑ j ∈ Finset.range N, P a j / (ζ - a) ^ (j + 1)) :
    (∮ ζ in C(0, R), h ζ) = 2 * Real.pi * Complex.I * ∑ a ∈ S, P a 0 := by
  have hsph : ∀ z ∈ sphere (0:ℂ) R, z ∈ U \ ↑S := fun z hz =>
    ⟨hRU (sphere_subset_closedBall hz), fun hzS => by
      have := hS hzS; rw [mem_ball] at this; rw [mem_sphere] at hz; linarith⟩
  have hne : ∀ z ∈ sphere (0:ℂ) R, ∀ a ∈ S, z - a ≠ 0 := fun z hz a ha h0 =>
    (hsph z hz).2 (by rw [sub_eq_zero.mp h0]; exact ha)
  have hint : ∀ a ∈ S, ∀ j, CircleIntegrable (fun z => P a j / (z - a) ^ (j + 1)) 0 R := by
    intro a ha j
    refine ContinuousOn.circleIntegrable hR.le ?_
    intro z hz
    exact (continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow _)
      (pow_ne_zero _ (hne z hz a ha))).continuousWithinAt
  have hint2 : ∀ a ∈ S, CircleIntegrable
      (fun z => ∑ j ∈ Finset.range N, P a j / (z - a) ^ (j + 1)) 0 R := by
    intro a ha
    have := CircleIntegrable.sum (Finset.range N) (fun j _ => hint a ha j)
    convert this using 1; ext z; simp
  rw [circleIntegral.integral_congr hR.le (fun z hz => hh z (hsph z hz))]
  rw [circleIntegral.integral_add]
  · rw [Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
      Set.countable_empty (hg.continuousOn.mono hRU)
      (fun z hz => hg.differentiableAt (hU.mem_nhds (hRU (ball_subset_closedBall hz.1)))),
      zero_add, circleIntegral.integral_fun_sum hint2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [circleIntegral.integral_fun_sum (fun j _ => hint a ha j)]
    simp_rw [circleIntegral_princ_term (hS ha)]
    rw [Finset.sum_ite_eq']; simp [hN]
  · exact ContinuousOn.circleIntegrable hR.le
      ((hg.continuousOn.mono hRU).mono sphere_subset_closedBall)
  · have := CircleIntegrable.sum S hint2
    convert this using 1; ext z; simp

/-- **Residue theorem** (External theorem E6, proved above): if `h` is holomorphic on `U \ S` and, near each
`a ∈ S`, differs from the principal part `∑_j P(a,j)/(z-a)^{j+1}` by a bounded function, then
`∮_{|z|=R} h = 2πi ∑_{a ∈ S} P(a,0)`. -/
theorem circleIntegral_eq_residues {R : ℝ} (hR : 0 < R) {U : Set ℂ}
    (hU : IsOpen U) (hRU : closedBall (0 : ℂ) R ⊆ U) (S : Finset ℂ) (hS : (S : Set ℂ) ⊆ ball 0 R)
    (h : ℂ → ℂ) (N : ℕ) (hN : 0 < N) (P : ℂ → ℕ → ℂ) (hd : DifferentiableOn ℂ h (U \ S))
    (hb : ∀ a ∈ S, ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖h z - princPart N P a z‖ ≤ C) :
    (∮ z in C(0, R), h z) = 2 * Real.pi * Complex.I * ∑ a ∈ S, P a 0 := by
  set F : ℂ → ℂ := fun z => h z - ∑ a ∈ S, princPart N P a z
  have hFd : DifferentiableOn ℂ F (U \ S) := by
    intro z hz
    have hV : U \ S ∈ 𝓝 z :=
      (hU.inter S.finite_toSet.isClosed.isOpen_compl).mem_nhds hz
    apply DifferentiableAt.differentiableWithinAt
    refine ((hd z hz).differentiableAt hV).sub ?_
    have : (fun w => ∑ a ∈ S, princPart N P a w) = ∑ a ∈ S, fun w => princPart N P a w := by
      ext w; simp
    rw [this]
    refine DifferentiableAt.sum fun a ha => differentiableAt_princPart N P ?_
    rintro rfl; exact hz.2 ha
  have hFb : ∀ a ∈ S, a ∈ U → ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖F z‖ ≤ C := by
    intro a ha _
    obtain ⟨C1, hC1⟩ := hb a ha
    have hcont : ContinuousAt (fun w => ∑ b ∈ S.erase a, princPart N P b w) a := by
      refine tendsto_finset_sum _ fun b hb => continuousAt_princPart N P ?_
      exact (Finset.ne_of_mem_erase hb).symm
    obtain ⟨C2, hC2⟩ := bdd_of_continuousAt hcont
    refine ⟨C1 + C2, ?_⟩
    filter_upwards [hC1, hC2] with z h1 h2
    have : F z = (h z - princPart N P a z) - ∑ b ∈ S.erase a, princPart N P b z := by
      simp only [F]
      rw [← Finset.add_sum_erase S _ ha]
      ring
    rw [this]
    exact (norm_sub_le _ _).trans (add_le_add h1 h2)
  have hg := differentiableOn_fillSing hU S hFd hFb
  refine circleIntegral_eq_explicit_residues R h (fillSing S F) S N P U hN hR hU hRU hS hg ?_
  intro z hz
  rw [fillSing_of_notMem hz.2]
  simp only [F, princPart]
  ring

/-- The principal part of `Φ(z)/(z-a)²` for `Φ` holomorphic near `a`:
`Φ(z)/(z-a)² - Φ'(a)/(z-a) - Φ(a)/(z-a)²` is bounded near `a`. -/
theorem bdd_sub_principal_two {Φ : ℂ → ℂ} {a : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 a)
    (hΦ : DifferentiableOn ℂ Φ s) :
    ∃ C, ∀ᶠ z in 𝓝[≠] a,
      ‖Φ z / (z - a) ^ 2 - (deriv Φ a / (z - a) ^ 1 + Φ a / (z - a) ^ 2)‖ ≤ C := by
  have h1 : DifferentiableOn ℂ (dslope Φ a) s := (Complex.differentiableOn_dslope hs).mpr hΦ
  have h2 : DifferentiableOn ℂ (dslope (dslope Φ a) a) s := (Complex.differentiableOn_dslope hs).mpr h1
  obtain ⟨C, hC⟩ := bdd_of_continuousAt ((h2.differentiableAt hs).continuousAt)
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with z hz hza
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have e1 := sub_smul_dslope Φ a z
  have e2 := sub_smul_dslope (dslope Φ a) a z
  rw [dslope_same] at e2
  simp only [smul_eq_mul] at e1 e2
  have : Φ z / (z - a) ^ 2 - (deriv Φ a / (z - a) ^ 1 + Φ a / (z - a) ^ 2) =
      dslope (dslope Φ a) a z := by
    field_simp
    linear_combination (-1) * e1 - (z - a) * e2
  rw [this]; exact hz

end Buckling
end
end ChunkedSource034
/- END SOURCE 034 -/

/- BEGIN SOURCE 035: RequestProject/Concavity/TaylorBound.lean -/
section ChunkedSource035

/-!
# Taylor coefficients and the principal part at the origin

For `f` holomorphic on a disc about `0` with Taylor coefficients `c_j`, the remainder
`f(z) - ∑_{j ≤ N} c_j z^j` is `O(|z|^{N+1})`; hence `f(z)/z^{N+1}` has principal part
`∑_{j ≤ N} c_j z^{j-N-1}` at `0`, with residue `c_N`.
-/

@[expose] public section

open Filter Topology Metric Set
open scoped Nat

namespace Buckling

/-- The Taylor coefficients of `f` at `0`. -/
noncomputable def tcoef (f : ℂ → ℂ) (j : ℕ) : ℂ := (j ! : ℂ)⁻¹ * iteratedDeriv j f 0

lemma hasSum_tcoef {f : ℂ → ℂ} {r : NNReal} (hf : DifferentiableOn ℂ f (ball 0 r)) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) r) : HasSum (fun j => tcoef f j * z ^ j) (f z) := by
  have := Complex.hasSum_taylorSeries_on_ball hf hz
  convert this using 1
  funext j
  simp only [tcoef, sub_zero, smul_eq_mul]
  ring

/-- The Taylor remainder is `O(|z|^{N+1})`. -/
theorem taylor_remainder {f : ℂ → ℂ} {r : NNReal} (hr : 0 < (r : ℝ))
    (hf : DifferentiableOn ℂ f (ball 0 r)) (N : ℕ) :
    ∃ C, ∀ᶠ z in 𝓝 (0 : ℂ),
      ‖f z - ∑ j ∈ Finset.range (N + 1), tcoef f j * z ^ j‖ ≤ C * ‖z‖ ^ (N + 1) := by
  set r1 : ℝ := r / 2
  have hr1 : 0 < r1 := by positivity
  have hmem : ((r1 : ℝ) : ℂ) ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr1]
    simp only [r1]; linarith
  have hs := hasSum_tcoef hf hmem
  obtain ⟨B, hB⟩ := (hs.summable.tendsto_atTop_zero.norm).bddAbove_range
  have hB' : ∀ j, ‖tcoef f j‖ * r1 ^ j ≤ B := by
    intro j
    have := hB ⟨j, rfl⟩
    simpa [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr1] using this
  have hB0 : 0 ≤ B := le_trans (by positivity) (hB' 0)
  refine ⟨2 * B / r1 ^ (N + 1), ?_⟩
  filter_upwards [ball_mem_nhds (0 : ℂ) (half_pos hr1)] with z hz
  rw [mem_ball, dist_zero_right] at hz
  set q := ‖z‖ / r1
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 / 2 := by
    rw [div_lt_iff₀ hr1]; linarith
  have hzr : z ∈ ball (0 : ℂ) r := by
    rw [mem_ball, dist_zero_right]; simp only [r1] at hz; linarith
  have hsz := hasSum_tcoef hf hzr
  have htail := (hasSum_nat_add_iff' (N + 1)).mpr hsz
  have hgeom : HasSum (fun n : ℕ => B * q ^ (N + 1) * q ^ n) (B * q ^ (N + 1) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hle := htail.norm_le_of_bounded hgeom (fun n => by
    rw [norm_mul, norm_pow, mul_assoc, ← pow_add, add_comm (N + 1) n]
    have h1 := hB' (n + (N + 1))
    have h2 : ‖z‖ ^ (n + (N + 1)) = r1 ^ (n + (N + 1)) * q ^ (n + (N + 1)) := by
      rw [← mul_pow]; congr 1; simp only [q]; field_simp
    rw [h2, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity))
  calc ‖f z - ∑ j ∈ Finset.range (N + 1), tcoef f j * z ^ j‖
      ≤ B * q ^ (N + 1) * (1 - q)⁻¹ := hle
    _ ≤ B * q ^ (N + 1) * 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    _ = 2 * B / r1 ^ (N + 1) * ‖z‖ ^ (N + 1) := by
        simp only [q]; rw [div_pow]; field_simp

/-- The principal part of `f(z)/z^{N+1}` at `0`. -/
theorem bdd_div_pow_sub_principal {f : ℂ → ℂ} {r : NNReal} (hr : 0 < (r : ℝ))
    (hf : DifferentiableOn ℂ f (ball 0 r)) (N : ℕ) :
    ∃ C, ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ‖f z / z ^ (N + 1) - princPart (N + 1) (fun _ i => tcoef f (N - i)) 0 z‖ ≤ C := by
  obtain ⟨C, hC⟩ := taylor_remainder hr hf N
  refine ⟨C, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with z hz hz0
  have hz0' : z ≠ 0 := hz0
  have hpp : princPart (N + 1) (fun _ i => tcoef f (N - i)) 0 z =
      (∑ j ∈ Finset.range (N + 1), tcoef f j * z ^ j) / z ^ (N + 1) := by
    unfold princPart
    rw [← Finset.sum_range_reflect, Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N + 1 := Finset.mem_range.mp hi
    dsimp only
    rw [sub_zero, show N - (N + 1 - 1 - i) = i by omega, show N + 1 - 1 - i + 1 = N + 1 - i by omega]
    rw [div_eq_div_iff (pow_ne_zero _ hz0') (pow_ne_zero _ hz0'), mul_assoc, ← pow_add,
      show i + (N + 1 - i) = N + 1 by omega]
  rw [hpp, ← sub_div, norm_div, norm_pow, div_le_iff₀ (pow_pos (norm_pos_iff.mpr hz0') _)]
  exact hz

end Buckling
end
end ChunkedSource035
/- END SOURCE 035 -/

/- BEGIN SOURCE 036: RequestProject/Functional/ZeroSet.lean -/
section ChunkedSource036

/-!
# Regular zero sets have measure zero (Lemma 9.10 of the paper)

If `h ∈ C¹(ℝ²)`, then `{x : h x = 0, ∇h x ≠ 0}` is Lebesgue-null.  We prove it by Fubini:
in the direction of a nonvanishing partial derivative, each slice of the set consists of
isolated points, hence is countable.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace Buckling

/-- A set of zeros of `g : ℝ → ℝ` at each of which `g` has a nonzero derivative is
countable. -/
lemma countable_of_regular_zeros {g : ℝ → ℝ} {s : Set ℝ}
    (h : ∀ t ∈ s, g t = 0 ∧ ∃ d ≠ 0, HasDerivAt g d t) : s.Countable := by
  have hd : DiscreteTopology s := by
    rw [discreteTopology_subtype_iff]
    intro t ht
    obtain ⟨-, d, hd, hg⟩ := h t ht
    have hne := hg.eventually_ne hd (c := 0)
    rw [Filter.inf_principal_eq_bot]
    filter_upwards [hne] with z hz hzs
    exact hz (h z hzs).1
  exact Set.countable_coe_iff.mp ((TopologicalSpace.separableSpace_iff_countable).mp inferInstance)

/-- A measurable subset of `ℝ × ℝ` all of whose vertical slices are countable is null. -/
lemma null_of_slices_countable {T : Set (ℝ × ℝ)} (hT : MeasurableSet T)
    (h : ∀ a, {t | (a, t) ∈ T}.Countable) : volume T = 0 := by
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hT]
  exact Filter.Eventually.of_forall fun a => (h a).measure_zero _

/-- The point `a e₀ + b e₁` of the plane. -/
noncomputable def planeOf (a b : ℝ) : Plane :=
  a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1

lemma planeOf_apply (x : Plane) : planeOf (x 0) (x 1) = x := by
  ext i; fin_cases i <;> simp [planeOf]

lemma continuous_planeOf : Continuous (fun p : ℝ × ℝ => planeOf p.1 p.2) := by
  unfold planeOf; fun_prop

lemma measurePreserving_coords :
    MeasurePreserving (fun x : Plane => (x 0, x 1)) volume volume :=
  (volume_preserving_finTwoArrow ℝ).comp (PiLp.volume_preserving_ofLp (Fin 2))

lemma hasDerivAt_planeOf_snd (a t : ℝ) :
    HasDerivAt (fun t => planeOf a t) (EuclideanSpace.single 1 1) t := by
  have := ((hasDerivAt_id t).smul_const (EuclideanSpace.single 1 (1 : ℝ) : Plane)).const_add
    (a • (EuclideanSpace.single 0 1 : Plane))
  simpa [planeOf] using this

lemma hasDerivAt_planeOf_fst (a t : ℝ) :
    HasDerivAt (fun t => planeOf t a) (EuclideanSpace.single 0 1) t := by
  have := ((hasDerivAt_id t).smul_const (EuclideanSpace.single 0 (1 : ℝ) : Plane)).add_const
    (a • (EuclideanSpace.single 1 1 : Plane))
  simpa [planeOf] using this

lemma measurableSet_regular_zeros {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) (i : Fin 2) :
    MeasurableSet {x | h x = 0 ∧ pderiv i h x ≠ 0} := by
  have hc : Continuous (pderiv i h) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact (isClosed_eq hh.continuous continuous_const).measurableSet.inter
    (isOpen_ne_fun hc continuous_const).measurableSet

/-- **Lemma 9.10, directional form (second coordinate).** -/
lemma null_regular_zeros_one {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) :
    volume {x | h x = 0 ∧ pderiv 1 h x ≠ 0} = 0 := by
  set S := {x | h x = 0 ∧ pderiv 1 h x ≠ 0} with hSdef
  have hS : MeasurableSet S := measurableSet_regular_zeros hh 1
  set T : Set (ℝ × ℝ) := {p | planeOf p.1 p.2 ∈ S} with hTdef
  have hT : MeasurableSet T := hS.preimage continuous_planeOf.measurable
  have hST : S = (fun x : Plane => (x 0, x 1)) ⁻¹' T := by
    ext x; simp only [hTdef, mem_preimage, mem_setOf_eq, planeOf_apply]
  rw [hST, measurePreserving_coords.measure_preimage hT.nullMeasurableSet]
  refine null_of_slices_countable hT fun a => ?_
  refine countable_of_regular_zeros (g := fun t => h (planeOf a t)) fun t ht => ⟨ht.1, _, ht.2, ?_⟩
  exact ((hh.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_planeOf_snd a t)

/-- **Lemma 9.10, directional form (first coordinate).** -/
lemma null_regular_zeros_zero {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) :
    volume {x | h x = 0 ∧ pderiv 0 h x ≠ 0} = 0 := by
  set S := {x | h x = 0 ∧ pderiv 0 h x ≠ 0} with hSdef
  have hS : MeasurableSet S := measurableSet_regular_zeros hh 0
  set T : Set (ℝ × ℝ) := {p | planeOf p.2 p.1 ∈ S} with hTdef
  have hT : MeasurableSet T :=
    hS.preimage (continuous_planeOf.comp continuous_swap).measurable
  have hST : S = (fun x : Plane => (x 1, x 0)) ⁻¹' T := by
    ext x; simp only [hTdef, mem_preimage, mem_setOf_eq, planeOf_apply]
  have hmp : MeasurePreserving (fun x : Plane => (x 1, x 0)) volume volume := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).comp measurePreserving_coords
    simpa [← Measure.volume_eq_prod] using! this
  rw [hST, hmp.measure_preimage hT.nullMeasurableSet]
  refine null_of_slices_countable hT fun a => ?_
  refine countable_of_regular_zeros (g := fun t => h (planeOf t a)) fun t ht => ⟨ht.1, _, ht.2, ?_⟩
  exact ((hh.differentiable one_ne_zero) _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_planeOf_fst a t)

end Buckling
end
end ChunkedSource036
/- END SOURCE 036 -/

/- BEGIN SOURCE 037: RequestProject/Profiles/Defs.lean -/
section ChunkedSource037

/-!
# Fixed parameters, radial profiles and the transformed test function

Definitions 3.1, 4.1, 4.4, 4.6, 9.2, 9.6, 9.8 and 9.13 of the paper.
-/

@[expose] public section

open Real

namespace Buckling

/-! ### Fixed parameters (Definition 3.1) -/

/-- `α = q/k`. -/
noncomputable def pAlpha : ℝ := jq / jk
/-- `λ = α²`. -/
noncomputable def pLam : ℝ := pAlpha ^ 2
/-- `c = -J₀(k)`. -/
noncomputable def pc : ℝ := -besselJ 0 jk
/-- `σ = 1 + c`. -/
noncomputable def pSigma : ℝ := 1 + pc
/-- `ℓ = 1/σ`. -/
noncomputable def pEll : ℝ := 1 / pSigma
/-- `K = (α J₁(q)/c)²`. -/
noncomputable def pK : ℝ := (pAlpha * besselJ 1 jq / pc) ^ 2
/-- `β = √K`. -/
noncomputable def pBeta : ℝ := Real.sqrt pK
/-- `a₀ = 1 - λ`. -/
noncomputable def pa0 : ℝ := 1 - pLam

/-- `B(x) = x (J₀(x)² + J₁(x)²) - J₀(x) J₁(x)`. -/
noncomputable def besselB (x : ℝ) : ℝ :=
  x * (besselJ 0 x ^ 2 + besselJ 1 x ^ 2) - besselJ 0 x * besselJ 1 x

/-! ### Radial variables (Definition 4.1) -/

/-- `p(r) = J₁(r)`. -/
noncomputable def rp (r : ℝ) : ℝ := besselJ 1 r
/-- `u(r) = J₀(r) + c`. -/
noncomputable def ru (r : ℝ) : ℝ := besselJ 0 r + pc
/-- `φ(r) = J₀(α r)`. -/
noncomputable def rPhi (r : ℝ) : ℝ := besselJ 0 (pAlpha * r)
/-- `t(r) = u(r)/p(r)`. -/
noncomputable def rt (r : ℝ) : ℝ := ru r / rp r

/-- The inverse `r : (0, ∞) → (0, k)` of `t` (Lemma 4.3); junk value `0` elsewhere. -/
noncomputable def rOf (t : ℝ) : ℝ :=
  open Classical in
  if h : ∃ r ∈ Set.Ioo 0 jk, rt r = t then h.choose else 0

/-! ### Profiles (Definitions 4.4 and 4.6) -/

/-- `f(t) = φ(r(t))/p(r(t))` for `t > 0`. -/
noncomputable def pf (t : ℝ) : ℝ := rPhi (rOf t) / rp (rOf t)

/-- `G(r) = K + (α r B(α r) - K r B(r))/p(r)²` (radial version). -/
noncomputable def rG (r : ℝ) : ℝ :=
  pK + (pAlpha * r * besselB (pAlpha * r) - pK * r * besselB r) / rp r ^ 2

/-- `b(r) = -K A + G/r - φ φ_r / p²`, where `A = -p_r/p` (radial version). -/
noncomputable def rb (r : ℝ) : ℝ :=
  pK * (deriv rp r / rp r) + rG r / r - rPhi r * deriv rPhi r / rp r ^ 2

/-- `G` in the variable `t`. -/
noncomputable def pG (t : ℝ) : ℝ := rG (rOf t)
/-- `b` in the variable `t`. -/
noncomputable def pb (t : ℝ) : ℝ := rb (rOf t)

/-! ### Parity extensions (Definition 9.2) -/

/-- The even extension of `f` to `ℝ`, with `f(0) = β`. -/
noncomputable def fExt (s : ℝ) : ℝ := if s = 0 then pBeta else pf |s|
/-- The odd extension of `b` to `ℝ`, with `b(0) = 0`. -/
noncomputable def bExt (s : ℝ) : ℝ := if s = 0 then 0 else SignType.sign s * pb |s|
/-- The even extension of `G` to `ℝ`, with `G(0) = 0`. -/
noncomputable def GExt (s : ℝ) : ℝ := if s = 0 then 0 else pG |s|

/-! ### Perspectives (Definitions 9.6 and 9.8) -/

/-- `𝓕(A,P) = P f(A/P)` for `P > 0` and `𝓕(A,0) = ℓ|A|`. -/
noncomputable def perspF (A P : ℝ) : ℝ := if 0 < P then P * fExt (A / P) else pEll * |A|

/-- `𝓑(A,P) = P b(A/P)` for `P > 0` and `𝓑(A,0) = 2λℓA`. -/
noncomputable def perspB (A P : ℝ) : ℝ := if 0 < P then P * bExt (A / P) else 2 * pLam * pEll * A

/-- `Ψ(A,ξ) = G(A/|ξ|) ξ` for `ξ ≠ 0` and `Ψ(A,0) = 0`. -/
noncomputable def perspPsi (A : ℝ) (ξ : Plane) : Plane :=
  if ξ = 0 then 0 else GExt (A / ‖ξ‖) • ξ

/-- The transformed test function `F = 𝓕(U, |∇U|)` (Definition 9.13). -/
noncomputable def transformF (U : Plane → ℝ) (x : Plane) : ℝ :=
  perspF (U x) ‖fderiv ℝ U x‖

end Buckling
end
end ChunkedSource037
/- END SOURCE 037 -/

/- BEGIN SOURCE 038: RequestProject/Bessel/Coarse.lean -/
section ChunkedSource038

/-!
# Coarse parameter bounds (Lemmas 3.2 and 3.8)
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- From E3: `|J_n(x)| ≤ 1`. -/
lemma abs_besselJ_le_one (hI : ExtIntegral) (n : ℕ) (x : ℝ) : |besselJ n x| ≤ 1 := by
  rw [hI n x, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / π)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π) (C := 1)
    (f := fun θ => Real.cos (x * Real.sin θ - n * θ)) (fun θ _ => by
      rw [Real.norm_eq_abs]; exact abs_cos_le_one _)
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos pi_pos, one_mul] at h
  calc 1 / π * |∫ θ in (0 : ℝ)..π, Real.cos (x * Real.sin θ - n * θ)| ≤ 1 / π * π := by gcongr
    _ = 1 := by field_simp

/-- `|J₀'| ≤ 1`, i.e. `J₀` is `1`-Lipschitz (from E3). -/
lemma abs_besselJ_zero_sub (hI : ExtIntegral) (x y : ℝ) :
    |besselJ 0 x - besselJ 0 y| ≤ |x - y| := by
  have hL : LipschitzWith 1 (besselJ 0) := by
    apply lipschitzWith_of_nnnorm_deriv_le (differentiable_besselJ 0)
    intro z
    rw [deriv_besselJ_zero, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs, abs_neg]
    simpa using abs_besselJ_le_one hI 1 z
  have := hL.dist_le_mul x y
  simpa [Real.dist_eq] using this

/-- `|J₁'| ≤ 1`, i.e. `J₁` is `1`-Lipschitz (from E3). -/
lemma abs_besselJ_one_sub (hI : ExtIntegral) (x y : ℝ) :
    |besselJ 1 x - besselJ 1 y| ≤ |x - y| := by
  have hL : LipschitzWith 1 (besselJ 1) := by
    apply lipschitzWith_of_nnnorm_deriv_le (differentiable_besselJ 1)
    intro z
    rw [show (1 : ℕ) = 0 + 1 from rfl, deriv_besselJ_succ 0, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.norm_eq_abs]
    have h0 := abs_besselJ_le_one hI 0 z
    have h2 := abs_besselJ_le_one hI 2 z
    simp only [NNReal.coe_one]
    rw [abs_div, abs_two]
    calc |besselJ 0 z - besselJ (0 + 2) z| / 2 ≤ (|besselJ 0 z| + |besselJ 2 z|) / 2 := by
          gcongr; exact abs_sub _ _
      _ ≤ 1 := by linarith
  have := hL.dist_le_mul x y
  simpa [Real.dist_eq] using this

/-- **Lemma 3.2 (signs of the fixed parameters).** -/
theorem parameter_signs (hZ : ExtZeros) :
    0 < jq ∧ jq < jk ∧ 0 < pAlpha ∧ pAlpha < 1 ∧ 0 < pLam ∧ pLam < 1 ∧ 0 < pc ∧
      0 < besselJ 1 jq ∧ 0 < pK := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := root_boxes hZ
  obtain ⟨hmono0, -, hzero0, hall0, hinter0⟩ := hZ 0 (by norm_num)
  have hq0 : 0 < jq := by linarith
  have hqk : jq < jk := by linarith
  have hk0 : 0 < jk := by linarith
  have hα0 : 0 < pAlpha := div_pos hq0 hk0
  have hα1 : pAlpha < 1 := (div_lt_one hk0).mpr hqk
  -- `J₀(k) < 0`: `J₀` has no zero in `(q, q₂)` and is negative just after `q`
  have hc : 0 < pc := by
    unfold pc
    have hI := hinter0 1 le_rfl
    -- `J₀` is negative at `k`: it has a sign change at `q`, no zero in `(q, q₂)`
    by_contra hcon
    push_neg at hcon
    have hJk : 0 ≤ besselJ 0 jk := by linarith
    -- `J₀(3.83170) < 0` from the certificate, and `|k - 3.8317| < 10⁻⁵` would need E3;
    -- instead use the intermediate value theorem with `J₀(2.40483) < 0`.
    have hneg : besselJ 0 (240483 / 100000) < 0 := by linarith [besselJ_bounds_row2.2]
    obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc (240483 / 100000 : ℝ) jk, besselJ 0 z = 0 :=
      intermediate_value_Icc (by linarith) (continuous_besselJ 0).continuousOn ⟨hneg.le, hJk⟩
    obtain ⟨n, hn, hnz⟩ := hall0 z (by linarith [hz.1]) hz0
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      change jq = z at hnz
      linarith [hz.1]
    · have : besselZero 0 2 ≤ besselZero 0 n := hmono0.le_iff_le.mpr h
      linarith [hz.2, hI.2]
  have hJ1q : 0 < besselJ 1 jq := by
    have := besselJ_one_pos_small
    -- `J₁ > 0` on `(0, k)`: no zero there, positive near `0`
    by_contra hcon
    push_neg at hcon
    obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc (1 : ℝ) jq, besselJ 1 z = 0 :=
      intermediate_value_Icc' (by linarith) (continuous_besselJ 1).continuousOn
        ⟨hcon, (besselJ_one_pos_small 1 one_pos (by norm_num)).le⟩
    obtain ⟨-, -, -, hall1, -⟩ := hZ 1 (by norm_num)
    obtain ⟨hmono1, -, -, -, -⟩ := hZ 1 (by norm_num)
    obtain ⟨n, hn, hnz⟩ := hall1 z (by linarith [hz.1]) hz0
    have : besselZero 1 1 ≤ besselZero 1 n := hmono1.le_iff_le.mpr hn
    change jk ≤ besselZero 1 n at this
    linarith [hz.2]
  refine ⟨hq0, hqk, hα0, hα1, by unfold pLam; positivity, ?_, hc, hJ1q, ?_⟩
  · unfold pLam; nlinarith
  · unfold pK; have : pAlpha * besselJ 1 jq / pc ≠ 0 := by positivity
    positivity

lemma coarse_J1q (hZ : ExtZeros) (hI : ExtIntegral) : (5191 / 10000 : ℝ) < besselJ 1 jq := by
  obtain ⟨hq1, hq2, -⟩ := root_boxes hZ
  have := abs_besselJ_one_sub hI jq (240482 / 100000)
  have hr := besselJ_bounds_row11.1
  rw [abs_of_pos (by linarith : (0 : ℝ) < jq - 240482 / 100000), abs_le] at this
  linarith [this.1]

lemma coarse_J0k (hZ : ExtZeros) (hI : ExtIntegral) :
    (-4028 / 10000 : ℝ) < besselJ 0 jk ∧ besselJ 0 jk < -4027 / 10000 := by
  obtain ⟨-, -, hk1, hk2, -⟩ := root_boxes hZ
  have := abs_besselJ_zero_sub hI jk (383170 / 100000)
  have hr := besselJ_bounds_row12
  rw [abs_of_pos (by linarith : (0 : ℝ) < jk - 383170 / 100000), abs_le] at this
  constructor <;> linarith [this.1, this.2, hr.1, hr.2]

lemma coarse_J1q2 (hZ : ExtZeros) (hI : ExtIntegral) :
    |besselJ 1 (besselZero 0 2)| < 3404 / 10000 := by
  obtain ⟨-, -, -, -, hQ1, hQ2, -⟩ := root_boxes hZ
  have := abs_besselJ_one_sub hI (besselZero 0 2) (55201 / 10000)
  have hr := besselJ_bounds_row13
  have hd : |besselZero 0 2 - 55201 / 10000| < 1 / 10000 := by
    rw [abs_lt]; constructor <;> linarith
  rw [abs_le] at this
  rw [abs_lt]
  constructor <;> linarith [this.1, this.2, hr.1, hr.2]

lemma coarse_c (hZ : ExtZeros) (hI : ExtIntegral) : (4027 / 10000 : ℝ) < pc ∧ pc < 4028 / 10000 := by
  have := coarse_J0k hZ hI
  unfold pc; constructor <;> linarith [this.1, this.2]

lemma coarse_alpha (hZ : ExtZeros) : (6276 / 10000 : ℝ) < pAlpha ∧ pAlpha < 628 / 1000 := by
  obtain ⟨hq1, hq2, hk1, hk2, -⟩ := root_boxes hZ
  have hk0 : 0 < jk := by linarith
  unfold pAlpha
  constructor
  · rw [lt_div_iff₀ hk0]; nlinarith
  · rw [div_lt_iff₀ hk0]; nlinarith

lemma coarse_lam (hZ : ExtZeros) : (1 / 4 : ℝ) < pLam ∧ pLam < 2 / 5 := by
  obtain ⟨h1, h2⟩ := coarse_alpha hZ
  unfold pLam; constructor <;> nlinarith

lemma coarse_K (hZ : ExtZeros) (hI : ExtIntegral) : (654 / 1000 : ℝ) < pK := by
  obtain ⟨hα1, -⟩ := coarse_alpha hZ
  have hJ := coarse_J1q hZ hI
  obtain ⟨-, hc2⟩ := coarse_c hZ hI
  have hc0 : 0 < pc := by linarith [(coarse_c hZ hI).1]
  have hα0 : 0 < pAlpha := by linarith
  set X := pAlpha * besselJ 1 jq / pc with hX
  have h1 : (6276 / 10000 : ℝ) * (5191 / 10000) < pAlpha * besselJ 1 jq :=
    mul_lt_mul hα1 hJ.le (by norm_num) hα0.le
  have h2 : (6276 / 10000 : ℝ) * (5191 / 10000) / (4028 / 10000) < X := by
    rw [hX, div_lt_div_iff₀ (by norm_num) hc0]
    calc (6276 / 10000 : ℝ) * (5191 / 10000) * pc < (6276 / 10000 : ℝ) * (5191 / 10000) * (4028 / 10000) := by
          gcongr
      _ < pAlpha * besselJ 1 jq * (4028 / 10000) := by gcongr
  have h3 : (654 / 1000 : ℝ) < ((6276 / 10000 : ℝ) * (5191 / 10000) / (4028 / 10000)) ^ 2 := by
    norm_num
  unfold pK
  rw [← hX]
  calc (654 / 1000 : ℝ) < ((6276 / 10000 : ℝ) * (5191 / 10000) / (4028 / 10000)) ^ 2 := h3
    _ < X ^ 2 := by gcongr

lemma coarse_J1q2_sq (hZ : ExtZeros) (hI : ExtIntegral) :
    besselJ 1 (besselZero 0 2) ^ 2 < 116 / 1000 := by
  have h := coarse_J1q2 hZ hI
  have : besselJ 1 (besselZero 0 2) ^ 2 = |besselJ 1 (besselZero 0 2)| ^ 2 := (sq_abs _).symm
  rw [this]
  have h0 := abs_nonneg (besselJ 1 (besselZero 0 2))
  nlinarith

lemma coarse_Bq2 (hZ : ExtZeros) (hI : ExtIntegral) : besselB (besselZero 0 2) < 640 / 1000 := by
  obtain ⟨-, -, -, -, hQ1, hQ2, -⟩ := root_boxes hZ
  obtain ⟨-, -, hzero0, -, -⟩ := hZ 0 (by norm_num)
  have h := coarse_J1q2 hZ hI
  unfold besselB
  rw [(hzero0 2 (by norm_num)).1]
  have : besselJ 1 (besselZero 0 2) ^ 2 = |besselJ 1 (besselZero 0 2)| ^ 2 := (sq_abs _).symm
  have h0 := abs_nonneg (besselJ 1 (besselZero 0 2))
  have h3 : |besselJ 1 (besselZero 0 2)| ^ 2 < (3404 / 10000) ^ 2 := by gcongr
  have h4 : 0 ≤ besselJ 1 (besselZero 0 2) ^ 2 := sq_nonneg _
  nlinarith

lemma coarse_J0k3 (hZ : ExtZeros) : besselJ 0 (besselZero 1 3) < -2497 / 10000 := by
  obtain ⟨-, -, -, -, -, -, hK1, hK2, hL1, hL2⟩ := root_boxes hZ
  obtain ⟨hmono1, -, hzero1, hall1, -⟩ := hZ 1 (by norm_num)
  set κ3 := besselZero 1 3
  have hr14 := besselJ_bounds_row14.2
  have hno : ∀ z ∈ Ioo (10173 / 1000 : ℝ) (10174 / 1000), z ≠ κ3 → besselJ 1 z ≠ 0 := by
    intro z hz hzk hz0
    obtain ⟨n, hn, hnz⟩ := hall1 z (by linarith [hz.1]) hz0
    rcases lt_trichotomy n 3 with h | h | h
    · have : besselZero 1 n ≤ besselZero 1 2 := hmono1.le_iff_le.mpr (by omega)
      linarith [hz.1]
    · subst h; exact hzk hnz.symm
    · have hgap := besselZero_one_gap hZ 3 (by norm_num)
      have : besselZero 1 4 ≤ besselZero 1 n := hmono1.le_iff_le.mpr (by omega)
      have := Real.pi_gt_three
      linarith [hz.2]
  have hpos : ∀ z ∈ Ioo (10173 / 1000 : ℝ) κ3, 0 < besselJ 1 z := by
    intro z hz
    by_contra hneg; push_neg at hneg
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hz.1.le (continuous_besselJ 1).continuousOn
      ⟨hneg, (besselJ_bounds_row9.1).le.trans' (by norm_num)⟩
    rcases eq_or_lt_of_le hw.1 with h | h
    · rw [← h] at hw0; linarith [besselJ_bounds_row9.1]
    · exact hno w ⟨h, by linarith [hw.2, hz.2]⟩ (by linarith [hw.2, hz.2]) hw0
  have hneg : ∀ z ∈ Ioo κ3 (10174 / 1000 : ℝ), besselJ 1 z < 0 := by
    intro z hz
    by_contra hp; push_neg at hp
    obtain ⟨w, hw, hw0⟩ := intermediate_value_Icc' hz.2.le (continuous_besselJ 1).continuousOn
      ⟨(besselJ_bounds_row10.2).le.trans (by norm_num), hp⟩
    rcases eq_or_lt_of_le hw.2 with h | h
    · rw [h] at hw0; linarith [besselJ_bounds_row10.2]
    · exact hno w ⟨by linarith [hw.1, hz.1], h⟩ (by linarith [hw.1, hz.1]) hw0
  rcases le_or_gt (101735 / 10000 : ℝ) κ3 with h | h
  · have hanti : AntitoneOn (besselJ 0) (Icc (101735 / 10000 : ℝ) κ3) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) (continuous_besselJ 0).continuousOn
        (differentiable_besselJ 0).differentiableOn
      intro z hz
      rw [interior_Icc] at hz
      rw [deriv_besselJ_zero]
      linarith [hpos z ⟨by linarith [hz.1], hz.2⟩]
    have := hanti ⟨le_rfl, h⟩ ⟨h, le_rfl⟩ h
    linarith
  · have hmono : MonotoneOn (besselJ 0) (Icc κ3 (101735 / 10000 : ℝ)) := by
      apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (continuous_besselJ 0).continuousOn
        (differentiable_besselJ 0).differentiableOn
      intro z hz
      rw [interior_Icc] at hz
      rw [deriv_besselJ_zero]
      linarith [hneg z ⟨hz.1, by linarith [hz.2]⟩]
    have := hmono ⟨le_rfl, h.le⟩ ⟨h.le, le_rfl⟩ h.le
    linarith

lemma coarse_Bk3 (hZ : ExtZeros) : (634 / 1000 : ℝ) < besselB (besselZero 1 3) := by
  obtain ⟨-, -, -, -, -, -, -, -, hL1, hL2⟩ := root_boxes hZ
  obtain ⟨-, -, hzero1, -, -⟩ := hZ 1 (by norm_num)
  have h := coarse_J0k3 hZ
  unfold besselB
  rw [(hzero1 3 (by norm_num)).1]
  have h1 : (2497 / 10000 : ℝ) ^ 2 < besselJ 0 (besselZero 1 3) ^ 2 := by nlinarith
  have h2 : (10173 / 1000 : ℝ) * (2497 / 10000) ^ 2 <
      besselZero 1 3 * besselJ 0 (besselZero 1 3) ^ 2 := by
    apply mul_lt_mul hL1 h1.le (by norm_num) (by linarith)
  have h3 : (634 / 1000 : ℝ) < (10173 / 1000 : ℝ) * (2497 / 10000) ^ 2 := by norm_num
  nlinarith

lemma coarse_order (hZ : ExtZeros) :
    jk < pAlpha * besselZero 1 2 ∧ pAlpha * besselZero 1 2 < besselZero 0 2 ∧
      besselZero 0 2 < pAlpha * besselZero 1 3 := by
  obtain ⟨-, -, hk1, hk2, hQ1, hQ2, hK1, hK2, hL1, hL2⟩ := root_boxes hZ
  obtain ⟨hα1, hα2⟩ := coarse_alpha hZ
  refine ⟨?_, ?_, ?_⟩
  · have : (6276 / 10000 : ℝ) * (7015 / 1000) < pAlpha * besselZero 1 2 :=
      mul_lt_mul hα1 hK1.le (by norm_num) (by linarith)
    linarith
  · have : pAlpha * besselZero 1 2 < (628 / 1000 : ℝ) * (7016 / 1000) :=
      mul_lt_mul' hα2.le hK2 (by linarith) (by norm_num)
    linarith
  · have : (6276 / 10000 : ℝ) * (10173 / 1000) < pAlpha * besselZero 1 3 :=
      mul_lt_mul hα1 hL1.le (by norm_num) (by linarith)
    linarith

/-- **Lemma 3.8 (coarse parameter bounds).** -/
theorem coarse_bounds (hZ : ExtZeros) (hI : ExtIntegral) :
    (6276 / 10000 : ℝ) < pAlpha ∧ pAlpha < 628 / 1000 ∧
    (1 / 4 : ℝ) < pLam ∧ pLam < 2 / 5 ∧
    (4027 / 10000 : ℝ) < pc ∧ pc < 4028 / 10000 ∧
    (19 / 5 : ℝ) < jk ∧ jk < 4 ∧
    (654 / 1000 : ℝ) < pK ∧
    (634 / 1000 : ℝ) < besselB (besselZero 1 3) ∧ besselB (besselZero 0 2) < 640 / 1000 ∧
    besselJ 1 (besselZero 0 2) ^ 2 < 116 / 1000 ∧
    jk < pAlpha * besselZero 1 2 ∧ pAlpha * besselZero 1 2 < besselZero 0 2 ∧
    besselZero 0 2 < pAlpha * besselZero 1 3 := by
  obtain ⟨-, -, hk1, hk2, -⟩ := root_boxes hZ
  exact ⟨(coarse_alpha hZ).1, (coarse_alpha hZ).2, (coarse_lam hZ).1, (coarse_lam hZ).2,
    (coarse_c hZ hI).1, (coarse_c hZ hI).2, by linarith, by linarith, coarse_K hZ hI,
    coarse_Bk3 hZ, coarse_Bq2 hZ hI, coarse_J1q2_sq hZ hI, (coarse_order hZ).1,
    (coarse_order hZ).2.1, (coarse_order hZ).2.2⟩

end Buckling
end
end ChunkedSource038
/- END SOURCE 038 -/

/- BEGIN SOURCE 039: RequestProject/Sobolev/Mollification.lean -/
section ChunkedSource039

/-!
# Mollification in `H¹(ℝ²)` and `H²(ℝ²)` (External theorem E8)

We prove the two forms `ExtMollification` and `ExtMollification2` of the paper's external
theorem E8 (Evans–Gariepy §4.2.1) by the standard mollifier argument:

* `moll n f = ηₙ * f`, with `ηₙ` a normalized smooth bump supported in `B(0, 1/(n+1))`;
* `‖ηₙ * f‖₂ ≤ ‖f‖₂` (Cauchy–Schwarz and Tonelli);
* `ηₙ * g → g` uniformly, hence in `L²`, for continuous compactly supported `g`; by density
  `ηₙ * f → f` in `L²` for every `f ∈ L²`;
* `∂ᵢ(ηₙ * v) = ηₙ * wᵢ` when `w` is the weak gradient of `v`;
* `ηₙ * v` is smooth and supported in the closed `1/(n+1)`-neighbourhood of `K` when `v`
  vanishes a.e. outside `K`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set Function ContinuousLinearMap
open scoped Convolution Pointwise ENNReal

namespace Buckling

/-- The smooth bump with support radius `1/(n+1)`. -/
noncomputable def mollBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := 1 / (2 * (n + 1))
  rOut := 1 / (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply one_div_lt_one_div_of_lt (by positivity)
    linarith

/-- The mollification `ηₙ * f`. -/
noncomputable def moll (n : ℕ) (f : Plane → ℝ) : Plane → ℝ :=
  ((mollBump n).normed volume) ⋆[lsmul ℝ ℝ, volume] f

lemma mollBump_rOut (n : ℕ) : (mollBump n).rOut = 1 / (n + 1) := rfl

lemma eventually_one_div_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine eventually_atTop.2 ⟨N, fun n hn => le_trans ?_ hN.le⟩
  apply one_div_le_one_div_of_le (by positivity)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

lemma moll_contDiff {f : Plane → ℝ} (hf : LocallyIntegrable f volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (moll n f) :=
  (mollBump n).hasCompactSupport_normed.contDiff_convolution_left _ (mollBump n).contDiff_normed hf

lemma moll_exists {f : Plane → ℝ} (hf : LocallyIntegrable f volume) (n : ℕ) :
    ConvolutionExists ((mollBump n).normed volume) f (lsmul ℝ ℝ) volume :=
  ((mollBump n).hasCompactSupport_normed (μ := volume)).convolutionExists_left (lsmul ℝ ℝ)
    (mollBump n).continuous_normed hf

lemma moll_sub {f g : Plane → ℝ} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) (n : ℕ) :
    moll n (fun x => f x - g x) = fun x => moll n f x - moll n g x := by
  ext x
  simp only [moll, convolution_def]
  rw [← integral_sub (moll_exists hf n x) (moll_exists hg n x)]
  congr 1; ext t; simp [mul_sub]

lemma moll_congr_ae {f g : Plane → ℝ} (h : f =ᵐ[volume] g) (n : ℕ) : moll n f = moll n g :=
  convolution_congr _ (EventuallyEq.refl _ _) h

/-- Cauchy–Schwarz for a probability weight: `(∫ a b)² ≤ ∫ a b²` when `∫ a = 1`. -/
lemma lintegral_sq_le_of_weight {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : α → ℝ≥0∞} (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (h1 : ∫⁻ t, a t ∂μ = 1) :
    (∫⁻ t, a t * b t ∂μ) ^ (2 : ℝ) ≤ ∫⁻ t, a t * b t ^ (2 : ℝ) ∂μ := by
  have hF : AEMeasurable (fun t => a t ^ (1 / 2 : ℝ)) μ := ha.pow_const _
  have hG : AEMeasurable (fun t => a t ^ (1 / 2 : ℝ) * b t) μ := (ha.pow_const _).mul hb
  have H := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two) hF hG
  have e1 : ∀ t, ((fun t => a t ^ (1 / 2 : ℝ)) * fun t => a t ^ (1 / 2 : ℝ) * b t) t
      = a t * b t := by
    intro t
    simp only [Pi.mul_apply]
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ t, (a t ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a t := by
    intro t; rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ t, (a t ^ (1 / 2 : ℝ) * b t) ^ (2 : ℝ) = a t * b t ^ (2 : ℝ) := by
    intro t; rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]
  simp only [e1, e2, e3, h1, ENNReal.one_rpow, one_mul] at H
  calc (∫⁻ t, a t * b t ∂μ) ^ (2 : ℝ)
      ≤ ((∫⁻ t, a t * b t ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) :=
        ENNReal.rpow_le_rpow H (by norm_num)
    _ = _ := by rw [← ENNReal.rpow_mul]; norm_num

/-- Young's inequality for the mollifier: `‖ηₙ * f‖₂ ≤ ‖f‖₂`. -/
lemma eLpNorm_moll_le {f : Plane → ℝ} (hf : AEStronglyMeasurable f volume) (n : ℕ) :
    eLpNorm (moll n f) 2 volume ≤ eLpNorm f 2 volume := by
  set φ := (mollBump n).normed volume with hφdef
  set a : Plane → ℝ≥0∞ := fun t => ‖φ t‖ₑ with hadef
  have ha : Measurable a := (mollBump n).continuous_normed.measurable.enorm
  have ha1 : ∫⁻ t, a t = 1 := by
    rw [hadef, ← ofReal_integral_norm_eq_lintegral_enorm (mollBump n).integrable_normed]
    simp only [Real.norm_eq_abs, abs_of_nonneg ((mollBump n).nonneg_normed _)]
    rw [(mollBump n).integral_normed, ENNReal.ofReal_one]
  have hb : AEMeasurable (fun p : Plane × Plane => ‖f (p.1 - p.2)‖ₑ) (volume.prod volume) :=
    (hf.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant volume volume)).enorm
  have hbx : ∀ x, AEMeasurable (fun t => ‖f (x - t)‖ₑ) volume := fun x =>
    (hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)).enorm
  have hpt : ∀ x, ‖moll n f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ t, a t * ‖f (x - t)‖ₑ ^ (2 : ℝ) := by
    intro x
    refine le_trans ?_ (lintegral_sq_le_of_weight ha.aemeasurable (hbx x) ha1)
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    simp [a, φ, enorm_mul]
  have hprod : AEMeasurable (uncurry fun x t => a t * ‖f (x - t)‖ₑ ^ (2 : ℝ))
      (volume.prod volume) :=
    (ha.comp measurable_snd).aemeasurable.mul (hb.pow_const _)
  have key : ∫⁻ x, ‖moll n f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
    calc ∫⁻ x, ‖moll n f x‖ₑ ^ (2 : ℝ) ≤ ∫⁻ x, ∫⁻ t, a t * ‖f (x - t)‖ₑ ^ (2 : ℝ) :=
          lintegral_mono hpt
      _ = ∫⁻ t, ∫⁻ x, a t * ‖f (x - t)‖ₑ ^ (2 : ℝ) := lintegral_lintegral_swap hprod
      _ = ∫⁻ t, a t * ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by
          congr 1; ext t
          rw [lintegral_const_mul' _ _ (by simp [a]),
            lintegral_sub_right_eq_self (fun x => ‖f x‖ₑ ^ (2 : ℝ)) t]
      _ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) := by rw [lintegral_mul_const _ ha, ha1, one_mul]
  have hm : AEStronglyMeasurable (moll n f) volume := by
    simpa only [moll] using
      ((mollBump n).continuous_normed.aestronglyMeasurable.convolution
        (L := lsmul ℝ ℝ) hf)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_le_rpow key (by norm_num)

lemma tendsto_moll_of_continuous {g : Plane → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun n => eLpNorm (fun x => moll n g x - g x) 2 volume) atTop (𝓝 0) := by
  set C := cthickening 1 (tsupport g) with hCdef
  have hCc : IsCompact C := hc.isCompact.cthickening
  set M : ℝ≥0∞ := volume C ^ (2 : ℝ≥0∞).toReal⁻¹ with hMdef
  have hM : M ≠ ⊤ := by
    simp only [hMdef]
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) hCc.measure_lt_top.ne
  have hsupp : ∀ n : ℕ, support (fun x => moll n g x - g x) ⊆ C := by
    intro n x hx
    by_contra hxC
    apply hx
    have hg0 : g x = 0 := by
      by_contra h; exact hxC (self_subset_cthickening _ (subset_tsupport _ h))
    have hm0 : moll n g x = 0 := by
      by_contra h
      have := (support_convolution_subset (lsmul ℝ ℝ) (μ := volume)) h
      rw [(mollBump n).support_normed_eq] at this
      obtain ⟨a, ha, b, hb, hab⟩ := this
      apply hxC
      refine mem_cthickening_of_dist_le x b 1 _ (subset_tsupport _ hb) ?_
      rw [← hab, dist_eq_norm, add_sub_cancel_right]
      have : ‖a‖ < 1 / (n + 1) := by simpa [mollBump_rOut] using ha
      have h1 : (1 : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      linarith
    simp [hm0, hg0]
  have hbound : ∀ η > 0, ∀ᶠ n in atTop,
      eLpNorm (fun x => moll n g x - g x) 2 volume ≤ M * ENNReal.ofReal η := by
    intro η hη
    obtain ⟨δ, hδ, hgδ⟩ := Metric.uniformContinuous_iff.mp
      (hc.uniformContinuous_of_continuous hg) η hη
    filter_upwards [eventually_one_div_le hδ] with n hn
    have hmeas : AEStronglyMeasurable (fun x => moll n g x - g x) volume :=
      ((moll_contDiff hg.locallyIntegrable n).continuous.fun_sub hg).aestronglyMeasurable
    rw [← eLpNorm_restrict_eq_of_support_subset hmeas (hsupp n)]
    refine (eLpNorm_le_of_ae_bound (C := η) hmeas.restrict
      (Eventually.of_forall fun x => ?_)).trans ?_
    · rw [← dist_eq_norm]
      exact (mollBump n).dist_normed_convolution_le hg.aestronglyMeasurable
        (fun y hy => (hgδ (lt_of_lt_of_le (mem_ball.1 hy) (by rw [mollBump_rOut]; exact hn))).le)
    · simp [hMdef]
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hT : Tendsto (fun η : ℝ => M * ENNReal.ofReal η) (𝓝[>] 0) (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul
      ((ENNReal.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
      (Or.inr hM)
    simpa using this
  obtain ⟨η, hη1, hη2⟩ := ((hT.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  filter_upwards [hbound η hη2] with n hn
  exact hn.trans hη1.le

lemma tendsto_moll {f : Plane → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => moll n f x - f x) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := by simp [hε.ne']
  obtain ⟨g, hgc, hfg, hgcont, -⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (by simp) hε3
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hgl : LocallyIntegrable g volume := hgcont.locallyIntegrable
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 (tendsto_moll_of_continuous hgcont hgc)) (ε / 3)
    (by simp [hε.ne'])] with n hn
  have hsplit : (fun x => moll n f x - f x) =
      (fun x => moll n (fun y => f y - g y) x + (moll n g x - g x)) + (fun x => g x - f x) := by
    rw [moll_sub hfl hgl]; ext x; simp
  have hm1 : AEStronglyMeasurable (moll n (fun y => f y - g y)) volume :=
    (moll_contDiff (hfl.sub hgl) n).continuous.aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun x => moll n g x - g x) volume :=
    ((moll_contDiff hgl n).continuous.sub hgcont).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun x => g x - f x) volume :=
    hgcont.aestronglyMeasurable.fun_sub hf.aestronglyMeasurable
  rw [hsplit]
  calc eLpNorm (((fun x => moll n (fun y => f y - g y) x + (moll n g x - g x)))
          + (fun x => g x - f x)) 2 volume
      ≤ eLpNorm (fun x => moll n (fun y => f y - g y) x + (moll n g x - g x)) 2 volume
        + eLpNorm (fun x => g x - f x) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ (eLpNorm (moll n (fun y => f y - g y)) 2 volume
          + eLpNorm (fun x => moll n g x - g x) 2 volume)
        + eLpNorm (fun x => g x - f x) 2 volume := by
        gcongr
        simpa only [Pi.add_apply] using!
          (eLpNorm_add_le
            (f := moll n (fun y => f y - g y))
            (g := fun x => moll n g x - g x)
            (p := 2) (μ := volume) (by norm_num))
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := by
        gcongr
        · exact (eLpNorm_moll_le
            (hf.aestronglyMeasurable.fun_sub hgcont.aestronglyMeasurable) n).trans hfg
        · rw [← eLpNorm_neg]; convert hfg using 2; ext x; simp
    _ = ε := by rw [ENNReal.add_thirds]

/-- `∂ᵢ(φ * v) = (∂ᵢφ) * v` for a smooth compactly supported kernel `φ`. -/
lemma pderiv_conv {φ : Plane → ℝ} (hφc : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {v : Plane → ℝ} (hv : LocallyIntegrable v volume) (i : Fin 2) :
    pderiv i (φ ⋆[lsmul ℝ ℝ, volume] v) = (pderiv i φ) ⋆[lsmul ℝ ℝ, volume] v := by
  ext x
  have hd := hφc.hasFDerivAt_convolution_left (lsmul ℝ ℝ) (hφ.of_le (by simp)) hv x
  have hc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hex := (hφc.fderiv (𝕜 := ℝ)).convolutionExists_left ((lsmul ℝ ℝ).precompL Plane) hc hv x
  simp only [pderiv, hd.fderiv, convolution_def]
  rw [ContinuousLinearMap.integral_apply hex]
  rfl

/-- `(∂ᵢφ) * v = φ * wᵢ` when `w` is the weak gradient of `v`. -/
lemma conv_weak {φ : Plane → ℝ} (hφc : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {v : Plane → ℝ} {w : Fin 2 → Plane → ℝ} (hvw : HasWeakGradient v w) (i : Fin 2) :
    (pderiv i φ) ⋆[lsmul ℝ ℝ, volume] v = φ ⋆[lsmul ℝ ℝ, volume] (w i) := by
  ext x
  set ψ : Plane → ℝ := fun t => φ (x - t) with hψdef
  have hψd : ∀ t, pderiv i ψ t = - pderiv i φ (x - t) := by
    intro t
    have h1 : HasFDerivAt (fun t : Plane => x - t) (-(ContinuousLinearMap.id ℝ Plane)) t :=
      (hasFDerivAt_id t).const_sub x
    have h2 := ((hφ.differentiable (by simp)) (x - t)).hasFDerivAt.comp t h1
    have h3 : fderiv ℝ (fun t => φ (x - t)) t = _ := h2.fderiv
    simp only [pderiv, hψdef]
    rw [h3]
    simp
  have hψ : IsTestFn Set.univ ψ := by
    refine ⟨hφ.comp (contDiff_const.sub contDiff_id), ?_, subset_univ _⟩
    exact hφc.comp_homeomorph (Homeomorph.subLeft x)
  have := hvw ψ hψ i
  simp only [hψd, mul_neg, integral_neg, neg_inj] at this
  rw [convolution_lsmul_swap, convolution_lsmul_swap]
  simp only [smul_eq_mul]
  rw [show (fun t => pderiv i φ (x - t) * v t) = fun t => v t * pderiv i φ (x - t) by ext; ring,
    this]
  congr 1; ext t; ring

lemma pderiv_moll {v : Plane → ℝ} {w : Fin 2 → Plane → ℝ} (hv : LocallyIntegrable v volume)
    (hvw : HasWeakGradient v w) (n : ℕ) (i : Fin 2) :
    pderiv i (moll n v) = moll n (w i) := by
  rw [moll, pderiv_conv (mollBump n).hasCompactSupport_normed (mollBump n).contDiff_normed hv,
    conv_weak (mollBump n).hasCompactSupport_normed (mollBump n).contDiff_normed hvw]
  rfl

lemma tsupport_moll {v : Plane → ℝ} {K : Set Plane} (hK : ∀ᵐ x, x ∉ K → v x = 0) (n : ℕ) :
    tsupport (moll n v) ⊆ cthickening (1 / (n + 1)) K := by
  have he : v =ᵐ[volume] K.indicator v := by
    filter_upwards [hK] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h, hx h]
  rw [moll_congr_ae he]
  refine (closure_mono ?_).trans (closure_thickening_subset_cthickening _ _)
  refine (support_convolution_subset _).trans ?_
  rw [(mollBump n).support_normed_eq, ← mollBump_rOut]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  have hbK : b ∈ K := by
    by_contra h; exact hb (by simp [h])
  rw [mem_thickening_iff]
  refine ⟨b, hbK, ?_⟩
  simpa [dist_eq_norm] using ha

lemma moll_zero (n : ℕ) : moll n (fun _ => 0) = fun _ => 0 :=
  convolution_zero

lemma eventually_moll_lt {f : Plane → ℝ} (hf : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, eLpNorm (fun x => moll n f x - f x) 2 volume < ENNReal.ofReal ε :=
  (tendsto_moll hf).eventually (gt_mem_nhds (by simpa using hε))

/-- **E8** (`H¹` form) holds. -/
theorem extMollification_holds : ExtMollification := by
  intro v w K hv hw hvw _ hvK ε hε
  have hvl : LocallyIntegrable v volume := hv.locallyIntegrable (by norm_num)
  have hwl : ∀ i, LocallyIntegrable (w i) volume :=
    fun i => (hw i).locallyIntegrable (by norm_num)
  have h1 : ∀ᶠ n in atTop, ∀ i,
      eLpNorm (fun x => moll n (w i) x - w i x) 2 volume < ENNReal.ofReal ε :=
    eventually_all.2 fun i => eventually_moll_lt (hw i) hε
  obtain ⟨n, hn0, hn1, hn2⟩ :=
    ((eventually_moll_lt hv hε).and (h1.and (eventually_one_div_le hε))).exists
  refine ⟨moll n v, moll_contDiff hvl n, (tsupport_moll hvK n).trans (cthickening_mono hn2 K),
    hn0, fun i => ?_, fun hw0 i x => ?_⟩
  · rw [pderiv_moll hvl hvw]; exact hn1 i
  · rw [pderiv_moll hvl hvw, moll_congr_ae (hw0 i), moll_zero]

/-- **E8** (`H²` form) holds. -/
theorem extMollification2_holds : ExtMollification2 := by
  intro v w h K hv hw hh hvw hwh _ hvK ε hε
  have hvl : LocallyIntegrable v volume := hv.locallyIntegrable (by norm_num)
  have hwl : ∀ i, LocallyIntegrable (w i) volume :=
    fun i => (hw i).locallyIntegrable (by norm_num)
  have hhl : ∀ i j, LocallyIntegrable (h i j) volume :=
    fun i j => (hh i j).locallyIntegrable (by norm_num)
  have h1 : ∀ᶠ n in atTop, ∀ i,
      eLpNorm (fun x => moll n (w i) x - w i x) 2 volume < ENNReal.ofReal ε :=
    eventually_all.2 fun i => eventually_moll_lt (hw i) hε
  have h2 : ∀ᶠ n in atTop, ∀ i j,
      eLpNorm (fun x => moll n (h i j) x - h i j x) 2 volume < ENNReal.ofReal ε :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_moll_lt (hh i j) hε
  obtain ⟨n, hn0, hn1, hn2, hn3⟩ :=
    ((eventually_moll_lt hv hε).and (h1.and (h2.and (eventually_one_div_le hε)))).exists
  refine ⟨moll n v, moll_contDiff hvl n, (tsupport_moll hvK n).trans (cthickening_mono hn3 K),
    hn0, fun i => ?_, fun i j => ?_⟩
  · rw [pderiv_moll hvl hvw]; exact hn1 i
  · rw [pderiv_moll hvl hvw, pderiv_moll (hwl j) (hwh j)]
    exact hn2 i j

end Buckling
end
end ChunkedSource039
/- END SOURCE 039 -/

/- BEGIN SOURCE 040: RequestProject/Variational.lean -/
section ChunkedSource040

/-!
# Sobolev form domains and the variational comparison (Section 10 of the paper)

* energies of test functions,
* Lemma 10.4 (compactly supported Lipschitz functions are admissible in `H₀¹`),
* Lemma 10.5 (density for the quotients), in the form needed,
* the reduction of Theorem 10.7 to the functional inequality (Theorem 9.21).
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology

namespace Buckling

/-! ### `L²` norms -/

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

lemma IsTestFn.integrable_sq {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    Integrable (fun x => φ x ^ 2) := by
  have hc : HasCompactSupport (fun x => φ x ^ 2) :=
    h.2.1.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact (h.1.continuous.pow 2).integrable_of_hasCompactSupport hc

lemma IsTestFn.eq_zero_of_notMem {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) {x : Plane}
    (hx : x ∉ Ω) : φ x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h' => hx (h.2.2 h'))

lemma sum_pderiv_sq (φ : Plane → ℝ) (x : Plane) :
    pderiv 0 φ x ^ 2 + pderiv 1 φ x ^ 2 = ‖fderiv ℝ φ x‖ ^ 2 := by
  rw [norm_fderiv_sq_eq]; rfl

lemma IsTestFn.integral_sq {Ω : Set Plane} {φ : Plane → ℝ} (h : IsTestFn Ω φ) :
    ‖h.toL2‖ ^ 2 = ∫ x, φ x ^ 2 := by
  rw [IsTestFn.toL2, norm_toLp_sq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [h.eq_zero_of_notMem hx]

lemma energy0_graphH1 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    energy0 (graphH1 φ) = ∫ x, φ.1 x ^ 2 := φ.2.integral_sq

lemma energy1_graphH1 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    energy1 (graphH1 φ) = ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 := by
  simp only [energy1, graphH1, Fin.sum_univ_two, IsTestFn.integral_sq]
  rw [← integral_add (φ.2.pderiv 0).integrable_sq (φ.2.pderiv 1).integrable_sq]
  simp only [sum_pderiv_sq]

lemma energy1'_graphH2 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    energy1' (graphH2 φ) = ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 := by
  simp only [energy1', graphH2, Fin.sum_univ_two, IsTestFn.integral_sq]
  rw [← integral_add (φ.2.pderiv 0).integrable_sq (φ.2.pderiv 1).integrable_sq]
  simp only [sum_pderiv_sq]

lemma energy2_graphH2 {Ω : Set Plane} (φ : {φ // IsTestFn Ω φ}) :
    energy2 (graphH2 φ) = ∫ x, laplacian φ.1 x ^ 2 := by
  simp only [energy2, graphH2, IsTestFn.toL2]
  rw [← MemLp.toLp_add, norm_toLp_sq]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [((φ.2.pderiv 0).pderiv 0).eq_zero_of_notMem hx,
    ((φ.2.pderiv 1).pderiv 1).eq_zero_of_notMem hx]

/-! ### Infima -/

lemma dirichletEig_le {Ω : Set Plane} (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω)
    (h0 : energy0 v ≠ 0) : dirichletEig Ω ≤ energy1 v / energy0 v := by
  refine ciInf_le ⟨0, ?_⟩ (⟨v, hv, h0⟩ : {v // v ∈ H01 Ω ∧ energy0 v ≠ 0})
  rintro _ ⟨w, rfl⟩
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)

lemma memLp_of_bdd_supp {f : Plane → ℝ} {K : Set Plane} (hK : IsCompact K)
    (hf : AEStronglyMeasurable f volume) (C : ℝ) (hb : ∀ x, |f x| ≤ C) (hs : ∀ x ∉ K, f x = 0) :
    MemLp f 2 volume := by
  have he : f = K.indicator f := by
    ext x; by_cases hx : x ∈ K <;> simp [hx, hs]
  rw [he, memLp_indicator_iff_restrict hK.measurableSet]
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.of_bound hf.restrict C (ae_of_all _ fun x => by simpa using hb x)

lemma fderiv_eq_zero_of_notMem_tsupport {G : Plane → ℝ} {x : Plane} (hx : x ∉ tsupport G) :
    fderiv ℝ G x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))

/-- A Lipschitz function has its a.e. gradient as weak gradient (from Rademacher's theorem
in Mathlib). -/
lemma lipschitz_hasWeakGradient {G : Plane → ℝ} {L : NNReal} (hG : LipschitzWith L G) :
    HasWeakGradient G (fun i x => fderiv ℝ G x (EuclideanSpace.single i 1)) := by
  intro ψ hψ i
  obtain ⟨D, hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hψ.2.1 hψ.1 (by simp)
  set v : Plane := EuclideanSpace.single i 1
  have key := hG.integral_lineDeriv_mul_eq hD hψ.2.1 v (μ := volume)
  have h1 : ∫ x, lineDeriv ℝ G x v * ψ x = ∫ x, fderiv ℝ G x v * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
    rw [hx.lineDeriv_eq_fderiv]
  have h2 : ∀ x, lineDeriv ℝ ψ x (-v) = -pderiv i ψ x := by
    intro x
    rw [((hψ.1.differentiable (by simp)) x).lineDeriv_eq_fderiv]
    simp [pderiv, v]
  rw [← h1, key]
  simp only [h2]
  rw [← integral_neg]
  congr 1; ext x; ring

/-- **Lemma 10.4.**  A Lipschitz function with compact support inside the open set `Ω`
defines an element of `H₀¹(Ω)` whose energies are `∫ G²` and `∫ |∇G|²`. -/
theorem lipschitz_mem_H01 (hM : ExtMollification) {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : NNReal} (hG : LipschitzWith L G) (hc : HasCompactSupport G)
    (hs : tsupport G ⊆ Ω) :
    ∃ v ∈ H01 Ω, energy0 v = ∫ x, G x ^ 2 ∧ energy1 v = ∫ x, ‖fderiv ℝ G x‖ ^ 2 := by
  set K := tsupport G with hKdef
  have hK : IsCompact K := hc
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open hΩ hs
  set w : Fin 2 → Plane → ℝ := fun i x => fderiv ℝ G x (EuclideanSpace.single i 1) with hw
  have hwK : ∀ i x, x ∉ K → w i x = 0 := fun i x hx => by
    simp [w, fderiv_eq_zero_of_notMem_tsupport hx]
  have hGK : ∀ x, x ∉ K → G x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hGm : MemLp G 2 volume := hG.continuous.memLp_of_hasCompactSupport hc
  have hwm : ∀ i, MemLp (w i) 2 volume := by
    intro i
    refine memLp_of_bdd_supp hK ?_ L (fun x => ?_) (hwK i)
    · exact (measurable_fderiv_apply_const ℝ G _).aestronglyMeasurable
    · calc |w i x| = ‖fderiv ℝ G x (EuclideanSpace.single i 1)‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ G x‖ * ‖(EuclideanSpace.single i 1 : Plane)‖ := (fderiv ℝ G x).le_opNorm _
        _ = ‖fderiv ℝ G x‖ := by simp
        _ ≤ L := norm_fderiv_le_of_lipschitz ℝ hG
  have hweak := lipschitz_hasWeakGradient hG
  set ε : ℕ → ℝ := fun n => min (δ / 2) (1 / ((n : ℝ) + 1)) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => lt_min (by positivity) (by positivity)
  have happrox := fun n => hM G w K hGm hwm hweak (isClosed_tsupport G)
    (ae_of_all _ hGK) (ε n) (hεpos n)
  choose ψ hψs hψsupp hψ0 hψ1 _ using happrox
  have htest : ∀ n, IsTestFn Ω (ψ n) := by
    intro n
    have hsub : Metric.cthickening (ε n) K ⊆ Ω :=
      (Metric.cthickening_mono (by simp only [hε]; linarith [min_le_left (δ / 2) (1 / ((n : ℝ) + 1))]) K).trans hδK
    exact ⟨hψs n, IsCompact.of_isClosed_subset hK.cthickening (isClosed_tsupport _) (hψsupp n),
      (hψsupp n).trans hsub⟩
  set v : L2 Ω × (Fin 2 → L2 Ω) :=
    ((hGm.restrict Ω).toLp G, fun i => ((hwm i).restrict Ω).toLp (w i)) with hv
  -- convergence of a single component
  have hconv : ∀ (n : ℕ) (f g : Plane → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume),
      eLpNorm (fun x => f x - g x) 2 volume < ENNReal.ofReal (ε n) →
      ‖(hf.restrict Ω).toLp f - (hg.restrict Ω).toLp g‖ ≤ ε n := by
    intro n f g hf hg hlt
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    refine (ENNReal.toReal_le_of_le_ofReal (hεpos n).le ?_)
    exact (eLpNorm_restrict_le _ _ _ _).trans hlt.le
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => (hεpos n).le) (fun n => min_le_right _ _) h1
  have hcomp : ∀ (f : ℕ → L2 Ω) (g : L2 Ω), (∀ n, ‖f n - g‖ ≤ ε n) → Tendsto f atTop (𝓝 g) := by
    intro f g hfg
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hfg hεlim
  refine ⟨v, ?_, ?_, ?_⟩
  · refine mem_closure_iff_seq_limit.mpr ⟨fun n => graphH1 ⟨ψ n, htest n⟩, fun n => ⟨_, rfl⟩, ?_⟩
    refine Prod.tendsto_iff _ _ |>.mpr ⟨?_, ?_⟩
    · exact hcomp _ _ fun n => hconv n (ψ n) G
        ((htest n).1.continuous.memLp_of_hasCompactSupport (htest n).2.1) hGm (hψ0 n)
    · refine tendsto_pi_nhds.mpr fun i => ?_
      exact hcomp _ _ fun n => hconv n (pderiv i (ψ n)) (w i)
        (((htest n).pderiv i).1.continuous.memLp_of_hasCompactSupport ((htest n).pderiv i).2.1)
        (hwm i) (hψ1 n i)
  · simp only [energy0, hv, norm_toLp_sq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hGK x (fun h => hx (hs h))]
  · simp only [energy1, hv, norm_toLp_sq, Fin.sum_univ_two]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        simp [hwK 0 x (fun h => hx (hs h))]),
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        simp [hwK 1 x (fun h => hx (hs h))]),
      ← integral_add (hwm 0).integrable_sq (hwm 1).integrable_sq]
    congr 1; ext x
    rw [norm_fderiv_sq_eq]

/-- Nonemptiness of the admissible class for the buckling quotient. -/
lemma exists_test_energy1_ne {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    ∃ φ : {φ // IsTestFn Ω φ}, ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 ≠ 0 := by
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x0 hx0
  let b : ContDiffBump x0 := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hb : IsTestFn Ω b := by
    refine ⟨b.contDiff, b.hasCompactSupport, ?_⟩
    rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ε / 2 < ε; linarith)).trans hball
  refine ⟨⟨b, hb⟩, ?_⟩
  have hcont : Continuous fun x => ‖fderiv ℝ (b : Plane → ℝ) x‖ ^ 2 :=
    ((b.contDiff (n := ⊤)).continuous_fderiv (by simp)).norm.pow 2
  have hsupp : HasCompactSupport fun x => ‖fderiv ℝ (b : Plane → ℝ) x‖ ^ 2 :=
    (b.hasCompactSupport.fderiv (𝕜 := ℝ)).comp_left (g := fun L => ‖L‖ ^ 2) (by simp)
  -- the gradient does not vanish identically
  obtain ⟨y, hy⟩ : ∃ y, fderiv ℝ (b : Plane → ℝ) y ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hconst := is_const_of_fderiv_eq_zero (b.contDiff (n := 1)).differentiable_one hall
    have h1 : (b : Plane → ℝ) x0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self
      (by show (0 : ℝ) ≤ ε / 4; positivity))
    set z : Plane := x0 + EuclideanSpace.single 0 ε
    have h0 : (b : Plane → ℝ) z = 0 := by
      apply b.zero_of_le_dist
      show ε / 2 ≤ dist z x0
      simp only [z, dist_eq_norm, add_sub_cancel_left, EuclideanSpace.norm_single, norm_eq_abs,
        abs_of_pos hε]
      linarith
    rw [hconst x0 z, h0] at h1
    exact zero_ne_one h1
  exact (hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hsupp
    (fun x => by positivity) (x := y) (by positivity)).ne'

/-- **Lemma 10.5 (density), lower-bound form.**  A lower bound for the buckling
quotient of all test functions is a lower bound for `Λ₁(Ω)`. -/
theorem le_bucklingEig_of_test {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (c : ℝ)
    (h : ∀ φ : {φ // IsTestFn Ω φ}, ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 ≠ 0 →
      c ≤ (∫ x, laplacian φ.1 x ^ 2) / ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2) :
    c ≤ bucklingEig Ω := by
  obtain ⟨φ0, hφ0⟩ := exists_test_energy1_ne hΩ hne
  haveI : Nonempty {v // v ∈ H02 Ω ∧ energy1' v ≠ 0} :=
    ⟨⟨graphH2 φ0, subset_closure ⟨φ0, rfl⟩, by rwa [energy1'_graphH2]⟩⟩
  refine le_ciInf fun ⟨v, hv, hv1⟩ => ?_
  have hc1 : Continuous fun w : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω) => energy1' w := by
    unfold energy1'; fun_prop
  have hc2 : Continuous fun w : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω) => energy2 w := by
    unfold energy2; fun_prop
  have hcont : ContinuousAt (fun w => energy2 w / energy1' w) v :=
    hc2.continuousAt.div hc1.continuousAt hv1
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hv
  have hE1 : Tendsto (fun n => energy1' (u n)) atTop (𝓝 (energy1' v)) :=
    (hc1.tendsto v).comp hlim
  have hev : ∀ᶠ n in atTop, energy1' (u n) ≠ 0 := hE1.eventually_ne hv1
  apply ge_of_tendsto (hcont.tendsto.comp hlim)
  filter_upwards [hev] with n hn
  obtain ⟨φ, hφ⟩ := hu n
  simp only [Function.comp_apply, ← hφ] at hn ⊢
  rw [energy2_graphH2, energy1'_graphH2] at *
  exact h φ hn

/-- The functional inequality (Theorem 9.21), as a proposition. -/
def FunctionalInequality : Prop :=
  ∀ U : Plane → ℝ, IsTestFn Set.univ U →
    (∃ L, LipschitzWith L (transformF U)) ∧ HasCompactSupport (transformF U) ∧
      (∫ x, ‖fderiv ℝ (transformF U) x‖ ^ 2) - pLam * ∫ x, transformF U x ^ 2
        ≤ pK * ((∫ x, laplacian U x ^ 2) - ∫ x, ‖fderiv ℝ U x‖ ^ 2)

/-! ### Dilations -/

lemma fderiv_comp_smul' (f : Plane → ℝ) {c : ℝ} (hc : c ≠ 0) (x : Plane) :
    fderiv ℝ (fun y => f (c • y)) x = c • fderiv ℝ f (c • x) := by
  simpa only using! (fderiv_comp_smul (𝕜 := ℝ) (f := f) (x := x) c)

lemma integral_comp_smul_plane (f : Plane → ℝ) (R : ℝ) :
    ∫ x, f (R • x) = |(R ^ 2)⁻¹| * ∫ x, f x := by
  have := Measure.integral_comp_smul (μ := (volume : Measure Plane)) f R
  simpa [finrank_euclideanSpace_fin] using this

lemma pderiv_comp_smul (f : Plane → ℝ) {c : ℝ} (hc : c ≠ 0) (i : Fin 2) (x : Plane) :
    pderiv i (fun y => f (c • y)) x = c * pderiv i f (c • x) := by
  simp [pderiv, fderiv_comp_smul' f hc]

lemma pderiv_const_mul (g : Plane → ℝ) (c : ℝ) (i : Fin 2) (x : Plane)
    (hg : DifferentiableAt ℝ g x) : pderiv i (fun y => c * g y) x = c * pderiv i g x := by
  simp [pderiv, fderiv_const_mul hg]

lemma laplacian_comp_smul (f : Plane → ℝ) (hf : ContDiff ℝ 2 f) {c : ℝ} (hc : c ≠ 0)
    (x : Plane) : laplacian (fun y => f (c • y)) x = c ^ 2 * laplacian f (c • x) := by
  have hd : ∀ i, Differentiable ℝ (pderiv i f) := by
    intro i
    have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
    exact (h1.clm_apply contDiff_const).differentiable (by norm_num)
  have h : ∀ i, pderiv i (fun y => f (c • y)) = fun y => c * pderiv i f (c • y) :=
    fun i => funext (pderiv_comp_smul f hc i)
  have hdi : ∀ i, Differentiable ℝ (fun y => pderiv i f (c • y)) :=
    fun i => (hd i).comp (differentiable_id.const_smul c)
  unfold laplacian
  rw [h 0, h 1, pderiv_const_mul _ _ _ _ ((hdi 0) x), pderiv_const_mul _ _ _ _ ((hdi 1) x),
    pderiv_comp_smul _ hc, pderiv_comp_smul _ hc]
  ring

lemma perspF_zero_zero : perspF 0 0 = 0 := by simp [perspF]

lemma perspF_zero_right (A : ℝ) : perspF A 0 = pEll * |A| := by simp [perspF]

/-- `∫ |∇φ|² = -∫ φ Δφ` for a test function. -/
lemma integral_norm_fderiv_sq_eq {Ω : Set Plane} {φ : Plane → ℝ} (hφ : IsTestFn Ω φ) :
    ∫ x, ‖fderiv ℝ φ x‖ ^ 2 = -∫ x, φ x * laplacian φ x := by
  have hc : ∀ {g : Plane → ℝ}, IsTestFn Ω g → ∀ {h : Plane → ℝ}, IsTestFn Ω h →
      Integrable (fun x => g x * h x) := by
    intro g hg h hh
    exact (hg.1.continuous.mul hh.1.continuous).integrable_of_hasCompactSupport
      (hg.2.1.mul_right)
  have ibp : ∀ i : Fin 2, ∫ x, φ x * pderiv i (pderiv i φ) x = -∫ x, pderiv i φ x ^ 2 := by
    intro i
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Plane))
      (f := φ) (g := pderiv i φ) (v := EuclideanSpace.single i 1)
      (hc (hφ.pderiv i) (hφ.pderiv i)) (hc hφ ((hφ.pderiv i).pderiv i)) (hc hφ (hφ.pderiv i))
      (fun x _ => (hφ.1.differentiable (by simp)) x)
      (fun x _ => ((hφ.pderiv i).1.differentiable (by simp)) x)
    simpa [pderiv, sq] using this
  have hint : ∀ i : Fin 2, Integrable fun x => φ x * pderiv i (pderiv i φ) x :=
    fun i => hc hφ ((hφ.pderiv i).pderiv i)
  simp only [laplacian, mul_add]
  rw [integral_add (hint 0) (hint 1), ibp 0, ibp 1, ← sum_pderiv_sq' hφ]
  · ring
where
  sum_pderiv_sq' {Ω : Set Plane} {φ : Plane → ℝ} (hφ : IsTestFn Ω φ) :
      (∫ x, pderiv 0 φ x ^ 2) + (∫ x, pderiv 1 φ x ^ 2) = ∫ x, ‖fderiv ℝ φ x‖ ^ 2 := by
    rw [← integral_add (hφ.pderiv 0).integrable_sq (hφ.pderiv 1).integrable_sq]
    simp only [sum_pderiv_sq]

/-- If `∫ |∇φ|² ≠ 0` then `∫ |Δφ|² > 0`. -/
lemma integral_laplacian_sq_pos {Ω : Set Plane} {φ : Plane → ℝ} (hφ : IsTestFn Ω φ)
    (h : ∫ x, ‖fderiv ℝ φ x‖ ^ 2 ≠ 0) : 0 < ∫ x, laplacian φ x ^ 2 := by
  have hcont : Continuous (laplacian φ) := by
    unfold laplacian
    exact ((hφ.pderiv 0).pderiv 0).1.continuous.add ((hφ.pderiv 1).pderiv 1).1.continuous
  have hsupp : HasCompactSupport (laplacian φ) := by
    unfold laplacian
    exact ((hφ.pderiv 0).pderiv 0).2.1.add ((hφ.pderiv 1).pderiv 1).2.1
  by_contra hle
  push_neg at hle
  have hzero : ∀ x, laplacian φ x = 0 := by
    intro x
    by_contra hx
    have hsquare : HasCompactSupport (fun y : Plane => laplacian φ y ^ 2) := by
      simpa only [Function.comp_def] using!
        hsupp.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    have hnonneg : (0 : Plane → ℝ) ≤ (fun y => laplacian φ y ^ 2) := by
      change ∀ y : Plane, (0 : ℝ) ≤ laplacian φ y ^ 2
      exact fun y => sq_nonneg _
    have hpos : 0 < ∫ y, laplacian φ y ^ 2 :=
      (hcont.fun_pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := volume) hsquare hnonneg (x := x) (pow_ne_zero 2 hx)
    linarith
  apply h
  rw [integral_norm_fderiv_sq_eq hφ]
  simp [hzero]

/-- **The core of the proof of Theorem 10.7.**  Assuming the functional inequality, every
test function satisfies `(k²/q²) λ₁ᴰ(Ω) ≤ E₂(φ)/E₁(φ)`. -/
theorem test_quotient_bound (hF : FunctionalInequality) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (φ : {φ // IsTestFn Ω φ}) (hφ : ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 ≠ 0) :
    jk ^ 2 / jq ^ 2 * dirichletEig Ω ≤
      (∫ x, laplacian φ.1 x ^ 2) / ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 := by
  obtain ⟨f, hf⟩ := φ
  simp only at hφ ⊢
  obtain ⟨hq0, hqk, -, -, hl0, -, hc0, -, -⟩ := parameter_signs extZeros_holds
  set A := ∫ x, ‖fderiv ℝ f x‖ ^ 2 with hA
  set B := ∫ x, laplacian f x ^ 2 with hB
  have hApos : 0 < A := lt_of_le_of_ne (integral_nonneg fun x => by positivity) (Ne.symm hφ)
  have hBpos : 0 < B := integral_laplacian_sq_pos hf hφ
  set a := Real.sqrt (B / A) with ha
  have ha0 : 0 < a := Real.sqrt_pos.mpr (div_pos hBpos hApos)
  have ha2 : a ^ 2 = B / A := Real.sq_sqrt (div_pos hBpos hApos).le
  have ha0' : a ≠ 0 := ha0.ne'
  have hai : a⁻¹ ≠ 0 := inv_ne_zero ha0'
  -- the dilated test function
  set U : Plane → ℝ := fun x => f (a⁻¹ • x) with hU
  have hUtest : IsTestFn Set.univ U :=
    ⟨hf.1.comp (contDiff_const_smul _), hf.2.1.comp_smul hai, subset_univ _⟩
  obtain ⟨⟨L, hL⟩, hFc, hineq⟩ := hF U hUtest
  set F := transformF U with hFdef
  have hfC2 : ContDiff ℝ 2 f := hf.1.of_le (WithTop.coe_le_coe.mpr le_top)
  -- energies of `U`
  have hUgrad : ∫ x, ‖fderiv ℝ U x‖ ^ 2 = A := by
    have : (fun x => ‖fderiv ℝ U x‖ ^ 2) = fun x => a⁻¹ ^ 2 * ‖fderiv ℝ f (a⁻¹ • x)‖ ^ 2 := by
      ext x; rw [hU, fderiv_comp_smul' f hai, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [this, integral_const_mul, integral_comp_smul_plane (fun y => ‖fderiv ℝ f y‖ ^ 2)]
    rw [abs_of_pos (by positivity)]
    field_simp
    exact hA.symm
  have hUlap : ∫ x, laplacian U x ^ 2 = B / a ^ 2 := by
    have : (fun x => laplacian U x ^ 2) = fun x => a⁻¹ ^ 4 * laplacian f (a⁻¹ • x) ^ 2 := by
      ext x; rw [hU, laplacian_comp_smul f hfC2 hai]; ring
    rw [this, integral_const_mul, integral_comp_smul_plane (fun y => laplacian f y ^ 2)]
    rw [abs_of_pos (by positivity)]
    field_simp
    exact hB.symm
  have hFineq : ∫ x, ‖fderiv ℝ F x‖ ^ 2 ≤ pLam * ∫ x, F x ^ 2 := by
    rw [hUgrad, hUlap, ha2] at hineq
    have : pK * (B / (B / A) - A) = 0 := by field_simp; ring
    linarith
  -- the rescaled transform
  set G : Plane → ℝ := fun y => F (a • y) with hG
  have hGval : ∀ y, G y = perspF (f y) (a⁻¹ * ‖fderiv ℝ f y‖) := by
    intro y
    simp only [hG, hFdef, transformF, hU, fderiv_comp_smul' f hai, smul_smul, inv_mul_cancel₀ ha0',
      one_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
  have hGlip : LipschitzWith (L * ‖a‖₊) G := hL.comp (lipschitzWith_smul a)
  have hGc : HasCompactSupport G := hFc.comp_smul ha0'
  have hGs : tsupport G ⊆ Ω := by
    refine (closure_minimal ?_ (isClosed_tsupport f)).trans hf.2.2
    intro y hy
    by_contra hy'
    have h1 : f y = 0 := image_eq_zero_of_notMem_tsupport hy'
    have h2 : fderiv ℝ f y = 0 := fderiv_eq_zero_of_notMem_tsupport hy'
    apply hy
    simp [hGval y, h1, h2, perspF_zero_zero]
  have hGgrad : ∫ y, ‖fderiv ℝ G y‖ ^ 2 = ∫ x, ‖fderiv ℝ F x‖ ^ 2 := by
    have : (fun y => ‖fderiv ℝ G y‖ ^ 2) = fun y => a ^ 2 * ‖fderiv ℝ F (a • y)‖ ^ 2 := by
      ext y; rw [hG, fderiv_comp_smul' F ha0', norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [this, integral_const_mul, integral_comp_smul_plane (fun x => ‖fderiv ℝ F x‖ ^ 2)]
    rw [abs_of_pos (by positivity)]
    field_simp
  have hGsq : ∫ y, G y ^ 2 = (a ^ 2)⁻¹ * ∫ x, F x ^ 2 := by
    rw [hG, integral_comp_smul_plane (fun x => F x ^ 2), abs_of_pos (by positivity)]
  -- positivity of `∫ G²`
  have hGpos : 0 < ∫ y, G y ^ 2 := by
    obtain ⟨x0, hx0⟩ := (hf.1.continuous.abs).exists_forall_ge_of_hasCompactSupport hf.2.1.abs
    have hfx0 : f x0 ≠ 0 := by
      intro h0
      have hall : ∀ y, f y = 0 := fun y => abs_nonpos_iff.mp (by have := hx0 y; rwa [h0, abs_zero] at this)
      apply hφ
      have : fderiv ℝ f = 0 := by
        have : f = fun _ => 0 := funext hall
        rw [this]; exact funext fun _ => fderiv_const_apply _
      simp [A, this]
    have hd0 : fderiv ℝ f x0 = 0 := by
      rcases lt_or_gt_of_ne hfx0 with hneg | hpos
      · apply IsLocalMin.fderiv_eq_zero
        refine Filter.Eventually.of_forall fun y => ?_
        have := hx0 y
        rw [abs_of_neg hneg] at this
        linarith [neg_abs_le (f y)]
      · apply IsLocalMax.fderiv_eq_zero
        refine Filter.Eventually.of_forall fun y => ?_
        have := hx0 y
        rw [abs_of_pos hpos] at this
        linarith [le_abs_self (f y)]
    have hGx0 : G x0 ≠ 0 := by
      rw [hGval, hd0, norm_zero, mul_zero, perspF_zero_right]
      have : 0 < pEll := by unfold pEll pSigma; positivity
      positivity
    exact (hGlip.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hGc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)) (fun y => sq_nonneg _)
      (x := x0) (by positivity)
  -- conclusion
  obtain ⟨v, hv, hv0, hv1⟩ := lipschitz_mem_H01 extMollification_holds hΩ hGlip hGc hGs
  have hle := dirichletEig_le v hv (by rw [hv0]; exact hGpos.ne')
  rw [hv0, hv1, hGgrad] at hle
  have hFsq : ∫ x, F x ^ 2 = a ^ 2 * ∫ y, G y ^ 2 := by
    rw [hGsq]; field_simp
  have hq : jk ^ 2 / jq ^ 2 = 1 / pLam := by
    unfold pLam pAlpha; field_simp
  rw [hq]
  have h1 : dirichletEig Ω ≤ pLam * (B / A) := by
    calc dirichletEig Ω ≤ (∫ x, ‖fderiv ℝ F x‖ ^ 2) / ∫ y, G y ^ 2 := hle
      _ ≤ pLam * (a ^ 2 * ∫ y, G y ^ 2) / ∫ y, G y ^ 2 := by
          gcongr; rw [← hFsq]; exact hFineq
      _ = pLam * (B / A) := by rw [ha2]; field_simp
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hl0]
  linarith

/-- **Theorem 10.7**, derived from the functional inequality. -/
theorem buckling_ge_dirichlet_of_functional (hF : FunctionalInequality)
    (Ω : Set Plane) (hΩ : IsOpen Ω) (hne : Ω.Nonempty) :
    jk ^ 2 / jq ^ 2 * dirichletEig Ω ≤ bucklingEig Ω :=
  le_bucklingEig_of_test hΩ hne _ fun φ hφ => test_quotient_bound hF hΩ φ hφ

end Buckling
end
end ChunkedSource040
/- END SOURCE 040 -/

/- BEGIN SOURCE 041: RequestProject/Disk/CoeffId.lean -/
section ChunkedSource041

/-!
# Pointwise identities for the angular coefficients

For each radius `r > 0` we express `∫_θ |∇φ|²` and `∫_θ (Δφ)²` on the circle of radius `r`
through the Fourier coefficients `aC n r`, `bC n r` (Parseval), and we show that each
coefficient is an admissible radial mode.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

namespace DiskCoeff

open Fourier1D Mode1D

lemma sec_cont {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F)) (r : ℝ) :
    Continuous (F r) :=
  hF.comp (continuous_const.prodMk continuous_id)

@[simp] lemma ePt_two_pi : ePt (2 * π) = ePt 0 := by simp [ePt]
@[simp] lemma ePt'_two_pi : ePt' (2 * π) = ePt' 0 := by simp [ePt']

/-- The gradient density of the `n`-th pair of modes at radius `r`. -/
noncomputable def gdens (φ : Plane → ℝ) (a : Plane) (n : ℤ) (r : ℝ) : ℝ :=
  (r * deriv (aC φ a n) r ^ 2 + ((n.natAbs : ℕ) : ℝ) ^ 2 * aC φ a n r ^ 2 / r) +
    (r * deriv (bC φ a n) r ^ 2 + ((n.natAbs : ℕ) : ℝ) ^ 2 * bC φ a n r ^ 2 / r)

/-- The Laplacian density of the `n`-th pair of modes at radius `r`. -/
noncomputable def ldens (φ : Plane → ℝ) (a : Plane) (n : ℤ) (r : ℝ) : ℝ :=
  r * (deriv (deriv (aC φ a n)) r + deriv (aC φ a n) r / r -
      ((n.natAbs : ℕ) : ℝ) ^ 2 * aC φ a n r / r ^ 2) ^ 2 +
    r * (deriv (deriv (bC φ a n)) r + deriv (bC φ a n) r / r -
      ((n.natAbs : ℕ) : ℝ) ^ 2 * bC φ a n r / r ^ 2) ^ 2

lemma natAbs_sq (n : ℤ) : ((n.natAbs : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 := by
  rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]

variable {φ : Plane → ℝ} (a : Plane)

/-- The first partial derivatives of `φ` in terms of `G1`, `G2`. -/
lemma norm_fderiv_polar (r θ : ℝ) :
    ‖fderiv ℝ φ (a + r • ePt θ)‖ ^ 2 = G1 φ a r θ ^ 2 + G2 φ a r θ ^ 2 := by
  rw [norm_fderiv_sq_eq]
  simp only [G1, G2]
  generalize fderiv ℝ φ (a + r • ePt θ) = L
  simp only [ePt, ePt', map_add, map_smul, smul_eq_mul]
  linear_combination (-(L (EuclideanSpace.single 0 1) ^ 2 +
    L (EuclideanSpace.single 1 1) ^ 2)) * sin_sq_add_cos_sq θ

lemma U0_zero : U0 φ a 0 = fun _ => φ a := by
  ext θ; simp [U0]

lemma G1_zero : G1 φ a 0 = fun θ => fderiv ℝ φ a (EuclideanSpace.single 0 1) * cos θ +
    fderiv ℝ φ a (EuclideanSpace.single 1 1) * sin θ := by
  ext θ; simp [G1, ePt, map_add, map_smul]; ring

lemma natAbs_ne_one {n : ℤ} (hn : n.natAbs ≠ 1) : n ≠ 1 ∧ n ≠ -1 :=
  ⟨fun h => hn (by simp [h]), fun h => hn (by simp [h])⟩

lemma supp_U0 {R : ℝ} (hR : 0 < R) (hsub : tsupport φ ⊆ ball a R) :
    ∃ R' ∈ Ioo 0 R, ∀ r, R' ≤ r → U0 φ a r = fun _ => 0 := by
  obtain ⟨R1, hR1, hs⟩ := exists_lt_subset_ball (isClosed_tsupport φ) hsub
  refine ⟨max R1 (R / 2), ⟨by positivity, max_lt hR1 (by linarith)⟩, fun r hr => ?_⟩
  ext θ
  show φ (a + r • ePt θ) = 0
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have h1 := hs hm
  rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, norm_ePt, mul_one,
    Real.norm_eq_abs] at h1
  have : R1 ≤ r := (le_max_left _ _).trans hr
  linarith [le_abs_self r]

section Smooth

variable (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
include hφ

lemma pderiv_pderiv (i : Fin 2) (x : Plane) :
    pderiv i (pderiv i φ) x =
      fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
  have h : HasFDerivAt (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1))
      ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1 : Plane)).comp
        (fderiv ℝ (fderiv ℝ φ) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1 : Plane)).hasFDerivAt.comp x
      ((diff2 hφ) x).hasFDerivAt
  change fderiv ℝ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x _ = _
  rw [h.fderiv]
  rfl

lemma laplacian_polar (r θ : ℝ) :
    laplacian φ (a + r • ePt θ) = G11 φ a r θ + G22 φ a r θ := by
  rw [laplacian, pderiv_pderiv hφ, pderiv_pderiv hφ]
  simp only [G11, G22]
  generalize fderiv ℝ (fderiv ℝ φ) (a + r • ePt θ) = B
  simp only [ePt, ePt', map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  linear_combination (-(B (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) +
    B (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1))) * sin_sq_add_cos_sq θ

lemma coeffs_G2 (n : ℤ) (r : ℝ) :
    r * cosC n (G2 φ a r) = n * bC φ a n r ∧ r * sinC n (G2 φ a r) = -(n * aC φ a n r) := by
  have h := deriv_rule (g := U0 φ a r) (g' := fun θ => r * G2 φ a r θ)
    (hasDerivAt_U0_θ a hφ r) (continuous_const.mul (sec_cont (cont_G2 a hφ) r))
    (by simp [U0]) n
  rw [cosC_const_mul, sinC_const_mul] at h
  exact h

lemma coeffs_G22 (n : ℤ) (r : ℝ) :
    r ^ 2 * cosC n (G22 φ a r) = r * cosC n (G1 φ a r) - n ^ 2 * aC φ a n r ∧
    r ^ 2 * sinC n (G22 φ a r) = r * sinC n (G1 φ a r) - n ^ 2 * bC φ a n r := by
  have hc1 := sec_cont (cont_G1 a hφ) r
  have hc22 := sec_cont (cont_G22 a hφ) r
  have e : (fun θ => r ^ 2 * G22 φ a r θ - r * G1 φ a r θ) =
      fun θ => r ^ 2 * G22 φ a r θ + (-r) * G1 φ a r θ := by ext; ring
  have hgc : Continuous fun θ => r ^ 2 * G22 φ a r θ - r * G1 φ a r θ :=
    (continuous_const.mul hc22).sub (continuous_const.mul hc1)
  have h := deriv_rule (g := fun θ => r * G2 φ a r θ)
    (g' := fun θ => r ^ 2 * G22 φ a r θ - r * G1 φ a r θ)
    (hasDerivAt_G2_θ a hφ r) hgc (by simp [G2]) n
  have hA : Continuous fun θ => r ^ 2 * G22 φ a r θ := continuous_const.mul hc22
  have hB : Continuous fun θ => -r * G1 φ a r θ := continuous_const.mul hc1
  rw [e, cosC_add hA hB, sinC_add hA hB, cosC_const_mul,
    cosC_const_mul, sinC_const_mul, sinC_const_mul, cosC_const_mul, sinC_const_mul] at h
  obtain ⟨g1, g2⟩ := coeffs_G2 a hφ n r
  constructor
  · linear_combination h.1 + (n : ℝ) * g2
  · linear_combination h.2 - (n : ℝ) * g1

variable (hc : HasCompactSupport φ)
include hc

lemma deriv_aC_apply (n : ℤ) (r : ℝ) : deriv (aC φ a n) r = cosC n (G1 φ a r) :=
  (hasDerivAt_aC a hφ hc n r).deriv

lemma deriv_bC_apply (n : ℤ) (r : ℝ) : deriv (bC φ a n) r = sinC n (G1 φ a r) :=
  (hasDerivAt_bC a hφ hc n r).deriv

lemma deriv2_aC_apply (n : ℤ) (r : ℝ) : deriv (deriv (aC φ a n)) r = cosC n (G11 φ a r) := by
  rw [deriv2_aC a hφ hc]

lemma deriv2_bC_apply (n : ℤ) (r : ℝ) : deriv (deriv (bC φ a n)) r = sinC n (G11 φ a r) := by
  rw [deriv2_bC a hφ hc]

lemma hasSum_gdens {r : ℝ} (hr : 0 < r) :
    HasSum (fun n => gdens φ a n r)
      (r * (1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, ‖fderiv ℝ φ (a + r • ePt θ)‖ ^ 2)) := by
  have hc1 := sec_cont (cont_G1 a hφ) r
  have hc2 := sec_cont (cont_G2 a hφ) r
  have P1 := hasSum_parseval (G1 φ a r) hc1
  have P2 := hasSum_parseval (G2 φ a r) hc2
  have h := (P1.add P2).mul_left r
  convert h using 1
  · ext n
    obtain ⟨g1, g2⟩ := coeffs_G2 a hφ n r
    have e1 : cosC n (G2 φ a r) = n * bC φ a n r / r := by
      field_simp; linarith
    have e2 : sinC n (G2 φ a r) = -(n * aC φ a n r) / r := by
      field_simp; linarith
    simp only [gdens]
    rw [deriv_aC_apply a hφ hc, deriv_bC_apply a hφ hc, natAbs_sq, e1, e2]
    field_simp
    ring
  · have i1 : IntervalIntegrable (fun θ => G1 φ a r θ ^ 2) volume 0 (2 * π) :=
      (hc1.pow 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => G2 φ a r θ ^ 2) volume 0 (2 * π) :=
      (hc2.pow 2).intervalIntegrable _ _
    simp_rw [norm_fderiv_polar]
    rw [intervalIntegral.integral_add i1 i2]
    ring

lemma hasSum_ldens {r : ℝ} (hr : 0 < r) :
    HasSum (fun n => ldens φ a n r)
      (r * (1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, laplacian φ (a + r • ePt θ) ^ 2)) := by
  have hc1 := sec_cont (cont_G11 a hφ) r
  have hc2 := sec_cont (cont_G22 a hφ) r
  have hcs : Continuous fun θ => G11 φ a r θ + G22 φ a r θ := hc1.add hc2
  have P := (hasSum_parseval _ hcs).mul_left r
  simp_rw [laplacian_polar a hφ]
  convert P using 1
  ext n
  obtain ⟨g1, g2⟩ := coeffs_G22 a hφ n r
  have e1 : cosC n (G22 φ a r) = (r * cosC n (G1 φ a r) - n ^ 2 * aC φ a n r) / r ^ 2 := by
    field_simp; linarith
  have e2 : sinC n (G22 φ a r) = (r * sinC n (G1 φ a r) - n ^ 2 * bC φ a n r) / r ^ 2 := by
    field_simp; linarith
  simp only [ldens]
  rw [cosC_add hc1 hc2, sinC_add hc1 hc2, deriv2_aC_apply a hφ hc, deriv2_bC_apply a hφ hc,
    deriv_aC_apply a hφ hc, deriv_bC_apply a hφ hc, natAbs_sq, e1, e2]
  field_simp
  ring

section Modes

variable {R : ℝ} (hR : 0 < R) (hsub : tsupport φ ⊆ ball a R)
include hR hsub

lemma modeFn_aC (n : ℤ) : ModeFn R n.natAbs (aC φ a n) := by
  refine ⟨hR, contDiff_aC a hφ hc n, fun hn => ?_, fun hn => ?_, ?_⟩
  · simp only [aC]
    rw [U0_zero a]
    exact (coeff_const (Int.natAbs_ne_zero.1 hn) _).1
  · rw [deriv_aC_apply a hφ hc, G1_zero a]
    obtain ⟨h1, h2⟩ := natAbs_ne_one hn
    have := (coeff_trig h1 h2 (fderiv ℝ φ a (EuclideanSpace.single 0 1))
      (fderiv ℝ φ a (EuclideanSpace.single 1 1))).1
    simpa only [mul_comm] using this
  · obtain ⟨R', hR', h⟩ := supp_U0 a hR hsub
    exact ⟨R', hR', fun r hr => by simp [aC, h r hr, cosC]⟩

lemma modeFn_bC (n : ℤ) : ModeFn R n.natAbs (bC φ a n) := by
  refine ⟨hR, contDiff_bC a hφ hc n, fun hn => ?_, fun hn => ?_, ?_⟩
  · simp only [bC]
    rw [U0_zero a]
    exact (coeff_const (Int.natAbs_ne_zero.1 hn) _).2
  · rw [deriv_bC_apply a hφ hc, G1_zero a]
    obtain ⟨h1, h2⟩ := natAbs_ne_one hn
    have := (coeff_trig h1 h2 (fderiv ℝ φ a (EuclideanSpace.single 0 1))
      (fderiv ℝ φ a (EuclideanSpace.single 1 1))).2
    simpa only [mul_comm] using this
  · obtain ⟨R', hR', h⟩ := supp_U0 a hR hsub
    exact ⟨R', hR', fun r hr => by simp [bC, h r hr, sinC]⟩

end Modes

end Smooth

end DiskCoeff

end Buckling
end
end ChunkedSource041
/- END SOURCE 041 -/

/- BEGIN SOURCE 042: RequestProject/Disk/Dirichlet.lean -/
section ChunkedSource042

/-!
# The first Dirichlet eigenvalue of a disk (Lemma 11.2)

`λ₁ᴰ(B_R(a)) = q²/R²`, where `q = j_{0,1}`.

* Lower bound: the ground-state (Picone) argument with `Φ(x) = J₀(q|x-a|/R)`, which is
  smooth, positive in the disk and satisfies `-ΔΦ = (q²/R²) Φ`, followed by density.
* Upper bound: the Lipschitz test functions `x ↦ J₀(q min(|x-a|/ρ, 1))` for `ρ < R`
  (admissible by Lemma 10.4), whose quotient is exactly `q²/ρ²` by the identity
  `∫₀^q t J₁(t)² dt = ∫₀^q t J₀(t)² dt`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

/-! ### The smooth radial function `J₀(c|x - a|)` -/

/-- `x ↦ J₀(c|x - a|)`, written as `G₀(c²|x - a|²)` to make smoothness evident. -/
noncomputable def radJ0 (c : ℝ) (a : Plane) (x : Plane) : ℝ := besselG 0 (c ^ 2 * ‖x - a‖ ^ 2)

lemma radJ0_eq (c : ℝ) (a x : Plane) : radJ0 c a x = besselJ 0 (c * ‖x - a‖) := by
  rw [besselJ_zero_eq_besselG, radJ0, mul_pow]

lemma contDiff_radJ0 (c : ℝ) (a : Plane) : ContDiff ℝ (⊤ : ℕ∞) (radJ0 c a) := by
  unfold radJ0
  exact (contDiff_besselG 0).comp (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

lemma hasFDerivAt_radG (n : ℕ) (c : ℝ) (a x : Plane) :
    HasFDerivAt (fun y : Plane => besselG n (c ^ 2 * ‖y - a‖ ^ 2))
      ((-(1 / 4) * besselG (n + 1) (c ^ 2 * ‖x - a‖ ^ 2)) •
        (c ^ 2 • (2 • (innerSL ℝ (x - a)).comp (ContinuousLinearMap.id ℝ Plane)))) x := by
  have h1 : HasFDerivAt (fun y : Plane => ‖y - a‖ ^ 2)
      (2 • (innerSL ℝ (x - a)).comp (ContinuousLinearMap.id ℝ Plane)) x :=
    ((hasFDerivAt_id x).sub_const a).norm_sq
  exact (hasDerivAt_besselG n (c ^ 2 * ‖x - a‖ ^ 2)).comp_hasFDerivAt x (h1.const_mul (c ^ 2))

lemma pderiv_radG (n : ℕ) (c : ℝ) (a : Plane) (i : Fin 2) (x : Plane) :
    pderiv i (fun y : Plane => besselG n (c ^ 2 * ‖y - a‖ ^ 2)) x =
      -(c ^ 2 / 2) * besselG (n + 1) (c ^ 2 * ‖x - a‖ ^ 2) * (x i - a i) := by
  rw [pderiv, (hasFDerivAt_radG n c a x).fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

lemma pderiv_radJ0 (c : ℝ) (a : Plane) (i : Fin 2) (x : Plane) :
    pderiv i (radJ0 c a) x = -(c ^ 2 / 2) * besselG 1 (c ^ 2 * ‖x - a‖ ^ 2) * (x i - a i) :=
  pderiv_radG 0 c a i x

lemma norm_sub_sq_plane (x a : Plane) : ‖x - a‖ ^ 2 = (x 0 - a 0) ^ 2 + (x 1 - a 1) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [Fin.sum_univ_two]

/-- `-Δ J₀(c|x-a|) = c² J₀(c|x-a|)`. -/
lemma laplacian_radJ0 (c : ℝ) (a : Plane) (x : Plane) :
    laplacian (radJ0 c a) x = -c ^ 2 * radJ0 c a x := by
  have hp : ∀ i, pderiv i (radJ0 c a) = fun y =>
      -(c ^ 2 / 2) * besselG 1 (c ^ 2 * ‖y - a‖ ^ 2) * (y i - a i) :=
    fun i => funext fun y => pderiv_radG 0 c a i y
  have hpp : ∀ i, pderiv i (pderiv i (radJ0 c a)) x =
      -(c ^ 2 / 2) * ((-(c ^ 2 / 2) * besselG 2 (c ^ 2 * ‖x - a‖ ^ 2) * (x i - a i)) * (x i - a i)
        + besselG 1 (c ^ 2 * ‖x - a‖ ^ 2)) := by
    intro i
    rw [hp i]
    have hco : HasFDerivAt (fun y : Plane => y i - a i) (EuclideanSpace.proj i : Plane →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj i : Plane →L[ℝ] ℝ).hasFDerivAt.sub_const _
    have h := (((hasFDerivAt_radG 1 c a x).const_mul (-(c ^ 2 / 2))).fun_mul hco)
    rw [pderiv, h.fderiv]
    simp [EuclideanSpace.inner_single_right]
    ring
  have hr := besselG_recurrence (c ^ 2 * ‖x - a‖ ^ 2)
  rw [laplacian, hpp, hpp, radJ0]
  rw [norm_sub_sq_plane] at hr ⊢
  linear_combination (c ^ 2) * hr

lemma norm_fderiv_radJ0_sq (c : ℝ) (a : Plane) (x : Plane) :
    ‖fderiv ℝ (radJ0 c a) x‖ ^ 2 = c ^ 2 * besselJ 1 (c * ‖x - a‖) ^ 2 := by
  rw [← sum_pderiv_sq, pderiv_radJ0, pderiv_radJ0, besselJ_eq_besselG, mul_pow c,
    norm_sub_sq_plane]
  have := norm_sub_sq_plane x a
  ring_nf
  rw [this]
  ring

/-- `J₀ > 0` on `[0, q)` (from E1). -/
lemma besselJ_zero_pos_of_lt_jq (hZ : ExtZeros) (t : ℝ) (ht0 : 0 ≤ t) (ht : t < jq) :
    0 < besselJ 0 t := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Icc (0 : ℝ) t, besselJ 0 z = 0 :=
    intermediate_value_Icc' ht0 (continuous_besselJ 0).continuousOn
      ⟨hcon, by rw [besselJ_zero_at_zero]; norm_num⟩
  have hzpos : 0 < z := by
    rcases hz.1.lt_or_eq with h | h
    · exact h
    · subst h; rw [besselJ_zero_at_zero] at hz0; norm_num at hz0
  obtain ⟨hmono0, -, -, hall0, -⟩ := hZ 0 (by norm_num)
  obtain ⟨n, hn, hnz⟩ := hall0 z hzpos hz0
  have : besselZero 0 1 ≤ besselZero 0 n := hmono0.le_iff_le.mpr hn
  change jq ≤ besselZero 0 n at this
  linarith [hz.2]

lemma radJ0_pos (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R) {x : Plane}
    (hx : x ∈ ball a R) : 0 < radJ0 (jq / R) a x := by
  have hq := (parameter_signs hZ).1
  rw [radJ0_eq]
  have hx' : ‖x - a‖ < R := by rw [mem_ball, dist_eq_norm] at hx; exact hx
  apply besselJ_zero_pos_of_lt_jq hZ _ (by positivity)
  rw [div_mul_eq_mul_div, div_lt_iff₀ hR]
  exact mul_lt_mul_of_pos_left hx' hq

/-! ### The lower bound -/

/-- Integration by parts: `∫ ∇u·∇g = -∫ (Δu) g` for smooth `u` and a test function `g`. -/
lemma integral_grad_mul_eq (u : Plane → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (g : Plane → ℝ)
    (hg : IsTestFn univ g) :
    ∫ x, (pderiv 0 u x * pderiv 0 g x + pderiv 1 u x * pderiv 1 g x) =
      -∫ x, laplacian u x * g x := by
  have hpu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (pderiv i u) := fun i =>
    (hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hpu2 : ∀ i, Continuous (pderiv i (pderiv i u)) := fun i =>
    (((hpu i).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
  have hint : ∀ {f h : Plane → ℝ}, Continuous f → IsTestFn univ h →
      Integrable (fun x => f x * h x) := fun hf hh =>
    (hf.mul hh.1.continuous).integrable_of_hasCompactSupport hh.2.1.mul_left
  have ibp : ∀ i : Fin 2, ∫ x, pderiv i u x * pderiv i g x =
      -∫ x, pderiv i (pderiv i u) x * g x := by
    intro i
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Plane))
      (f := pderiv i u) (g := g) (v := EuclideanSpace.single i 1)
      (hint (hpu2 i) hg) (hint (hpu i).continuous (hg.pderiv i))
      (hint (hpu i).continuous hg)
      (fun x _ => ((hpu i).differentiable (by simp)) x)
      (fun x _ => (hg.1.differentiable (by simp)) x)
  have hi : ∀ i : Fin 2, Integrable fun x => pderiv i u x * pderiv i g x :=
    fun i => hint (hpu i).continuous (hg.pderiv i)
  have hi2 : ∀ i : Fin 2, Integrable fun x => pderiv i (pderiv i u) x * g x :=
    fun i => hint (hpu2 i) hg
  rw [integral_add (hi 0) (hi 1), ibp 0, ibp 1]
  simp only [laplacian, add_mul]
  rw [integral_add (hi2 0) (hi2 1)]
  ring

/-- The ground-state inequality for test functions. -/
theorem dirichlet_test_lower (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R) (φ : Plane → ℝ)
    (hφ : IsTestFn (ball a R) φ) :
    jq ^ 2 / R ^ 2 * ∫ x, φ x ^ 2 ≤ ∫ x, ‖fderiv ℝ φ x‖ ^ 2 := by
  set c := jq / R with hc
  set u := radJ0 c a with hu
  set g : Plane → ℝ := fun x => φ x ^ 2 * (u x)⁻¹ with hg
  have hupos : ∀ x ∈ ball a R, 0 < u x := fun x hx => radJ0_pos hZ a hR hx
  have hucd := contDiff_radJ0 c a
  have hφ0 : ∀ x ∉ ball a R, φ =ᶠ[𝓝 x] 0 := fun x hx =>
    notMem_tsupport_iff_eventuallyEq.mp (fun h => hx (hφ.2.2 h))
  have hg0 : ∀ x ∉ ball a R, g =ᶠ[𝓝 x] 0 := fun x hx => by
    filter_upwards [hφ0 x hx] with y hy
    simp [g, hy]
  have hgcd : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ ball a R
    · exact (hφ.1.pow 2).contDiffAt.mul (hucd.contDiffAt.inv (hupos x hx).ne')
    · exact contDiffAt_const.congr_of_eventuallyEq (hg0 x hx)
  have hgt : IsTestFn univ g := by
    refine ⟨hgcd, hφ.2.1.mono ?_, subset_univ _⟩
    intro x hx
    simp only [Function.mem_support, g] at hx ⊢
    intro h; apply hx; simp [h]
  -- pointwise inequality
  have hpt : ∀ x, pderiv 0 u x * pderiv 0 g x + pderiv 1 u x * pderiv 1 g x ≤
      ‖fderiv ℝ φ x‖ ^ 2 := by
    intro x
    by_cases hx : x ∈ ball a R
    · have hux := hupos x hx
      have hφd : HasFDerivAt φ (fderiv ℝ φ x) x :=
        (hφ.1.differentiable (by simp) x).hasFDerivAt
      have hud : HasFDerivAt u (fderiv ℝ u x) x := (hucd.differentiable (by simp) x).hasFDerivAt
      have hgd : HasFDerivAt g _ x := (hφd.pow 2).fun_mul ((hasDerivAt_inv hux.ne').comp_hasFDerivAt x hud)
      have hpg : ∀ i, pderiv i g x = 2 * φ x * pderiv i φ x * (u x)⁻¹ -
          φ x ^ 2 * ((u x) ^ 2)⁻¹ * pderiv i u x := by
        intro i
        rw [pderiv, hgd.fderiv]
        simp [pderiv]
        ring
      rw [hpg, hpg, ← sum_pderiv_sq]
      set p := φ x; set w := u x
      set a0 := pderiv 0 φ x; set a1 := pderiv 1 φ x
      set b0 := pderiv 0 u x; set b1 := pderiv 1 u x
      have key : b0 * (2 * p * a0 * w⁻¹ - p ^ 2 * (w ^ 2)⁻¹ * b0) +
          b1 * (2 * p * a1 * w⁻¹ - p ^ 2 * (w ^ 2)⁻¹ * b1) =
          a0 ^ 2 + a1 ^ 2 - ((a0 - p * b0 / w) ^ 2 + (a1 - p * b1 / w) ^ 2) := by
        field_simp; ring
      rw [key]
      nlinarith [sq_nonneg (a0 - p * b0 / w), sq_nonneg (a1 - p * b1 / w)]
    · have hfd : fderiv ℝ g x = 0 := by
        rw [(hg0 x hx).fderiv_eq]; simp
      simp only [pderiv, hfd, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
      positivity
  have hint_phi : Integrable fun x => ‖fderiv ℝ φ x‖ ^ 2 := by
    have := ((hφ.pderiv 0).integrable_sq).add ((hφ.pderiv 1).integrable_sq)
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [sum_pderiv_sq]
  have hint_l : Integrable fun x => pderiv 0 u x * pderiv 0 g x + pderiv 1 u x * pderiv 1 g x := by
    have hpu : ∀ i, Continuous (pderiv i u) := fun i =>
      ((hucd.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).continuous
    refine Integrable.add ?_ ?_
    · exact ((hpu 0).mul (hgt.pderiv 0).1.continuous).integrable_of_hasCompactSupport
        (hgt.pderiv 0).2.1.mul_left
    · exact ((hpu 1).mul (hgt.pderiv 1).1.continuous).integrable_of_hasCompactSupport
        (hgt.pderiv 1).2.1.mul_left
  have hug : ∀ x, φ x ^ 2 = u x * g x := by
    intro x
    by_cases hx : x ∈ ball a R
    · simp only [g]; field_simp [(hupos x hx).ne']
    · have : φ x = 0 := (hφ0 x hx).self_of_nhds
      simp [g, this]
  calc jq ^ 2 / R ^ 2 * ∫ x, φ x ^ 2 = -∫ x, laplacian u x * g x := by
        rw [← integral_const_mul, ← integral_neg]
        congr 1; ext x
        rw [laplacian_radJ0, hug, hc, div_pow]; ring
    _ = ∫ x, (pderiv 0 u x * pderiv 0 g x + pderiv 1 u x * pderiv 1 g x) :=
        (integral_grad_mul_eq u hucd g hgt).symm
    _ ≤ ∫ x, ‖fderiv ℝ φ x‖ ^ 2 := integral_mono hint_l hint_phi hpt

/-- The ground-state inequality on `H₀¹(B_R(a))`, by density. -/
theorem dirichlet_lower (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R)
    (v : L2 (ball a R) × (Fin 2 → L2 (ball a R))) (hv : v ∈ H01 (ball a R)) :
    jq ^ 2 / R ^ 2 * energy0 v ≤ energy1 v := by
  have hS : IsClosed {w : L2 (ball a R) × (Fin 2 → L2 (ball a R)) |
      jq ^ 2 / R ^ 2 * energy0 w ≤ energy1 w} := by
    apply isClosed_le
    · exact continuous_const.mul (continuous_fst.norm.pow 2)
    · exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp continuous_snd).norm.pow 2
  have hsub : range (graphH1 (Ω := ball a R)) ⊆ {w | jq ^ 2 / R ^ 2 * energy0 w ≤ energy1 w} := by
    rintro _ ⟨φ, rfl⟩
    simp only [mem_setOf_eq, energy0_graphH1, energy1_graphH1]
    exact dirichlet_test_lower hZ a hR φ.1 φ.2
  exact closure_minimal hsub hS hv

/-! ### The upper bound -/

/-- The Lipschitz test function `x ↦ J₀(q min(|x-a|/ρ, 1))`. -/
noncomputable def capJ (a : Plane) (ρ : ℝ) (x : Plane) : ℝ :=
  besselJ 0 (jq * min (‖x - a‖ / ρ) 1)

lemma capJ_lipschitz (hI : ExtIntegral) (a : Plane) {ρ : ℝ} (hρ : 0 < ρ) (hq : 0 ≤ jq) :
    LipschitzWith (Real.toNNReal (jq / ρ)) (capJ a ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  unfold capJ
  refine (abs_besselJ_zero_sub hI _ _).trans ?_
  rw [← mul_sub, abs_mul, abs_of_nonneg hq, div_mul_eq_mul_div, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ hq
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _), ← sub_div, abs_div, abs_of_pos hρ]
  apply div_le_div_of_nonneg_right _ hρ.le
  calc |‖x - a‖ - ‖y - a‖| ≤ ‖(x - a) - (y - a)‖ := abs_norm_sub_norm_le _ _
    _ = ‖x - y‖ := by rw [sub_sub_sub_cancel_right]

lemma capJ_eq_zero (hZ : ExtZeros) (a : Plane) {ρ : ℝ} (hρ : 0 < ρ) {x : Plane}
    (hx : ρ ≤ ‖x - a‖) : capJ a ρ x = 0 := by
  unfold capJ
  rw [min_eq_right ((one_le_div hρ).mpr hx), mul_one]
  exact ((hZ 0 (by norm_num)).2.2.1 1 le_rfl).1

lemma capJ_eq_radJ0 (a : Plane) {ρ : ℝ} (hρ : 0 < ρ) {x : Plane}
    (hx : ‖x - a‖ ≤ ρ) : capJ a ρ x = radJ0 (jq / ρ) a x := by
  unfold capJ
  rw [min_eq_left ((div_le_one hρ).mpr hx), radJ0_eq]
  ring_nf

lemma tsupport_capJ (hZ : ExtZeros) (a : Plane) {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (capJ a ρ) ⊆ closedBall a ρ := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hx (capJ_eq_zero hZ a hρ (le_of_lt (not_le.mp h)))

lemma integral_radial (F : ℝ → ℝ) (a : Plane) :
    ∫ x, F ‖x - a‖ = 2 * π * ∫ y in Ioi (0 : ℝ), y * F y := by
  rw [integral_sub_right_eq_self (fun x => F ‖x‖) a, integral_fun_norm_addHaar volume F]
  have h1 : volume.real (ball (0 : Plane) 1) = π := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_two, pi_pos.le]
  rw [h1, finrank_euclideanSpace, Fintype.card_fin]
  simp [smul_eq_mul, mul_assoc]

lemma hasDerivAt_bessel_product (c y : ℝ) :
    HasDerivAt (fun y => y * besselJ 0 (c * y) * besselJ 1 (c * y))
      (c * y * (besselJ 0 (c * y) ^ 2 - besselJ 1 (c * y) ^ 2)) y := by
  have h0 : HasDerivAt (fun y => besselJ 0 (c * y)) (-besselJ 1 (c * y) * (c * 1)) y :=
    (hasDerivAt_besselJ_zero (c * y)).comp y ((hasDerivAt_id y).const_mul c)
  have h1 : HasDerivAt (fun y => besselJ 1 (c * y))
      ((besselJ 0 (c * y) - besselJ 2 (c * y)) / 2 * (c * 1)) y :=
    (hasDerivAt_besselJ_succ 0 (c * y)).comp y ((hasDerivAt_id y).const_mul c)
  have h : HasDerivAt (fun y => y * besselJ 0 (c * y) * besselJ 1 (c * y)) _ y :=
    ((hasDerivAt_id' y).fun_mul h0).fun_mul h1
  convert h using 1
  have hr := besselJ_recurrence 0 (c * y)
  push_cast at hr
  linear_combination (besselJ 0 (c * y) / 2) * hr

/-- A radial integrand vanishing beyond `ρ` reduces to an interval integral. -/
lemma integral_Ioi_ite {ρ : ℝ} (hρ : 0 < ρ) (f : ℝ → ℝ) :
    ∫ y in Ioi (0 : ℝ), y * (if y ≤ ρ then f y else 0) = ∫ y in (0 : ℝ)..ρ, y * f y := by
  calc ∫ y in Ioi (0 : ℝ), y * (if y ≤ ρ then f y else 0)
      = ∫ y in Ioc (0 : ℝ) ρ, y * (if y ≤ ρ then f y else 0) := by
        refine setIntegral_eq_of_subset_of_ae_diff_eq_zero measurableSet_Ioi.nullMeasurableSet
          Ioc_subset_Ioi_self (Eventually.of_forall fun y hy => ?_)
        have : ¬ y ≤ ρ := fun h => hy.2 ⟨hy.1, h⟩
        simp [this]
    _ = ∫ y in Ioc (0 : ℝ) ρ, y * f y :=
        setIntegral_congr_fun measurableSet_Ioc fun y hy => by simp [hy.2]
    _ = ∫ y in (0 : ℝ)..ρ, y * f y := (intervalIntegral.integral_of_le hρ.le).symm

/-- `∫₀^ρ y J₁(cy)² dy = ∫₀^ρ y J₀(cy)² dy` when `J₀(cρ) J₁(cρ) = 0`. -/
lemma bessel_radial_identity (c ρ : ℝ) (hρ : 0 < ρ)
    (hc : besselJ 0 (c * ρ) * besselJ 1 (c * ρ) = 0) :
    ∫ y in Ioi (0 : ℝ), y * (if y ≤ ρ then c ^ 2 * besselJ 1 (c * y) ^ 2 else 0) =
      c ^ 2 * ∫ y in Ioi (0 : ℝ), y * (if y ≤ ρ then besselJ 0 (c * y) ^ 2 else 0) := by
  have red := integral_Ioi_ite hρ
  rw [red, red, ← intervalIntegral.integral_const_mul]
  have hcont : Continuous fun y => c * y * (besselJ 0 (c * y) ^ 2 - besselJ 1 (c * y) ^ 2) := by
    have := continuous_besselJ 0; have := continuous_besselJ 1
    fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hasDerivAt_bessel_product c y) (hcont.intervalIntegrable 0 ρ)
  replace hftc : ∫ y in (0 : ℝ)..ρ, c * y * (besselJ 0 (c * y) ^ 2 - besselJ 1 (c * y) ^ 2) = 0 := by
    rw [hftc]; simp [mul_assoc, hc]
  have hsub : ∫ y in (0 : ℝ)..ρ, (c ^ 2 * (y * besselJ 0 (c * y) ^ 2) - y * (c ^ 2 * besselJ 1 (c * y) ^ 2)) = 0 := by
    have : ∫ y in (0 : ℝ)..ρ, (c ^ 2 * (y * besselJ 0 (c * y) ^ 2) -
        y * (c ^ 2 * besselJ 1 (c * y) ^ 2)) =
        c * ∫ y in (0 : ℝ)..ρ, c * y * (besselJ 0 (c * y) ^ 2 - besselJ 1 (c * y) ^ 2) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; ext y; ring
    rw [this, hftc, mul_zero]
  have hi1 : IntervalIntegrable (fun y => c ^ 2 * (y * besselJ 0 (c * y) ^ 2)) volume 0 ρ := by
    have := continuous_besselJ 0
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun y => y * (c ^ 2 * besselJ 1 (c * y) ^ 2)) volume 0 ρ := by
    have := continuous_besselJ 1
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [intervalIntegral.integral_sub hi1 hi2] at hsub
  linarith

/-- The quotient of the test function `capJ a ρ` equals `q²/ρ²`. -/
theorem capJ_test (a : Plane) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ v ∈ H01 (ball a R), energy0 v ≠ 0 ∧ energy1 v = jq ^ 2 / ρ ^ 2 * energy0 v := by
  have hZ := extZeros_holds
  have hq := (parameter_signs hZ).1
  set c := jq / ρ with hc
  have hlip := capJ_lipschitz extIntegral_holds a hρ hq.le
  have hts := tsupport_capJ hZ a hρ
  have hcs : HasCompactSupport (capJ a ρ) :=
    (isCompact_closedBall a ρ).of_isClosed_subset (isClosed_tsupport _) hts
  have hsub : tsupport (capJ a ρ) ⊆ ball a R := hts.trans (closedBall_subset_ball hρR)
  obtain ⟨v, hv, h0, h1⟩ := lipschitz_mem_H01 extMollification_holds isOpen_ball hlip hcs hsub
  set F0 : ℝ → ℝ := fun r => if r ≤ ρ then besselJ 0 (c * r) ^ 2 else 0 with hF0
  set F1 : ℝ → ℝ := fun r => if r ≤ ρ then c ^ 2 * besselJ 1 (c * r) ^ 2 else 0 with hF1
  have hI0 : ∫ x, capJ a ρ x ^ 2 = ∫ x, F0 ‖x - a‖ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases h : ‖x - a‖ ≤ ρ
    · simp only [F0, h, if_true]
      rw [capJ_eq_radJ0 a hρ h, radJ0_eq]
    · simp only [F0, h, if_false]
      rw [capJ_eq_zero hZ a hρ (le_of_lt (not_le.mp h))]
      simp
  have hI1 : ∫ x, ‖fderiv ℝ (capJ a ρ) x‖ ^ 2 = ∫ x, F1 ‖x - a‖ := by
    have hsph : ∀ᵐ x ∂(volume : Measure Plane), x ∉ sphere a ρ :=
      measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume a ρ)
    refine integral_congr_ae ?_
    filter_upwards [hsph] with x hx
    rw [mem_sphere, dist_eq_norm] at hx
    rcases lt_or_gt_of_ne hx with h | h
    · have hev : capJ a ρ =ᶠ[𝓝 x] radJ0 c a := by
        have hxb : x ∈ ball a ρ := by rw [mem_ball, dist_eq_norm]; exact h
        filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
        rw [mem_ball, dist_eq_norm] at hy
        exact capJ_eq_radJ0 a hρ hy.le
      rw [hev.fderiv_eq, norm_fderiv_radJ0_sq]
      simp [F1, h.le]
    · have hev : capJ a ρ =ᶠ[𝓝 x] fun _ => 0 := by
        have hop : IsOpen {y : Plane | ρ < ‖y - a‖} :=
          isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
        filter_upwards [hop.mem_nhds (show x ∈ {y : Plane | ρ < ‖y - a‖} from h)] with y hy
        exact capJ_eq_zero hZ a hρ (le_of_lt hy)
      rw [hev.fderiv_eq]
      have : ¬ ‖x - a‖ ≤ ρ := not_le.mpr h
      simp [F1, this]
  have hcρ : c * ρ = jq := by rw [hc]; field_simp
  have key := bessel_radial_identity c ρ hρ (by
    have h0 : besselJ 0 jq = 0 := ((hZ 0 (by norm_num)).2.2.1 1 le_rfl).1
    rw [hcρ, h0, zero_mul])
  refine ⟨v, hv, ?_, ?_⟩
  · rw [h0]
    have hsquare : HasCompactSupport (fun x : Plane => capJ a ρ x ^ 2) := by
      simpa only [Function.comp_def] using!
        hcs.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    have hnonneg : (0 : Plane → ℝ) ≤ (fun x => capJ a ρ x ^ 2) := by
      change ∀ x : Plane, (0 : ℝ) ≤ capJ a ρ x ^ 2
      exact fun x => sq_nonneg _
    have hcenter : capJ a ρ a ^ 2 ≠ 0 := by
      simp only [capJ, sub_self, norm_zero, zero_div]
      rw [min_eq_left zero_le_one, mul_zero, besselJ_zero_at_zero]
      norm_num
    have hpos : 0 < ∫ x, capJ a ρ x ^ 2 :=
      (hlip.continuous.fun_pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
        (μ := volume) hsquare hnonneg (x := a) hcenter
    exact hpos.ne'
  · rw [h1, h0, hI1, hI0, integral_radial, integral_radial, key, ← div_pow]
    ring

/-- **Lemma 11.2.**  `λ₁ᴰ(B_R(a)) = q²/R²`. -/
theorem dirichletEig_ball' (a : Plane) (R : ℝ) (hR : 0 < R) :
    dirichletEig (ball a R) = jq ^ 2 / R ^ 2 := by
  apply le_antisymm
  · -- upper bound: `λ₁ᴰ ≤ q²/ρ²` for every `ρ < R`
    have hle : ∀ ρ, 0 < ρ → ρ < R → dirichletEig (ball a R) ≤ jq ^ 2 / ρ ^ 2 := by
      intro ρ hρ hρR
      obtain ⟨v, hv, h0, h1⟩ := capJ_test a hρ hρR
      calc dirichletEig (ball a R) ≤ energy1 v / energy0 v := dirichletEig_le v hv h0
        _ = jq ^ 2 / ρ ^ 2 := by rw [h1]; field_simp
    have hcont : Tendsto (fun ρ : ℝ => jq ^ 2 / ρ ^ 2) (𝓝[<] R) (𝓝 (jq ^ 2 / R ^ 2)) :=
      ((continuousAt_const.div (continuous_pow 2).continuousAt
        (pow_ne_zero 2 hR.ne')).tendsto).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto hcont ?_
    filter_upwards [Ioo_mem_nhdsLT hR] with ρ hρ using hle ρ hρ.1 hρ.2
  · -- lower bound
    obtain ⟨v, hv, h0, -⟩ := capJ_test a (half_pos hR) (half_lt_self hR)
    haveI : Nonempty {v // v ∈ H01 (ball a R) ∧ energy0 v ≠ 0} := ⟨⟨v, hv, h0⟩⟩
    refine le_ciInf fun w => ?_
    have hpos : 0 < energy0 w.1 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm w.2.2)
    rw [le_div_iff₀ hpos]
    exact dirichlet_lower extZeros_holds a hR w.1 w.2.1

end Buckling
end
end ChunkedSource042
/- END SOURCE 042 -/

/- BEGIN SOURCE 043: RequestProject/Disk/BucklingUpper.lean -/
section ChunkedSource043

/-!
# The upper bound `Λ₁(B_R(a)) ≤ k²/R²` (part of Lemma 11.6)

We use the clamped test functions `U_ρ(x) = J₀(k min(|x-a|/ρ, 1)) - J₀(k)`, `ρ < R`, which
are `C¹` with Lipschitz gradient.  They are admissible in `H₀²(B_R(a))` by the second-order
case of the mollification theorem, and their buckling quotient is exactly `k²/ρ²`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric Asymptotics

namespace Buckling

lemma bucklingEig_le {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) (hv : v ∈ H02 Ω)
    (h0 : energy1' v ≠ 0) : bucklingEig Ω ≤ energy2 v / energy1' v := by
  refine ciInf_le ⟨0, ?_⟩ (⟨v, hv, h0⟩ : {v // v ∈ H02 Ω ∧ energy1' v ≠ 0})
  rintro _ ⟨w, rfl⟩
  exact div_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)

lemma tsupport_pderiv_subset (G : Plane → ℝ) (i : Fin 2) :
    tsupport (pderiv i G) ⊆ tsupport G := by
  refine (tsupport_fderiv_subset ℝ (f := G)).trans' ?_
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [pderiv, h0])

/-- A compactly supported Lipschitz function with Lipschitz partial derivatives, supported
inside the open set `Ω`, defines an element of `H₀²(Ω)` with the expected energies. -/
theorem lipschitz_mem_H02 (hM : ExtMollification2) {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : NNReal} (hG : LipschitzWith L G) (hc : HasCompactSupport G)
    (hs : tsupport G ⊆ Ω) (hw : ∀ j, ∃ L' : NNReal, LipschitzWith L' (pderiv j G)) :
    ∃ v ∈ H02 Ω, energy1' v = ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∧
      energy2 v = ∫ x, laplacian G x ^ 2 := by
  choose Lw hLw using hw
  set K := tsupport G with hKdef
  have hK : IsCompact K := hc
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open hΩ hs
  set w : Fin 2 → Plane → ℝ := fun i => pderiv i G with hw
  set h : Fin 2 → Fin 2 → Plane → ℝ := fun i j => pderiv i (pderiv j G) with hh
  have hwK : ∀ i x, x ∉ K → w i x = 0 := fun i x hx => by
    simp [w, pderiv, fderiv_eq_zero_of_notMem_tsupport hx]
  have hhK : ∀ i j x, x ∉ K → h i j x = 0 := fun i j x hx => by
    simp [h, pderiv, fderiv_eq_zero_of_notMem_tsupport
      (fun h' => hx (tsupport_pderiv_subset G j h'))]
  have hGK : ∀ x, x ∉ K → G x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hGm : MemLp G 2 volume := hG.continuous.memLp_of_hasCompactSupport hc
  have bound : ∀ (F : Plane → ℝ) (L' : NNReal), LipschitzWith L' F → ∀ i x,
      |fderiv ℝ F x (EuclideanSpace.single i 1)| ≤ L' := by
    intro F L' hF i x
    calc |fderiv ℝ F x (EuclideanSpace.single i 1)|
        = ‖fderiv ℝ F x (EuclideanSpace.single i 1)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ F x‖ * ‖(EuclideanSpace.single i 1 : Plane)‖ := (fderiv ℝ F x).le_opNorm _
      _ = ‖fderiv ℝ F x‖ := by simp
      _ ≤ L' := norm_fderiv_le_of_lipschitz ℝ hF
  have hwm : ∀ i, MemLp (w i) 2 volume := by
    intro i
    refine memLp_of_bdd_supp hK ?_ L (fun x => bound G L hG i x) (hwK i)
    exact (measurable_fderiv_apply_const ℝ G _).aestronglyMeasurable
  have hhm : ∀ i j, MemLp (h i j) 2 volume := by
    intro i j
    refine memLp_of_bdd_supp hK ?_ (Lw j) (fun x => bound _ _ (hLw j) i x) (hhK i j)
    exact (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable
  have hweak : HasWeakGradient G w := lipschitz_hasWeakGradient hG
  have hweak2 : ∀ j, HasWeakGradient (w j) (fun i => h i j) := fun j =>
    lipschitz_hasWeakGradient (hLw j)
  set ε : ℕ → ℝ := fun n => min (δ / 2) (1 / ((n : ℝ) + 1)) with hε
  have hεpos : ∀ n, 0 < ε n := fun n => lt_min (by positivity) (by positivity)
  have happrox := fun n => hM G w h K hGm hwm hhm hweak hweak2 (isClosed_tsupport G)
    (ae_of_all _ hGK) (ε n) (hεpos n)
  choose ψ hψs hψsupp hψ0 hψ1 hψ2 using happrox
  have htest : ∀ n, IsTestFn Ω (ψ n) := by
    intro n
    have hsub : Metric.cthickening (ε n) K ⊆ Ω :=
      (Metric.cthickening_mono (by simp only [hε]; linarith [min_le_left (δ / 2) (1 / ((n : ℝ) + 1))]) K).trans hδK
    exact ⟨hψs n, IsCompact.of_isClosed_subset hK.cthickening (isClosed_tsupport _) (hψsupp n),
      (hψsupp n).trans hsub⟩
  set v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω) :=
    ((hGm.restrict Ω).toLp G, fun i => ((hwm i).restrict Ω).toLp (w i),
      fun i j => ((hhm i j).restrict Ω).toLp (h i j)) with hv
  have hconv : ∀ (n : ℕ) (f g : Plane → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume),
      eLpNorm (fun x => f x - g x) 2 volume < ENNReal.ofReal (ε n) →
      ‖(hf.restrict Ω).toLp f - (hg.restrict Ω).toLp g‖ ≤ ε n := by
    intro n f g hf hg hlt
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    refine (ENNReal.toReal_le_of_le_ofReal (hεpos n).le ?_)
    exact (eLpNorm_restrict_le _ _ _ _).trans hlt.le
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine squeeze_zero (fun n => (hεpos n).le) (fun n => min_le_right _ _) h1
  have hcomp : ∀ (f : ℕ → L2 Ω) (g : L2 Ω), (∀ n, ‖f n - g‖ ≤ ε n) → Tendsto f atTop (𝓝 g) := by
    intro f g hfg
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hfg hεlim
  have hint_sq : ∀ (f : Plane → ℝ) (hf : MemLp f 2 volume), (∀ x, x ∉ K → f x = 0) →
      ‖(hf.restrict Ω).toLp f‖ ^ 2 = ∫ x, f x ^ 2 := by
    intro f hf hfK
    rw [norm_toLp_sq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [hfK x (fun h' => hx (hs h'))]
  refine ⟨v, ?_, ?_, ?_⟩
  · refine mem_closure_iff_seq_limit.mpr ⟨fun n => graphH2 ⟨ψ n, htest n⟩, fun n => ⟨_, rfl⟩, ?_⟩
    refine Prod.tendsto_iff _ _ |>.mpr ⟨?_, Prod.tendsto_iff _ _ |>.mpr ⟨?_, ?_⟩⟩
    · exact hcomp _ _ fun n => hconv n (ψ n) G
        ((htest n).1.continuous.memLp_of_hasCompactSupport (htest n).2.1) hGm (hψ0 n)
    · refine tendsto_pi_nhds.mpr fun i => ?_
      exact hcomp _ _ fun n => hconv n (pderiv i (ψ n)) (w i)
        (((htest n).pderiv i).1.continuous.memLp_of_hasCompactSupport ((htest n).pderiv i).2.1)
        (hwm i) (hψ1 n i)
    · refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
      exact hcomp _ _ fun n => hconv n (pderiv i (pderiv j (ψ n))) (h i j)
        ((((htest n).pderiv j).pderiv i).1.continuous.memLp_of_hasCompactSupport
          (((htest n).pderiv j).pderiv i).2.1)
        (hhm i j) (hψ2 n i j)
  · simp only [energy1', hv, Fin.sum_univ_two]
    rw [hint_sq _ (hwm 0) (hwK 0), hint_sq _ (hwm 1) (hwK 1),
      ← integral_add (hwm 0).integrable_sq (hwm 1).integrable_sq]
    congr 1; ext x
    rw [← sum_pderiv_sq]
  · simp only [energy2, hv]
    rw [← MemLp.toLp_add, hint_sq _ ((hhm 0 0).add (hhm 1 1))
      (fun x hx => by simp [hhK 0 0 x hx, hhK 1 1 x hx])]
    rfl

/-! ### Gluing a function on a closed disk with zero outside -/

/-- `g` on the closed ball `B̄_ρ(a)`, `0` outside. -/
noncomputable def ballGlue {E : Type*} [Zero E] (a : Plane) (ρ : ℝ) (g : Plane → E) (x : Plane) :
    E := if ‖x - a‖ ≤ ρ then g x else 0

lemma ballGlue_lipschitz (a : Plane) {ρ : ℝ} {g : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (h0 : ∀ x, ‖x - a‖ = ρ → g x = 0) : ∃ L, LipschitzWith L (ballGlue a ρ g) := by
  obtain ⟨K, hK⟩ := hg.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall a ρ)
  -- the mixed case
  have mixed : ∀ x y, ‖x - a‖ ≤ ρ → ρ < ‖y - a‖ → |g x| ≤ K * dist x y := by
    intro x y hx hy
    have hcont : ContinuousOn (fun t : ℝ => ‖(x + t • (y - x)) - a‖) (Icc 0 1) := by
      fun_prop
    obtain ⟨t, ht, hteq⟩ := intermediate_value_Icc (zero_le_one) hcont
      ⟨by simpa using hx, by simpa using hy.le⟩
    set z := x + t • (y - x)
    have hz : z ∈ closedBall a ρ := by rw [mem_closedBall, dist_eq_norm]; exact hteq.le
    have hgz : g z = 0 := h0 z hteq
    have hxz : dist x z ≤ dist x y := by
      simp only [z, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1]
      rw [norm_sub_rev]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have := hK.dist_le_mul x (by rw [mem_closedBall, dist_eq_norm]; exact hx) z hz
    rw [Real.dist_eq, hgz, sub_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_left hxz K.2)
  refine ⟨K, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  unfold ballGlue
  by_cases hx : ‖x - a‖ ≤ ρ <;> by_cases hy : ‖y - a‖ ≤ ρ <;> simp only [hx, hy, if_true, if_false]
  · exact hK.dist_le_mul x (by rw [mem_closedBall, dist_eq_norm]; exact hx) y
      (by rw [mem_closedBall, dist_eq_norm]; exact hy)
  · rw [Real.dist_eq, sub_zero]; exact mixed x y hx (not_le.mp hy)
  · rw [Real.dist_eq, zero_sub, abs_neg, dist_comm]; exact mixed y x hy (not_le.mp hx)
  · rw [dist_self]; positivity

lemma hasFDerivAt_ballGlue_sphere (a : Plane) {ρ : ℝ} {g : Plane → ℝ} {x : Plane}
    (hx : ‖x - a‖ = ρ) (hgx : g x = 0) (hd : HasFDerivAt g (0 : Plane →L[ℝ] ℝ) x) :
    HasFDerivAt (ballGlue a ρ g) (0 : Plane →L[ℝ] ℝ) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hd ⊢
  refine IsBigO.trans_isLittleO (IsBigO.of_bound 1 (Eventually.of_forall fun y => ?_)) hd
  simp only [ballGlue, hx, le_refl, if_true, hgx, ContinuousLinearMap.zero_apply, sub_zero,
    one_mul]
  split_ifs <;> simp

lemma ballGlue_eventually_inside (a : Plane) {ρ : ℝ} (g : Plane → ℝ) {x : Plane}
    (hx : ‖x - a‖ < ρ) : ballGlue a ρ g =ᶠ[𝓝 x] g := by
  have hxb : x ∈ ball a ρ := by rw [mem_ball, dist_eq_norm]; exact hx
  filter_upwards [isOpen_ball.mem_nhds hxb] with y hy
  rw [mem_ball, dist_eq_norm] at hy
  simp [ballGlue, hy.le]

lemma ballGlue_eventually_outside (a : Plane) {ρ : ℝ} (g : Plane → ℝ) {x : Plane}
    (hx : ρ < ‖x - a‖) : ballGlue a ρ g =ᶠ[𝓝 x] fun _ => 0 := by
  have hop : IsOpen {y : Plane | ρ < ‖y - a‖} :=
    isOpen_lt continuous_const (continuous_id.sub continuous_const).norm
  filter_upwards [hop.mem_nhds (show x ∈ {y : Plane | ρ < ‖y - a‖} from hx)] with y hy
  simp [ballGlue, not_le.mpr (show ρ < ‖y - a‖ from hy)]

lemma fderiv_ballGlue (a : Plane) {ρ : ℝ} {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (h0 : ∀ x, ‖x - a‖ = ρ → g x = 0 ∧ fderiv ℝ g x = 0) (x : Plane) :
    fderiv ℝ (ballGlue a ρ g) x = ballGlue a ρ (fderiv ℝ g) x := by
  rcases lt_trichotomy ‖x - a‖ ρ with h | h | h
  · rw [(ballGlue_eventually_inside a g h).fderiv_eq]; simp [ballGlue, h.le]
  · have hd : HasFDerivAt g (0 : Plane →L[ℝ] ℝ) x := by
      rw [← (h0 x h).2]; exact (hg x).hasFDerivAt
    rw [(hasFDerivAt_ballGlue_sphere a h (h0 x h).1 hd).fderiv]
    simp [ballGlue, h.le, (h0 x h).2]
  · rw [(ballGlue_eventually_outside a g h).fderiv_eq]; simp [ballGlue, not_le.mpr h]

lemma pderiv_ballGlue (a : Plane) {ρ : ℝ} {g : Plane → ℝ} (hg : Differentiable ℝ g)
    (h0 : ∀ x, ‖x - a‖ = ρ → g x = 0 ∧ fderiv ℝ g x = 0) (i : Fin 2) :
    pderiv i (ballGlue a ρ g) = ballGlue a ρ (pderiv i g) := by
  ext x
  simp only [pderiv, fderiv_ballGlue a hg h0 x, ballGlue]
  split_ifs <;> simp

lemma clm_eq_zero_of_pderiv (L : Plane →L[ℝ] ℝ) (h0 : L (EuclideanSpace.single 0 1) = 0)
    (h1 : L (EuclideanSpace.single 1 1) = 0) : L = 0 := by
  have := norm_fderiv_sq_eq L
  rw [h0, h1] at this
  have : ‖L‖ = 0 := by nlinarith [norm_nonneg L]
  exact norm_eq_zero.mp this

/-! ### The clamped radial profile -/

/-- `J₁ > 0` on `(0, k)` (from E1 and Lemma 3.3). -/
lemma besselJ_one_pos_of_lt_jk (hZ : ExtZeros) (r : ℝ) (hr0 : 0 < r) (hr : r < jk) :
    0 < besselJ 1 r := by
  rcases le_or_gt r (28 / 10) with h | h
  · exact besselJ_one_pos_small r hr0 h
  by_contra hcon
  push_neg at hcon
  obtain ⟨z, hz, hz0⟩ : ∃ z ∈ Set.Icc (1 : ℝ) r, besselJ 1 z = 0 :=
    intermediate_value_Icc' (by linarith) (continuous_besselJ 1).continuousOn
      ⟨hcon, (besselJ_one_pos_small 1 one_pos (by norm_num)).le⟩
  obtain ⟨hmono1, -, -, hall1, -⟩ := hZ 1 (by norm_num)
  obtain ⟨n, hn, hnz⟩ := hall1 z (by linarith [hz.1]) hz0
  have : besselZero 1 1 ≤ besselZero 1 n := hmono1.le_iff_le.mpr hn
  change jk ≤ besselZero 1 n at this
  linarith [hz.2]

/-- `x ↦ J₀(c|x-a|) - J₀(k)`. -/
noncomputable def clampG (c : ℝ) (a : Plane) (x : Plane) : ℝ := radJ0 c a x - besselJ 0 jk

lemma contDiff_clampG (c : ℝ) (a : Plane) : ContDiff ℝ (⊤ : ℕ∞) (clampG c a) :=
  (contDiff_radJ0 c a).sub contDiff_const

lemma fderiv_clampG (c : ℝ) (a : Plane) : fderiv ℝ (clampG c a) = fderiv ℝ (radJ0 c a) := by
  ext1 x; exact fderiv_sub_const _

lemma pderiv_clampG (c : ℝ) (a : Plane) (i : Fin 2) :
    pderiv i (clampG c a) = pderiv i (radJ0 c a) := by
  ext x; simp [pderiv, fderiv_clampG]

lemma laplacian_clampG (c : ℝ) (a : Plane) (x : Plane) :
    laplacian (clampG c a) x = -c ^ 2 * radJ0 c a x := by
  rw [← laplacian_radJ0]; simp [laplacian, pderiv_clampG]

lemma contDiff_pderiv_of_smooth {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (pderiv i f) :=
  (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

lemma jk_pos (hZ : ExtZeros) : 0 < jk := by
  have := parameter_signs hZ; linarith [this.1, this.2.1]

lemma clampG_sphere (hZ : ExtZeros) (a : Plane) {ρ : ℝ} (hρ : 0 < ρ) (x : Plane)
    (hx : ‖x - a‖ = ρ) :
    clampG (jk / ρ) a x = 0 ∧ fderiv ℝ (clampG (jk / ρ) a) x = 0 := by
  have hk := jk_pos hZ
  have hcr : jk / ρ * ‖x - a‖ = jk := by rw [hx]; field_simp
  constructor
  · simp [clampG, radJ0_eq, hcr]
  · have hJ1 : besselJ 1 jk = 0 := ((hZ 1 (by norm_num)).2.2.1 1 le_rfl).1
    have hG1 : besselG 1 ((jk / ρ) ^ 2 * ‖x - a‖ ^ 2) = 0 := by
      rw [← mul_pow, hcr]
      rw [besselJ_eq_besselG] at hJ1
      have : jk / 2 ≠ 0 := by positivity
      simpa [this] using hJ1
    rw [fderiv_clampG]
    apply clm_eq_zero_of_pderiv
    · have := pderiv_radJ0 (jk / ρ) a 0 x
      simp only [pderiv] at this
      rw [this, hG1]; ring
    · have := pderiv_radJ0 (jk / ρ) a 1 x
      simp only [pderiv] at this
      rw [this, hG1]; ring

lemma pderiv_clampG_sphere (hZ : ExtZeros) (a : Plane) {ρ : ℝ} (hρ : 0 < ρ) (j : Fin 2)
    (x : Plane) (hx : ‖x - a‖ = ρ) : pderiv j (clampG (jk / ρ) a) x = 0 := by
  simp [pderiv, (clampG_sphere hZ a hρ x hx).2]

/-! ### The clamped test and the upper bound -/

/-- The clamped test function `U_ρ` has buckling quotient `k²/ρ²`. -/
theorem clamped_test (a : Plane) {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) :
    ∃ v ∈ H02 (ball a R), energy1' v ≠ 0 ∧ energy2 v = jk ^ 2 / ρ ^ 2 * energy1' v := by
  have hZ := extZeros_holds
  have hk := jk_pos hZ
  set c := jk / ρ with hc
  have hc0 : 0 < c := by positivity
  set g := clampG c a with hg
  set U := ballGlue a ρ g with hU
  have hsph : ∀ x, ‖x - a‖ = ρ → g x = 0 ∧ fderiv ℝ g x = 0 := clampG_sphere hZ a hρ
  have hgd : Differentiable ℝ g := (contDiff_clampG c a).differentiable (by simp)
  have hpU : ∀ j, pderiv j U = ballGlue a ρ (pderiv j g) := pderiv_ballGlue a hgd hsph
  obtain ⟨L, hL⟩ := ballGlue_lipschitz a ((contDiff_clampG c a).of_le (by simp))
    (fun x hx => (hsph x hx).1)
  have hLw : ∀ j, ∃ L' : NNReal, LipschitzWith L' (pderiv j U) := by
    intro j
    rw [hpU j]
    exact ballGlue_lipschitz a ((contDiff_pderiv_of_smooth (contDiff_clampG c a) j).of_le
      (by simp)) (fun x hx => pderiv_clampG_sphere hZ a hρ j x hx)
  have hts : tsupport U ⊆ closedBall a ρ := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    by_contra h
    exact hx (by simp [U, ballGlue, h])
  have hcs : HasCompactSupport U :=
    (isCompact_closedBall a ρ).of_isClosed_subset (isClosed_tsupport _) hts
  obtain ⟨v, hv, h1, h2⟩ := lipschitz_mem_H02 extMollification2_holds isOpen_ball hL hcs
    (hts.trans (closedBall_subset_ball hρR)) hLw
  set F1 : ℝ → ℝ := fun r => if r ≤ ρ then c ^ 2 * besselJ 1 (c * r) ^ 2 else 0 with hF1
  set F2 : ℝ → ℝ := fun r => if r ≤ ρ then c ^ 2 * (c ^ 2 * besselJ 0 (c * r) ^ 2) else 0
    with hF2
  have hI1 : ∫ x, ‖fderiv ℝ U x‖ ^ 2 = ∫ x, F1 ‖x - a‖ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [U, fderiv_ballGlue a hgd hsph x, ballGlue, F1]
    split_ifs
    · rw [hg, fderiv_clampG, norm_fderiv_radJ0_sq]
    · simp
  have hI2 : ∫ x, laplacian U x ^ 2 = ∫ x, F2 ‖x - a‖ := by
    have hsph0 : ∀ᵐ x ∂(volume : Measure Plane), x ∉ sphere a ρ :=
      measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume a ρ)
    refine integral_congr_ae ?_
    filter_upwards [hsph0] with x hx
    rw [mem_sphere, dist_eq_norm] at hx
    rcases lt_or_gt_of_ne hx with h | h
    · have hl : laplacian U x = laplacian g x := by
        simp only [laplacian, hpU]
        simp only [pderiv]
        rw [(ballGlue_eventually_inside a (pderiv 0 g) h).fderiv_eq,
          (ballGlue_eventually_inside a (pderiv 1 g) h).fderiv_eq]
      rw [hl, hg, laplacian_clampG, radJ0_eq]
      simp only [F2, h.le, if_true]
      ring
    · have hl : laplacian U x = 0 := by
        simp only [laplacian, hpU]
        simp only [pderiv]
        rw [(ballGlue_eventually_outside a (pderiv 0 g) h).fderiv_eq,
          (ballGlue_eventually_outside a (pderiv 1 g) h).fderiv_eq]
        simp
      rw [hl]
      simp [F2, not_le.mpr h]
  have hJ : besselJ 0 (c * ρ) * besselJ 1 (c * ρ) = 0 := by
    have : c * ρ = jk := by rw [hc]; field_simp
    have h1k : besselJ 1 jk = 0 := ((hZ 1 (by norm_num)).2.2.1 1 le_rfl).1
    rw [this, h1k, mul_zero]
  have key := bessel_radial_identity c ρ hρ hJ
  have hF2' : ∫ y in Ioi (0 : ℝ), y * F2 y =
      c ^ 2 * (c ^ 2 * ∫ y in Ioi (0 : ℝ), y * (if y ≤ ρ then besselJ 0 (c * y) ^ 2 else 0)) := by
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1; ext y
    simp only [F2]; split_ifs <;> ring
  have hpos : 0 < ∫ y in Ioi (0 : ℝ), y * F1 y := by
    rw [integral_Ioi_ite hρ]
    have hcont : Continuous fun y => y * (c ^ 2 * besselJ 1 (c * y) ^ 2) := by
      have := continuous_besselJ 1; fun_prop
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
      (fun y hy => ?_) hρ
    have hy1 : c * y < jk := by
      rw [hc, div_mul_eq_mul_div, div_lt_iff₀ hρ]; exact mul_lt_mul_of_pos_left hy.2 hk
    have := besselJ_one_pos_of_lt_jk hZ (c * y) (by nlinarith [hy.1]) hy1
    have := hy.1
    positivity
  refine ⟨v, hv, ?_, ?_⟩
  · rw [h1, hI1, integral_radial]
    positivity
  · rw [h2, h1, hI2, hI1, integral_radial, integral_radial, hF2', key, ← key, hc, div_pow]
    ring

/-- **Lemma 11.6, upper bound.**  `Λ₁(B_R(a)) ≤ k²/R²`. -/
theorem bucklingEig_ball_le (a : Plane) {R : ℝ} (hR : 0 < R) :
    bucklingEig (ball a R) ≤ jk ^ 2 / R ^ 2 := by
  have hle : ∀ ρ, 0 < ρ → ρ < R → bucklingEig (ball a R) ≤ jk ^ 2 / ρ ^ 2 := by
    intro ρ hρ hρR
    obtain ⟨v, hv, h0, h1⟩ := clamped_test a hρ hρR
    calc bucklingEig (ball a R) ≤ energy2 v / energy1' v := bucklingEig_le v hv h0
      _ = jk ^ 2 / ρ ^ 2 := by rw [h1]; field_simp
  have hcont : Tendsto (fun ρ : ℝ => jk ^ 2 / ρ ^ 2) (𝓝[<] R) (𝓝 (jk ^ 2 / R ^ 2)) :=
    ((continuousAt_const.div (continuous_pow 2).continuousAt
      (pow_ne_zero 2 hR.ne')).tendsto).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsLT hR] with ρ hρ using hle ρ hρ.1 hρ.2

end Buckling
end
end ChunkedSource043
/- END SOURCE 043 -/

/- BEGIN SOURCE 044: RequestProject/Disk/BesselGround.lean -/
section ChunkedSource044

/-!
# The Bessel ground state `χ(r) = J₁(k r / R)`

We check that `χ(r) = J₁(k r / R)` (with `k = j₁,₁`) satisfies the hypotheses of the
one-dimensional ground-state inequality on `(0, R)` with `μ = k² / R²`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology

namespace Buckling

namespace Ground1D

/-- `χ(r) = J₁(k r / R)`. -/
noncomputable def chiB (R : ℝ) (r : ℝ) : ℝ := besselJ 1 (jk / R * r)

/-- Its derivative `χ'(r) = (k/R) J₁'(k r / R)`. -/
noncomputable def dchiB (R : ℝ) (r : ℝ) : ℝ :=
  jk / R * ((besselJ 0 (jk / R * r) - besselJ 2 (jk / R * r)) / 2)

lemma hasDerivAt_chiB (R r : ℝ) : HasDerivAt (chiB R) (dchiB R r) r := by
  have h := (hasDerivAt_besselJ_succ 0 (jk / R * r)).comp r
    ((hasDerivAt_id r).const_mul (jk / R))
  unfold chiB dchiB
  convert! h using 1 <;> simp [Function.comp_def] <;> ring

lemma flux_chiB (R s : ℝ) :
    s * dchiB R s = jk / R * s * besselJ 0 (jk / R * s) - besselJ 1 (jk / R * s) := by
  have hr := besselJ_recurrence 0 (jk / R * s)
  push_cast at hr
  unfold dchiB
  linear_combination (-1 / 2 : ℝ) * hr

theorem groundState_chiB {R : ℝ} (hR : 0 < R) :
    GroundState R ((jk / R) ^ 2) (chiB R) (dchiB R) := by
  have hk := jk_pos extZeros_holds
  have hJ1 : besselJ 1 jk = 0 := ((extZeros_holds 1 (by norm_num)).2.2.1 1 le_rfl).1
  have hJ0 := (coarse_J0k extZeros_holds extIntegral_holds).2
  have hc : Continuous fun r : ℝ => jk / R * r := continuous_const.mul continuous_id
  refine ⟨hR, (continuous_besselJ 1).comp hc, ?_, hasDerivAt_chiB R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_const.mul ((((continuous_besselJ 0).comp hc).sub
      ((continuous_besselJ 2).comp hc)).div_const 2)
  · simp [chiB, besselJ_zero_arg]
  · simp only [chiB]; rw [div_mul_cancel₀ _ hR.ne']; exact hJ1
  · intro r hr
    exact besselJ_one_pos_of_lt_jk extZeros_holds _ (by have := hr.1; positivity)
      (by rw [div_mul_eq_mul_div, div_lt_iff₀ hR]; exact mul_lt_mul_of_pos_left hr.2 hk)
  · simp [dchiB, besselJ_zero_arg]; positivity
  · have hr := besselJ_recurrence 0 jk
    push_cast at hr
    rw [hJ1] at hr
    have h2 : besselJ 2 jk = -besselJ 0 jk := by
      have : jk * (besselJ 0 jk + besselJ 2 jk) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hk.ne'
      · linarith
    simp only [dchiB]
    rw [div_mul_cancel₀ _ hR.ne', h2]
    have : 0 < jk / R := div_pos hk hR
    nlinarith
  · intro r hr
    have hfun : (fun s => s * dchiB R s) =
        fun s => jk / R * s * besselJ 0 (jk / R * s) - besselJ 1 (jk / R * s) :=
      funext (flux_chiB R)
    rw [hfun]
    have h0 := (hasDerivAt_besselJ_zero (jk / R * r)).comp r
      ((hasDerivAt_id r).const_mul (jk / R))
    have h1 := (hasDerivAt_besselJ_succ 0 (jk / R * r)).comp r
      ((hasDerivAt_id r).const_mul (jk / R))
    have h := (((hasDerivAt_id r).const_mul (jk / R)).fun_mul h0).fun_sub h1
    convert! h using 1
    have hrec := besselJ_recurrence 0 (jk / R * r)
    push_cast at hrec
    have hr0 : r ≠ 0 := hr.1.ne'
    simp only [chiB, Function.comp_apply, id, zero_add]
    linear_combination (norm := (field_simp; ring)) (-1 / (2 * r) : ℝ) * hrec

end Ground1D

end Buckling
end
end ChunkedSource044
/- END SOURCE 044 -/

/- BEGIN SOURCE 045: RequestProject/Disk/GapParts.lean -/
section ChunkedSource045

/-!
# Ingredients of the disk spectral gap

Integrating the per-radius Parseval identities over `0 < r < R` expresses the two energies
of a test function as sums of one-dimensional mode energies, and the pairing with the disk
eigenfunction only sees the radial mode.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

namespace DiskCoeff

open Fourier1D Mode1D Ground1D

/-- Interchanging a sum of nonnegative functions with an interval integral. -/
lemma hasSum_integral_nonneg {f : ℤ → ℝ → ℝ} {g : ℝ → ℝ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ n, ContinuousOn (f n) (Ioi 0)) (hnn : ∀ n r, 0 < r → 0 ≤ f n r)
    (hs : ∀ r, 0 < r → HasSum (fun n => f n r) (g r)) (hg : Continuous g) :
    HasSum (fun n => ∫ r in (0 : ℝ)..R, f n r) (∫ r in (0 : ℝ)..R, g r) := by
  have hI : uIoc (0 : ℝ) R = Ioc 0 R := uIoc_of_le hR.le
  refine intervalIntegral.hasSum_integral_of_dominated_convergence f (fun n => ?_)
    (fun n => Eventually.of_forall fun r hr => ?_) (Eventually.of_forall fun r hr => ?_) ?_
    (Eventually.of_forall fun r hr => ?_)
  · rw [hI]
    exact ((hf n).mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  · rw [hI] at hr
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn n r hr.1)]
  · rw [hI] at hr
    exact (hs r hr.1).summable
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le]
    exact (hg.integrableOn_Icc.mono_set Ioc_subset_Icc_self).congr_fun
      (fun r hr => ((hs r hr.1).tsum_eq).symm) measurableSet_Ioc
  · rw [hI] at hr
    exact hs r hr.1

lemma hasSum_polar_aux {F : Plane → ℝ} (hF : Continuous F) (a : Plane) {R : ℝ} (hR : 0 < R)
    (hs : ∀ x, R ≤ ‖x - a‖ → F x = 0) {f : ℤ → ℝ → ℝ}
    (hf : ∀ n, ContinuousOn (f n) (Ioi 0)) (hnn : ∀ n r, 0 < r → 0 ≤ f n r)
    (hsum : ∀ r, 0 < r → HasSum (fun n => f n r)
      (r * (1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, F (a + r • ePt θ)))) :
    HasSum (fun n => ∫ r in (0 : ℝ)..R, f n r) (1 / (2 * π) * ∫ x, F x) := by
  have hc : Continuous fun r : ℝ => r * (1 / (2 * π) * ∫ θ in (0 : ℝ)..2 * π, F (a + r • ePt θ)) := by
    refine continuous_id.mul (continuous_const.mul ?_)
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun r θ => F (a + r • ePt θ)) (hF.comp (cont_pt a)) _ _
  have h := hasSum_integral_nonneg hR hf hnn hsum hc
  rw [integral_polar hF a hR hs]
  convert h using 1
  rw [← intervalIntegral.integral_const_mul]
  congr 1; ext r; ring

lemma pderiv_clampG_polar (a : Plane) (c : ℝ) (i : Fin 2) (r θ : ℝ) :
    pderiv i (clampG c a) (a + r • ePt θ) = -(c * besselJ 1 (c * r)) * ePt θ i := by
  rw [pderiv_clampG, pderiv_radJ0, add_sub_cancel_left, norm_smul, norm_ePt, mul_one,
    Real.norm_eq_abs, sq_abs, besselJ_eq_besselG]
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, add_sub_cancel_left]
  ring_nf

variable {φ : Plane → ℝ} (a : Plane) {R : ℝ}


lemma fderiv_eq_zero_of_far (hφ : IsTestFn (ball a R) φ) {x : Plane} (hx : R ≤ ‖x - a‖) : fderiv ℝ φ x = 0 := by
  have hx' : x ∉ tsupport φ := fun h => by
    have := hφ.2.2 h
    rw [mem_ball, dist_eq_norm] at this
    linarith
  exact Function.notMem_support.1 fun h => hx' (support_fderiv_subset ℝ h)

lemma laplacian_eq_zero_of_far (hφ : IsTestFn (ball a R) φ) {x : Plane} (hx : R ≤ ‖x - a‖) : laplacian φ x = 0 := by
  have hx' : x ∉ ball a R := by rw [mem_ball, dist_eq_norm]; linarith
  rw [laplacian, ((hφ.pderiv 0).pderiv 0).eq_zero_of_notMem hx',
    ((hφ.pderiv 1).pderiv 1).eq_zero_of_notMem hx', add_zero]

variable (hR : 0 < R) (hφ : IsTestFn (ball a R) φ)
include hR hφ

/-- `∫ |∇φ|² = 2π Σₙ (E(aₙ) + E(bₙ))`. -/
theorem hasSum_gradE :
    HasSum (fun n : ℤ => gradE R n.natAbs (aC φ a n) + gradE R n.natAbs (bC φ a n))
      (1 / (2 * π) * ∫ x, ‖fderiv ℝ φ x‖ ^ 2) := by
  have hsm := hφ.1
  have hc := hφ.2.1
  have hA := fun n => modeFn_aC a hsm hc hR hφ.2.2 n
  have hB := fun n => modeFn_bC a hsm hc hR hφ.2.2 n
  have h := hasSum_polar_aux (F := fun x => ‖fderiv ℝ φ x‖ ^ 2) ((cont1 hsm).norm.pow 2) a hR
    (fun x hx => by simp [fderiv_eq_zero_of_far a hφ hx]) (f := gdens φ a) ?_ ?_
    (fun r hr => hasSum_gdens a hsm hc hr)
  · convert h using 1
    ext n
    unfold gdens gradE
    rw [intervalIntegral.integral_add (hA n).int_grad (hB n).int_grad]
  · intro n
    have cA := (hA n).diff.continuous
    have dA := (hA n).ddiff.continuous
    have cB := (hB n).diff.continuous
    have dB := (hB n).ddiff.continuous
    have h0 : ∀ r ∈ Ioi (0 : ℝ), r ≠ 0 := fun r hr => ne_of_gt hr
    exact ((continuousOn_id.mul (dA.continuousOn.pow 2)).add
      ((continuousOn_const.mul (cA.continuousOn.pow 2)).div continuousOn_id h0)).add
      ((continuousOn_id.mul (dB.continuousOn.pow 2)).add
      ((continuousOn_const.mul (cB.continuousOn.pow 2)).div continuousOn_id h0))
  · intro n r hr
    unfold gdens
    positivity

/-- `∫ (Δφ)² = 2π Σₙ (L(aₙ) + L(bₙ))`. -/
theorem hasSum_lapE :
    HasSum (fun n : ℤ => lapE R n.natAbs (aC φ a n) + lapE R n.natAbs (bC φ a n))
      (1 / (2 * π) * ∫ x, laplacian φ x ^ 2) := by
  have hsm := hφ.1
  have hc := hφ.2.1
  have hA := fun n => modeFn_aC a hsm hc hR hφ.2.2 n
  have hB := fun n => modeFn_bC a hsm hc hR hφ.2.2 n
  have hLc : Continuous (laplacian φ) := by
    have h0 := hφ.pderiv 0
    have h1 := hφ.pderiv 1
    exact (((h0.pderiv 0).1.continuous).add ((h1.pderiv 1).1.continuous))
  have h := hasSum_polar_aux (F := fun x => laplacian φ x ^ 2) (hLc.pow 2) a hR
    (fun x hx => by simp [laplacian_eq_zero_of_far a hφ hx]) (f := ldens φ a) ?_ ?_
    (fun r hr => hasSum_ldens a hsm hc hr)
  · convert h using 1
    ext n
    unfold ldens lapE
    rw [intervalIntegral.integral_add (hA n).int_lap (hB n).int_lap]
  · intro n
    have h0 : ∀ r ∈ Ioi (0 : ℝ), r ≠ 0 := fun r hr => ne_of_gt hr
    have h2 : ∀ r ∈ Ioi (0 : ℝ), r ^ 2 ≠ 0 := fun r hr => pow_ne_zero _ (ne_of_gt hr)
    have key : ∀ v : ℝ → ℝ, ModeFn R n.natAbs v → ContinuousOn (fun r => r * (deriv (deriv v) r +
        deriv v r / r - ((n.natAbs : ℕ) : ℝ) ^ 2 * v r / r ^ 2) ^ 2) (Ioi 0) := by
      intro v hv
      exact continuousOn_id.mul (((hv.d2cont.continuousOn.add
        (hv.ddiff.continuous.continuousOn.div continuousOn_id h0)).sub
        ((continuousOn_const.mul hv.diff.continuous.continuousOn).div
          (continuousOn_id.pow 2) h2)).pow 2)
    exact (key _ (hA n)).add (key _ (hB n))
  · intro n r hr
    unfold ldens
    positivity

/-- The pairing with the disk eigenfunction only sees the radial mode. -/
theorem gradPair_eq :
    ∫ x, (pderiv 0 φ x * pderiv 0 (clampG (jk / R) a) x +
        pderiv 1 φ x * pderiv 1 (clampG (jk / R) a) x) =
      -(2 * π * (jk / R) * ∫ r in (0 : ℝ)..R, r * deriv (aC φ a 0) r * chiB R r) := by
  have hsm := hφ.1
  have hc := hφ.2.1
  have hcU := contDiff_clampG (jk / R) a
  have hH : Continuous fun x => pderiv 0 φ x * pderiv 0 (clampG (jk / R) a) x +
      pderiv 1 φ x * pderiv 1 (clampG (jk / R) a) x :=
    (((hφ.pderiv 0).1.continuous).mul (contDiff_pderiv_of_smooth hcU 0).continuous).add
      (((hφ.pderiv 1).1.continuous).mul (contDiff_pderiv_of_smooth hcU 1).continuous)
  rw [integral_polar hH a hR (fun x hx => by
    simp [pderiv, fderiv_eq_zero_of_far a hφ hx])]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr (fun r _ => ?_)
  have hpt : ∀ θ, pderiv 0 φ (a + r • ePt θ) * pderiv 0 (clampG (jk / R) a) (a + r • ePt θ) +
      pderiv 1 φ (a + r • ePt θ) * pderiv 1 (clampG (jk / R) a) (a + r • ePt θ) =
      -(jk / R * besselJ 1 (jk / R * r)) * G1 φ a r θ := by
    intro θ
    rw [pderiv_clampG_polar, pderiv_clampG_polar]
    simp only [G1, pderiv, ePt, map_add, map_smul, smul_eq_mul, PiLp.add_apply, PiLp.smul_apply]
    simp
    ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, deriv_aC_apply a hsm hc]
  simp only [cosC, chiB, Int.cast_zero, zero_mul, Real.cos_zero, mul_one]
  have := Real.pi_pos
  field_simp

end DiskCoeff

/-- `∫_B |∇U|² = 2π (k/R)² ∫₀ᴿ r χ²`. -/
theorem E1U_eq (a : Plane) {R : ℝ} (hR : 0 < R) :
    ∫ x in ball a R, ‖fderiv ℝ (clampG (jk / R) a) x‖ ^ 2 =
      2 * π * (jk / R) ^ 2 * Ground1D.mass R (Ground1D.chiB R) := by
  set c := jk / R
  have hJ1 : besselJ 1 jk = 0 := ((extZeros_holds 1 (by norm_num)).2.2.1 1 le_rfl).1
  have hcR : c * R = jk := div_mul_cancel₀ _ hR.ne'
  set F : Plane → ℝ := fun x => c ^ 2 * besselJ 1 (c * min ‖x - a‖ R) ^ 2 with hF
  have hFc : Continuous F := continuous_const.mul (((continuous_besselJ 1).comp
    (continuous_const.mul ((continuous_id.sub continuous_const).norm.min continuous_const))).pow 2)
  have hFs : ∀ x, R ≤ ‖x - a‖ → F x = 0 := by
    intro x hx
    simp [hF, min_eq_right hx, hcR, hJ1]
  have h1 : ∫ x in ball a R, ‖fderiv ℝ (clampG c a) x‖ ^ 2 = ∫ x in ball a R, F x := by
    refine setIntegral_congr_fun measurableSet_ball (fun x hx => ?_)
    rw [mem_ball, dist_eq_norm] at hx
    simp only [hF, fderiv_clampG, norm_fderiv_radJ0_sq, min_eq_left hx.le]
  have h2 : ∫ x in ball a R, F x = ∫ x, F x := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => hFs x ?_)
    rw [mem_ball, dist_eq_norm, not_lt] at hx
    exact hx
  rw [h1, h2, integral_polar hFc a hR hFs, Ground1D.mass, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr (fun r hr => ?_)
  rw [uIcc_of_le hR.le] at hr
  have hm : min ‖a + r • ePt 0 - a‖ R = r := by
    rw [add_sub_cancel_left, norm_smul, norm_ePt, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.1,
      min_eq_left hr.2]
  have hpt : ∀ θ, F (a + r • ePt θ) = c ^ 2 * besselJ 1 (c * r) ^ 2 := by
    intro θ
    simp only [hF]
    rw [add_sub_cancel_left, norm_smul, norm_ePt, mul_one, Real.norm_eq_abs, abs_of_nonneg hr.1,
      min_eq_left hr.2]
  simp only [hpt, intervalIntegral.integral_const, smul_eq_mul, Ground1D.chiB]
  ring

end Buckling
end
end ChunkedSource045
/- END SOURCE 045 -/

/- BEGIN SOURCE 046: RequestProject/Disk/Gap.lean -/
section ChunkedSource046

/-!
# A spectral gap for the buckling quotient on a disk

Let `B = B_R(a)`, `μ = k²/R²` and `U = U_{R,a}`, `U(x) = J₀(k|x-a|/R) - J₀(k)`.
The key quantitative input for the second part of Lemma 11.6 and for Lemma 12.1 is a
spectral gap: there is `δ > 0` such that for every test function `φ ∈ C_c^∞(B)`,
`E₂(φ) - μ E₁(φ) ≥ δ · E₁(φ - cU)`, where `cU` is the `E₁`-orthogonal projection of `φ`
on `U`.  Multiplying out by `E₁(U)`, this reads
`δ (E₁(φ) E₁(U) - ⟨∇φ, ∇U⟩²) ≤ E₁(U) (E₂(φ) - μ E₁(φ))`.

It follows from the angular decomposition of Section 11: the nonradial modes have
quotient at least `μ + 3/R²`, and on the radial mode the quotient exceeds `μ` by a
multiple of the distance to `U`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

/-- The disk buckling eigenfunction `U_{R,a}(x) = J₀(k|x-a|/R) - J₀(k)`, as a smooth
function on the whole plane. -/
noncomputable abbrev diskU (a : Plane) (R : ℝ) : Plane → ℝ := clampG (jk / R) a

/-- The pairing `∫ ∇φ · ∇ψ` of gradients over the whole plane. -/
noncomputable def gradPair (φ ψ : Plane → ℝ) : ℝ :=
  ∫ x, (pderiv 0 φ x * pderiv 0 ψ x + pderiv 1 φ x * pderiv 1 ψ x)

open DiskCoeff Mode1D Ground1D in
/-- **Spectral gap on the disk.** -/
theorem disk_gap (a : Plane) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ φ : Plane → ℝ, IsTestFn (ball a R) φ →
      δ * ((∫ x, ‖fderiv ℝ φ x‖ ^ 2) * (∫ x in ball a R, ‖fderiv ℝ (diskU a R) x‖ ^ 2)
          - gradPair φ (diskU a R) ^ 2)
        ≤ (∫ x in ball a R, ‖fderiv ℝ (diskU a R) x‖ ^ 2) *
          ((∫ x, laplacian φ x ^ 2) - jk ^ 2 / R ^ 2 * ∫ x, ‖fderiv ℝ φ x‖ ^ 2) := by
  have hk := jk_pos extZeros_holds
  have gs := groundState_chiB hR
  obtain ⟨δ0, hδ0, h0⟩ := mode_zero gs
  have hM : 0 < mass R (chiB R) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on ((continuous_id.mul (gs.cont.pow 2)).intervalIntegrable _ _)
      (fun r hr => mul_pos hr.1 (pow_pos (gs.pos r hr) 2)) hR
  have hδ : 0 < min δ0 (3 / R ^ 2) := lt_min hδ0 (by positivity)
  refine ⟨min δ0 (3 / R ^ 2), hδ, fun φ hφ => ?_⟩
  set δ := min δ0 (3 / R ^ 2) with hδdef
  set M := mass R (chiB R) with hMdef
  set μ := (jk / R) ^ 2 with hμ
  set P := ∫ r in (0 : ℝ)..R, r * deriv (aC φ a 0) r * chiB R r with hPdef
  have hsm := hφ.1
  have hc := hφ.2.1
  have hsub := hφ.2.2
  have hG := hasSum_gradE a hR hφ
  have hL := hasSum_lapE a hR hφ
  have hP : gradPair φ (diskU a R) = -(2 * π * (jk / R) * P) := gradPair_eq a hR hφ
  have hU := E1U_eq a hR
  have hb0 : bC φ a 0 = fun _ => 0 := by ext r; simp [bC, Fourier1D.sinC]
  have hterm : ∀ n : ℤ, 0 ≤ (lapE R n.natAbs (aC φ a n) + lapE R n.natAbs (bC φ a n)) -
      μ * (gradE R n.natAbs (aC φ a n) + gradE R n.natAbs (bC φ a n)) -
      δ * (gradE R n.natAbs (aC φ a n) + gradE R n.natAbs (bC φ a n)) +
      (if n = 0 then δ * P ^ 2 / M else 0) := by
    intro n
    have hA := modeFn_aC a hsm hc hR hsub n
    have hB := modeFn_bC a hsm hc hR hsub n
    have gA := hA.gradE_nonneg
    have gB := hB.gradE_nonneg
    by_cases hn : n = 0
    · subst hn
      have e1 : gradE R (0 : ℤ).natAbs (bC φ a 0) = 0 := by simp [hb0, gradE]
      have e2 : lapE R (0 : ℤ).natAbs (bC φ a 0) = 0 := by simp [hb0, lapE]
      rw [e1, e2, if_pos rfl]
      simp only [Int.natAbs_zero] at hA ⊢
      have h0' := h0 _ hA
      have hge := hA.mode_ge gs
      have hδ1 : δ ≤ δ0 := min_le_left _ _
      set x := gradE R 0 (aC φ a 0) - P ^ 2 / M with hx
      have : δ * x ≤ lapE R 0 (aC φ a 0) - μ * gradE R 0 (aC φ a 0) := by
        rcases le_total 0 x with h | h
        · exact (mul_le_mul_of_nonneg_right hδ1 h).trans h0'
        · nlinarith
      have e : δ * x = δ * gradE R 0 (aC φ a 0) - δ * P ^ 2 / M := by rw [hx]; ring
      linarith
    · rw [if_neg hn]
      have hn' : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
      have pA := mode_pos gs hn' hA
      have pB := mode_pos gs hn' hB
      have hδ2 : δ ≤ 3 / R ^ 2 := min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_right hδ2 gA, mul_le_mul_of_nonneg_right hδ2 gB]
  have hsum := ((hL.sub (hG.mul_left μ)).sub (hG.mul_left δ)).add
    (hasSum_ite_eq (0 : ℤ) (δ * P ^ 2 / M))
  have key := hsum.nonneg hterm
  rw [hP, hU]
  set E1 := ∫ x, ‖fderiv ℝ φ x‖ ^ 2
  set E2 := ∫ x, laplacian φ x ^ 2
  have hpi := Real.pi_pos
  have hfac : 0 ≤ 4 * π ^ 2 * μ * M := by positivity
  have hprod := mul_nonneg hfac key
  have e : 2 * π * (jk / R) ^ 2 * M * (E2 - jk ^ 2 / R ^ 2 * E1) -
      δ * (E1 * (2 * π * (jk / R) ^ 2 * M) - (-(2 * π * (jk / R) * P)) ^ 2) =
      4 * π ^ 2 * μ * M * (1 / (2 * π) * E2 - μ * (1 / (2 * π) * E1) -
        δ * (1 / (2 * π) * E1) + δ * P ^ 2 / M) := by
    rw [hμ]; field_simp; ring
  linarith

end Buckling
end
end ChunkedSource046
/- END SOURCE 046 -/

/- BEGIN SOURCE 047: RequestProject/Functional/Calculus.lean -/
section ChunkedSource047

/-!
# Calculus helpers for Section 9

Support of derivatives, symmetry of second partial derivatives, integration by parts for
test functions, and integrability of the derivatives of compactly supported Lipschitz
functions.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

lemma tsupport_pderiv_subset' (φ : Plane → ℝ) (i : Fin 2) :
    tsupport (pderiv i φ) ⊆ tsupport φ := by
  refine (tsupport_fderiv_subset ℝ (f := φ)).trans' ?_
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h0
  exact hx (by simp [Buckling.pderiv, h0])

lemma tsupport_subset_of_vanish {f U : Plane → ℝ} (h : ∀ x, x ∉ tsupport U → f x = 0) :
    tsupport f ⊆ tsupport U :=
  closure_minimal (fun x hx => by_contra fun hc => hx (h x hc)) (isClosed_tsupport _)

lemma pderiv_eq_zero_of_notMem {U : Plane → ℝ} {x : Plane} (hx : x ∉ tsupport U) (i : Fin 2) :
    pderiv i U x = 0 := by
  simp [pderiv, fderiv_eq_zero_of_notMem_tsupport hx]

lemma pderiv2_eq_zero_of_notMem {U : Plane → ℝ} {x : Plane} (hx : x ∉ tsupport U) (i j : Fin 2) :
    pderiv i (pderiv j U) x = 0 :=
  pderiv_eq_zero_of_notMem (fun h => hx (tsupport_pderiv_subset' U j h)) i

lemma integrable_pderiv_of_lipschitz {V : Plane → ℝ} {L : NNReal} (hV : LipschitzWith L V)
    (hc : HasCompactSupport V) (i : Fin 2) : Integrable (pderiv i V) := by
  have hm : Measurable (pderiv i V) := measurable_fderiv_apply_const ℝ V _
  have hb : ∀ x, ‖pderiv i V x‖ ≤ L := by
    intro x
    calc ‖pderiv i V x‖ ≤ ‖fderiv ℝ V x‖ * ‖(EuclideanSpace.single i (1:ℝ) : Plane)‖ :=
          (fderiv ℝ V x).le_opNorm _
      _ ≤ L * 1 := by
          gcongr
          · exact norm_fderiv_le_of_lipschitz ℝ hV
          · simp
      _ = L := mul_one _
  have hs : Function.support (pderiv i V) ⊆ tsupport V := fun x hx =>
    by_contra fun hc' => hx (pderiv_eq_zero_of_notMem hc' i)
  rw [← integrableOn_iff_integrable_of_support_subset hs]
  exact Measure.integrableOn_of_bounded (M := L) hc.measure_lt_top.ne hm.aestronglyMeasurable
    (ae_of_all _ hb)

lemma pderiv_comm {f : Plane → ℝ} (hf : ContDiff ℝ 2 f) (i j : Fin 2) (x : Plane) :
    pderiv i (pderiv j f) x = pderiv j (pderiv i f) x := by
  have hd : ∀ k : Fin 2, pderiv i (pderiv k f) x = fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single k 1) := by
    intro k
    unfold pderiv
    rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      (differentiableAt_const _)]
    simp
  have hd' : ∀ k : Fin 2, pderiv j (pderiv k f) x = fderiv ℝ (fderiv ℝ f) x
      (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
    intro k
    unfold pderiv
    rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
      (differentiableAt_const _)]
    simp
  rw [hd, hd']
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

lemma ibp_test {f g : Plane → ℝ} (hf : IsTestFn univ f) (hg : IsTestFn univ g) (i : Fin 2) :
    ∫ x, f x * pderiv i g x = -∫ x, pderiv i f x * g x := by
  have hc : ∀ {g : Plane → ℝ}, IsTestFn univ g → ∀ {h : Plane → ℝ}, IsTestFn univ h →
      Integrable (fun x => g x * h x) := by
    intro g hg h hh
    exact (hg.1.continuous.mul hh.1.continuous).integrable_of_hasCompactSupport
      (hg.2.1.mul_right)
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Plane))
    (f := f) (g := g) (v := EuclideanSpace.single i 1)
    (hc (hf.pderiv i) hg) (hc hf (hg.pderiv i)) (hc hf hg)
    (fun x _ => (hf.1.differentiable (by simp)) x)
    (fun x _ => (hg.1.differentiable (by simp)) x)
  simpa [pderiv] using this

lemma lipschitz_mul_bdd {f g : Plane → ℝ} {Lf Lg : NNReal} (hf : LipschitzWith Lf f)
    (hg : LipschitzWith Lg g) {Cf Cg : ℝ} (hCf : ∀ x, |f x| ≤ Cf) (hCg : ∀ x, |g x| ≤ Cg) :
    ∃ L, LipschitzWith L (fun x => f x * g x) := by
  refine ⟨_, LipschitzWith.of_dist_le' (K := Cf * Lg + Cg * Lf) fun x y => ?_⟩
  rw [Real.dist_eq]
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  have h1 := hf.dist_le_mul x y
  have h2 := hg.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2
  calc |f x * (g x - g y) + g y * (f x - f y)|
      ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ Cf * (Lg * dist x y) + Cg * (Lf * dist x y) := by
        gcongr
        · exact le_trans (abs_nonneg _) (hCf x)
        · exact hCf x
        · exact le_trans (abs_nonneg _) (hCg y)
        · exact hCg y
    _ = (Cf * Lg + Cg * Lf) * dist x y := by ring

lemma IsTestFn.lipschitz {U : Plane → ℝ} (hU : IsTestFn univ U) : ∃ L, LipschitzWith L U :=
  ContDiff.lipschitzWith_of_hasCompactSupport hU.2.1 hU.1 (by simp)

lemma IsTestFn.bdd {U : Plane → ℝ} (hU : IsTestFn univ U) : ∃ C, ∀ x, |U x| ≤ C := by
  obtain ⟨C, hC⟩ := hU.1.continuous.bounded_above_of_compact_support hU.2.1
  exact ⟨C, fun x => by simpa using hC x⟩

lemma IsTestFn.lipschitz_fderiv {U : Plane → ℝ} (hU : IsTestFn univ U) :
    ∃ L, LipschitzWith L (fderiv ℝ U) :=
  ContDiff.lipschitzWith_of_hasCompactSupport (hU.2.1.fderiv (𝕜 := ℝ))
    (hU.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)) (by simp)

lemma IsTestFn.bdd_fderiv {U : Plane → ℝ} (hU : IsTestFn univ U) :
    ∃ C, ∀ x, ‖fderiv ℝ U x‖ ≤ C :=
  ((hU.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).continuous).bounded_above_of_compact_support
    (hU.2.1.fderiv (𝕜 := ℝ))

/-- Composition of a Lipschitz perspective with Lipschitz maps. -/
lemma lipschitz_persp_comp {Φ : ℝ → ℝ → ℝ} {L : ℝ}
    (hΦ : ∀ A A' P P' : ℝ, 0 ≤ P → 0 ≤ P' → |Φ A P - Φ A' P'| ≤ L * (|A - A'| + |P - P'|))
    {a p : Plane → ℝ} {La Lp : NNReal} (ha : LipschitzWith La a) (hp : LipschitzWith Lp p)
    (hp0 : ∀ x, 0 ≤ p x) : ∃ K, LipschitzWith K (fun x => Φ (a x) (p x)) := by
  refine ⟨_, LipschitzWith.of_dist_le' (K := L * (La + Lp)) fun x y => ?_⟩
  have h1 := ha.dist_le_mul x y
  have h2 := hp.dist_le_mul x y
  rw [Real.dist_eq] at h1 h2 ⊢
  have hL : 0 ≤ L := by
    have := hΦ 1 0 0 0 le_rfl le_rfl
    simp at this
    nlinarith [abs_nonneg (Φ 1 0 - Φ 0 0)]
  calc |Φ (a x) (p x) - Φ (a y) (p y)| ≤ L * (|a x - a y| + |p x - p y|) :=
        hΦ _ _ _ _ (hp0 x) (hp0 y)
    _ ≤ L * (La * dist x y + Lp * dist x y) := by gcongr
    _ = L * (La + Lp) * dist x y := by ring

lemma IsTestFn.lip_bdd {U : Plane → ℝ} (hU : IsTestFn univ U) :
    (∃ L, LipschitzWith L U) ∧ ∃ C, ∀ x, |U x| ≤ C := ⟨hU.lipschitz, hU.bdd⟩

lemma lip_bdd_mul {f g : Plane → ℝ} (hf : (∃ L, LipschitzWith L f) ∧ ∃ C, ∀ x, |f x| ≤ C)
    (hg : (∃ L, LipschitzWith L g) ∧ ∃ C, ∀ x, |g x| ≤ C) :
    (∃ L, LipschitzWith L (fun x => f x * g x)) ∧ ∃ C, ∀ x, |f x * g x| ≤ C := by
  obtain ⟨⟨Lf, hLf⟩, Cf, hCf⟩ := hf
  obtain ⟨⟨Lg, hLg⟩, Cg, hCg⟩ := hg
  refine ⟨lipschitz_mul_bdd hLf hLg hCf hCg, Cf * Cg, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hCf x) (hCg x) (abs_nonneg _) (le_trans (abs_nonneg _) (hCf x))

lemma integrable_of_bdd_supp {g : Plane → ℝ} (hm : AEStronglyMeasurable g volume) (C : ℝ)
    (hb : ∀ x, ‖g x‖ ≤ C) {K : Set Plane} (hK : IsCompact K) (hs : ∀ x ∉ K, g x = 0) :
    Integrable g := by
  have hs' : Function.support g ⊆ K := fun x hx => by_contra fun h => hx (hs x h)
  rw [← integrableOn_iff_integrable_of_support_subset hs']
  exact Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne hm
    (ae_of_all _ hb)

lemma IsTestFn.integrable_cont {U : Plane → ℝ} (hU : IsTestFn univ U) {g : Plane → ℝ}
    (hg : Continuous g) (hs : ∀ x ∉ tsupport U, g x = 0) : Integrable g := by
  refine hg.integrable_of_hasCompactSupport ?_
  exact IsCompact.of_isClosed_subset hU.2.1 (isClosed_tsupport _)
    (closure_minimal (fun x hx => by_contra fun h => hx (hs x h)) (isClosed_tsupport _))

lemma integrable_norm_fderiv_sq_of_lipschitz {V : Plane → ℝ} {L : NNReal}
    (hV : LipschitzWith L V) (hc : HasCompactSupport V) :
    Integrable (fun x => ‖fderiv ℝ V x‖ ^ 2) := by
  refine integrable_of_bdd_supp ((measurable_fderiv ℝ V).norm.pow_const 2).aestronglyMeasurable
    (L ^ 2) (fun x => ?_) hc (fun x hx => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    gcongr
    exact norm_fderiv_le_of_lipschitz ℝ hV
  · simp [fderiv_eq_zero_of_notMem_tsupport hx]

end Buckling
end
end ChunkedSource047
/- END SOURCE 047 -/

/- BEGIN SOURCE 048: RequestProject/Disk/TestAlgebra.lean -/
section ChunkedSource048

/-!
# Linear algebra of test functions and the Hessian identity

* linear combinations of test functions are test functions, and `graphH2` is linear;
* `∑ᵢⱼ ∫ (∂ᵢ∂ⱼφ)² = ∫ (Δφ)²` for a test function (Lemma 10.2 of the paper, first identity);
* the Cauchy–Schwarz inequality for pairs of `L²` functions.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology

namespace Buckling

lemma IsTestFn.lincomb {Ω : Set Plane} {φ ψ : Plane → ℝ} (hφ : IsTestFn Ω φ) (hψ : IsTestFn Ω ψ)
    (s t : ℝ) : IsTestFn Ω (fun x => s * φ x + t * ψ x) := by
  refine ⟨(contDiff_const.mul hφ.1).add (contDiff_const.mul hψ.1), ?_, ?_⟩
  · exact (hφ.2.1.mul_left (f := fun _ => s)).add (hψ.2.1.mul_left (f := fun _ => t))
  · refine (tsupport_add _ _).trans (union_subset ?_ ?_)
    · exact (tsupport_mul_subset_right (f := fun _ => s)).trans hφ.2.2
    · exact (tsupport_mul_subset_right (f := fun _ => t)).trans hψ.2.2

lemma IsTestFn.mono {Ω Ω' : Set Plane} {φ : Plane → ℝ} (hφ : IsTestFn Ω φ) (h : Ω ⊆ Ω') :
    IsTestFn Ω' φ :=
  ⟨hφ.1, hφ.2.1, hφ.2.2.trans h⟩

lemma pderiv_lincomb {φ ψ : Plane → ℝ} (hφ : Differentiable ℝ φ) (hψ : Differentiable ℝ ψ)
    (s t : ℝ) (i : Fin 2) :
    pderiv i (fun x => s * φ x + t * ψ x) = fun x => s * pderiv i φ x + t * pderiv i ψ x := by
  ext x
  have h1 : HasFDerivAt (fun x => s * φ x + t * ψ x)
      (s • fderiv ℝ φ x + t • fderiv ℝ ψ x) x :=
    ((hφ x).hasFDerivAt.const_mul s).add ((hψ x).hasFDerivAt.const_mul t)
  simp [pderiv, h1.fderiv]

lemma graphH2_lincomb {Ω : Set Plane} {φ ψ : Plane → ℝ} (hφ : IsTestFn Ω φ) (hψ : IsTestFn Ω ψ)
    (s t : ℝ) :
    graphH2 ⟨_, hφ.lincomb hψ s t⟩ = s • graphH2 ⟨φ, hφ⟩ + t • graphH2 ⟨ψ, hψ⟩ := by
  have d : ∀ {f : Plane → ℝ}, IsTestFn Ω f → Differentiable ℝ f :=
    fun hf => hf.1.differentiable (by simp)
  have key : ∀ {f g : Plane → ℝ} (hf : IsTestFn Ω f) (hg : IsTestFn Ω g)
      (h : IsTestFn Ω (fun x => s * f x + t * g x)),
      h.toL2 = s • hf.toL2 + t • hg.toL2 := by
    intro f g hf hg h
    simp only [IsTestFn.toL2]
    rw [← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul, ← MemLp.toLp_add]
    rfl
  have hp : ∀ i, pderiv i (fun x => s * φ x + t * ψ x) =
      fun x => s * pderiv i φ x + t * pderiv i ψ x := fun i => pderiv_lincomb (d hφ) (d hψ) s t i
  have hpp : ∀ i j, pderiv i (pderiv j (fun x => s * φ x + t * ψ x)) =
      fun x => s * pderiv i (pderiv j φ) x + t * pderiv i (pderiv j ψ) x := by
    intro i j
    rw [hp j]
    exact pderiv_lincomb (d (hφ.pderiv j)) (d (hψ.pderiv j)) s t i
  have congr : ∀ {f g : Plane → ℝ} (hf : IsTestFn Ω f) (hg : IsTestFn Ω g), f = g →
      hf.toL2 = hg.toL2 := by
    intro f g hf hg h; subst h; rfl
  simp only [graphH2, Prod.smul_mk, Prod.mk_add_mk]
  refine Prod.ext (key hφ hψ (hφ.lincomb hψ s t)) (Prod.ext ?_ ?_)
  · funext i
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [congr _ ((hφ.pderiv i).lincomb (hψ.pderiv i) s t) (hp i), key]
  · funext i j
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [congr _ (((hφ.pderiv j).pderiv i).lincomb ((hψ.pderiv j).pderiv i) s t) (hpp i j), key]

/-- Cauchy–Schwarz for pairs of `L²` functions. -/
lemma sum_inner_sq_le {Ω : Set Plane} (u g : Fin 2 → L2 Ω) :
    (∑ i, inner ℝ (u i) (g i)) ^ 2 ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖g i‖ ^ 2) := by
  simp only [Fin.sum_univ_two]
  have h0 := real_inner_le_norm (u 0) (g 0)
  have h1 := real_inner_le_norm (u 1) (g 1)
  have h0' := neg_le_of_abs_le (abs_real_inner_le_norm (u 0) (g 0))
  have h1' := neg_le_of_abs_le (abs_real_inner_le_norm (u 1) (g 1))
  have hn := norm_nonneg (u 0); have hn1 := norm_nonneg (u 1)
  have hg0 := norm_nonneg (g 0); have hg1 := norm_nonneg (g 1)
  have key : (‖u 0‖ * ‖g 0‖ + ‖u 1‖ * ‖g 1‖) ^ 2 ≤
      (‖u 0‖ ^ 2 + ‖u 1‖ ^ 2) * (‖g 0‖ ^ 2 + ‖g 1‖ ^ 2) := by
    nlinarith [sq_nonneg (‖u 0‖ * ‖g 1‖ - ‖u 1‖ * ‖g 0‖)]
  have habs : |inner ℝ (u 0) (g 0) + inner ℝ (u 1) (g 1)| ≤ ‖u 0‖ * ‖g 0‖ + ‖u 1‖ * ‖g 1‖ :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc (inner ℝ (u 0) (g 0) + inner ℝ (u 1) (g 1)) ^ 2
      = |inner ℝ (u 0) (g 0) + inner ℝ (u 1) (g 1)| ^ 2 := (sq_abs _).symm
    _ ≤ (‖u 0‖ * ‖g 0‖ + ‖u 1‖ * ‖g 1‖) ^ 2 := by gcongr
    _ ≤ _ := key

/-- **Hessian identity.**  `∑ᵢⱼ ∫ (∂ᵢ∂ⱼφ)² = ∫ (Δφ)²` for a test function. -/
lemma sum_integral_hessian_sq {Ω : Set Plane} {φ : Plane → ℝ} (hφ : IsTestFn Ω φ) :
    ∑ i, ∑ j, ∫ x, pderiv i (pderiv j φ) x ^ 2 = ∫ x, laplacian φ x ^ 2 := by
  have hc : ∀ {f g : Plane → ℝ}, IsTestFn Ω f → IsTestFn Ω g → Integrable (fun x => f x * g x) :=
    fun hf hg => (hf.1.continuous.mul hg.1.continuous).integrable_of_hasCompactSupport
      hf.2.1.mul_right
  have ibp : ∀ {f g : Plane → ℝ}, IsTestFn Ω f → IsTestFn Ω g → ∀ i,
      ∫ x, f x * pderiv i g x = -∫ x, pderiv i f x * g x := by
    intro f g hf hg i
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Plane))
      (hc (hf.pderiv i) hg) (hc hf (hg.pderiv i)) (hc hf hg)
      (fun x _ => hf.1.differentiable (by simp) x)
      (fun x _ => hg.1.differentiable (by simp) x)
  have h01 : pderiv 0 (pderiv 1 φ) = pderiv 1 (pderiv 0 φ) :=
    funext fun x => pderiv_comm (hφ.1.of_le (by norm_cast)) 0 1 x
  have h010 : pderiv 0 (pderiv 1 (pderiv 0 φ)) = pderiv 1 (pderiv 0 (pderiv 0 φ)) :=
    funext fun x => pderiv_comm ((hφ.pderiv 0).1.of_le (by norm_cast)) 0 1 x
  have key : ∫ x, pderiv 0 (pderiv 1 φ) x ^ 2 =
      ∫ x, pderiv 0 (pderiv 0 φ) x * pderiv 1 (pderiv 1 φ) x := by
    have e1 : ∫ x, pderiv 0 (pderiv 1 φ) x ^ 2 =
        ∫ x, pderiv 0 (pderiv 1 φ) x * pderiv 1 (pderiv 0 φ) x := by
      congr 1; ext x; rw [h01]; ring
    have e2 := ibp (hφ.pderiv 1) ((hφ.pderiv 0).pderiv 1) 0
    have e5 := ibp (hφ.pderiv 1) ((hφ.pderiv 0).pderiv 0) 1
    rw [h010] at e2
    have e6 : ∫ x, pderiv 1 (pderiv 1 φ) x * pderiv 0 (pderiv 0 φ) x =
        ∫ x, pderiv 0 (pderiv 0 φ) x * pderiv 1 (pderiv 1 φ) x := by
      congr 1; ext x; ring
    linarith
  have hsq : ∀ i j, Integrable (fun x => pderiv i (pderiv j φ) x ^ 2) := fun i j =>
    ((hφ.pderiv j).pderiv i).integrable_sq
  have hm := hc ((hφ.pderiv 0).pderiv 0) ((hφ.pderiv 1).pderiv 1)
  simp only [Fin.sum_univ_two]
  have h10 : ∫ x, pderiv 1 (pderiv 0 φ) x ^ 2 = ∫ x, pderiv 0 (pderiv 1 φ) x ^ 2 := by
    congr 1; ext x; rw [h01]
  rw [h10, key]
  have hl : ∫ x, laplacian φ x ^ 2 = ∫ x, (pderiv 0 (pderiv 0 φ) x ^ 2 +
      pderiv 1 (pderiv 1 φ) x ^ 2 + 2 * (pderiv 0 (pderiv 0 φ) x * pderiv 1 (pderiv 1 φ) x)) := by
    congr 1; ext x; simp only [laplacian]; ring
  have hI : ∫ x, (pderiv 0 (pderiv 0 φ) x ^ 2 + pderiv 1 (pderiv 1 φ) x ^ 2 +
      2 * (pderiv 0 (pderiv 0 φ) x * pderiv 1 (pderiv 1 φ) x)) =
      (∫ x, pderiv 0 (pderiv 0 φ) x ^ 2) + (∫ x, pderiv 1 (pderiv 1 φ) x ^ 2) +
        2 * ∫ x, pderiv 0 (pderiv 0 φ) x * pderiv 1 (pderiv 1 φ) x := by
    rw [integral_add (f := fun x => pderiv 0 (pderiv 0 φ) x ^ 2 + pderiv 1 (pderiv 1 φ) x ^ 2)
      (g := fun x => 2 * (pderiv 0 (pderiv 0 φ) x * pderiv 1 (pderiv 1 φ) x))
      ((hsq 0 0).add (hsq 1 1)) (hm.const_mul 2),
      integral_add (hsq 0 0) (hsq 1 1), integral_const_mul]
  rw [hl, hI]
  ring

end Buckling
end
end ChunkedSource048
/- END SOURCE 048 -/

/- BEGIN SOURCE 049: RequestProject/Functional/Reduction.lean -/
section ChunkedSource049

/-!
# Section 9: from one-variable profile facts to the functional inequality

The functional inequality (Theorem 9.21) is derived here from the properties of the
parity-extended one-variable profiles `f, b, G` established in Sections 4–8 and Lemmas 9.1,
9.3 of the paper.  These properties are collected in `ProfileFacts`:

* regularity: `f, b ∈ C¹(ℝ)`, `G` Lipschitz and differentiable off `0` (Lemma 9.3);
* boundedness of `f', f - s f', b', b - s b', G, s G'` (Lemmas 9.1 and 9.3);
* the asymptotics `f(s)/s → ±ℓ` and `b(s)/s → 2λℓ` as `s → ±∞` (Lemma 9.1);
* the matrix positivity `M(s) ⪰ 0` and `2K - g² - d ≥ 0` for `s ≠ 0` (Lemma 9.3).

The reduction (Lemmas 9.5–9.20) is the content of this file.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

/-! ### The profile data -/

/-- The calibration quadratic form `(X,Y,P) M(s) (X,Y,P)ᵀ` built from the profiles at `s`
(Definition 4.10 with `s` in place of `t`). -/
noncomputable def calibAt (s X Y P : ℝ) : ℝ :=
  calibForm (pK - (fExt s - s * deriv fExt s) ^ 2) (2 * GExt s - s * deriv GExt s) pK
    (2 * bExt s - s * deriv bExt s - 2 * deriv fExt s * (fExt s - s * deriv fExt s))
    (bExt s + deriv GExt s) (-pK - deriv fExt s ^ 2 + pLam * fExt s ^ 2 + deriv bExt s) X Y P

/-- The coupling coefficient `2K - g(s)² - d(s)`. -/
noncomputable def couplingAt (s : ℝ) : ℝ :=
  2 * pK - (fExt s - s * deriv fExt s) ^ 2 - (2 * GExt s - s * deriv GExt s)

/-- The properties of the one-variable profiles used in Section 9 (outputs of Sections 4–8 and
of Lemmas 9.1, 9.3). -/
structure ProfileFacts : Prop where
  f_c1 : ContDiff ℝ 1 fExt
  b_c1 : ContDiff ℝ 1 bExt
  G_lip : ∃ L, LipschitzWith L GExt
  G_diff : ∀ s, s ≠ 0 → DifferentiableAt ℝ GExt s
  f_bdd : ∃ C, ∀ s, |deriv fExt s| ≤ C ∧ |fExt s - s * deriv fExt s| ≤ C
  b_bdd : ∃ C, ∀ s, |deriv bExt s| ≤ C ∧ |bExt s - s * deriv bExt s| ≤ C
  G_bdd : ∃ C, ∀ s, |GExt s| ≤ C ∧ |s * deriv GExt s| ≤ C
  f_atTop : Tendsto (fun s => fExt s / s) atTop (𝓝 pEll)
  f_atBot : Tendsto (fun s => fExt s / s) atBot (𝓝 (-pEll))
  b_atTop : Tendsto (fun s => bExt s / s) atTop (𝓝 (2 * pLam * pEll))
  b_atBot : Tendsto (fun s => bExt s / s) atBot (𝓝 (2 * pLam * pEll))
  matrix_pos : ∀ s, s ≠ 0 → ∀ X Y P, 0 ≤ calibAt s X Y P
  coupling_pos : ∀ s, s ≠ 0 → 0 ≤ couplingAt s

/-! ### Lipschitz perspectives (Lemmas 9.4–9.8) -/

/-- **Lemma 9.5/9.7.**  `𝓕` is Lipschitz on `ℝ × [0, ∞)`. -/
lemma perspF_lipschitz (hP : ProfileFacts) : ∃ L : ℝ, ∀ A A' P P' : ℝ, 0 ≤ P → 0 ≤ P' →
    |perspF A P - perspF A' P'| ≤ L * (|A - A'| + |P - P'|) := by
  obtain ⟨C, hC⟩ := hP.f_bdd
  have hd : Differentiable ℝ fExt := hP.f_c1.differentiable (by norm_num)
  have hlim : ∀ A, Tendsto (fun t => t * fExt (A / t)) (𝓝[>] 0) (𝓝 (pEll * |A|)) := by
    intro A
    convert persp_boundary_limit hP.f_atTop hP.f_atBot A using 2
    rcases lt_trichotomy A 0 with hA | rfl | hA
    · simp [hA, not_lt.mpr hA.le, abs_of_neg hA]
    · simp
    · simp [hA, abs_of_pos hA]
  exact ⟨C, persp_lipschitz hd (fun s => (hC s).1) (fun s => (hC s).2) _ hlim⟩

/-- **Lemma 9.5/9.7.**  `𝓑` is Lipschitz on `ℝ × [0, ∞)`. -/
lemma perspB_lipschitz (hP : ProfileFacts) : ∃ L : ℝ, ∀ A A' P P' : ℝ, 0 ≤ P → 0 ≤ P' →
    |perspB A P - perspB A' P'| ≤ L * (|A - A'| + |P - P'|) := by
  obtain ⟨C, hC⟩ := hP.b_bdd
  have hd : Differentiable ℝ bExt := hP.b_c1.differentiable (by norm_num)
  have hlim : ∀ A, Tendsto (fun t => t * bExt (A / t)) (𝓝[>] 0) (𝓝 (2 * pLam * pEll * A)) := by
    intro A
    convert persp_boundary_limit hP.b_atTop hP.b_atBot A using 2
    rcases lt_trichotomy A 0 with hA | rfl | hA
    · simp [hA, not_lt.mpr hA.le]
    · simp
    · simp [hA]
  exact ⟨C, persp_lipschitz hd (fun s => (hC s).1) (fun s => (hC s).2) _ hlim⟩

/-- **Lemma 9.9.**  `Ψ` is Lipschitz. -/
lemma perspPsi_lipschitz (hP : ProfileFacts) : ∃ L : ℝ, ∀ (A A' : ℝ) (ξ ξ' : Plane),
    ‖perspPsi A ξ - perspPsi A' ξ'‖ ≤ L * (|A - A'| + ‖ξ - ξ'‖) := by
  obtain ⟨L, hL⟩ := hP.G_lip
  obtain ⟨C, hC⟩ := hP.G_bdd
  have hGL : ∀ s t, |GExt s - GExt t| ≤ L * |s - t| := fun s t => by
    simpa [Real.dist_eq] using hL.dist_le_mul s t
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0).1
  refine ⟨L + 2 * C, fun A A' ξ ξ' => ?_⟩
  have := vpersp_lipschitz (E := Plane) hGL (by simp [GExt]) hP.G_diff (fun s => (hC s).1)
    (fun s => (hC s).2) A A' ξ ξ'
  unfold perspPsi
  calc _ ≤ L * |A - A'| + 2 * C * ‖ξ - ξ'‖ := by convert this
    _ ≤ (L + 2 * C) * (|A - A'| + ‖ξ - ξ'‖) := by
      have h0 : (0:ℝ) ≤ L := L.2
      have h1 := mul_nonneg h0 (norm_nonneg (ξ - ξ'))
      have h2 := mul_nonneg (mul_nonneg zero_le_two hC0) (abs_nonneg (A - A'))
      nlinarith

/-! ### The fluxes (Definition 9.13) -/

/-- The gradient vector `∇U`. -/
noncomputable abbrev gradU (U : Plane → ℝ) (x : Plane) : Plane := gradient U x

/-- The flux `V₁ = 𝓑(U, |∇U|) ∇U`, component `i`. -/
noncomputable def fluxV1 (U : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  perspB (U x) ‖fderiv ℝ U x‖ * pderiv i U x

/-- The flux `V₂ = cof(D²U) Ψ(U, ∇U)`, component `i`. -/
noncomputable def fluxV2 (U : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  if i = 0 then
    pderiv 1 (pderiv 1 U) x * (perspPsi (U x) (gradU U x)) 0 -
      pderiv 0 (pderiv 1 U) x * (perspPsi (U x) (gradU U x)) 1
  else
    -pderiv 0 (pderiv 1 U) x * (perspPsi (U x) (gradU U x)) 0 +
      pderiv 0 (pderiv 0 U) x * (perspPsi (U x) (gradU U x)) 1

/-- The divergence of a planar vector field given by components. -/
noncomputable def divergence2 (V : Fin 2 → Plane → ℝ) (x : Plane) : ℝ :=
  pderiv 0 (V 0) x + pderiv 1 (V 1) x

/-- `|D²U|²`. -/
noncomputable def hessSq (U : Plane → ℝ) (x : Plane) : ℝ :=
  pderiv 0 (pderiv 0 U) x ^ 2 + 2 * pderiv 0 (pderiv 1 U) x ^ 2 + pderiv 1 (pderiv 1 U) x ^ 2

/-- The pointwise density of Lemma 9.18. -/
noncomputable def densityFn (U : Plane → ℝ) (x : Plane) : ℝ :=
  pK * (hessSq U x - ‖fderiv ℝ U x‖ ^ 2) -
    (‖fderiv ℝ (transformF U) x‖ ^ 2 - pLam * transformF U x ^ 2) +
    divergence2 (fluxV1 U) x + divergence2 (fluxV2 U) x

lemma lipschitz_gradient {U : Plane → ℝ} (hU : IsTestFn univ U) :
    ∃ L, LipschitzWith L (gradU U) := by
  obtain ⟨L, hL⟩ := hU.lipschitz_fderiv
  exact ⟨_, (InnerProductSpace.toDual ℝ Plane).symm.lipschitz.comp hL⟩

lemma norm_gradU {U : Plane → ℝ} (x : Plane) : ‖gradU U x‖ = ‖fderiv ℝ U x‖ := by
  simp [gradU, gradient]

lemma perspB_comp_lip_bdd (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) :
    (∃ L, LipschitzWith L (fun x => perspB (U x) ‖fderiv ℝ U x‖)) ∧
      ∃ C, ∀ x, |perspB (U x) ‖fderiv ℝ U x‖| ≤ C := by
  obtain ⟨Lp, hΦ⟩ := perspB_lipschitz hP
  obtain ⟨LU, hLU⟩ := hU.lipschitz
  obtain ⟨LD, hLD⟩ := hU.lipschitz_fderiv
  obtain ⟨CU, hCU⟩ := hU.bdd
  obtain ⟨CD, hCD⟩ := hU.bdd_fderiv
  refine ⟨lipschitz_persp_comp hΦ hLU (lipschitzWith_one_norm.comp hLD) (fun x => norm_nonneg _),
    Lp * (CU + CD), fun x => ?_⟩
  have h := hΦ (U x) 0 ‖fderiv ℝ U x‖ 0 (norm_nonneg _) le_rfl
  have h0 : perspB 0 0 = 0 := by simp [perspB]
  rw [h0, sub_zero, sub_zero, sub_zero, abs_norm] at h
  have hL : 0 ≤ Lp := by
    have := hΦ 1 0 0 0 le_rfl le_rfl
    simp at this
    nlinarith [abs_nonneg (perspB 1 0 - perspB 0 0)]
  exact h.trans (by gcongr; exacts [hCU x, hCD x])

lemma perspPsi_comp_lip_bdd (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U)
    (k : Fin 2) :
    (∃ L, LipschitzWith L (fun x => perspPsi (U x) (gradU U x) k)) ∧
      ∃ C, ∀ x, |perspPsi (U x) (gradU U x) k| ≤ C := by
  obtain ⟨Lp, hΦ⟩ := perspPsi_lipschitz hP
  obtain ⟨LU, hLU⟩ := hU.lipschitz
  obtain ⟨LD, hLD⟩ := lipschitz_gradient hU
  obtain ⟨CU, hCU⟩ := hU.bdd
  obtain ⟨CD, hCD⟩ := hU.bdd_fderiv
  have hL : 0 ≤ Lp := by
    have := hΦ 1 0 0 0
    simp at this
    nlinarith [norm_nonneg (perspPsi 1 0 - perspPsi 0 0)]
  have hcomp : ∀ ξ ξ' : Plane, |ξ k - ξ' k| ≤ ‖ξ - ξ'‖ := fun ξ ξ' => by
    have := PiLp.norm_apply_le (ξ - ξ') k
    simpa using this
  refine ⟨⟨_, LipschitzWith.of_dist_le' (K := Lp * (LU + LD)) fun x y => ?_⟩,
    Lp * (CU + CD), fun x => ?_⟩
  · have h1 := hLU.dist_le_mul x y
    have h2 := hLD.dist_le_mul x y
    rw [Real.dist_eq] at h1 ⊢
    rw [dist_eq_norm] at h2
    calc |perspPsi (U x) (gradU U x) k - perspPsi (U y) (gradU U y) k|
        ≤ ‖perspPsi (U x) (gradU U x) - perspPsi (U y) (gradU U y)‖ := hcomp _ _
      _ ≤ Lp * (|U x - U y| + ‖gradU U x - gradU U y‖) := hΦ _ _ _ _
      _ ≤ Lp * (LU * dist x y + LD * dist x y) := by gcongr
      _ = _ := by ring
  · have h := hΦ (U x) 0 (gradU U x) 0
    have h0 : perspPsi 0 0 = 0 := by simp [perspPsi]
    rw [h0, sub_zero, sub_zero, sub_zero, norm_gradU] at h
    have := hcomp (perspPsi (U x) (gradU U x)) 0
    simp only [PiLp.zero_apply, sub_zero] at this
    exact this.trans (h.trans (by gcongr; exacts [hCU x, hCD x]))

/-- **Lemma 9.14 (regularity and support).** -/
lemma transformF_lipschitz (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) :
    ∃ L, LipschitzWith L (transformF U) := by
  obtain ⟨Lp, hΦ⟩ := perspF_lipschitz hP
  obtain ⟨LU, hLU⟩ := hU.lipschitz
  obtain ⟨LD, hLD⟩ := hU.lipschitz_fderiv
  exact lipschitz_persp_comp hΦ hLU (lipschitzWith_one_norm.comp hLD) (fun x => norm_nonneg _)

lemma fluxV1_lipschitz (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) (i : Fin 2) :
    ∃ L, LipschitzWith L (fluxV1 U i) :=
  (lip_bdd_mul (perspB_comp_lip_bdd hP hU) (hU.pderiv i).lip_bdd).1

lemma fluxV2_lipschitz (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) (i : Fin 2) :
    ∃ L, LipschitzWith L (fluxV2 U i) := by
  have hh : ∀ a b, (∃ L, LipschitzWith L (fun x => pderiv a (pderiv b U) x *
      perspPsi (U x) (gradU U x) 0)) ∧ (∃ L, LipschitzWith L (fun x => pderiv a (pderiv b U) x *
      perspPsi (U x) (gradU U x) 1)) := fun a b =>
    ⟨(lip_bdd_mul ((hU.pderiv b).pderiv a).lip_bdd (perspPsi_comp_lip_bdd hP hU 0)).1,
     (lip_bdd_mul ((hU.pderiv b).pderiv a).lip_bdd (perspPsi_comp_lip_bdd hP hU 1)).1⟩
  fin_cases i
  · obtain ⟨L1, h1⟩ := (hh 1 1).1
    obtain ⟨L2, h2⟩ := (hh 0 1).2
    refine ⟨L1 + L2, ?_⟩
    convert h1.sub h2 using 1
    ext x
    simp [fluxV2]
  · obtain ⟨L1, h1⟩ := (hh 0 0).2
    obtain ⟨L2, h2⟩ := (hh 0 1).1
    refine ⟨L1 + L2, ?_⟩
    convert h1.sub h2 using 1
    ext x; simp [fluxV2]; ring

lemma tsupport_transformF_subset {U : Plane → ℝ} :
    tsupport (transformF U) ⊆ tsupport U := by
  refine tsupport_subset_of_vanish fun x hx => ?_
  simp [transformF, fderiv_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx,
    perspF_zero_zero]

lemma tsupport_fluxV1_subset {U : Plane → ℝ} (i : Fin 2) :
    tsupport (fluxV1 U i) ⊆ tsupport U := by
  refine tsupport_subset_of_vanish fun x hx => ?_
  simp [fluxV1, pderiv_eq_zero_of_notMem hx]

lemma tsupport_fluxV2_subset {U : Plane → ℝ} (i : Fin 2) :
    tsupport (fluxV2 U i) ⊆ tsupport U := by
  refine tsupport_subset_of_vanish fun x hx => ?_
  simp [fluxV2, pderiv2_eq_zero_of_notMem hx]

/-! ### Integral identities (Lemma 9.19) -/

/-- The integral of a partial derivative of a compactly supported Lipschitz function vanishes. -/
lemma integral_pderiv_lipschitz_eq_zero {V : Plane → ℝ} {L : NNReal} (hV : LipschitzWith L V)
    (hc : HasCompactSupport V) (i : Fin 2) : ∫ x, pderiv i V x = 0 := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_ball (0 : Plane)
  let R' := max R 1
  have hR' : tsupport V ⊆ ball 0 R' := hR.trans (ball_subset_ball (le_max_left _ _))
  let b : ContDiffBump (0 : Plane) := ⟨R', R' + 1, by positivity, by linarith⟩
  have hψ : IsTestFn univ b := ⟨b.contDiff, b.hasCompactSupport, subset_univ _⟩
  have key := lipschitz_hasWeakGradient hV b hψ i
  have h1 : ∀ x, V x * pderiv i b x = 0 := by
    intro x
    by_cases hx : x ∈ ball (0 : Plane) R'
    · have : (b : Plane → ℝ) =ᶠ[𝓝 x] fun _ => 1 := by
        filter_upwards [isOpen_ball.mem_nhds hx] with y hy
        exact b.one_of_mem_closedBall (ball_subset_closedBall hy)
      simp [pderiv, this.fderiv_eq]
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hx (hR' h))]
  have h2 : ∀ x, fderiv ℝ V x (EuclideanSpace.single i 1) * b x = pderiv i V x := by
    intro x
    by_cases hx : x ∈ ball (0 : Plane) R'
    · rw [b.one_of_mem_closedBall (ball_subset_closedBall hx)]; simp [pderiv]
    · simp [pderiv, fderiv_eq_zero_of_notMem_tsupport (fun h => hx (hR' h))]
  simp only [h1, h2, integral_zero] at key
  linarith

/-- `∫ |D²U|² = ∫ |ΔU|²`. -/
lemma integral_hessSq_eq {U : Plane → ℝ} (hU : IsTestFn univ U) :
    ∫ x, hessSq U x = ∫ x, laplacian U x ^ 2 := by
  have hc : ∀ {g : Plane → ℝ}, IsTestFn univ g → ∀ {h : Plane → ℝ}, IsTestFn univ h →
      Integrable (fun x => g x * h x) := by
    intro g hg h hh
    exact (hg.1.continuous.mul hh.1.continuous).integrable_of_hasCompactSupport
      (hg.2.1.mul_right)
  have h2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have h2' : ContDiff ℝ 2 (pderiv 1 U) := (hU.pderiv 1).1.of_le (WithTop.coe_le_coe.mpr le_top)
  have key : ∫ x, pderiv 1 (pderiv 1 U) x * pderiv 0 (pderiv 0 U) x =
      ∫ x, pderiv 0 (pderiv 1 U) x * pderiv 0 (pderiv 1 U) x := by
    rw [ibp_test ((hU.pderiv 1).pderiv 1) (hU.pderiv 0) 0]
    have e1 : ∀ x, pderiv 0 (pderiv 1 (pderiv 1 U)) x * pderiv 0 U x =
        pderiv 0 U x * pderiv 1 (pderiv 0 (pderiv 1 U)) x := fun x => by
      rw [pderiv_comm h2' 0 1]; ring
    simp only [e1]
    rw [ibp_test (hU.pderiv 0) ((hU.pderiv 1).pderiv 0) 1, neg_neg]
    congr 1; ext x; rw [pderiv_comm h2 1 0]
  have e : ∀ x, hessSq U x = laplacian U x ^ 2 +
      2 * (pderiv 0 (pderiv 1 U) x * pderiv 0 (pderiv 1 U) x) -
      2 * (pderiv 1 (pderiv 1 U) x * pderiv 0 (pderiv 0 U) x) := fun x => by
    unfold hessSq laplacian; ring
  have i1 : Integrable fun x => laplacian U x ^ 2 := by
    have := ((hc ((hU.pderiv 0).pderiv 0) ((hU.pderiv 0).pderiv 0)).add
      ((hc ((hU.pderiv 0).pderiv 0) ((hU.pderiv 1).pderiv 1)).const_mul 2)).add
      (hc ((hU.pderiv 1).pderiv 1) ((hU.pderiv 1).pderiv 1))
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [laplacian, Pi.add_apply]; ring
  have i2 := (hc ((hU.pderiv 1).pderiv 0) ((hU.pderiv 1).pderiv 0)).const_mul 2
  have i3 := (hc ((hU.pderiv 1).pderiv 1) ((hU.pderiv 0).pderiv 0)).const_mul 2
  simp only [e]
  rw [integral_sub (f := fun x => laplacian U x ^ 2 +
      2 * (pderiv 0 (pderiv 1 U) x * pderiv 0 (pderiv 1 U) x)) (i1.add i2) i3, integral_add i1 i2, integral_const_mul, integral_const_mul, key]
  ring

/-- All terms of the density are integrable. -/
lemma densityFn_integrable (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) :
    Integrable (hessSq U) ∧ Integrable (fun x => ‖fderiv ℝ U x‖ ^ 2) ∧
      Integrable (fun x => ‖fderiv ℝ (transformF U) x‖ ^ 2) ∧
      Integrable (fun x => transformF U x ^ 2) ∧
      Integrable (divergence2 (fluxV1 U)) ∧ Integrable (divergence2 (fluxV2 U)) := by
  have hcU : ∀ {V : Plane → ℝ}, tsupport V ⊆ tsupport U → HasCompactSupport V := fun h =>
    IsCompact.of_isClosed_subset hU.2.1 (isClosed_tsupport _) h
  obtain ⟨LF, hLF⟩ := transformF_lipschitz hP hU
  have hcF : HasCompactSupport (transformF U) := hcU tsupport_transformF_subset
  refine ⟨?_, ?_, integrable_norm_fderiv_sq_of_lipschitz hLF hcF, ?_, ?_, ?_⟩
  · refine hU.integrable_cont ?_ (fun x hx => by simp [hessSq, pderiv2_eq_zero_of_notMem hx])
    unfold hessSq
    exact ((((hU.pderiv 0).pderiv 0).1.continuous.pow 2).add
      (continuous_const.mul (((hU.pderiv 1).pderiv 0).1.continuous.pow 2))).add
      (((hU.pderiv 1).pderiv 1).1.continuous.pow 2)
  · refine hU.integrable_cont ?_ (fun x hx => by simp [fderiv_eq_zero_of_notMem_tsupport hx])
    exact ((hU.1.continuous_fderiv (by simp)).norm.pow 2)
  · have hcSq : HasCompactSupport (fun x => transformF U x ^ 2) :=
      hcF.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
    exact (hLF.continuous.fun_pow 2).integrable_of_hasCompactSupport hcSq
  · obtain ⟨L0, h0⟩ := fluxV1_lipschitz hP hU 0
    obtain ⟨L1, h1⟩ := fluxV1_lipschitz hP hU 1
    exact (integrable_pderiv_of_lipschitz h0 (hcU (tsupport_fluxV1_subset 0)) 0).add
      (integrable_pderiv_of_lipschitz h1 (hcU (tsupport_fluxV1_subset 1)) 1)
  · obtain ⟨L0, h0⟩ := fluxV2_lipschitz hP hU 0
    obtain ⟨L1, h1⟩ := fluxV2_lipschitz hP hU 1
    exact (integrable_pderiv_of_lipschitz h0 (hcU (tsupport_fluxV2_subset 0)) 0).add
      (integrable_pderiv_of_lipschitz h1 (hcU (tsupport_fluxV2_subset 1)) 1)

end Buckling
end
end ChunkedSource049
/- END SOURCE 049 -/

/- BEGIN SOURCE 050: RequestProject/Functional/Density.lean -/
section ChunkedSource050

/-!
# The pointwise density at regular points (Lemmas 9.15–9.18 of the paper)

Partial-derivative calculus for the transformed function and the fluxes on the open set
`{|∇U| > 0, U ≠ 0}`, and the identification of the density there with the calibration form
plus the coupling term.
-/

@[expose] public section
open MeasureTheory Real Set Filter Topology Metric
namespace Buckling

lemma pderiv_congr {f g : Plane → ℝ} {x : Plane} (h : f =ᶠ[𝓝 x] g) (i : Fin 2) :
    pderiv i f x = pderiv i g x := by
  simp [pderiv, h.fderiv_eq]

lemma pderiv_mul' {f g : Plane → ℝ} {x : Plane} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pderiv i (fun y => f y * g y) x = pderiv i f x * g x + f x * pderiv i g x := by
  show fderiv ℝ (fun y => f y * g y) x _ = _
  rw [show (fun y => f y * g y) = f * g from rfl, (hf.hasFDerivAt.mul hg.hasFDerivAt).fderiv]
  simp [pderiv]; ring

lemma pderiv_comp' {φ : ℝ → ℝ} {g : Plane → ℝ} {x : Plane} (hφ : DifferentiableAt ℝ φ (g x))
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pderiv i (fun y => φ (g y)) x = deriv φ (g x) * pderiv i g x := by
  have := (hφ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt).fderiv
  simp only [pderiv]
  rw [show (fun y => φ (g y)) = φ ∘ g from rfl, this]
  simp

lemma pderiv_div' {f g : Plane → ℝ} {x : Plane} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hg0 : g x ≠ 0) (i : Fin 2) :
    pderiv i (fun y => f y / g y) x =
      (pderiv i f x * g x - f x * pderiv i g x) / g x ^ 2 := by
  have h1 : pderiv i (fun y => f y * (g y)⁻¹) x =
      pderiv i f x * (g x)⁻¹ + f x * pderiv i (fun y => (g y)⁻¹) x :=
    pderiv_mul' hf (hg.inv hg0) i
  have h2 : pderiv i (fun y => (g y)⁻¹) x = deriv (fun t : ℝ => t⁻¹) (g x) * pderiv i g x :=
    pderiv_comp' (φ := fun t : ℝ => t⁻¹) (differentiableAt_inv hg0) hg i
  simp only [div_eq_mul_inv]
  rw [h1, h2, deriv_inv]
  field_simp
  ring

lemma pderiv_sqrt' {g : Plane → ℝ} {x : Plane} (hg : DifferentiableAt ℝ g x) (hg0 : 0 < g x)
    (i : Fin 2) :
    pderiv i (fun y => Real.sqrt (g y)) x = pderiv i g x / (2 * Real.sqrt (g x)) := by
  have hs := Real.hasDerivAt_sqrt hg0.ne'
  rw [pderiv_comp' (φ := Real.sqrt) hs.differentiableAt hg i, hs.deriv]
  ring

lemma pderiv_add' {f g : Plane → ℝ} {x : Plane} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pderiv i (fun y => f y + g y) x = pderiv i f x + pderiv i g x := by
  show fderiv ℝ (fun y => f y + g y) x _ = _
  rw [show (fun y => f y + g y) = f + g from rfl, (hf.hasFDerivAt.add hg.hasFDerivAt).fderiv]
  simp [pderiv]

lemma pderiv_sub' {f g : Plane → ℝ} {x : Plane} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pderiv i (fun y => f y - g y) x = pderiv i f x - pderiv i g x := by
  show fderiv ℝ (fun y => f y - g y) x _ = _
  rw [show (fun y => f y - g y) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  simp [pderiv]

/-- `P = |∇U|` written through the partial derivatives. -/
noncomputable def gradNorm (U : Plane → ℝ) (y : Plane) : ℝ :=
  Real.sqrt (pderiv 0 U y ^ 2 + pderiv 1 U y ^ 2)

lemma norm_fderiv_eq_gradNorm (U : Plane → ℝ) (y : Plane) : ‖fderiv ℝ U y‖ = gradNorm U y := by
  rw [gradNorm, sum_pderiv_sq, Real.sqrt_sq (norm_nonneg _)]

lemma gradU_apply (U : Plane → ℝ) (y : Plane) (k : Fin 2) : gradU U y k = pderiv k U y := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := Plane) (x := EuclideanSpace.single k 1)
    (y := fderiv ℝ U y)
  simp only [EuclideanSpace.inner_single_right, one_mul] at this
  simp only [gradU, gradient]
  rw [show pderiv k U y = fderiv ℝ U y (EuclideanSpace.single k 1) from rfl, ← this]
  simp

lemma perspPsi_apply_of_pos {U : Plane → ℝ} {y : Plane} (hy : 0 < gradNorm U y) (k : Fin 2) :
    perspPsi (U y) (gradU U y) k = GExt (U y / gradNorm U y) * pderiv k U y := by
  have hn : ‖gradU U y‖ = gradNorm U y := by rw [norm_gradU, norm_fderiv_eq_gradNorm]
  have h0 : gradU U y ≠ 0 := fun h => by rw [h, norm_zero] at hn; linarith
  simp only [perspPsi, h0, if_false, hn, PiLp.smul_apply, smul_eq_mul, gradU_apply]

lemma pderiv_sq' {g : Plane → ℝ} {x : Plane} (hg : DifferentiableAt ℝ g x) (i : Fin 2) :
    pderiv i (fun y => g y ^ 2) x = 2 * g x * pderiv i g x := by
  rw [pderiv_comp' (φ := fun t : ℝ => t ^ 2) (differentiableAt_pow 2) hg i]
  simp

lemma gradNorm_continuous {U : Plane → ℝ} (hU : IsTestFn univ U) : Continuous (gradNorm U) := by
  unfold gradNorm
  exact (((hU.pderiv 0).1.continuous.pow 2).add ((hU.pderiv 1).1.continuous.pow 2)).sqrt

lemma gradNorm_sq (U : Plane → ℝ) (y : Plane) :
    gradNorm U y ^ 2 = pderiv 0 U y ^ 2 + pderiv 1 U y ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- Partial derivatives of `P = |∇U|` where `P > 0`. -/
lemma pderiv_gradNorm {U : Plane → ℝ} (hU : IsTestFn univ U) {x : Plane} (hx : 0 < gradNorm U x)
    (i : Fin 2) :
    pderiv i (gradNorm U) x = (pderiv 0 U x * pderiv i (pderiv 0 U) x +
      pderiv 1 U x * pderiv i (pderiv 1 U) x) / gradNorm U x := by
  have d0 : DifferentiableAt ℝ (pderiv 0 U) x := ((hU.pderiv 0).1.differentiable (by simp)) x
  have d1 : DifferentiableAt ℝ (pderiv 1 U) x := ((hU.pderiv 1).1.differentiable (by simp)) x
  have hQ : 0 < pderiv 0 U x ^ 2 + pderiv 1 U x ^ 2 := by rw [← gradNorm_sq]; positivity
  have hd : DifferentiableAt ℝ (fun y => pderiv 0 U y ^ 2 + pderiv 1 U y ^ 2) x :=
    (d0.pow 2).add (d1.pow 2)
  show pderiv i (fun y => Real.sqrt (pderiv 0 U y ^ 2 + pderiv 1 U y ^ 2)) x = _
  rw [pderiv_sqrt' hd hQ, pderiv_add' (f := fun y => pderiv 0 U y ^ 2)
    (g := fun y => pderiv 1 U y ^ 2) (d0.pow 2) (d1.pow 2), pderiv_sq' d0, pderiv_sq' d1]
  unfold gradNorm
  field_simp

lemma gradNorm_differentiableAt {U : Plane → ℝ} (hU : IsTestFn univ U) {x : Plane}
    (hx : 0 < gradNorm U x) : DifferentiableAt ℝ (gradNorm U) x := by
  have d0 : DifferentiableAt ℝ (pderiv 0 U) x := ((hU.pderiv 0).1.differentiable (by simp)) x
  have d1 : DifferentiableAt ℝ (pderiv 1 U) x := ((hU.pderiv 1).1.differentiable (by simp)) x
  have hQ : 0 < pderiv 0 U x ^ 2 + pderiv 1 U x ^ 2 := by rw [← gradNorm_sq]; positivity
  exact ((d0.pow 2).add (d1.pow 2)).sqrt hQ.ne'

attribute [local irreducible] gradNorm in
/-- **Lemmas 9.17–9.18 at a regular point.**  Where `P = |∇U| > 0` and `U ≠ 0`, the density
equals the calibration form plus the coupling term, in the local frame `e₁ = ∇U/P`. -/
lemma densityFn_eq_frame (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) {x : Plane}
    (hx : 0 < gradNorm U x) (hu : U x ≠ 0) :
    densityFn U x = calibAt (U x / gradNorm U x)
        ((pderiv 0 U x / gradNorm U x) ^ 2 * pderiv 0 (pderiv 0 U) x +
          2 * (pderiv 0 U x / gradNorm U x) * (pderiv 1 U x / gradNorm U x) *
            pderiv 0 (pderiv 1 U) x +
          (pderiv 1 U x / gradNorm U x) ^ 2 * pderiv 1 (pderiv 1 U) x)
        ((pderiv 1 U x / gradNorm U x) ^ 2 * pderiv 0 (pderiv 0 U) x -
          2 * (pderiv 0 U x / gradNorm U x) * (pderiv 1 U x / gradNorm U x) *
            pderiv 0 (pderiv 1 U) x +
          (pderiv 0 U x / gradNorm U x) ^ 2 * pderiv 1 (pderiv 1 U) x) (gradNorm U x) +
      couplingAt (U x / gradNorm U x) *
        (-(pderiv 0 U x / gradNorm U x) * (pderiv 1 U x / gradNorm U x) *
            pderiv 0 (pderiv 0 U) x +
          ((pderiv 0 U x / gradNorm U x) ^ 2 - (pderiv 1 U x / gradNorm U x) ^ 2) *
            pderiv 0 (pderiv 1 U) x +
          (pderiv 0 U x / gradNorm U x) * (pderiv 1 U x / gradNorm U x) *
            pderiv 1 (pderiv 1 U) x) ^ 2 := by
  -- smoothness
  have dU : ∀ y, DifferentiableAt ℝ U y := fun y => (hU.1.differentiable (by simp)) y
  have dp : ∀ j y, DifferentiableAt ℝ (pderiv j U) y := fun j y =>
    ((hU.pderiv j).1.differentiable (by simp)) y
  have dh : ∀ i j y, DifferentiableAt ℝ (pderiv i (pderiv j U)) y := fun i j y =>
    (((hU.pderiv j).pderiv i).1.differentiable (by simp)) y
  have hC2 : ContDiff ℝ 2 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hC2' : ∀ j, ContDiff ℝ 2 (pderiv j U) := fun j =>
    (hU.pderiv j).1.of_le (WithTop.coe_le_coe.mpr le_top)
  have h10 : pderiv 1 (pderiv 0 U) x = pderiv 0 (pderiv 1 U) x := pderiv_comm hC2 1 0 x
  have h3a : pderiv 0 (pderiv 1 (pderiv 1 U)) x = pderiv 1 (pderiv 0 (pderiv 1 U)) x :=
    pderiv_comm (hC2' 1) 0 1 x
  have h3b : pderiv 1 (pderiv 0 (pderiv 0 U)) x = pderiv 0 (pderiv 0 (pderiv 1 U)) x := by
    rw [pderiv_comm (hC2' 0) 1 0 x]
    have : pderiv 1 (pderiv 0 U) = pderiv 0 (pderiv 1 U) := funext fun y => pderiv_comm hC2 1 0 y
    rw [this]
  have dP := gradNorm_differentiableAt hU hx
  set P := gradNorm U x with hPdef
  set s := U x / P with hsdef
  have hs0 : s ≠ 0 := div_ne_zero hu hx.ne'
  have ds : DifferentiableAt ℝ (fun y => U y / gradNorm U y) x :=
    by simpa only [div_eq_mul_inv] using! (dU x).mul (dP.inv hx.ne')
  have df : Differentiable ℝ fExt := hP.f_c1.differentiable (by norm_num)
  have db : Differentiable ℝ bExt := hP.b_c1.differentiable (by norm_num)
  have dG : DifferentiableAt ℝ GExt s := hP.G_diff s hs0
  have dGs : DifferentiableAt ℝ (fun y => GExt (U y / gradNorm U y)) x := DifferentiableAt.comp (g := GExt) x dG ds
  have dfs : DifferentiableAt ℝ (fun y => fExt (U y / gradNorm U y)) x := (df _).comp x ds
  have dbs : DifferentiableAt ℝ (fun y => bExt (U y / gradNorm U y)) x := (db _).comp x ds
  have hev : ∀ᶠ y in 𝓝 x, 0 < gradNorm U y :=
    (gradNorm_continuous hU).continuousAt.eventually (lt_mem_nhds hx)
  have hds : ∀ i, pderiv i (fun y => U y / gradNorm U y) x =
      (pderiv i U x * P - U x * pderiv i (gradNorm U) x) / P ^ 2 := fun i =>
    pderiv_div' (dU x) dP hx.ne' i
  -- the transformed function
  have hFloc : transformF U =ᶠ[𝓝 x] fun y => gradNorm U y * fExt (U y / gradNorm U y) := by
    filter_upwards [hev] with y hy
    simp [transformF, perspF, norm_fderiv_eq_gradNorm, hy]
  have hF : ∀ i, pderiv i (transformF U) x = pderiv i (gradNorm U) x * fExt s +
      P * (deriv fExt s * pderiv i (fun y => U y / gradNorm U y) x) := by
    intro i
    rw [pderiv_congr hFloc, pderiv_mul' (f := gradNorm U)
      (g := fun y => fExt (U y / gradNorm U y)) dP dfs i, pderiv_comp' (df _) ds i]
  have hFx : transformF U x = P * fExt s := hFloc.self_of_nhds
  -- the first flux
  have hV1 : ∀ i, pderiv i (fluxV1 U i) x = (pderiv i (gradNorm U) x * bExt s +
      P * (deriv bExt s * pderiv i (fun y => U y / gradNorm U y) x)) * pderiv i U x +
      P * bExt s * pderiv i (pderiv i U) x := by
    intro i
    have hloc : fluxV1 U i =ᶠ[𝓝 x] fun y =>
        (gradNorm U y * bExt (U y / gradNorm U y)) * pderiv i U y := by
      filter_upwards [hev] with y hy
      simp [fluxV1, perspB, norm_fderiv_eq_gradNorm, hy]
    rw [pderiv_congr hloc, pderiv_mul' (f := fun y => gradNorm U y * bExt (U y / gradNorm U y))
      (g := pderiv i U) (dP.mul dbs) (dp i x) i, pderiv_mul' (f := gradNorm U)
      (g := fun y => bExt (U y / gradNorm U y)) dP dbs i, pderiv_comp' (db _) ds i]
  -- the second flux
  have hGp : ∀ i j, pderiv i (fun y => GExt (U y / gradNorm U y) * pderiv j U y) x =
      deriv GExt s * pderiv i (fun y => U y / gradNorm U y) x * pderiv j U x +
        GExt s * pderiv i (pderiv j U) x := by
    intro i j
    rw [pderiv_mul' (f := fun y => GExt (U y / gradNorm U y)) (g := pderiv j U) dGs (dp j x) i,
      pderiv_comp' dG ds i]
  have dGp : ∀ j, DifferentiableAt ℝ (fun y => GExt (U y / gradNorm U y) * pderiv j U y) x :=
    fun j => dGs.mul (dp j x)
  have hV20 : pderiv 0 (fluxV2 U 0) x =
      (pderiv 0 (pderiv 1 (pderiv 1 U)) x * (GExt s * pderiv 0 U x) +
        pderiv 1 (pderiv 1 U) x * pderiv 0 (fun y => GExt (U y / gradNorm U y) * pderiv 0 U y) x) -
      (pderiv 0 (pderiv 0 (pderiv 1 U)) x * (GExt s * pderiv 1 U x) +
        pderiv 0 (pderiv 1 U) x * pderiv 0 (fun y => GExt (U y / gradNorm U y) * pderiv 1 U y) x)
      := by
    have hloc : fluxV2 U 0 =ᶠ[𝓝 x] fun y =>
        pderiv 1 (pderiv 1 U) y * (GExt (U y / gradNorm U y) * pderiv 0 U y) -
          pderiv 0 (pderiv 1 U) y * (GExt (U y / gradNorm U y) * pderiv 1 U y) := by
      filter_upwards [hev] with y hy
      simp [fluxV2, perspPsi_apply_of_pos hy]
    rw [pderiv_congr hloc,
      pderiv_sub' (f := fun y => pderiv 1 (pderiv 1 U) y * (GExt (U y / gradNorm U y) * pderiv 0 U y))
        (g := fun y => pderiv 0 (pderiv 1 U) y * (GExt (U y / gradNorm U y) * pderiv 1 U y))
        ((dh 1 1 x).mul (dGp 0)) ((dh 0 1 x).mul (dGp 1)),
      pderiv_mul' (f := pderiv 1 (pderiv 1 U)) (dh 1 1 x) (dGp 0),
      pderiv_mul' (f := pderiv 0 (pderiv 1 U)) (dh 0 1 x) (dGp 1)]
  have hV21 : pderiv 1 (fluxV2 U 1) x =
      (pderiv 1 (pderiv 0 (pderiv 0 U)) x * (GExt s * pderiv 1 U x) +
        pderiv 0 (pderiv 0 U) x * pderiv 1 (fun y => GExt (U y / gradNorm U y) * pderiv 1 U y) x) -
      (pderiv 1 (pderiv 0 (pderiv 1 U)) x * (GExt s * pderiv 0 U x) +
        pderiv 0 (pderiv 1 U) x * pderiv 1 (fun y => GExt (U y / gradNorm U y) * pderiv 0 U y) x)
      := by
    have hloc : fluxV2 U 1 =ᶠ[𝓝 x] fun y =>
        pderiv 0 (pderiv 0 U) y * (GExt (U y / gradNorm U y) * pderiv 1 U y) -
          pderiv 0 (pderiv 1 U) y * (GExt (U y / gradNorm U y) * pderiv 0 U y) := by
      filter_upwards [hev] with y hy
      simp [fluxV2, perspPsi_apply_of_pos hy]; ring
    rw [pderiv_congr hloc,
      pderiv_sub' (f := fun y => pderiv 0 (pderiv 0 U) y * (GExt (U y / gradNorm U y) * pderiv 1 U y))
        (g := fun y => pderiv 0 (pderiv 1 U) y * (GExt (U y / gradNorm U y) * pderiv 0 U y))
        ((dh 0 0 x).mul (dGp 1)) ((dh 0 1 x).mul (dGp 0)),
      pderiv_mul' (f := pderiv 0 (pderiv 0 U)) (dh 0 0 x) (dGp 1),
      pderiv_mul' (f := pderiv 0 (pderiv 1 U)) (dh 0 1 x) (dGp 0)]
  -- frame variables
  set p0 := pderiv 0 U x with hp0
  set p1 := pderiv 1 U x with hp1
  set h11 := pderiv 0 (pderiv 0 U) x with hh11
  set h12 := pderiv 0 (pderiv 1 U) x with hh12
  set h22 := pderiv 1 (pderiv 1 U) x with hh22
  have hPP : P ^ 2 = p0 ^ 2 + p1 ^ 2 := gradNorm_sq U x
  have hP0 : P ≠ 0 := hx.ne'
  have hdP0 : pderiv 0 (gradNorm U) x = (p0 * h11 + p1 * h12) / P := pderiv_gradNorm hU hx 0
  have hdP1 : pderiv 1 (gradNorm U) x = (p0 * h12 + p1 * h22) / P := by
    rw [pderiv_gradNorm hU hx 1, h10]
  have hcd : (p0 / P) ^ 2 + (p1 / P) ^ 2 = 1 := by
    field_simp; linarith [hPP]
  set T := pderiv 0 (pderiv 1 (pderiv 1 U)) x * (GExt s * p0) -
    pderiv 0 (pderiv 0 (pderiv 1 U)) x * (GExt s * p1) with hT
  set T' := pderiv 1 (pderiv 0 (pderiv 0 U)) x * (GExt s * p1) -
    pderiv 1 (pderiv 0 (pderiv 1 U)) x * (GExt s * p0) with hT'
  have hTT : T + T' = 0 := by rw [hT, hT', h3a, h3b]; ring
  have key := density_frame_identity P (p0 / P) (p1 / P) s h11 h12 h22 (fExt s) (deriv fExt s)
    (bExt s) (deriv bExt s) (GExt s) (deriv GExt s) pK pLam (pderiv 0 (transformF U) x)
    (pderiv 1 (transformF U) x) (pderiv 0 (fluxV1 U 0) x) (pderiv 1 (fluxV1 U 1) x)
    (pderiv 0 (fluxV2 U 0) x - T) (pderiv 1 (fluxV2 U 1) x - T') hcd ?_ ?_ ?_ ?_ ?_ ?_
  · simp only [densityFn, divergence2, hessSq, calibAt, couplingAt]
    rw [← sum_pderiv_sq (transformF U) x, norm_fderiv_eq_gradNorm, hFx]
    linear_combination key + hTT
  · rw [hF 0, hds 0, hdP0, hsdef]; field_simp; ring
  · rw [hF 1, hds 1, hdP1, hsdef]; field_simp; ring
  · rw [hV1 0, hds 0, hdP0, hsdef]; field_simp; ring
  · rw [hV1 1, hds 1, hdP1, hsdef]; field_simp; ring
  · rw [hV20, hGp 0 0, hGp 0 1, hds 0, hdP0, hsdef, hT]; field_simp; ring
  · rw [hV21, hGp 1 0, hGp 1 1, hds 1, hdP1, h10, hsdef, hT']; field_simp; ring

end Buckling
end
end ChunkedSource050
/- END SOURCE 050 -/

/- BEGIN SOURCE 051: RequestProject/Functional/Critical.lean -/
section ChunkedSource051

/-!
# The density on the critical set (Lemmas 9.11, 9.12 and 9.14 of the paper)

At a point where `∇U = 0` and `D²U = 0`, the transformed function and the fluxes are
differentiable with zero derivative (Lipschitz composition at a stationary point), so the
density reduces to `λ F² ≥ 0`.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric Asymptotics

namespace Buckling

lemma fderiv_eq_zero_of_pderiv {g : Plane → ℝ} {x : Plane} (h : ∀ i, pderiv i g x = 0) :
    fderiv ℝ g x = 0 := by
  have h2 : ‖fderiv ℝ g x‖ ^ 2 = 0 := by rw [← sum_pderiv_sq, h 0, h 1]; ring
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)

lemma hasFDerivAt_zero_of_pderiv {g : Plane → ℝ} {x : Plane} (hg : DifferentiableAt ℝ g x)
    (h : ∀ i, pderiv i g x = 0) : HasFDerivAt g (0 : Plane →L[ℝ] ℝ) x := by
  have := hg.hasFDerivAt
  rwa [fderiv_eq_zero_of_pderiv h] at this

lemma isLittleO_of_hasFDerivAt_zero {g : Plane → ℝ} {x : Plane}
    (h : HasFDerivAt g (0 : Plane →L[ℝ] ℝ) x) :
    (fun y => g y - g x) =o[𝓝 x] (fun y => y - x) := by
  simpa using h.isLittleO

lemma hasFDerivAt_zero_of_isLittleO {g : Plane → ℝ} {x : Plane}
    (h : (fun y => g y - g x) =o[𝓝 x] (fun y => y - x)) :
    HasFDerivAt g (0 : Plane →L[ℝ] ℝ) x := by
  refine HasFDerivAtFilter.of_isLittleO ?_
  simpa [Function.comp_def] using! h

/-- **Lemma 9.12 (Lipschitz composition at a stationary point)**, in the form used for the
scalar perspectives. -/
lemma isLittleO_persp_comp {Φ : ℝ → ℝ → ℝ} {L : ℝ}
    (hΦ : ∀ A A' P P' : ℝ, 0 ≤ P → 0 ≤ P' → |Φ A P - Φ A' P'| ≤ L * (|A - A'| + |P - P'|))
    {a p : Plane → ℝ} (hp0 : ∀ y, 0 ≤ p y) {x : Plane}
    (ha : (fun y => a y - a x) =o[𝓝 x] (fun y => y - x))
    (hp : (fun y => p y - p x) =o[𝓝 x] (fun y => y - x)) :
    (fun y => Φ (a y) (p y) - Φ (a x) (p x)) =o[𝓝 x] (fun y => y - x) := by
  have hsum : (fun y => |a y - a x| + |p y - p x|) =o[𝓝 x] (fun y => y - x) := by
    have h1 := ha.norm_left
    have h2 := hp.norm_left
    simp only [Real.norm_eq_abs] at h1 h2
    exact h1.add h2
  refine IsBigO.trans_isLittleO ?_ hsum
  refine IsBigO.of_bound L (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |a y - a x| + |p y - p x|)]
  exact hΦ _ _ _ _ (hp0 y) (hp0 x)

lemma gradNorm_le (U : Plane → ℝ) (y : Plane) :
    gradNorm U y ≤ |pderiv 0 U y| + |pderiv 1 U y| := by
  unfold gradNorm
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [abs_nonneg (pderiv 0 U y), abs_nonneg (pderiv 1 U y), sq_abs (pderiv 0 U y),
    sq_abs (pderiv 1 U y), abs_mul_abs_self (pderiv 0 U y)]

lemma pderiv_eq_zero_of_hasFDerivAt {g : Plane → ℝ} {x : Plane}
    (h : HasFDerivAt g (0 : Plane →L[ℝ] ℝ) x) (i : Fin 2) : pderiv i g x = 0 := by
  simp [pderiv, h.fderiv]

/-- **Lemma 9.14, critical-set part.**  At a point where all first and second derivatives of
`U` vanish, the density is `λ F² ≥ 0`. -/
lemma densityFn_nonneg_critical (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U)
    {x : Plane} (h1 : ∀ j, pderiv j U x = 0) (h2 : ∀ i j, pderiv i (pderiv j U) x = 0) :
    0 ≤ densityFn U x := by
  have dU : ∀ y, DifferentiableAt ℝ U y := fun y => (hU.1.differentiable (by simp)) y
  have dp : ∀ j y, DifferentiableAt ℝ (pderiv j U) y := fun j y =>
    ((hU.pderiv j).1.differentiable (by simp)) y
  have dh : ∀ i j y, DifferentiableAt ℝ (pderiv i (pderiv j U)) y := fun i j y =>
    (((hU.pderiv j).pderiv i).1.differentiable (by simp)) y
  have hUo := isLittleO_of_hasFDerivAt_zero (hasFDerivAt_zero_of_pderiv (dU x) h1)
  have hpD : ∀ j, HasFDerivAt (pderiv j U) (0 : Plane →L[ℝ] ℝ) x := fun j =>
    hasFDerivAt_zero_of_pderiv (dp j x) (fun i => h2 i j)
  have hpo : ∀ j, (fun y => pderiv j U y - pderiv j U x) =o[𝓝 x] (fun y => y - x) := fun j =>
    isLittleO_of_hasFDerivAt_zero (hpD j)
  have hP0 : gradNorm U x = 0 := by simp [gradNorm, h1]
  have hPo : (fun y => gradNorm U y - gradNorm U x) =o[𝓝 x] (fun y => y - x) := by
    have hs : (fun y => |pderiv 0 U y - pderiv 0 U x| + |pderiv 1 U y - pderiv 1 U x|)
        =o[𝓝 x] (fun y => y - x) := by
      have a := (hpo 0).norm_left
      have b := (hpo 1).norm_left
      simp only [Real.norm_eq_abs] at a b
      exact a.add b
    refine IsBigO.trans_isLittleO ?_ hs
    refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, hP0, sub_zero, h1 0, h1 1, sub_zero,
      sub_zero, abs_of_nonneg (show 0 ≤ gradNorm U y from Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity)]
    exact gradNorm_le U y
  have hgN : ∀ y, 0 ≤ gradNorm U y := fun y => Real.sqrt_nonneg _
  -- the transformed function
  have hFeq : transformF U = fun y => perspF (U y) (gradNorm U y) := by
    funext y; simp [transformF, norm_fderiv_eq_gradNorm]
  obtain ⟨LF, hLF⟩ := perspF_lipschitz hP
  have hFD : HasFDerivAt (transformF U) (0 : Plane →L[ℝ] ℝ) x := by
    rw [hFeq]; exact hasFDerivAt_zero_of_isLittleO (isLittleO_persp_comp hLF hgN hUo hPo)
  -- the first flux
  obtain ⟨LB, hLB⟩ := perspB_lipschitz hP
  have hBD : HasFDerivAt (fun y => perspB (U y) (gradNorm U y)) (0 : Plane →L[ℝ] ℝ) x :=
    hasFDerivAt_zero_of_isLittleO (isLittleO_persp_comp hLB hgN hUo hPo)
  have hV1 : ∀ i, pderiv i (fluxV1 U i) x = 0 := by
    intro i
    have hfe : fluxV1 U i = fun y => perspB (U y) (gradNorm U y) * pderiv i U y := by
      funext y; simp [fluxV1, norm_fderiv_eq_gradNorm]
    have h' : HasFDerivAt (fun y => perspB (U y) (gradNorm U y) * pderiv i U y)
        (0 : Plane →L[ℝ] ℝ) x := by
      convert hBD.mul (hpD i) using 1; simp
    rw [hfe]; exact pderiv_eq_zero_of_hasFDerivAt h' i
  -- the second flux
  obtain ⟨LΨ, hLΨ⟩ := perspPsi_lipschitz hP
  have hgx : gradU U x = 0 := by
    have : ‖gradU U x‖ = 0 := by rw [norm_gradU, norm_fderiv_eq_gradNorm, hP0]
    exact norm_eq_zero.mp this
  have hΨx : ∀ k, perspPsi (U x) (gradU U x) k = 0 := fun k => by simp [hgx, perspPsi]
  have hΨD : ∀ k, HasFDerivAt (fun y => perspPsi (U y) (gradU U y) k) (0 : Plane →L[ℝ] ℝ) x := by
    intro k
    refine hasFDerivAt_zero_of_isLittleO ?_
    have hs : (fun y => |U y - U x| + |gradNorm U y - gradNorm U x|) =o[𝓝 x] (fun y => y - x) := by
      have a := hUo.norm_left
      have b := hPo.norm_left
      simp only [Real.norm_eq_abs] at a b
      exact a.add b
    refine IsBigO.trans_isLittleO ?_ hs
    refine IsBigO.of_bound LΨ (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ |U y - U x| + |gradNorm U y - gradNorm U x|)]
    have hc := PiLp.norm_apply_le (perspPsi (U y) (gradU U y) - perspPsi (U x) (gradU U x)) k
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at hc
    refine hc.trans ((hLΨ _ _ _ _).trans (le_of_eq ?_))
    rw [hgx, sub_zero, norm_gradU, norm_fderiv_eq_gradNorm, hP0, sub_zero,
      abs_of_nonneg (hgN y)]
  have hV2 : ∀ i, pderiv i (fluxV2 U i) x = 0 := by
    intro i
    fin_cases i
    · have hfe : fluxV2 U 0 = fun y => pderiv 1 (pderiv 1 U) y * perspPsi (U y) (gradU U y) 0 -
          pderiv 0 (pderiv 1 U) y * perspPsi (U y) (gradU U y) 1 := by
        funext y; simp [fluxV2]
      have h' : HasFDerivAt (fun y => pderiv 1 (pderiv 1 U) y * perspPsi (U y) (gradU U y) 0 -
          pderiv 0 (pderiv 1 U) y * perspPsi (U y) (gradU U y) 1) (0 : Plane →L[ℝ] ℝ) x := by
        convert ((dh 1 1 x).hasFDerivAt.mul (hΨD 0)).sub ((dh 0 1 x).hasFDerivAt.mul (hΨD 1))
          using 1
        simp [hΨx]
      simp only [Fin.zero_eta, Fin.isValue]
      rw [hfe]; exact pderiv_eq_zero_of_hasFDerivAt h' 0
    · have hfe : fluxV2 U 1 = fun y => pderiv 0 (pderiv 0 U) y * perspPsi (U y) (gradU U y) 1 -
          pderiv 0 (pderiv 1 U) y * perspPsi (U y) (gradU U y) 0 := by
        funext y; simp [fluxV2]; ring
      have h' : HasFDerivAt (fun y => pderiv 0 (pderiv 0 U) y * perspPsi (U y) (gradU U y) 1 -
          pderiv 0 (pderiv 1 U) y * perspPsi (U y) (gradU U y) 0) (0 : Plane →L[ℝ] ℝ) x := by
        convert ((dh 0 0 x).hasFDerivAt.mul (hΨD 1)).sub ((dh 0 1 x).hasFDerivAt.mul (hΨD 0))
          using 1
        simp [hΨx]
      simp only [Fin.mk_one, Fin.isValue]
      rw [hfe]; exact pderiv_eq_zero_of_hasFDerivAt h' 1
  -- assemble
  have hDU : fderiv ℝ U x = 0 := fderiv_eq_zero_of_pderiv h1
  simp only [densityFn, divergence2, hessSq, h2, hDU, hFD.fderiv, hV1, hV2]
  have : 0 ≤ pLam := sq_nonneg _
  simp
  positivity

end Buckling
end
end ChunkedSource051
/- END SOURCE 051 -/

/- BEGIN SOURCE 052: RequestProject/Functional/Inequality.lean -/
section ChunkedSource052

/-!
# The functional inequality (Lemma 9.18 a.e. and Theorem 9.21 of the paper)

The density is nonnegative almost everywhere: at regular points (`|∇U| > 0`, `U ≠ 0`) it is the
calibration form plus the coupling term; on the critical set it is `λF²` wherever `D²U = 0`;
the remaining points form a null set by Lemma 9.10.  Integrating gives the functional
inequality from the profile facts.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

lemma null_regular_zeros {h : Plane → ℝ} (hh : ContDiff ℝ 1 h) (i : Fin 2) :
    volume {x | h x = 0 ∧ pderiv i h x ≠ 0} = 0 := by
  fin_cases i
  · exact null_regular_zeros_zero hh
  · exact null_regular_zeros_one hh

/-- **Lemma 9.18.**  The density is nonnegative almost everywhere. -/
lemma densityFn_nonneg_ae (hP : ProfileFacts) {U : Plane → ℝ} (hU : IsTestFn univ U) :
    ∀ᵐ x, 0 ≤ densityFn U x := by
  have hC1 : ContDiff ℝ 1 U := hU.1.of_le (WithTop.coe_le_coe.mpr le_top)
  have hC1' : ∀ j, ContDiff ℝ 1 (pderiv j U) := fun j =>
    (hU.pderiv j).1.of_le (WithTop.coe_le_coe.mpr le_top)
  set N := (⋃ i : Fin 2, {x | U x = 0 ∧ pderiv i U x ≠ 0}) ∪
    ⋃ i : Fin 2, ⋃ j : Fin 2, {x | pderiv j U x = 0 ∧ pderiv i (pderiv j U) x ≠ 0} with hN
  have hN0 : volume N = 0 := by
    refine measure_union_null (measure_iUnion_null fun i => null_regular_zeros hC1 i)
      (measure_iUnion_null fun i => measure_iUnion_null fun j => null_regular_zeros (hC1' j) i)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN0] with x hx
  simp only [hN, mem_union, mem_iUnion, mem_setOf_eq, not_or, not_exists, not_and, not_not] at hx
  obtain ⟨hx1, hx2⟩ := hx
  by_cases hpos : 0 < gradNorm U x
  · have hu : U x ≠ 0 := by
      intro hu
      have h0 : pderiv 0 U x = 0 := hx1 0 hu
      have h1 : pderiv 1 U x = 0 := hx1 1 hu
      simp [gradNorm, h0, h1] at hpos
    rw [densityFn_eq_frame hP hU hpos hu]
    have hs : U x / gradNorm U x ≠ 0 := div_ne_zero hu hpos.ne'
    exact add_nonneg (hP.matrix_pos _ hs _ _ _)
      (mul_nonneg (hP.coupling_pos _ hs) (sq_nonneg _))
  · have hz : gradNorm U x = 0 := le_antisymm (not_lt.mp hpos) (Real.sqrt_nonneg _)
    have hsq := gradNorm_sq U x
    rw [hz] at hsq
    have h1 : ∀ j, pderiv j U x = 0 := by
      intro j; fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue]; nlinarith [sq_nonneg (pderiv 0 U x), sq_nonneg (pderiv 1 U x)]
      · simp only [Fin.mk_one, Fin.isValue]; nlinarith [sq_nonneg (pderiv 0 U x), sq_nonneg (pderiv 1 U x)]
    exact densityFn_nonneg_critical hP hU h1 fun i j => hx2 i j (h1 j)

/-! ### The functional inequality (Theorem 9.21) -/

/-- **The functional inequality from the profile facts** (Section 9 of the paper). -/
theorem functionalInequality_of_profileFacts (hP : ProfileFacts) :
    FunctionalInequality := by
  intro U hU
  refine ⟨transformF_lipschitz hP hU, ?_, ?_⟩
  · exact IsCompact.of_isClosed_subset hU.2.1 (isClosed_tsupport _) tsupport_transformF_subset
  · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := densityFn_integrable hP hU
    have hint : 0 ≤ ∫ x, densityFn U x := integral_nonneg_of_ae (densityFn_nonneg_ae hP hU)
    have hdiv : ∀ (V : Fin 2 → Plane → ℝ), (∀ i, ∃ L, LipschitzWith L (V i)) →
        (∀ i, tsupport (V i) ⊆ tsupport U) → ∫ x, divergence2 V x = 0 := by
      intro V hL hs
      obtain ⟨L0, hL0⟩ := hL 0
      obtain ⟨L1, hL1⟩ := hL 1
      have hc : ∀ i, HasCompactSupport (V i) := fun i =>
        IsCompact.of_isClosed_subset hU.2.1 (isClosed_tsupport _) (hs i)
      have hi : ∀ i, Integrable (pderiv i (V i)) := by
        intro i
        obtain ⟨L, hL⟩ := hL i
        exact integrable_pderiv_of_lipschitz hL (hc i) i
      unfold divergence2
      rw [integral_add (hi 0) (hi 1), integral_pderiv_lipschitz_eq_zero hL0 (hc 0),
        integral_pderiv_lipschitz_eq_zero hL1 (hc 1), add_zero]
    have hd1 := hdiv (fluxV1 U) (fluxV1_lipschitz hP hU) tsupport_fluxV1_subset
    have hd2 := hdiv (fluxV2 U) (fluxV2_lipschitz hP hU) tsupport_fluxV2_subset
    have hsplit : ∫ x, densityFn U x = pK * ((∫ x, hessSq U x) - ∫ x, ‖fderiv ℝ U x‖ ^ 2) -
        ((∫ x, ‖fderiv ℝ (transformF U) x‖ ^ 2) - pLam * ∫ x, transformF U x ^ 2) +
        (∫ x, divergence2 (fluxV1 U) x) + ∫ x, divergence2 (fluxV2 U) x := by
      have e : ∀ x, densityFn U x = pK * hessSq U x - pK * ‖fderiv ℝ U x‖ ^ 2 -
          ‖fderiv ℝ (transformF U) x‖ ^ 2 + pLam * transformF U x ^ 2 +
          divergence2 (fluxV1 U) x + divergence2 (fluxV2 U) x := fun x => by
        unfold densityFn; ring
      simp only [e]
      have j1 : Integrable (fun x => pK * hessSq U x - pK * ‖fderiv ℝ U x‖ ^ 2) :=
        (h1.const_mul pK).sub (h2.const_mul pK)
      have j2 : Integrable (fun x => pK * hessSq U x - pK * ‖fderiv ℝ U x‖ ^ 2 -
          ‖fderiv ℝ (transformF U) x‖ ^ 2) := j1.sub h3
      have j3 : Integrable (fun x => pK * hessSq U x - pK * ‖fderiv ℝ U x‖ ^ 2 -
          ‖fderiv ℝ (transformF U) x‖ ^ 2 + pLam * transformF U x ^ 2) := j2.add (h4.const_mul pLam)
      have j4 : Integrable (fun x => pK * hessSq U x - pK * ‖fderiv ℝ U x‖ ^ 2 -
          ‖fderiv ℝ (transformF U) x‖ ^ 2 + pLam * transformF U x ^ 2 +
          divergence2 (fluxV1 U) x) := j3.add h5
      rw [integral_add j4 h6, integral_add j3 h5, integral_add j2 (h4.const_mul pLam),
        integral_sub j1 h3, integral_sub (h1.const_mul pK) (h2.const_mul pK),
        integral_const_mul, integral_const_mul, integral_const_mul]
      ring
    rw [hsplit, hd1, hd2, integral_hessSq_eq hU] at hint
    linarith

end Buckling
end
end ChunkedSource052
/- END SOURCE 052 -/

/- BEGIN SOURCE 053: RequestProject/Profiles/Radial.lean -/
section ChunkedSource053

/-!
# Positivity and the radial equations (Lemma 4.2 of the paper)

On `I = (0, k)`: `p, u, φ > 0`, `u' = -p`, `p' = u - c - p/r`,
`p'' = -p'/r - (1 - r⁻²) p`, `φ'' = -φ'/r - λ φ` and `u(r) = ∫_r^k p`.
-/

@[expose] public section

open Real Set

namespace Buckling

lemma hasDerivAt_rp (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt rp (ru r - pc - rp r / r) r := by
  have := hasDerivAt_besselJ_one r hr
  unfold rp ru; convert this using 1; ring

lemma hasDerivAt_ru (r : ℝ) : HasDerivAt ru (-rp r) r := by
  unfold ru rp
  simpa using (hasDerivAt_besselJ_zero r).add_const pc

lemma hasDerivAt_rPhi (r : ℝ) : HasDerivAt rPhi (-pAlpha * besselJ 1 (pAlpha * r)) r := by
  unfold rPhi
  have h := (hasDerivAt_besselJ_zero (pAlpha * r)).comp r ((hasDerivAt_id r).const_mul pAlpha)
  convert! h using 1 <;> simp [Function.comp_def] <;> ring

lemma deriv_rPhi : deriv rPhi = fun r => -pAlpha * besselJ 1 (pAlpha * r) :=
  funext fun r => (hasDerivAt_rPhi r).deriv

/-- **Lemma 4.2 (positivity and the radial equations).** -/
theorem radial_equations (hZ : ExtZeros) (r : ℝ) (hr0 : 0 < r) (hrk : r < jk) :
    0 < rp r ∧ 0 < ru r ∧ 0 < rPhi r ∧
    HasDerivAt ru (-rp r) r ∧
    HasDerivAt rp (ru r - pc - rp r / r) r ∧
    HasDerivAt (deriv rp) (-(deriv rp r) / r - (1 - 1 / r ^ 2) * rp r) r ∧
    HasDerivAt (deriv rPhi) (-(deriv rPhi r) / r - pLam * rPhi r) r ∧
    ru r = ∫ s in r..jk, rp s := by
  obtain ⟨hq0, hqk, hα0, hα1, -, -, hc, -, -⟩ := parameter_signs hZ
  have hk0 : 0 < jk := hr0.trans hrk
  -- the integral formula
  have hint : ru r = ∫ s in r..jk, rp s := by
    have hcont : Continuous rp := continuous_besselJ 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := r) (b := jk) (f := ru)
      (f' := fun s => -rp s) (fun s _ => hasDerivAt_ru s) (hcont.neg.intervalIntegrable _ _)
    rw [intervalIntegral.integral_neg] at this
    have hk : ru jk = 0 := by simp [ru, pc]
    linarith
  have hp : 0 < rp r := besselJ_one_pos_of_lt_jk hZ r hr0 hrk
  have hu : 0 < ru r := by
    rw [hint]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_besselJ 1).intervalIntegrable _ _) (fun s hs => ?_) hrk
    exact besselJ_one_pos_of_lt_jk hZ s (hr0.trans hs.1) hs.2
  have hφ : 0 < rPhi r := by
    refine besselJ_zero_pos_of_lt_jq hZ _ (by positivity) ?_
    have : pAlpha * jk = jq := by unfold pAlpha; field_simp
    nlinarith
  have hr : r ≠ 0 := hr0.ne'
  refine ⟨hp, hu, hφ, hasDerivAt_ru r, hasDerivAt_rp r hr, ?_, ?_, hint⟩
  · have h := hasDerivAt_deriv_besselJ_one r hr
    have hd : deriv rp r = besselJ 0 r - besselJ 1 r / r := (hasDerivAt_besselJ_one r hr).deriv
    unfold rp at hd ⊢
    rw [hd]; convert h using 1
  · have hαr : pAlpha * r ≠ 0 := by positivity
    have h := ((hasDerivAt_besselJ_one (pAlpha * r) hαr).comp r
      ((hasDerivAt_id r).const_mul pAlpha)).const_mul (-pAlpha)
    rw [deriv_rPhi]
    convert! h using 1 <;>
      try simp only [Function.comp_def, rPhi, pLam, mul_one]
    all_goals field_simp [hr, hαr]
    all_goals ring

/-- **Lemma 4.2, last part.**  `T = t' = -S/p² = tA - 1` with `S = p² + u p'` and
`A = -p'/p`. -/
theorem hasDerivAt_rt (hZ : ExtZeros) (r : ℝ) (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rt (-(rp r ^ 2 + ru r * deriv rp r) / rp r ^ 2) r ∧
      -(rp r ^ 2 + ru r * deriv rp r) / rp r ^ 2 = rt r * (-(deriv rp r) / rp r) - 1 := by
  obtain ⟨hp, -, -, hu', hp', -⟩ := radial_equations hZ r hr0 hrk
  have hd : deriv rp r = ru r - pc - rp r / r := hp'.deriv
  refine ⟨?_, ?_⟩
  · have h := hu'.fun_div hp' hp.ne'
    simpa only [rt] using! (h.congr_deriv (by rw [← hd]; ring))
  · unfold rt; field_simp; ring

end Buckling
end
end ChunkedSource053
/- END SOURCE 053 -/

/- BEGIN SOURCE 054: RequestProject/Profiles/TChange.lean -/
section ChunkedSource054

/-!
# The radial change of variable (Lemma 4.3 of the paper)

`T = t' < 0` on `(0, k)`, and `t = u/p` maps `(0, k)` bijectively onto `(0, ∞)` in reverse
order.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

lemma besselJ_zero_gt_small (r : ℝ) (hr0 : 0 < r) (hr : r ^ 2 < 36) :
    1 - r ^ 2 / 4 < besselJ 0 r := by
  have h := besselJ_tail_general 0 1 r hr0 (by push_cast; nlinarith)
  simp [besselPartialR, Finset.sum_range_succ] at h
  nlinarith [h.1]

lemma besselJ_one_lt_small (r : ℝ) (hr0 : 0 < r) (hr : r ^ 2 < 16) :
    besselJ 1 r < r / 2 := by
  have h := besselJ_tail_general 1 0 r hr0 (by push_cast; nlinarith)
  simp [besselPartialR] at h
  linarith [h.1]

/-- `p' > 0` for `0 < r`, `r² ≤ 2`. -/
lemma deriv_rp_pos_small (r : ℝ) (hr0 : 0 < r) (hr : r ^ 2 ≤ 2) : 0 < deriv rp r := by
  have hd : deriv rp r = besselJ 0 r - besselJ 1 r / r := (hasDerivAt_besselJ_one r hr0.ne').deriv
  rw [hd]
  have h1 := besselJ_zero_gt_small r hr0 (by linarith)
  have h2 := besselJ_one_lt_small r hr0 (by linarith)
  have h3 : besselJ 1 r / r < 1 / 2 := by rw [div_lt_iff₀ hr0]; linarith
  linarith

lemma besselJ_one_jk (hZ : ExtZeros) : besselJ 1 jk = 0 := ((hZ 1 (by norm_num)).2.2.1 1 le_rfl).1

/-- The logarithmic derivative `L = p'/p` and its derivative on `(0, k)`. -/
lemma hasDerivAt_logderiv_rp (hZ : ExtZeros) (s : ℝ) (hs0 : 0 < s) (hsk : s < jk) :
    HasDerivAt (fun s => deriv rp s / rp s)
      (-1 + 1 / s ^ 2 - (deriv rp s / rp s) / s - (deriv rp s / rp s) ^ 2) s := by
  obtain ⟨hp, -, -, -, hp', hp'', -⟩ := radial_equations hZ s hs0 hsk
  have := hp''.div hp' hp.ne'
  convert this using 1
  rw [← hp'.deriv]
  field_simp
  ring

/-- `L = p'/p` is strictly decreasing on `(√5/2, k)` (log-concavity of `p`). -/
lemma logderiv_rp_strictAnti (hZ : ExtZeros) :
    StrictAntiOn (fun s => deriv rp s / rp s) (Ioo (Real.sqrt 5 / 2) jk) := by
  have h52 : 0 < Real.sqrt 5 / 2 := by positivity
  have hsq : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro s hs
    exact (hasDerivAt_logderiv_rp hZ s (h52.trans hs.1) hs.2).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    have hs0 : 0 < s := h52.trans hs.1
    rw [(hasDerivAt_logderiv_rp hZ s hs0 hs.2).deriv]
    have h5 : 5 / 4 < s ^ 2 := by nlinarith [hs.1]
    set L := deriv rp s / rp s
    have key : -1 + 1 / s ^ 2 - L / s - L ^ 2 = -1 + 5 / (4 * s ^ 2) - (L + 1 / (2 * s)) ^ 2 := by
      field_simp; ring
    rw [key]
    have : 5 / (4 * s ^ 2) < 1 := by rw [div_lt_one (by positivity)]; linarith
    nlinarith [sq_nonneg (L + 1 / (2 * s))]

/-- Tangent-line bound for the concave function `log p` beyond `√5/2`. -/
lemma rp_lt_tangent (hZ : ExtZeros) {r s : ℝ} (hr : Real.sqrt 5 / 2 < r) (hrs : r < s)
    (hsk : s < jk) : rp s < rp r * Real.exp (deriv rp r / rp r * (s - r)) := by
  have h52 : 0 < Real.sqrt 5 / 2 := by positivity
  have hr0 : 0 < r := h52.trans hr
  have hpos : ∀ x ∈ Icc r s, 0 < rp x := fun x hx =>
    (radial_equations hZ x (hr0.trans_le hx.1) (hx.2.trans_lt hsk)).1
  -- mean value theorem for `log p`
  have hcont : ContinuousOn (fun x => Real.log (rp x)) (Icc r s) :=
    fun x hx => ((continuous_besselJ 1).continuousAt.log (hpos x hx).ne').continuousWithinAt
  have hdiff : ∀ x ∈ Ioo r s, HasDerivAt (fun x => Real.log (rp x)) (deriv rp x / rp x) x := by
    intro x hx
    have hx0 : 0 < x := hr0.trans hx.1
    have hp' := (radial_equations hZ x hx0 (hx.2.trans hsk)).2.2.2.2.1
    have := hp'.log (hpos x ⟨hx.1.le, hx.2.le⟩).ne'
    rwa [← hp'.deriv] at this
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun x => Real.log (rp x))
    (fun x => deriv rp x / rp x) hrs hcont hdiff
  have hlt : deriv rp ξ / rp ξ < deriv rp r / rp r :=
    logderiv_rp_strictAnti hZ ⟨hr, hrs.trans hsk⟩ ⟨hr.trans hξ.1, hξ.2.trans hsk⟩ hξ.1
  have hlog : Real.log (rp s) - Real.log (rp r) < deriv rp r / rp r * (s - r) := by
    rw [hξeq] at hlt
    rw [div_lt_iff₀ (sub_pos.mpr hrs)] at hlt
    linarith
  have hps := hpos s ⟨hrs.le, le_rfl⟩
  have hpr := hpos r ⟨le_rfl, hrs.le⟩
  calc rp s = Real.exp (Real.log (rp s)) := (Real.exp_log hps).symm
    _ < Real.exp (Real.log (rp r) + deriv rp r / rp r * (s - r)) := by
        apply Real.exp_lt_exp.mpr; linarith
    _ = rp r * Real.exp (deriv rp r / rp r * (s - r)) := by
        rw [Real.exp_add, Real.exp_log hpr]

lemma rp_jk (hZ : ExtZeros) : rp jk = 0 := besselJ_one_jk hZ

/-- `∫_r^k e^{L(s-r)} ds = (e^{L(k-r)} - 1)/L`. -/
lemma integral_exp_tangent (L r k : ℝ) (hL : L ≠ 0) :
    ∫ s in r..k, Real.exp (L * (s - r)) = (Real.exp (L * (k - r)) - 1) / L := by
  have : ∀ x ∈ uIcc r k, HasDerivAt (fun s => Real.exp (L * (s - r)) / L)
      (Real.exp (L * (x - r))) x := by
    intro x _
    have h := ((((hasDerivAt_id x).sub_const r).const_mul L).exp).div_const L
    convert! h using 1 <;> try simp only [Function.comp_def, id, mul_one]
    all_goals field_simp [hL]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp; ring

/-- If `p'(r) < 0` then `u(r) < p(r)/A(r) = -p(r)²/p'(r)`. -/
lemma ru_lt_of_deriv_neg (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk)
    (hneg : deriv rp r < 0) : ru r < -(rp r) / (deriv rp r / rp r) := by
  have h52 : Real.sqrt 5 / 2 < r := by
    by_contra h
    push_neg at h
    have : r ^ 2 ≤ 2 := by
      have h5 : (Real.sqrt 5 / 2) ^ 2 = 5 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
      nlinarith
    linarith [deriv_rp_pos_small r hr0 this]
  obtain ⟨hp, -, -, -, -, -, -, hint⟩ := radial_equations hZ r hr0 hrk
  set L := deriv rp r / rp r with hLdef
  have hL : L < 0 := div_neg_of_neg_of_pos hneg hp
  have hcont : Continuous rp := continuous_besselJ 1
  have hlt : ∫ s in r..jk, rp s < ∫ s in r..jk, rp r * Real.exp (L * (s - r)) := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hrk
      hcont.continuousOn (by fun_prop)
    · intro s hs
      rcases eq_or_lt_of_le hs.2 with h | h
      · rw [h, rp_jk hZ]; positivity
      · exact (rp_lt_tangent hZ h52 hs.1 h).le
    · refine ⟨jk, ⟨hrk.le, le_rfl⟩, ?_⟩
      rw [rp_jk hZ]; positivity
  rw [intervalIntegral.integral_const_mul, integral_exp_tangent L r jk hL.ne] at hlt
  rw [hint]
  calc _ < _ := hlt
    _ ≤ -(rp r) / L := by
      rw [mul_div_assoc']
      apply div_le_div_of_nonpos_of_le hL.le
      have := Real.exp_pos (L * (jk - r))
      nlinarith

/-- `S = p² + u p' > 0` on `(0, k)`. -/
theorem rS_pos (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    0 < rp r ^ 2 + ru r * deriv rp r := by
  obtain ⟨hp, hu, -⟩ := radial_equations hZ r hr0 hrk
  rcases le_or_gt 0 (deriv rp r) with h | h
  · positivity
  · have := ru_lt_of_deriv_neg hZ hr0 hrk h
    rw [div_div_eq_mul_div, lt_div_iff_of_neg h] at this
    nlinarith

/-- `T = t' < 0` on `(0, k)`. -/
theorem rT_neg (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    -(rp r ^ 2 + ru r * deriv rp r) / rp r ^ 2 < 0 := by
  have h := rS_pos hZ hr0 hrk
  have hp := (radial_equations hZ r hr0 hrk).1
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

theorem rt_pos (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) : 0 < rt r := by
  obtain ⟨hp, hu, -⟩ := radial_equations hZ r hr0 hrk
  exact div_pos hu hp

theorem rt_strictAntiOn (hZ : ExtZeros) : StrictAntiOn rt (Ioo 0 jk) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · intro r hr
    exact (hasDerivAt_rt hZ r hr.1 hr.2).1.continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hasDerivAt_rt hZ r hr.1 hr.2).1.deriv]
    exact rT_neg hZ hr.1 hr.2

theorem tendsto_rt_zero (hZ : ExtZeros) : Tendsto rt (𝓝[>] 0) atTop := by
  have hk0 : 0 < jk := (parameter_signs hZ).1.trans (parameter_signs hZ).2.1
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  have hu : Tendsto ru (𝓝[>] 0) (𝓝 (1 + pc)) := by
    have : Continuous ru := (continuous_besselJ 0).add continuous_const
    have h := this.tendsto 0
    simp only [ru, besselJ_zero_at_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hp : Tendsto rp (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have h := (continuous_besselJ 1).tendsto 0
      simp only [besselJ_zero_arg] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT hk0] with r hr
      exact (radial_equations hZ r hr.1 hr.2).1
  have := Filter.Tendsto.pos_mul_atTop (by linarith) hu (tendsto_inv_nhdsGT_zero.comp hp)
  exact this.congr fun r => by simp [rt, div_eq_mul_inv]

theorem tendsto_rt_jk (hZ : ExtZeros) : Tendsto rt (𝓝[<] jk) (𝓝 0) := by
  have hk0 : 0 < jk := (parameter_signs hZ).1.trans (parameter_signs hZ).2.1
  have hc := (parameter_signs hZ).2.2.2.2.2.2.1
  set g : ℝ → ℝ := fun x => ru x - pc - rp x / x with hg
  have hgc : Tendsto g (𝓝[<] jk) (𝓝 (-pc)) := by
    have : ContinuousAt g jk := by
      have h1 : Continuous ru := (continuous_besselJ 0).add continuous_const
      have h2 : Continuous rp := continuous_besselJ 1
      exact ((h1.continuousAt.sub continuousAt_const).sub
        (h2.continuousAt.div continuousAt_id hk0.ne'))
    have h := this.tendsto
    have hv : g jk = -pc := by simp [g, ru, rp_jk hZ, pc]
    rw [hv] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hpc : Tendsto rp (𝓝[<] jk) (𝓝 0) := by
    have h := (continuous_besselJ 1).tendsto jk
    rw [show besselJ 1 jk = 0 from rp_jk hZ] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hup : Tendsto (fun x => -rp x / g x) (𝓝[<] jk) (𝓝 0) := by
    have h := (hpc.neg).div hgc (by linarith)
    have hfun : ((fun x : ℝ => -rp x) / g) = (fun x => -rp x / g x) := by
      funext x
      simp only [Pi.div_apply]
    rw [hfun] at h
    simpa only [neg_zero, zero_div] using! h
  have hev : ∀ᶠ x in 𝓝[<] jk, 0 < x ∧ g x < 0 := by
    filter_upwards [Ioo_mem_nhdsLT hk0, hgc.eventually (gt_mem_nhds (by linarith : -pc < 0))]
      with x hx hgx
    exact ⟨hx.1, hgx⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [Ioo_mem_nhdsLT hk0] with x hx
    exact (rt_pos hZ hx.1 hx.2).le
  · filter_upwards [Ioo_mem_nhdsLT hk0, hev] with x hx hx'
    have hd : deriv rp x = g x := (hasDerivAt_rp x hx.1.ne').deriv
    have hp := (radial_equations hZ x hx.1 hx.2).1
    have := ru_lt_of_deriv_neg hZ hx.1 hx.2 (hd ▸ hx'.2)
    rw [hd] at this
    unfold rt
    rw [div_le_iff₀ hp]
    rw [div_div_eq_mul_div, lt_div_iff_of_neg hx'.2] at this
    rw [div_mul_eq_mul_div, le_div_iff_of_neg hx'.2]
    nlinarith

/-- **Lemma 4.3 (the radial change of variable).**  `t` maps `(0, k)` bijectively onto
`(0, ∞)`, strictly decreasing. -/
theorem rt_bijOn (hZ : ExtZeros) : BijOn rt (Ioo 0 jk) (Ioi 0) := by
  have hk0 : 0 < jk := (parameter_signs hZ).1.trans (parameter_signs hZ).2.1
  refine ⟨fun r hr => rt_pos hZ hr.1 hr.2, (rt_strictAntiOn hZ).injOn, ?_⟩
  intro y hy
  obtain ⟨a, hya, ha⟩ := (((tendsto_rt_zero hZ).eventually (eventually_gt_atTop y)).and
    (Ioo_mem_nhdsGT hk0)).exists
  obtain ⟨b, hyb, hb⟩ := (((tendsto_rt_jk hZ).eventually (gt_mem_nhds hy)).and
    (Ioo_mem_nhdsLT hk0)).exists
  have hab : a < b := by
    by_contra h
    push_neg at h
    rcases eq_or_lt_of_le h with h | h
    · subst h; linarith
    · have := (rt_strictAntiOn hZ) ⟨hb.1, hb.2⟩ ⟨ha.1, ha.2⟩ h
      linarith
  have hcont : ContinuousOn rt (Icc a b) := fun x hx =>
    (hasDerivAt_rt hZ x (ha.1.trans_le hx.1) (hx.2.trans_lt hb.2)).1.continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcy⟩ := intermediate_value_Icc' hab.le hcont ⟨hyb.le, hya.le⟩
  exact ⟨c, ⟨ha.1.trans_le hc.1, hc.2.trans_lt hb.2⟩, hcy⟩

theorem rOf_spec (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) : rOf t ∈ Ioo 0 jk ∧ rt (rOf t) = t := by
  have h : ∃ r ∈ Ioo 0 jk, rt r = t := (rt_bijOn hZ).surjOn ht
  unfold rOf
  rw [dif_pos h]
  exact h.choose_spec

theorem rOf_rt (hZ : ExtZeros) {r : ℝ} (hr : r ∈ Ioo 0 jk) : rOf (rt r) = r :=
  (rt_bijOn hZ).injOn (rOf_spec hZ (rt_pos hZ hr.1 hr.2)).1 hr
    (rOf_spec hZ (rt_pos hZ hr.1 hr.2)).2

theorem rOf_strictAntiOn (hZ : ExtZeros) : StrictAntiOn rOf (Ioi 0) := by
  intro a ha b hb hab
  have hA := rOf_spec hZ ha
  have hB := rOf_spec hZ hb
  by_contra h
  push_neg at h
  rcases eq_or_lt_of_le h with h | h
  · have : a = b := by rw [← hA.2, ← hB.2, h]
    linarith
  · have := rt_strictAntiOn hZ hA.1 hB.1 h
    rw [hA.2, hB.2] at this
    linarith

theorem rOf_image (hZ : ExtZeros) : rOf '' Ioi 0 = Ioo 0 jk := by
  ext r
  constructor
  · rintro ⟨t, ht, rfl⟩; exact (rOf_spec hZ ht).1
  · intro hr; exact ⟨rt r, rt_pos hZ hr.1 hr.2, rOf_rt hZ hr⟩

theorem continuousAt_rOf (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) : ContinuousAt rOf t := by
  have hmono : MonotoneOn (fun s => -rOf s) (Ioi 0) := fun a ha b hb hab => by
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact neg_le_neg (rOf_strictAntiOn hZ ha hb h).le
  have himg : (fun s => -rOf s) '' Ioi 0 = Ioo (-jk) 0 := by
    rw [show (fun s => -rOf s) = Neg.neg ∘ rOf from rfl, Set.image_comp, rOf_image hZ]
    simp
  have := continuousAt_of_monotoneOn_of_image_mem_nhds hmono (Ioi_mem_nhds ht) (by
    rw [himg]
    have h := (rOf_spec hZ ht).1
    exact Ioo_mem_nhds (by linarith [h.2]) (by linarith [h.1]))
  have hn : ContinuousAt (fun s => -rOf s) t := this
  convert! hn.neg using 1
  ext s
  simp only [Pi.neg_apply, neg_neg]

/-- The inverse `r(t)` is differentiable with `r_t = 1/T(r(t))`. -/
theorem hasDerivAt_rOf (hZ : ExtZeros) {t : ℝ} (ht : 0 < t) :
    HasDerivAt rOf (-(rp (rOf t) ^ 2 + ru (rOf t) * deriv rp (rOf t)) / rp (rOf t) ^ 2)⁻¹ t := by
  have h := rOf_spec hZ ht
  apply HasDerivAt.of_local_left_inverse (continuousAt_rOf hZ ht)
    (hasDerivAt_rt hZ _ h.1.1 h.1.2).1 (rT_neg hZ h.1.1 h.1.2).ne
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact (rOf_spec hZ hs).2

end Buckling
end
end ChunkedSource054
/- END SOURCE 054 -/

/- BEGIN SOURCE 055: RequestProject/Profiles/Identities.lean -/
section ChunkedSource055

/-!
# Explicit profile identities (Lemmas 4.5, 4.7 and 4.8 of the paper)

All radial quantities are expressed through `J₀(r), J₁(r), J₀(αr), J₁(αr)`; the
differential identities then become rational-function identities.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-! ### Radial quantities (Definitions 4.1 and 4.4) -/

/-- `A = -p'/p`. -/
noncomputable def rA (r : ℝ) : ℝ := -(deriv rp r) / rp r
/-- `C = -1/r`. -/
noncomputable def rC (r : ℝ) : ℝ := -1 / r
/-- `S = p² + u p'`. -/
noncomputable def rS (r : ℝ) : ℝ := rp r ^ 2 + ru r * deriv rp r
/-- `T = t' = -S/p²`. -/
noncomputable def rT (r : ℝ) : ℝ := -rS r / rp r ^ 2
/-- `f = φ/p` (radial). -/
noncomputable def rf (r : ℝ) : ℝ := rPhi r / rp r
/-- `w = φ'/p`. -/
noncomputable def rw (r : ℝ) : ℝ := deriv rPhi r / rp r
/-- `z = (φ p' - p φ')/S` (radial version of `f_t`). -/
noncomputable def rz (r : ℝ) : ℝ := (rPhi r * deriv rp r - rp r * deriv rPhi r) / rS r
/-- `g = (p φ + u φ')/S` (radial version of `f - t f_t`). -/
noncomputable def rg (r : ℝ) : ℝ := (rp r * rPhi r + ru r * deriv rPhi r) / rS r

/-! ### Explicit derivatives -/

lemma deriv_rp_eq (r : ℝ) (hr : r ≠ 0) : deriv rp r = besselJ 0 r - besselJ 1 r / r :=
  (hasDerivAt_besselJ_one r hr).deriv

lemma deriv_rPhi_eq (r : ℝ) : deriv rPhi r = -pAlpha * besselJ 1 (pAlpha * r) :=
  (hasDerivAt_rPhi r).deriv

lemma pLam_eq : pLam = pAlpha ^ 2 := rfl

/-- `B'(x) = J₀(x) J₁(x)/x`. -/
lemma hasDerivAt_besselB (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt besselB (besselJ 0 x * besselJ 1 x / x) x := by
  have h0 := hasDerivAt_besselJ_zero x
  have h1 := hasDerivAt_besselJ_one x hx
  have h := ((hasDerivAt_id x).fun_mul
    ((h0.fun_pow 2).fun_add (h1.fun_pow 2))).fun_sub (h0.fun_mul h1)
  convert! h using 1 <;>
    try simp only [besselB, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  all_goals field_simp [hx]
  all_goals ring

/-- `(x B(x))' = x (J₀(x)² + J₁(x)²)`. -/
lemma hasDerivAt_xB (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun x => x * besselB x) (x * (besselJ 0 x ^ 2 + besselJ 1 x ^ 2)) x := by
  have h := (hasDerivAt_id x).fun_mul (hasDerivAt_besselB x hx)
  convert! h using 1 <;> try simp only [besselB, id, one_mul]
  all_goals field_simp [hx]
  all_goals ring

/-- **Lemma 4.7 (endpoint identities for `B`).** -/
theorem besselB_endpoints (hZ : ExtZeros) :
    besselB jk = jk * pc ^ 2 ∧ besselB jq = jq * besselJ 1 jq ^ 2 ∧
      pK * besselB jk = pAlpha * besselB jq := by
  obtain ⟨hq0, hqk, -, -, -, -, hc, -, -⟩ := parameter_signs hZ
  have hJ1k : besselJ 1 jk = 0 := besselJ_one_jk hZ
  have hJ0q : besselJ 0 jq = 0 := ((hZ 0 (by norm_num)).2.2.1 1 le_rfl).1
  have h1 : besselB jk = jk * pc ^ 2 := by simp [besselB, hJ1k, pc]
  have h2 : besselB jq = jq * besselJ 1 jq ^ 2 := by simp [besselB, hJ0q]
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  have hk0 : 0 < jk := hq0.trans hqk
  have : jq = pAlpha * jk := by unfold pAlpha; field_simp
  unfold pK
  rw [this]
  field_simp

/-! ### Lemma 4.5 -/

/-- **Lemma 4.5 (explicit profile identities)**, algebraic part. -/
theorem profile_identities_alg (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    0 < rS r ∧ rPhi r = rp r * rg r + ru r * rz r ∧ rw r + rA r * rf r = rT r * rz r ∧
      rw r = -rz r - rA r * rg r := by
  have hS : 0 < rS r := rS_pos hZ hr0 hrk
  have hp := (radial_equations hZ r hr0 hrk).1
  refine ⟨hS, ?_, ?_, ?_⟩
  · unfold rg rz; field_simp; unfold rS; ring
  · unfold rw rA rf rT rz; field_simp; ring
  · unfold rw rz rA rg; field_simp; unfold rS; ring

/-- **Lemma 4.5**, Riccati equations: `A_r = A² + AC + 1 - C²`, `C_r = C²`. -/
theorem hasDerivAt_rA (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rA (rA r ^ 2 + rA r * rC r + 1 - rC r ^ 2) r := by
  obtain ⟨hp, -, -, -, hp', hp'', -⟩ := radial_equations hZ r hr0 hrk
  have := (hp''.neg).div hp' hp.ne'
  rw [← hp'.deriv] at this
  unfold rA
  convert this using 1
  simp only [rC, Pi.neg_apply]
  field_simp
  ring

theorem hasDerivAt_rC {r : ℝ} (hr : r ≠ 0) : HasDerivAt rC (rC r ^ 2) r := by
  have := (hasDerivAt_inv hr).neg
  unfold rC
  convert this using 1
  · ext x; simp [div_eq_mul_inv]
  · field_simp

/-- **Lemma 4.5**: `f_r = w + A f`. -/
theorem hasDerivAt_rf (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rf (rw r + rA r * rf r) r := by
  obtain ⟨hp, -, -, -, hp', -⟩ := radial_equations hZ r hr0 hrk
  have := (hasDerivAt_rPhi r).div hp' hp.ne'
  rw [← hp'.deriv, ← deriv_rPhi_eq] at this
  unfold rf
  convert this using 1
  simp only [rw, rA]
  field_simp
  ring

/-- **Lemma 4.5**: `w_r = (A + C) w - λ f`. -/
theorem hasDerivAt_rw (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rw ((rA r + rC r) * rw r - pLam * rf r) r := by
  obtain ⟨hp, -, -, -, hp', -, hφ'', -⟩ := radial_equations hZ r hr0 hrk
  have := hφ''.div hp' hp.ne'
  rw [← hp'.deriv] at this
  unfold rw
  convert this using 1
  simp only [rA, rf, rC]
  field_simp
  ring

/-! ### Lemma 4.8 -/

/-- **Lemma 4.8, (4.4)**: `V := w² - C f w + λ f² = K A_r + G C²` (with `A_r` written via the
Riccati equation). -/
theorem V_identity {r : ℝ} (hr : r ≠ 0) (hp : rp r ≠ 0) :
    rw r ^ 2 - rC r * rf r * rw r + pLam * rf r ^ 2 =
      pK * (rA r ^ 2 + rA r * rC r + 1 - rC r ^ 2) + rG r * rC r ^ 2 := by
  simp only [rw, rC, rf, rA, rG, deriv_rp_eq r hr, deriv_rPhi_eq, besselB, rPhi, pLam_eq]
  unfold rp at hp ⊢
  field_simp
  ring

lemma hasDerivAt_N (r : ℝ) (hr : r ≠ 0) (hα : pAlpha ≠ 0) :
    HasDerivAt (fun r => pAlpha * r * besselB (pAlpha * r) - pK * r * besselB r)
      (pAlpha * (pAlpha * r) * (besselJ 0 (pAlpha * r) ^ 2 + besselJ 1 (pAlpha * r) ^ 2) -
        pK * (r * (besselJ 0 r ^ 2 + besselJ 1 r ^ 2))) r := by
  have h1 := (hasDerivAt_xB (pAlpha * r) (mul_ne_zero hα hr)).comp r
    ((hasDerivAt_id r).const_mul pAlpha)
  have h2 := (hasDerivAt_xB r hr).const_mul pK
  convert h1.sub h2 using 1
  · ext x; simp [mul_assoc]
  · simp; ring

/-- **Lemma 4.8, (4.5)**: `G_r = b + 2AG + 2KC`. -/
theorem hasDerivAt_rG (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rG (rb r + 2 * rA r * rG r + 2 * pK * rC r) r := by
  have hα : pAlpha ≠ 0 := (parameter_signs hZ).2.2.1.ne'
  have hr : r ≠ 0 := hr0.ne'
  have hp : rp r ≠ 0 := (radial_equations hZ r hr0 hrk).1.ne'
  have h := ((hasDerivAt_N r hr hα).fun_div
    ((hasDerivAt_rp r hr).fun_pow 2) (pow_ne_zero 2 hp)).const_add pK
  convert! h using 1 <;>
    try simp only [rb, rA, rG, rC, deriv_rp_eq r hr, deriv_rPhi_eq, besselB, rPhi, ru,
      Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  all_goals unfold rp at hp ⊢
  all_goals field_simp
  all_goals ring

/-- **Lemma 4.8, (4.6)**: `b_r + C G_r = -2 f_r w`. -/
theorem hasDerivAt_rb (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    HasDerivAt rb (-2 * (rw r + rA r * rf r) * rw r -
      rC r * (rb r + 2 * rA r * rG r + 2 * pK * rC r)) r := by
  have hr : r ≠ 0 := hr0.ne'
  obtain ⟨hp, -, -, -, hp', hp'', hφ'', -⟩ := radial_equations hZ r hr0 hrk
  have h := (((hp''.fun_div hp' hp.ne').const_mul pK).fun_add
    ((hasDerivAt_rG hZ hr0 hrk).fun_div (hasDerivAt_id r) hr)).fun_sub
    (((hasDerivAt_rPhi r).fun_mul hφ'').fun_div (hp'.fun_pow 2) (pow_ne_zero 2 hp.ne'))
  have hpn := hp.ne'
  convert! h using 1 <;>
    try simp only [rb, rA, rG, rC, rw, rf, deriv_rp_eq r hr, deriv_rPhi_eq, besselB, rPhi, ru,
      Pi.pow_apply, Pi.mul_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat, id, pLam_eq]
  all_goals unfold rp at hpn ⊢
  all_goals field_simp
  all_goals ring

/-! ### Proposition 4.9 (kernel identities, radial form) -/

/-- `G_t = G_r / T`. -/
noncomputable def rGt (r : ℝ) : ℝ := (rb r + 2 * rA r * rG r + 2 * pK * rC r) / rT r
/-- `b_t = b_r / T`. -/
noncomputable def rbt (r : ℝ) : ℝ :=
  (-2 * (rw r + rA r * rf r) * rw r - rC r * (rb r + 2 * rA r * rG r + 2 * pK * rC r)) / rT r

lemma rG_eq_V {r : ℝ} (hr : r ≠ 0) (hp : rp r ≠ 0) :
    rG r = r ^ 2 * (rw r ^ 2 - rC r * rf r * rw r + pLam * rf r ^ 2 -
      pK * (rA r ^ 2 + rA r * rC r + 1 - rC r ^ 2)) := by
  have h := V_identity hr hp
  rw [h]; unfold rC; field_simp; ring

lemma rg_eq (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    rg r = rf r - rt r * rz r := by
  have hS : rS r ≠ 0 := (rS_pos hZ hr0 hrk).ne'
  have hp := (radial_equations hZ r hr0 hrk).1.ne'
  unfold rg rf rt rz
  unfold rS at hS ⊢
  field_simp
  ring

/-- **Proposition 4.9 (the kernel identities)**, in the radial variable. -/
theorem kernel_identities (hZ : ExtZeros) {r : ℝ} (hr0 : 0 < r) (hrk : r < jk) :
    rb r + rGt r = -(2 * rG r - rt r * rGt r) * rA r - 2 * pK * rC r ∧
    2 * rb r - rt r * rbt r - 2 * rz r * rg r =
      -2 * (pK - rg r ^ 2) * rA r - (2 * rG r - rt r * rGt r) * rC r ∧
    -pK - rz r ^ 2 + pLam * rf r ^ 2 + rbt r =
      (pK - rg r ^ 2) * rA r ^ 2 + (2 * rG r - rt r * rGt r) * rA r * rC r +
        pK * rC r ^ 2 := by
  have hr : r ≠ 0 := hr0.ne'
  have hS : rS r ≠ 0 := (rS_pos hZ hr0 hrk).ne'
  have hp := (radial_equations hZ r hr0 hrk).1.ne'
  have hT : rp r ^ 2 + ru r * deriv rp r ≠ 0 := hS
  simp only [rGt, rbt, rb, rG_eq_V hr hp, rA, rC, rT, rS, rt, rf, rw, rz, rg]
  generalize rp r = P at *
  generalize ru r = U at *
  generalize deriv rp r = D at *
  generalize rPhi r = F at *
  generalize deriv rPhi r = F' at *
  have hT' : P ^ 2 + D * U ≠ 0 := by rwa [mul_comm D U]
  refine ⟨?_, ?_, ?_⟩
  · field_simp; ring
  · field_simp; ring
  · field_simp; ring

end Buckling
end
end ChunkedSource055
/- END SOURCE 055 -/

/- BEGIN SOURCE 056: RequestProject/Concavity/Envelope.lean -/
section ChunkedSource056

/-!
# The envelope of `B` and positivity of the residue numerators (Lemmas 8.1 and 8.4)

With `V = B + J₀²/(2x)`, `W = 2B - J₁²/x` and `E = J₀² + J₁²` one has
`V' = -J₀²/(2x²) ≤ 0`, `W' = 3J₁²/x² ≥ 0` and `E' = -2J₁²/x ≤ 0` on `(0, ∞)`.
Hence `B(x) ≤ B(q_n)` for `x ≥ q_n`, and `B(κ_n)` increases with `n`.  Combined with the
coarse numerical bounds this gives `L(κ_n) > 0` and `3L(κ_n) - φ(κ_n)φ_r(κ_n) > 0` for `n ≥ 2`.
-/

@[expose] public section

open Real Set Filter Topology

namespace Buckling

/-- `V(x) = B(x) + J₀(x)²/(2x)`. -/
noncomputable def envV (x : ℝ) : ℝ := besselB x + besselJ 0 x ^ 2 / (2 * x)
/-- `W(x) = 2B(x) - J₁(x)²/x`. -/
noncomputable def envW (x : ℝ) : ℝ := 2 * besselB x - besselJ 1 x ^ 2 / x
/-- `E(x) = J₀(x)² + J₁(x)²`. -/
noncomputable def envE (x : ℝ) : ℝ := besselJ 0 x ^ 2 + besselJ 1 x ^ 2

lemma hasDerivAt_envV {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt envV (-(besselJ 0 x ^ 2) / (2 * x ^ 2)) x := by
  have h0 := hasDerivAt_besselJ_zero x
  have h := (hasDerivAt_besselB x hx).fun_add
    ((h0.fun_pow 2).fun_div ((hasDerivAt_id x).const_mul 2) (mul_ne_zero two_ne_zero hx))
  convert! h using 1 <;>
    try simp only [envV, id, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
  all_goals field_simp [hx]
  all_goals ring

lemma hasDerivAt_envW {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt envW (3 * besselJ 1 x ^ 2 / x ^ 2) x := by
  have h1 := hasDerivAt_besselJ_one x hx
  have h := ((hasDerivAt_besselB x hx).const_mul 2).fun_sub
    ((h1.fun_pow 2).fun_div (hasDerivAt_id x) hx)
  convert! h using 1 <;>
    try simp only [envW, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  all_goals field_simp [hx]
  all_goals ring

lemma hasDerivAt_envE {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt envE (-2 * besselJ 1 x ^ 2 / x) x := by
  have h0 := hasDerivAt_besselJ_zero x
  have h1 := hasDerivAt_besselJ_one x hx
  have h := (h0.fun_pow 2).fun_add (h1.fun_pow 2)
  convert! h using 1 <;>
    try simp only [envE, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  all_goals field_simp [hx]
  all_goals ring

/-- A function with a nonpositive derivative on `(0, ∞)` is antitone there. -/
lemma antitoneOn_Ioi_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 < x → f' x ≤ 0) : AntitoneOn f (Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  · intro x hx; rw [interior_Ioi] at hx; exact (hf x hx).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Ioi] at hx; rw [(hf x hx).deriv]; exact hf' x hx

lemma monotoneOn_Ioi_of_hasDerivAt {f f' : ℝ → ℝ} (hf : ∀ x, 0 < x → HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 < x → 0 ≤ f' x) : MonotoneOn f (Ioi 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioi 0)
    (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
  · intro x hx; rw [interior_Ioi] at hx; exact (hf x hx).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Ioi] at hx; rw [(hf x hx).deriv]; exact hf' x hx

lemma envV_antitoneOn : AntitoneOn envV (Ioi 0) :=
  antitoneOn_Ioi_of_hasDerivAt (fun x hx => hasDerivAt_envV hx.ne')
    (fun x hx => by
      have : 0 < 2 * x ^ 2 := by positivity
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (besselJ 0 x)]) this.le)

lemma envW_monotoneOn : MonotoneOn envW (Ioi 0) :=
  monotoneOn_Ioi_of_hasDerivAt (fun x hx => hasDerivAt_envW hx.ne')
    (fun x hx => by positivity)

lemma envE_antitoneOn : AntitoneOn envE (Ioi 0) :=
  antitoneOn_Ioi_of_hasDerivAt (fun x hx => hasDerivAt_envE hx.ne')
    (fun x hx => div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (besselJ 1 x)]) hx.le)

lemma besselZero_pos (hZ : ExtZeros) (ν n : ℕ) (hn : 1 ≤ n) (hν : ν ≤ 1 := by norm_num) :
    0 < besselZero ν n := by
  have := (hZ ν hν).1 (show 0 < n by omega)
  simpa [besselZero] using this

/-- **Lemma 8.1 (upper envelope)**: `B(x) ≤ B(q_n)` for `x ≥ q_n`. -/
theorem besselB_le_of_ge (hZ : ExtZeros) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : besselZero 0 n ≤ x) : besselB x ≤ besselB (besselZero 0 n) := by
  have hq := besselZero_pos hZ 0 n hn
  have hx0 : 0 < x := hq.trans_le hx
  have hJ : besselJ 0 (besselZero 0 n) = 0 := ((hZ 0 (by norm_num)).2.2.1 n hn).1
  have h1 : besselB x ≤ envV x := by
    unfold envV; have : 0 ≤ besselJ 0 x ^ 2 / (2 * x) := by positivity
    linarith
  have h2 : envV x ≤ envV (besselZero 0 n) := envV_antitoneOn hq hx0 hx
  have h3 : envV (besselZero 0 n) = besselB (besselZero 0 n) := by simp [envV, hJ]
  linarith

/-- `E(x) ≤ J₁(q_n)²` for `x ≥ q_n`. -/
theorem envE_le_of_ge (hZ : ExtZeros) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : besselZero 0 n ≤ x) : envE x ≤ besselJ 1 (besselZero 0 n) ^ 2 := by
  have hq := besselZero_pos hZ 0 n hn
  have hJ : besselJ 0 (besselZero 0 n) = 0 := ((hZ 0 (by norm_num)).2.2.1 n hn).1
  have := envE_antitoneOn hq (hq.trans_le hx) hx
  simpa [envE, hJ] using this

lemma envW_besselZero_one (hZ : ExtZeros) {n : ℕ} (hn : 1 ≤ n) :
    envW (besselZero 1 n) = 2 * besselB (besselZero 1 n) := by
  have hJ : besselJ 1 (besselZero 1 n) = 0 := ((hZ 1 (by norm_num)).2.2.1 n hn).1
  simp [envW, hJ]

/-- **Lemma 8.1 (lower envelope)**: `B(κ_i) ≤ B(κ_j)` for `1 ≤ i ≤ j`. -/
theorem besselB_besselZero_one_mono (hZ : ExtZeros) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    besselB (besselZero 1 i) ≤ besselB (besselZero 1 j) := by
  have hi0 := besselZero_pos hZ 1 i hi
  have hj0 := besselZero_pos hZ 1 j (hi.trans hij)
  have := envW_monotoneOn hi0 hj0 ((hZ 1 (by norm_num)).1.monotone hij)
  rw [envW_besselZero_one hZ hi, envW_besselZero_one hZ (hi.trans hij)] at this
  linarith

/-- `J₁` has no zero strictly between `κ_n` and `κ_{n+1}`. -/
lemma besselJ_one_ne_zero_between (hZ : ExtZeros) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx1 : besselZero 1 n < x) (hx2 : x < besselZero 1 (n + 1)) : besselJ 1 x ≠ 0 := by
  intro h
  obtain ⟨hmono, -, -, hall, -⟩ := hZ 1 (by norm_num)
  obtain ⟨m, hm, hmx⟩ := hall x ((besselZero_pos hZ 1 n hn).trans hx1) h
  rw [← hmx] at hx1 hx2
  have h1 := hmono.lt_iff_lt.mp hx1
  have h2 := hmono.lt_iff_lt.mp hx2
  omega

/-- `J₀` has no zero strictly between `q_n` and `q_{n+1}`. -/
lemma besselJ_zero_ne_zero_between (hZ : ExtZeros) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx1 : besselZero 0 n < x) (hx2 : x < besselZero 0 (n + 1)) : besselJ 0 x ≠ 0 := by
  intro h
  obtain ⟨hmono, -, -, hall, -⟩ := hZ 0 (by norm_num)
  obtain ⟨m, hm, hmx⟩ := hall x ((besselZero_pos hZ 0 n hn).trans hx1) h
  rw [← hmx] at hx1 hx2
  have h1 := hmono.lt_iff_lt.mp hx1
  have h2 := hmono.lt_iff_lt.mp hx2
  omega

/-- `B(k) < B(κ₂)`. -/
theorem besselB_jk_lt (hZ : ExtZeros) : besselB jk < besselB (besselZero 1 2) := by
  have hk0 := besselZero_pos hZ 1 1 le_rfl
  have hk2 := besselZero_pos hZ 1 2 (by norm_num)
  have hlt : besselZero 1 1 < besselZero 1 2 := (hZ 1 (by norm_num)).1 (by norm_num)
  have hstrict : StrictMonoOn envW (Icc (besselZero 1 1) (besselZero 1 2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro x hx
      exact (hasDerivAt_envW (hk0.trans_le hx.1).ne').continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx0 : 0 < x := hk0.trans hx.1
      rw [(hasDerivAt_envW hx0.ne').deriv]
      have := besselJ_one_ne_zero_between hZ le_rfl hx.1 hx.2
      positivity
  have := hstrict ⟨le_rfl, hlt.le⟩ ⟨hlt.le, le_rfl⟩ hlt
  rw [envW_besselZero_one hZ le_rfl, envW_besselZero_one hZ (by norm_num)] at this
  change 2 * besselB jk < _ at this
  linarith

/-- A continuous function without zeros on an open interval keeps the sign it has at one
point. -/
lemma neg_of_no_zero {f : ℝ → ℝ} (hf : Continuous f) {a b c : ℝ} (hc : c ∈ Ioo a b)
    (hfc : f c < 0) (hz : ∀ x ∈ Ioo a b, f x ≠ 0) : ∀ x ∈ Ioo a b, f x < 0 := by
  intro x hx
  by_contra hcon
  push_neg at hcon
  rcases le_total x c with h | h
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc' h hf.continuousOn ⟨hfc.le, hcon⟩
    exact hz y ⟨hx.1.trans_le hy.1, hy.2.trans_lt hc.2⟩ hy0
  · obtain ⟨y, hy, hy0⟩ := intermediate_value_Icc h hf.continuousOn ⟨hfc.le, hcon⟩
    exact hz y ⟨hc.1.trans_le hy.1, hy.2.trans_lt hx.2⟩ hy0

/-- `L(x) = K B(x) - α B(α x)` (real). -/
noncomputable def LR (x : ℝ) : ℝ := pK * besselB x - pAlpha * besselB (pAlpha * x)

/-- **Lemma 8.4**: for `n ≥ 2`, `L(κ_n) > 0` and `3L(κ_n) - φ(κ_n) φ_r(κ_n) > 0`, where
`φ φ_r = -α J₀(ακ) J₁(ακ)`. -/
theorem residue_numerator_pos (hZ : ExtZeros) (hI : ExtIntegral) {n : ℕ} (hn : 2 ≤ n) :
    0 < LR (besselZero 1 n) ∧
      0 < 3 * LR (besselZero 1 n) +
        pAlpha * (besselJ 0 (pAlpha * besselZero 1 n) * besselJ 1 (pAlpha * besselZero 1 n)) := by
  obtain ⟨hα1, hα2, -, -, -, -, hk1, hk2, hK, hBk3, hBq2, hJq2, hord1, hord2, hord3⟩ :=
    coarse_bounds hZ hI
  obtain ⟨hq0, hqk, hα0, -, -, -, hc0, -, hK0⟩ := parameter_signs hZ
  obtain ⟨-, -, -, -, hQ1, hQ2, hK21, hK22, -, -⟩ := root_boxes hZ
  have hmono1 := (hZ 1 (by norm_num)).1
  set κ := besselZero 1 n
  have hκ2 : besselZero 1 2 ≤ κ := hmono1.monotone hn
  have hκ0 : 0 < κ := besselZero_pos hZ 1 n (by omega)
  have hBκ : besselB jk < besselB κ :=
    (besselB_jk_lt hZ).trans_le (besselB_besselZero_one_mono hZ (by norm_num) hn)
  have hendp := (besselB_endpoints hZ).2.2
  have hακq : jq ≤ pAlpha * κ := by
    have : pAlpha * besselZero 1 2 ≤ pAlpha * κ := mul_le_mul_of_nonneg_left hκ2 hα0.le
    linarith
  have hBα : besselB (pAlpha * κ) ≤ besselB jq := besselB_le_of_ge hZ le_rfl hακq
  have hL : 0 < LR κ := by
    unfold LR
    have h1 : pK * besselB jk < pK * besselB κ := mul_lt_mul_of_pos_left hBκ hK0
    have h2 : pAlpha * besselB (pAlpha * κ) ≤ pAlpha * besselB jq :=
      mul_le_mul_of_nonneg_left hBα hα0.le
    linarith
  refine ⟨hL, ?_⟩
  rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
  · -- `n = 2`: both `J₀(ακ₂)` and `J₁(ακ₂)` are negative
    have hx1 : jq < pAlpha * κ := by linarith
    have hx2 : pAlpha * κ < besselZero 0 2 := hord2
    have hJ0 : besselJ 0 (pAlpha * κ) < 0 := by
      refine neg_of_no_zero (continuous_besselJ 0) (c := jk) ⟨hqk, by linarith⟩ ?_ ?_
        (pAlpha * κ) ⟨hx1, hx2⟩
      · have := hc0; unfold pc at this; linarith
      · intro x hx; exact besselJ_zero_ne_zero_between hZ le_rfl hx.1 hx.2
    have hJ1 : besselJ 1 (pAlpha * κ) < 0 := by
      refine neg_of_no_zero (continuous_besselJ 1) (a := jk) (b := besselZero 1 2)
        (c := 55201 / 10000) ⟨by linarith, by linarith⟩ ?_ ?_ (pAlpha * κ)
        ⟨hord1, by linarith⟩
      · linarith [besselJ_bounds_row13.2]
      · intro x hx; exact besselJ_one_ne_zero_between hZ le_rfl hx.1 hx.2
    have : 0 < besselJ 0 (pAlpha * κ) * besselJ 1 (pAlpha * κ) := mul_pos_of_neg_of_neg hJ0 hJ1
    positivity
  · -- `n ≥ 3`: numerical estimate
    have hκ3 : besselZero 1 3 ≤ κ := hmono1.monotone hn3
    have hBκ3 : besselB (besselZero 1 3) ≤ besselB κ :=
      besselB_besselZero_one_mono hZ (by norm_num) hn3
    have hακq2 : besselZero 0 2 ≤ pAlpha * κ := by
      have : pAlpha * besselZero 1 3 ≤ pAlpha * κ := mul_le_mul_of_nonneg_left hκ3 hα0.le
      linarith
    have hBα2 : besselB (pAlpha * κ) ≤ besselB (besselZero 0 2) :=
      besselB_le_of_ge hZ (by norm_num) hακq2
    have hE := envE_le_of_ge hZ (by norm_num : 1 ≤ 2) hακq2
    have hprod : |besselJ 0 (pAlpha * κ) * besselJ 1 (pAlpha * κ)| ≤
        envE (pAlpha * κ) / 2 := by
      unfold envE
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg (besselJ 0 (pAlpha * κ) - besselJ 1 (pAlpha * κ)),
        sq_nonneg (besselJ 0 (pAlpha * κ) + besselJ 1 (pAlpha * κ))]
    have hp : -(116 / 1000 / 2 : ℝ) ≤ besselJ 0 (pAlpha * κ) * besselJ 1 (pAlpha * κ) := by
      have := (abs_le.mp hprod).1
      linarith
    have hBκ' : (634 / 1000 : ℝ) < besselB κ := hBk3.trans_le hBκ3
    have hBα' : besselB (pAlpha * κ) < 640 / 1000 := hBα2.trans_lt hBq2
    unfold LR
    have e1 : (654 / 1000 : ℝ) * (634 / 1000) < pK * besselB κ :=
      mul_lt_mul hK hBκ'.le (by norm_num) hK0.le
    have e2 : pAlpha * besselB (pAlpha * κ) < 628 / 1000 * (640 / 1000) := by
      rcases le_or_gt 0 (besselB (pAlpha * κ)) with hB | hB
      · calc pAlpha * besselB (pAlpha * κ) ≤ 628 / 1000 * besselB (pAlpha * κ) :=
            mul_le_mul_of_nonneg_right hα2.le hB
          _ < 628 / 1000 * (640 / 1000) := by linarith
      · have := mul_neg_of_pos_of_neg hα0 hB
        linarith
    have e3 : 628 / 1000 * -(116 / 1000 / 2) ≤
        pAlpha * (besselJ 0 (pAlpha * κ) * besselJ 1 (pAlpha * κ)) := by
      set P := besselJ 0 (pAlpha * κ) * besselJ 1 (pAlpha * κ)
      rcases le_or_gt 0 P with hP | hP
      · have := mul_nonneg hα0.le hP
        linarith
      · have h1 : 628 / 1000 * P ≤ pAlpha * P := mul_le_mul_of_nonpos_right hα2.le hP.le
        have h2 : 628 / 1000 * -(116 / 1000 / 2) ≤ 628 / 1000 * P := by linarith
        linarith
    linarith

end Buckling
end
end ChunkedSource056
/- END SOURCE 056 -/

/- BEGIN SOURCE 057: RequestProject/Concavity/GHol.lean -/
section ChunkedSource057

/-!
# The meromorphic continuation of `G` (Definition 8.2 and Lemma 8.5 of the paper)

`L(ζ) = K B(ζ) - α B(αζ)` and `G(ζ) = K - ζ L(ζ)/J₁(ζ)²`.  The points `0, ±k` are removable
singularities; we fill them (`Ghol`) and show that `Ghol` is holomorphic on every open set
containing no other zero of `J₁`.  On `(0, k)`, `Ghol` agrees with the real profile `G`.
-/

@[expose] public section

open Filter Topology Metric Set

namespace Buckling

/-! ### Complex `B`, `L` and `G` -/

/-- `B(ζ) = ζ (J₀² + J₁²) - J₀ J₁`. -/
noncomputable def besselBC (ζ : ℂ) : ℂ :=
  ζ * (besselJC 0 ζ ^ 2 + besselJC 1 ζ ^ 2) - besselJC 0 ζ * besselJC 1 ζ

/-- `L(ζ) = K B(ζ) - α B(α ζ)`. -/
noncomputable def LC (ζ : ℂ) : ℂ :=
  (pK : ℂ) * besselBC ζ - (pAlpha : ℂ) * besselBC ((pAlpha : ℂ) * ζ)

/-- `G(ζ) = K - ζ L(ζ)/J₁(ζ)²` (junk value `K` at zeros of `J₁`). -/
noncomputable def Gfun (ζ : ℂ) : ℂ := (pK : ℂ) - ζ * LC ζ / besselJC 1 ζ ^ 2

/-- The removable singularities `0, ±k` of `G`. -/
noncomputable def Gsing : Finset ℂ := {0, (jk : ℂ), -(jk : ℂ)}

/-- `G` with its removable singularities at `0, ±k` filled in. -/
noncomputable def Ghol : ℂ → ℂ := fillSing Gsing Gfun

/-! ### Derivatives -/

/-- The derivative of `J₁`. -/
noncomputable def dJ1C (ζ : ℂ) : ℂ := (besselJC 0 ζ - besselJC 2 ζ) / 2

lemma hasDerivAt_besselJC_one (ζ : ℂ) : HasDerivAt (besselJC 1) (dJ1C ζ) ζ :=
  hasDerivAt_besselJC_succ 0 ζ

lemma mul_dJ1C (ζ : ℂ) : ζ * dJ1C ζ = ζ * besselJC 0 ζ - besselJC 1 ζ := by
  unfold dJ1C
  linear_combination (-1 / 2 : ℂ) * besselJC_two_mul ζ

lemma deriv_besselJC_one (ζ : ℂ) : deriv (besselJC 1) ζ = dJ1C ζ :=
  (hasDerivAt_besselJC_one ζ).deriv

/-- The derivative of `B`. -/
noncomputable def dBC (ζ : ℂ) : ℂ :=
  (besselJC 0 ζ ^ 2 + besselJC 1 ζ ^ 2) +
    ζ * (2 * besselJC 0 ζ * (-besselJC 1 ζ) + 2 * besselJC 1 ζ * dJ1C ζ) -
    ((-besselJC 1 ζ) * besselJC 1 ζ + besselJC 0 ζ * dJ1C ζ)

lemma hasDerivAt_besselBC (ζ : ℂ) : HasDerivAt besselBC (dBC ζ) ζ := by
  have h0 := hasDerivAt_besselJC_zero ζ
  have h1 := hasDerivAt_besselJC_one ζ
  have h := ((hasDerivAt_id ζ).fun_mul
    ((h0.fun_pow 2).fun_add (h1.fun_pow 2))).fun_sub (h0.fun_mul h1)
  convert! h using 1 <;>
    try simp only [besselBC, dBC, id, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  all_goals try push_cast
  all_goals ring

/-- `ζ B'(ζ) = J₀(ζ) J₁(ζ)`. -/
lemma mul_dBC (ζ : ℂ) : ζ * dBC ζ = besselJC 0 ζ * besselJC 1 ζ := by
  unfold dBC
  linear_combination (2 * ζ * besselJC 1 ζ - besselJC 0 ζ) * mul_dJ1C ζ

lemma differentiable_besselBC : Differentiable ℂ besselBC :=
  fun ζ => (hasDerivAt_besselBC ζ).differentiableAt

/-- The derivative of `L`. -/
noncomputable def dLC (ζ : ℂ) : ℂ :=
  (pK : ℂ) * dBC ζ - (pAlpha : ℂ) * ((pAlpha : ℂ) * dBC ((pAlpha : ℂ) * ζ))

lemma hasDerivAt_LC (ζ : ℂ) : HasDerivAt LC (dLC ζ) ζ := by
  have h1 := hasDerivAt_besselBC ζ
  have h2 := (hasDerivAt_besselBC ((pAlpha : ℂ) * ζ)).comp ζ
    ((hasDerivAt_id ζ).const_mul (pAlpha : ℂ))
  have h := (h1.const_mul (pK : ℂ)).fun_sub (h2.const_mul (pAlpha : ℂ))
  convert! h using 1 <;> try simp only [LC, dLC, Function.comp_def, id, mul_one]
  all_goals ring

lemma differentiable_LC : Differentiable ℂ LC := fun ζ => (hasDerivAt_LC ζ).differentiableAt

lemma deriv_LC (ζ : ℂ) : deriv LC ζ = dLC ζ := (hasDerivAt_LC ζ).deriv

/-! ### Real values, parity -/

lemma besselBC_ofReal (x : ℝ) : besselBC (x : ℂ) = (besselB x : ℂ) := by
  simp [besselBC, besselB, besselJC_ofReal]

lemma LC_ofReal (x : ℝ) :
    LC (x : ℂ) = ((pK * besselB x - pAlpha * besselB (pAlpha * x) : ℝ) : ℂ) := by
  simp only [LC]
  rw [show (pAlpha : ℂ) * (x : ℂ) = ((pAlpha * x : ℝ) : ℂ) by push_cast; ring,
    besselBC_ofReal, besselBC_ofReal]
  push_cast; ring

lemma besselBC_neg (ζ : ℂ) : besselBC (-ζ) = -besselBC ζ := by
  simp only [besselBC, besselJC_neg]; ring

lemma LC_neg (ζ : ℂ) : LC (-ζ) = -LC ζ := by
  simp only [LC, mul_neg, besselBC_neg]; ring

lemma Gfun_neg (ζ : ℂ) : Gfun (-ζ) = Gfun ζ := by
  simp only [Gfun, LC_neg, besselJC_neg]; ring

lemma besselBC_zero : besselBC 0 = 0 := by simp [besselBC, besselJC_zero_arg]

lemma LC_zero : LC 0 = 0 := by simp [LC, besselBC_zero]

/-- On `(0, k)` (indeed wherever `J₁(r) ≠ 0`), `G` agrees with the real profile. -/
lemma Gfun_ofReal (r : ℝ) : Gfun (r : ℂ) = (rG r : ℂ) := by
  simp only [Gfun, LC_ofReal, besselJC_ofReal, rG, rp]
  push_cast
  ring

/-! ### Removable singularities -/

/-- If `f` has a double zero and `g` a simple zero at `a`, then `z f(z)/g(z)²` is bounded near
`a`. -/
lemma bdd_mul_div_sq_double {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {a : ℂ} (hfa : f a = 0) (hf'a : deriv f a = 0) (hga : g a = 0) (hg'a : deriv g a ≠ 0) :
    ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖z * f z / g z ^ 2‖ ≤ C := by
  have hu : (univ : Set ℂ) ∈ 𝓝 a := univ_mem
  have hf1 : DifferentiableOn ℂ (dslope f a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hf.differentiableOn
  have hf2 : DifferentiableOn ℂ (dslope (dslope f a) a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hf1
  have hg1 : DifferentiableOn ℂ (dslope g a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hg.differentiableOn
  have hg1a : dslope g a a ≠ 0 := by rwa [dslope_same]
  have hcont : ContinuousAt (fun z => z * dslope (dslope f a) a z / dslope g a z ^ 2) a := by
    refine (continuousAt_id.mul (hf2.differentiableAt hu).continuousAt).div
      (((hg1.differentiableAt hu).continuousAt).pow 2) (pow_ne_zero 2 hg1a)
  obtain ⟨C, hC⟩ := bdd_of_continuousAt hcont
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with z hz hza
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have e1 := sub_smul_dslope f a z
  have e2 := sub_smul_dslope (dslope f a) a z
  have e3 := sub_smul_dslope g a z
  rw [dslope_same, hf'a] at e2
  simp only [smul_eq_mul, hfa, hga, sub_zero] at e1 e2 e3
  have : z * f z / g z ^ 2 = z * dslope (dslope f a) a z / dslope g a z ^ 2 := by
    rw [← e1, ← e3, ← e2, mul_pow,
      show z * ((z - a) * ((z - a) * dslope (dslope f a) a z)) =
        (z - a) ^ 2 * (z * dslope (dslope f a) a z) by ring,
      mul_div_mul_left _ _ (pow_ne_zero 2 hza')]
  rw [this]; exact hz

/-- If `f` and `g` vanish at `a` and `g'(a) ≠ 0`, then `(z - a) f(z)/g(z)²` is bounded near `a`. -/
lemma bdd_mul_div_sq_single {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {a : ℂ} (hfa : f a = 0) (hga : g a = 0) (hg'a : deriv g a ≠ 0) :
    ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖(z - a) * f z / g z ^ 2‖ ≤ C := by
  have hu : (univ : Set ℂ) ∈ 𝓝 a := univ_mem
  have hf1 : DifferentiableOn ℂ (dslope f a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hf.differentiableOn
  have hg1 : DifferentiableOn ℂ (dslope g a) univ :=
    (Complex.differentiableOn_dslope hu).mpr hg.differentiableOn
  have hg1a : dslope g a a ≠ 0 := by rwa [dslope_same]
  have hcont : ContinuousAt (fun z => dslope f a z / dslope g a z ^ 2) a :=
    ((hf1.differentiableAt hu).continuousAt).div
      (((hg1.differentiableAt hu).continuousAt).pow 2) (pow_ne_zero 2 hg1a)
  obtain ⟨C, hC⟩ := bdd_of_continuousAt hcont
  refine ⟨C, ?_⟩
  filter_upwards [hC, self_mem_nhdsWithin] with z hz hza
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have e1 := sub_smul_dslope f a z
  have e3 := sub_smul_dslope g a z
  simp only [smul_eq_mul, hfa, hga, sub_zero] at e1 e3
  have : (z - a) * f z / g z ^ 2 = dslope f a z / dslope g a z ^ 2 := by
    rw [← e1, ← e3, mul_pow, ← mul_assoc, ← sq, mul_div_mul_left _ _ (pow_ne_zero 2 hza')]
  rw [this]; exact hz

/-! ### Values at the zeros of `J₁` -/

lemma besselJC_one_jk (hZ : ExtZeros) : besselJC 1 (jk : ℂ) = 0 := by
  rw [besselJC_ofReal, besselJ_one_jk hZ, Complex.ofReal_zero]

lemma besselJC_one_neg_jk (hZ : ExtZeros) : besselJC 1 (-(jk : ℂ)) = 0 := by
  rw [besselJC_neg, besselJC_one_jk hZ, mul_zero]

/-- At a nonzero zero of `J₁`, `J₁' = J₀`. -/
lemma deriv_besselJC_one_of_zero {a : ℂ} (ha : a ≠ 0) (h : besselJC 1 a = 0) :
    deriv (besselJC 1) a = besselJC 0 a := by
  rw [deriv_besselJC_one]
  have := mul_dJ1C a
  rw [h, sub_zero] at this
  exact mul_left_cancel₀ ha this

lemma jk_ne_zero (hZ : ExtZeros) : (jk : ℂ) ≠ 0 := by
  exact_mod_cast (jk_pos hZ).ne'

lemma besselJC_zero_jk : besselJC 0 (jk : ℂ) = ((-pc : ℝ) : ℂ) := by
  rw [besselJC_ofReal]; simp [pc]

lemma besselJC_zero_neg_jk : besselJC 0 (-(jk : ℂ)) = ((-pc : ℝ) : ℂ) := by
  rw [besselJC_neg, besselJC_zero_jk]; simp

lemma pAlpha_mul_jk (hZ : ExtZeros) : pAlpha * jk = jq := by
  unfold pAlpha; field_simp [(jk_pos hZ).ne']

lemma besselJC_zero_jq (hZ : ExtZeros) : besselJC 0 (jq : ℂ) = 0 := by
  have h : besselJ 0 jq = 0 := ((hZ 0 (by norm_num)).2.2.1 1 le_rfl).1
  rw [besselJC_ofReal, h, Complex.ofReal_zero]

/-- `B'(a) = 0` at a nonzero zero of `J₀ J₁`. -/
lemma dBC_eq_zero {a : ℂ} (ha : a ≠ 0) (h : besselJC 0 a * besselJC 1 a = 0) : dBC a = 0 := by
  have := mul_dBC a
  rw [h] at this
  exact (mul_eq_zero.mp this).resolve_left ha

lemma LC_jk (hZ : ExtZeros) : LC (jk : ℂ) = 0 := by
  rw [LC_ofReal, pAlpha_mul_jk hZ, (besselB_endpoints hZ).2.2, sub_self, Complex.ofReal_zero]

lemma LC_neg_jk (hZ : ExtZeros) : LC (-(jk : ℂ)) = 0 := by rw [LC_neg, LC_jk hZ, neg_zero]

lemma dLC_jk (hZ : ExtZeros) : dLC (jk : ℂ) = 0 := by
  have hq : (jq : ℂ) ≠ 0 := by exact_mod_cast (parameter_signs hZ).1.ne'
  have hαk : (pAlpha : ℂ) * (jk : ℂ) = (jq : ℂ) := by exact_mod_cast pAlpha_mul_jk hZ
  unfold dLC
  rw [hαk, dBC_eq_zero (jk_ne_zero hZ) (by rw [besselJC_one_jk hZ, mul_zero]),
    dBC_eq_zero hq (by rw [besselJC_zero_jq hZ, zero_mul])]
  ring

lemma dLC_neg_jk (hZ : ExtZeros) : dLC (-(jk : ℂ)) = 0 := by
  have hq : -(jq : ℂ) ≠ 0 := by
    rw [neg_ne_zero]; exact_mod_cast (parameter_signs hZ).1.ne'
  have hαk : (pAlpha : ℂ) * -(jk : ℂ) = -(jq : ℂ) := by
    rw [mul_neg]; exact_mod_cast congrArg Neg.neg (pAlpha_mul_jk hZ)
  have hk : -(jk : ℂ) ≠ 0 := neg_ne_zero.mpr (jk_ne_zero hZ)
  unfold dLC
  rw [hαk, dBC_eq_zero hk (by rw [besselJC_one_neg_jk hZ, mul_zero]),
    dBC_eq_zero hq (by rw [besselJC_neg, besselJC_zero_jq hZ]; ring)]
  ring

/-! ### Holomorphy of `Ghol` -/

lemma differentiableAt_Gfun {z : ℂ} (hz : besselJC 1 z ≠ 0) : DifferentiableAt ℂ Gfun z := by
  unfold Gfun
  exact (differentiableAt_const _).sub ((differentiableAt_id.mul (differentiable_LC z)).div
    ((differentiable_besselJC 1 z).pow 2) (pow_ne_zero 2 hz))

/-- `G` is bounded near each of its removable singularities `0, ±k`. -/
lemma Gfun_bdd (hZ : ExtZeros) : ∀ a ∈ Gsing, ∃ C, ∀ᶠ z in 𝓝[≠] a, ‖Gfun z‖ ≤ C := by
  have hK : ∀ C : ℝ, (∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z * LC z / besselJC 1 z ^ 2‖ ≤ C) →
      ∀ a, (∀ᶠ z in 𝓝[≠] a, ‖z * LC z / besselJC 1 z ^ 2‖ ≤ C) →
      ∃ C', ∀ᶠ z in 𝓝[≠] a, ‖Gfun z‖ ≤ C' := by
    intro C _ a ha
    refine ⟨‖(pK : ℂ)‖ + C, ha.mono fun z hz => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hz)
  have hJ : ∀ a : ℂ, a ≠ 0 → besselJC 1 a = 0 → besselJC 0 a ≠ 0 →
      deriv (besselJC 1) a ≠ 0 := by
    intro a ha h h0; rwa [deriv_besselJC_one_of_zero ha h]
  have hc : ((-pc : ℝ) : ℂ) ≠ 0 := by
    have := (parameter_signs hZ).2.2.2.2.2.2.1
    exact_mod_cast (neg_ne_zero.mpr this.ne')
  intro a ha
  simp only [Gsing, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · -- at `0`
    have hd : deriv (besselJC 1) 0 ≠ 0 := by
      rw [deriv_besselJC_one]; simp [dJ1C, besselJC_zero_arg]
    obtain ⟨C, hC⟩ := bdd_mul_div_sq_single differentiable_LC (differentiable_besselJC 1)
      LC_zero (by simp [besselJC_zero_arg]) hd
    refine ⟨‖(pK : ℂ)‖ + C, hC.mono fun z hz => ?_⟩
    rw [sub_zero] at hz
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hz)
  · obtain ⟨C, hC⟩ := bdd_mul_div_sq_double differentiable_LC (differentiable_besselJC 1)
      (LC_jk hZ) (by rw [deriv_LC, dLC_jk hZ]) (besselJC_one_jk hZ)
      (hJ _ (jk_ne_zero hZ) (besselJC_one_jk hZ) (by rw [besselJC_zero_jk]; exact hc))
    refine ⟨‖(pK : ℂ)‖ + C, hC.mono fun z hz => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hz)
  · obtain ⟨C, hC⟩ := bdd_mul_div_sq_double differentiable_LC (differentiable_besselJC 1)
      (LC_neg_jk hZ) (by rw [deriv_LC, dLC_neg_jk hZ]) (besselJC_one_neg_jk hZ)
      (hJ _ (neg_ne_zero.mpr (jk_ne_zero hZ)) (besselJC_one_neg_jk hZ)
        (by rw [besselJC_zero_neg_jk]; exact hc))
    refine ⟨‖(pK : ℂ)‖ + C, hC.mono fun z hz => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hz)

/-- **Lemma 8.5**: `Ghol` is holomorphic on every open set on which the only zeros of `J₁` are
among `0, ±k`. -/
theorem differentiableOn_Ghol (hZ : ExtZeros) {U : Set ℂ} (hU : IsOpen U)
    (hzeros : ∀ z ∈ U, besselJC 1 z = 0 → z ∈ Gsing) : DifferentiableOn ℂ Ghol U := by
  refine differentiableOn_fillSing hU Gsing ?_ (fun a ha _ => Gfun_bdd hZ a ha)
  intro z hz
  refine (differentiableAt_Gfun fun h => hz.2 ?_).differentiableWithinAt
  exact hzeros z hz.1 h

lemma Ghol_of_notMem {z : ℂ} (hz : z ∉ Gsing) : Ghol z = Gfun z := fillSing_of_notMem hz

end Buckling
end
end ChunkedSource057
/- END SOURCE 057 -/

/- BEGIN SOURCE 058: RequestProject/Concavity/Circles.lean -/
section ChunkedSource058

/-!
# Pole-free circles (Lemma 8.7 of the paper)

On the circles `|ζ| = R_N = (N + 3/4)π`, for `N` large, `J₁` has no zero and
`|G(ζ)| ≤ C R_N²`.  The proof uses the large-argument asymptotics (External theorem E4):
it gives `|J_ν(ζ)| ≤ C e^{|Im ζ|}/√|ζ|` for `|ζ|` large, and on the circles
`|cos(ζ - 3π/4)| ≥ e^{|Im ζ|}/6`, whence `|J₁(ζ)| ≥ c e^{|Im ζ|}/√|ζ|`.
-/

@[expose] public section

open Filter Topology Metric Set Real

namespace Buckling

/-! ### Elementary estimates for the complex cosine -/

lemma cos_re' (w : ℂ) : (Complex.cos w).re = Real.cos w.re * Real.cosh w.im := by
  conv_lhs => rw [← Complex.re_add_im w]
  rw [Complex.cos_add_mul_I]
  simp [← Complex.ofReal_cosh, ← Complex.ofReal_sinh, ← Complex.ofReal_sin, ← Complex.ofReal_cos]

lemma norm_cos_le_exp (w : ℂ) : ‖Complex.cos w‖ ≤ Real.exp |w.im| := by
  have h : Complex.cos w = (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2 := rfl
  rw [h, norm_div, Complex.norm_two]
  have h1 : ‖Complex.exp (w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact neg_le_abs _
  have h2 : ‖Complex.exp (-w * Complex.I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; exact le_abs_self _
  have := norm_add_le (Complex.exp (w * Complex.I)) (Complex.exp (-w * Complex.I))
  linarith

lemma norm_cos_ge_sinh (w : ℂ) :
    (Real.exp |w.im| - Real.exp (-|w.im|)) / 2 ≤ ‖Complex.cos w‖ := by
  have h : Complex.cos w = (Complex.exp (w * Complex.I) + Complex.exp (-w * Complex.I)) / 2 := rfl
  rw [h, norm_div, Complex.norm_two]
  have e1 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp (w.im) := by rw [Complex.norm_exp]; simp
  have h1 := norm_sub_norm_le (Complex.exp (-w * Complex.I)) (-Complex.exp (w * Complex.I))
  have h2 := norm_sub_norm_le (Complex.exp (w * Complex.I)) (-Complex.exp (-w * Complex.I))
  rw [norm_neg, sub_neg_eq_add] at h1 h2
  rw [e1, e2] at h1 h2
  rw [add_comm] at h1
  gcongr
  rcases abs_cases w.im with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> simp at h1 h2 ⊢ <;> linarith

lemma norm_sqrt_factor {ζ : ℂ} (hζ : ζ ≠ 0) :
    ‖((π : ℂ) * ζ / 2) ^ (1 / 2 : ℂ)‖ = Real.sqrt (π / 2) * Real.sqrt ‖ζ‖ := by
  have hne : (π : ℂ) * ζ / 2 ≠ 0 := by simp [hζ, Real.pi_ne_zero]
  rw [Complex.norm_cpow_of_ne_zero hne]
  have h1 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have h2 : (1 / 2 : ℂ).im = 0 := by norm_num
  rw [h1, h2, mul_zero, Real.exp_zero, div_one, ← Real.sqrt_mul (by positivity),
    Real.sqrt_eq_rpow]
  congr 1
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_two, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  ring

/-- On the circle `|z| = (N + 3/4)π` with `Re z ≥ 0`: `|cos(z - 3π/4)| ≥ e^{|Im z|}/6`. -/
lemma norm_cos_circle {N : ℕ} (hN : 1 ≤ N) {z : ℂ} (hre : 0 ≤ z.re)
    (hz : ‖z‖ = ((N : ℝ) + 3 / 4) * π) :
    Real.exp |z.im| / 6 ≤ ‖Complex.cos (z - (π : ℂ) / 2 - (π : ℂ) / 4)‖ := by
  set w := z - (π : ℂ) / 2 - (π : ℂ) / 4 with hw
  have hwim : w.im = z.im := by simp [w]
  have hwre : w.re = z.re - 3 * π / 4 := by simp [w]; ring
  set b := z.im
  rcases le_or_gt 1 |b| with hb | hb
  · have h := norm_cos_ge_sinh w
    rw [hwim] at h
    have h1 : 2 ≤ Real.exp |b| := by linarith [Real.add_one_le_exp |b|]
    have h2 : Real.exp (-|b|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg b])
    linarith
  · set R := ((N : ℝ) + 3 / 4) * π with hRdef
    have hpi := Real.pi_gt_three
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hR1 : 1 ≤ R := by rw [hRdef]; nlinarith
    have hsq : z.re ^ 2 + b ^ 2 = R ^ 2 := by
      rw [← hz, Complex.sq_norm, Complex.normSq_apply]; ring
    have hxle : z.re ≤ R := hz ▸ Complex.re_le_norm z
    have hδ0 : 0 ≤ R - z.re := sub_nonneg.mpr hxle
    have hb2 : b ^ 2 < 1 := by
      have := sq_abs b
      nlinarith [abs_nonneg b]
    have hδ1 : R - z.re ≤ 1 := by
      have : (R - z.re) * (R + z.re) = b ^ 2 := by nlinarith
      nlinarith
    have hre' : w.re = N * π - (R - z.re) := by rw [hwre, hRdef]; ring
    have hc : |Real.cos w.re| = Real.cos (R - z.re) := by
      rw [hre', Real.cos_nat_mul_pi_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩)
    have hcδ : 1 / 2 ≤ Real.cos (R - z.re) := by
      have := Real.one_sub_sq_div_two_le_cos (x := R - z.re)
      nlinarith
    have hnorm : |Real.cos w.re| ≤ ‖Complex.cos w‖ := by
      have := Complex.abs_re_le_norm (Complex.cos w)
      rw [cos_re', abs_mul, abs_of_pos (Real.cosh_pos _)] at this
      nlinarith [Real.one_le_cosh w.im, abs_nonneg (Real.cos w.re)]
    have he : Real.exp |b| ≤ 3 := by
      have h1 := Real.exp_one_lt_d9
      have h2 : Real.exp |b| ≤ Real.exp 1 := Real.exp_le_exp.mpr hb.le
      norm_num at h1; linarith
    linarith

/-! ### Bounds for `J₀`, `J₁` -/

/-- Upper bound `|J_ν(ζ)| ≤ C e^{|Im ζ|}/√|ζ|` for `|ζ|` large (`ν ≤ 1`). -/
theorem besselJC_upper (hA : ExtAsymptotic) {ν : ℕ} (hν : ν ≤ 1) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ ζ : ℂ, R ≤ ‖ζ‖ →
      ‖besselJC ν ζ‖ ≤ C * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ := by
  obtain ⟨C, R, hC, hR, h⟩ := hA ν hν
  have hs : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨(1 + C / R) / Real.sqrt (π / 2), R, by positivity, hR, ?_⟩
  have key : ∀ ζ : ℂ, R ≤ ‖ζ‖ → 0 ≤ ζ.re → ‖besselJC ν ζ‖ ≤
      (1 + C / R) / Real.sqrt (π / 2) * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ := by
    intro ζ hζ hre
    have hζ0 : 0 < ‖ζ‖ := hR.trans_le hζ
    have hne : ζ ≠ 0 := norm_pos_iff.mp hζ0
    have hb := h ζ hζ (Complex.abs_arg_le_pi_div_two_iff.mpr hre)
    have hcos := norm_cos_le_exp (ζ - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4)
    have him : (ζ - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4).im = ζ.im := by simp
    rw [him] at hcos
    have htri := norm_sub_norm_le (((π : ℂ) * ζ / 2) ^ (1 / 2 : ℂ) * besselJC ν ζ)
      (Complex.cos (ζ - (ν : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4))
    rw [norm_mul, norm_sqrt_factor hne] at htri
    have h3 : C * Real.exp |ζ.im| / ‖ζ‖ ≤ C * Real.exp |ζ.im| / R :=
      div_le_div_of_nonneg_left (by positivity) hR hζ
    have h4 : C * Real.exp |ζ.im| / R = C / R * Real.exp |ζ.im| := by ring
    have hsz : 0 < Real.sqrt ‖ζ‖ := Real.sqrt_pos.mpr hζ0
    have hmain : Real.sqrt (π / 2) * Real.sqrt ‖ζ‖ * ‖besselJC ν ζ‖ ≤
        (1 + C / R) * Real.exp |ζ.im| := by nlinarith
    rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
    nlinarith
  intro ζ hζ
  rcases le_or_gt 0 ζ.re with hre | hre
  · exact key ζ hζ hre
  · have := key (-ζ) (by rwa [norm_neg]) (by simp; linarith)
    rwa [besselJC_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.neg_im,
      abs_neg, norm_neg] at this

/-- Lower bound `|J₁(ζ)| ≥ c e^{|Im ζ|}/√|ζ|` on the circles `|ζ| = (N + 3/4)π`, `N` large. -/
theorem besselJC_one_lower (hA : ExtAsymptotic) :
    ∃ c : ℝ, ∃ N0 : ℕ, 0 < c ∧ ∀ N : ℕ, N0 ≤ N → ∀ z : ℂ, ‖z‖ = ((N : ℝ) + 3 / 4) * π →
      c * Real.exp |z.im| / Real.sqrt ‖z‖ ≤ ‖besselJC 1 z‖ := by
  obtain ⟨C, R, hC, hR, h⟩ := hA 1 le_rfl
  have hs : 0 < Real.sqrt (π / 2) := Real.sqrt_pos.mpr (by positivity)
  set T := max (max R (12 * C)) 1 with hT
  refine ⟨1 / (12 * Real.sqrt (π / 2)), ⌈T⌉₊ + 1, by positivity, ?_⟩
  intro N hN
  have hNR : T ≤ ((N : ℝ) + 3 / 4) * π := by
    have h1 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈T⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast hN
    have := Real.pi_gt_three
    have hT1 : 1 ≤ T := le_max_right _ _
    nlinarith
  have hN1 : 1 ≤ N := by omega
  have key : ∀ z : ℂ, ‖z‖ = ((N : ℝ) + 3 / 4) * π → 0 ≤ z.re →
      1 / (12 * Real.sqrt (π / 2)) * Real.exp |z.im| / Real.sqrt ‖z‖ ≤ ‖besselJC 1 z‖ := by
    intro z hz hre
    have hRz : R ≤ ‖z‖ := by rw [hz]; exact (le_max_left _ _).trans ((le_max_left _ _).trans hNR)
    have hCz : 12 * C ≤ ‖z‖ := by
      rw [hz]; exact (le_max_right _ _).trans ((le_max_left _ _).trans hNR)
    have hz0 : 0 < ‖z‖ := hR.trans_le hRz
    have hne : z ≠ 0 := norm_pos_iff.mp hz0
    have hb := h z hRz (Complex.abs_arg_le_pi_div_two_iff.mpr hre)
    have hcos := norm_cos_circle hN1 hre hz
    have harg : z - ((1 : ℕ) : ℂ) * (π : ℂ) / 2 - (π : ℂ) / 4 = z - (π : ℂ) / 2 - (π : ℂ) / 4 := by
      push_cast; ring
    rw [harg] at hb
    have htri := norm_sub_norm_le (Complex.cos (z - (π : ℂ) / 2 - (π : ℂ) / 4))
      (((π : ℂ) * z / 2) ^ (1 / 2 : ℂ) * besselJC 1 z)
    rw [norm_sub_rev, norm_mul (((π : ℂ) * z / 2) ^ (1 / 2 : ℂ)), norm_sqrt_factor hne] at htri
    have h3 : C * Real.exp |z.im| / ‖z‖ ≤ Real.exp |z.im| / 12 := by
      rw [div_le_iff₀ hz0]
      have := Real.exp_pos |z.im|
      nlinarith
    have hmain : Real.exp |z.im| / 12 ≤ Real.sqrt (π / 2) * Real.sqrt ‖z‖ * ‖besselJC 1 z‖ := by
      linarith
    have hsz : 0 < Real.sqrt ‖z‖ := Real.sqrt_pos.mpr hz0
    calc 1 / (12 * Real.sqrt (π / 2)) * Real.exp |z.im| / Real.sqrt ‖z‖
        = (Real.exp |z.im| / 12) / (Real.sqrt (π / 2) * Real.sqrt ‖z‖) := by
          field_simp
      _ ≤ ‖besselJC 1 z‖ := by
          rw [div_le_iff₀ (by positivity)]; linarith
  intro z hz
  rcases le_or_gt 0 z.re with hre | hre
  · exact key z hz hre
  · have := key (-z) (by rwa [norm_neg]) (by simp; linarith)
    simpa only [besselJC_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
      Complex.neg_im, abs_neg] using this

/-! ### The circle bound -/

/-- `|B(ζ)| ≤ 3 C² e^{2|Im ζ|}` for `|ζ|` large. -/
lemma besselBC_bound {C R : ℝ} (hC : 0 < C) (hR : 0 < R)
    (h0 : ∀ ζ : ℂ, R ≤ ‖ζ‖ → ‖besselJC 0 ζ‖ ≤ C * Real.exp |ζ.im| / Real.sqrt ‖ζ‖)
    (h1 : ∀ ζ : ℂ, R ≤ ‖ζ‖ → ‖besselJC 1 ζ‖ ≤ C * Real.exp |ζ.im| / Real.sqrt ‖ζ‖)
    {ζ : ℂ} (hζ : max R 1 ≤ ‖ζ‖) :
    ‖besselBC ζ‖ ≤ 3 * C ^ 2 * Real.exp |ζ.im| ^ 2 := by
  have hRz : R ≤ ‖ζ‖ := (le_max_left _ _).trans hζ
  have h1z : 1 ≤ ‖ζ‖ := (le_max_right _ _).trans hζ
  have hz0 : 0 < ‖ζ‖ := by linarith
  set M := C * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ with hM
  have hM0 : 0 ≤ M := by positivity
  have hM2 : M ^ 2 * ‖ζ‖ = C ^ 2 * Real.exp |ζ.im| ^ 2 := by
    rw [hM, div_pow, Real.sq_sqrt hz0.le]; field_simp
  have hJ0 := h0 ζ hRz
  have hJ1 := h1 ζ hRz
  have hn : ‖besselBC ζ‖ ≤ ‖ζ‖ * (‖besselJC 0 ζ‖ ^ 2 + ‖besselJC 1 ζ‖ ^ 2) +
      ‖besselJC 0 ζ‖ * ‖besselJC 1 ζ‖ := by
    unfold besselBC
    calc _ ≤ ‖ζ * (besselJC 0 ζ ^ 2 + besselJC 1 ζ ^ 2)‖ + ‖besselJC 0 ζ * besselJC 1 ζ‖ :=
          norm_sub_le _ _
      _ ≤ _ := by
          rw [norm_mul, norm_mul]
          gcongr
          calc _ ≤ ‖besselJC 0 ζ ^ 2‖ + ‖besselJC 1 ζ ^ 2‖ := norm_add_le _ _
            _ = _ := by rw [norm_pow, norm_pow]
  have hA : ‖besselJC 0 ζ‖ ^ 2 + ‖besselJC 1 ζ‖ ^ 2 ≤ 2 * M ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hJ0 2
    have := pow_le_pow_left₀ (norm_nonneg _) hJ1 2
    linarith
  have hB : ‖besselJC 0 ζ‖ * ‖besselJC 1 ζ‖ ≤ M ^ 2 := by
    rw [sq]; exact mul_le_mul hJ0 hJ1 (norm_nonneg _) hM0
  have hM2' : M ^ 2 ≤ C ^ 2 * Real.exp |ζ.im| ^ 2 := by
    rw [← hM2]; nlinarith [sq_nonneg M]
  nlinarith

/-- **Lemma 8.7.** -/
theorem circle_bound (hZ : ExtZeros) (hA : ExtAsymptotic) :
    ∃ C : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ z : ℂ, ‖z‖ = ((N : ℝ) + 3 / 4) * π →
      besselJC 1 z ≠ 0 ∧ ‖Gfun z‖ ≤ C * (((N : ℝ) + 3 / 4) * π) ^ 2 := by
  obtain ⟨c, N1, hc, hlow⟩ := besselJC_one_lower hA
  obtain ⟨C0, R0, hC0, hR0, h0⟩ := besselJC_upper hA (ν := 0) (by norm_num)
  obtain ⟨C1, R1, hC1, hR1, h1⟩ := besselJC_upper hA (ν := 1) le_rfl
  obtain ⟨-, -, hα0, hα1, -, -, -, -, hK⟩ := parameter_signs hZ
  set C2 := max C0 C1
  set R2 := max R0 R1
  have hC2 : 0 < C2 := lt_max_of_lt_left hC0
  have hR2 : 0 < R2 := lt_max_of_lt_left hR0
  have h0' : ∀ ζ : ℂ, R2 ≤ ‖ζ‖ → ‖besselJC 0 ζ‖ ≤ C2 * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ :=
    fun ζ hζ => (h0 ζ ((le_max_left _ _).trans hζ)).trans (by gcongr; exact le_max_left _ _)
  have h1' : ∀ ζ : ℂ, R2 ≤ ‖ζ‖ → ‖besselJC 1 ζ‖ ≤ C2 * Real.exp |ζ.im| / Real.sqrt ‖ζ‖ :=
    fun ζ hζ => (h1 ζ ((le_max_right _ _).trans hζ)).trans (by gcongr; exact le_max_right _ _)
  set T := max R2 1
  refine ⟨pK + 3 * (pK + pAlpha) * C2 ^ 2 / c ^ 2, max N1 (⌈T / pAlpha⌉₊ + 1), ?_⟩
  intro N hN z hz
  set R := ((N : ℝ) + 3 / 4) * π with hRdef
  have hpi := Real.pi_gt_three
  have hNT : T / pAlpha + 1 ≤ N := by
    have h1 : T / pAlpha ≤ (⌈T / pAlpha⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈T / pAlpha⌉₊ : ℝ) + 1 ≤ N := by exact_mod_cast (le_max_right _ _).trans hN
    linarith
  have hT1 : 1 ≤ T := le_max_right _ _
  have hTα : T / pAlpha ≥ T := by rw [ge_iff_le, le_div_iff₀ hα0]; nlinarith
  have hNR : (N : ℝ) ≤ R := by rw [hRdef]; nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hz0 : 0 < ‖z‖ := by rw [hz]; exact hR0
  -- the lower bound for `J₁`
  have hl := hlow N ((le_max_left _ _).trans hN) z hz
  set E := Real.exp |z.im| with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hJ1pos : 0 < ‖besselJC 1 z‖ := lt_of_lt_of_le (by positivity) hl
  refine ⟨norm_pos_iff.mp hJ1pos, ?_⟩
  -- bounds for `B(z)` and `B(αz)`
  have hzT : max R2 1 ≤ ‖z‖ := by rw [hz]; linarith
  have hαz : max R2 1 ≤ ‖(pAlpha : ℂ) * z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hα0, hz]
    have : T ≤ pAlpha * N := by
      have := (div_le_iff₀' hα0).mp (by linarith : T / pAlpha ≤ N)
      linarith
    nlinarith
  have hBz := besselBC_bound hC2 hR2 h0' h1' hzT
  have hBαz := besselBC_bound hC2 hR2 h0' h1' hαz
  have him : |((pAlpha : ℂ) * z).im| ≤ |z.im| := by
    rw [Complex.im_ofReal_mul, abs_mul, abs_of_pos hα0]
    nlinarith [abs_nonneg z.im]
  have hEα : Real.exp |((pAlpha : ℂ) * z).im| ^ 2 ≤ E ^ 2 := by
    gcongr
    exact Real.exp_le_exp.mpr him
  have hL : ‖LC z‖ ≤ 3 * (pK + pAlpha) * C2 ^ 2 * E ^ 2 := by
    unfold LC
    calc _ ≤ ‖(pK : ℂ) * besselBC z‖ + ‖(pAlpha : ℂ) * besselBC ((pAlpha : ℂ) * z)‖ :=
          norm_sub_le _ _
      _ = pK * ‖besselBC z‖ + pAlpha * ‖besselBC ((pAlpha : ℂ) * z)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos hK, abs_of_pos hα0]
      _ ≤ pK * (3 * C2 ^ 2 * E ^ 2) + pAlpha * (3 * C2 ^ 2 * E ^ 2) := by
          gcongr
          exact hBαz.trans (by gcongr)
      _ = _ := by ring
  -- `|J₁|² ≥ c² E²/R`
  have hJ2 : c ^ 2 * E ^ 2 / R ≤ ‖besselJC 1 z‖ ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hl 2
    rw [div_pow, mul_pow, Real.sq_sqrt hz0.le, hz] at this
    exact this
  have hfrac : ‖z * LC z / besselJC 1 z ^ 2‖ ≤ 3 * (pK + pAlpha) * C2 ^ 2 / c ^ 2 * R ^ 2 := by
    rw [norm_div, norm_mul, norm_pow, hz, div_le_iff₀ (by positivity)]
    calc R * ‖LC z‖ ≤ R * (3 * (pK + pAlpha) * C2 ^ 2 * E ^ 2) := by gcongr
      _ = 3 * (pK + pAlpha) * C2 ^ 2 / c ^ 2 * R ^ 2 * (c ^ 2 * E ^ 2 / R) := by
          field_simp
      _ ≤ _ := by gcongr
  unfold Gfun
  calc ‖(pK : ℂ) - z * LC z / besselJC 1 z ^ 2‖
      ≤ ‖(pK : ℂ)‖ + ‖z * LC z / besselJC 1 z ^ 2‖ := norm_sub_le _ _
    _ ≤ pK * R ^ 2 + 3 * (pK + pAlpha) * C2 ^ 2 / c ^ 2 * R ^ 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hK]
        have hR2' : 1 ≤ R ^ 2 := by nlinarith
        exact add_le_add (le_mul_of_one_le_right hK.le hR2') hfrac
    _ = _ := by ring

end Buckling
end
end ChunkedSource058
/- END SOURCE 058 -/

/- BEGIN SOURCE 059: RequestProject/Concavity/Poles.lean -/
section ChunkedSource059

/-!
# Principal parts of `G(ζ)/ζ^{2m+1}` at the poles (Lemma 8.8 of the paper)

At a nonzero zero `a` of `J₁` other than `±k`, write `J₁(ζ) = (ζ - a) F(ζ)`.  Then
`G(ζ)/ζ^{2m+1} = K/ζ^{2m+1} - Φ(ζ)/(ζ - a)²` with `Φ = L/(ζ^{2m} F²)` holomorphic near `a`,
and the residue is
`-Φ'(a) = ((2m - 1) L(a) - a L'(a)) / (a^{2m+1} J₀(a)²)`.
-/

@[expose] public section

open Filter Topology Metric Set

namespace Buckling

/-- For an entire `f`, the derivative of `dslope f a` at `a` is `f''(a)/2`. -/
lemma deriv_dslope_same {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    deriv (dslope f a) a = deriv (deriv f) a / 2 := by
  have hu : (univ : Set ℂ) ∈ 𝓝 a := univ_mem
  have hF : Differentiable ℂ (dslope f a) := fun z =>
    (((Complex.differentiableOn_dslope (c := a) univ_mem).mpr hf.differentiableOn) z
      (mem_univ z)).differentiableAt univ_mem
  have hF' : Differentiable ℂ (deriv (dslope f a)) := fun z =>
    ((hF.differentiableOn.deriv isOpen_univ) z (mem_univ z)).differentiableAt univ_mem
  have hfeq : f = fun z => f a + (z - a) * dslope f a z := by
    funext z
    have := sub_smul_dslope f a z
    rw [smul_eq_mul] at this
    linear_combination -this
  have hd : deriv f = fun z => dslope f a z + (z - a) * deriv (dslope f a) z := by
    funext z
    have h1 : HasDerivAt (fun z => f a + (z - a) * dslope f a z)
        (1 * dslope f a z + (z - a) * deriv (dslope f a) z) z :=
      (((hasDerivAt_id z).sub_const a).mul (hF z).hasDerivAt).const_add (f a)
    have := h1.deriv
    rw [← hfeq] at this
    rw [this]; ring
  have h2 : HasDerivAt (fun z => dslope f a z + (z - a) * deriv (dslope f a) z)
      (deriv (dslope f a) a + (1 * deriv (dslope f a) a + (a - a) * deriv (deriv (dslope f a)) a))
      a :=
    (hF a).hasDerivAt.add (((hasDerivAt_id a).sub_const a).mul (hF' a).hasDerivAt)
  rw [hd, h2.deriv]; ring

/-- `J₁''(a) = -J₀(a)/a` at a nonzero zero `a` of `J₁`. -/
lemma deriv_deriv_besselJC_one {a : ℂ} (ha : a ≠ 0) (h : besselJC 1 a = 0) :
    deriv (deriv (besselJC 1)) a = -besselJC 0 a / a := by
  have hd : deriv (besselJC 1) = dJ1C := funext deriv_besselJC_one
  have h2 := hasDerivAt_besselJC_succ 1 a
  have h0 := hasDerivAt_besselJC_zero a
  have hdd : HasDerivAt dJ1C ((-besselJC 1 a - (besselJC 1 a - besselJC 3 a) / 2) / 2) a := by
    have := (h0.sub h2).div_const 2
    exact this
  rw [hd, hdd.deriv]
  have r1 := besselJC_recurrence 1 a
  have r0 := besselJC_two_mul a
  rw [h] at r1 r0
  push_cast at r1
  have hJ2 : besselJC 2 a = -besselJC 0 a := mul_left_cancel₀ ha (by rw [r0]; ring)
  rw [h]
  field_simp
  linear_combination r1 + 4 * hJ2

/-- The residue of `G(ζ)/ζ^{2m+1}` at a nonzero zero `a ≠ ±k` of `J₁`. -/
noncomputable def residG (m : ℕ) (a : ℂ) : ℂ :=
  ((2 * m - 1) * LC a - a * dLC a) / (a ^ (2 * m + 1) * besselJC 0 a ^ 2)

/-- The coefficient of `(ζ - a)^{-2}` in `G(ζ)/ζ^{2m+1}` at a pole `a`. -/
noncomputable def resid2 (m : ℕ) (a : ℂ) : ℂ := -(LC a / (a ^ (2 * m) * besselJC 0 a ^ 2))

/-- **The principal part at a pole.**  Near a nonzero zero `a ∉ {0, ±k}` of `J₁` with
`J₀(a) ≠ 0`, `G(ζ)/ζ^{2m+1} - residG m a/(ζ - a) - c/(ζ - a)²` is bounded for some `c`. -/
theorem Ghol_principal_part (n : ℕ) {a : ℂ} (ha0 : a ≠ 0) (haS : a ∉ Gsing)
    (h1 : besselJC 1 a = 0) (h0 : besselJC 0 a ≠ 0) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] a,
      ‖Ghol z / z ^ (2 * (n + 1) + 1) -
        (residG (n + 1) a / (z - a) ^ 1 + resid2 (n + 1) a / (z - a) ^ 2)‖ ≤ C := by
  set F := dslope (besselJC 1) a with hFdef
  have hu : (univ : Set ℂ) ∈ 𝓝 a := univ_mem
  have hF : Differentiable ℂ F := fun z =>
    (((Complex.differentiableOn_dslope (c := a) univ_mem).mpr
      (differentiable_besselJC 1).differentiableOn) z (mem_univ z)).differentiableAt univ_mem
  have hFa : F a = besselJC 0 a := by
    rw [hFdef, dslope_same, deriv_besselJC_one_of_zero ha0 h1]
  have hF'a : HasDerivAt F (-besselJC 0 a / a / 2) a := by
    have := (hF a).hasDerivAt
    rwa [deriv_dslope_same (differentiable_besselJC 1) a,
      deriv_deriv_besselJC_one ha0 h1] at this
  set Φ : ℂ → ℂ := fun z => LC z / (z ^ (2 * (n + 1)) * F z ^ 2) with hΦdef
  set s : Set ℂ := {z | z ≠ 0} ∩ {z | F z ≠ 0}
  have hs : s ∈ 𝓝 a := by
    refine inter_mem (isOpen_ne.mem_nhds ha0) ?_
    exact (hF a).continuousAt.eventually_ne (by rw [hFa]; exact h0)
  have hΦd : DifferentiableOn ℂ Φ s := by
    intro z hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact (differentiable_LC z).div ((differentiableAt_id.pow _).mul ((hF z).pow 2))
      (mul_ne_zero (pow_ne_zero _ hz.1) (pow_ne_zero 2 hz.2))
  obtain ⟨C1, hC1⟩ := bdd_sub_principal_two hs hΦd
  obtain ⟨C2, hC2⟩ := bdd_of_continuousAt (f := fun z => (pK : ℂ) / z ^ (2 * (n + 1) + 1))
    (continuousAt_const.div (continuousAt_id.pow _) (pow_ne_zero _ ha0))
  -- the derivative of `Φ` at `a`
  have hD : HasDerivAt (fun z => z ^ (2 * (n + 1)) * F z ^ 2)
      (((2 * (n + 1) : ℕ) : ℂ) * a ^ (2 * (n + 1) - 1) * F a ^ 2 +
        a ^ (2 * (n + 1)) * (((2 : ℕ) : ℂ) * F a ^ (2 - 1) * (-besselJC 0 a / a / 2))) a :=
    (hasDerivAt_pow _ a).mul (hF'a.pow 2)
  have hDa : a ^ (2 * (n + 1)) * F a ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ha0) (pow_ne_zero 2 (by rw [hFa]; exact h0))
  have hΦ' := (hasDerivAt_LC a).div hD hDa
  have hderiv : deriv Φ a = -residG (n + 1) a := by
    rw [show deriv Φ a = _ from hΦ'.deriv, hFa, residG]
    rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show 2 - 1 = 1 by rfl]
    push_cast
    field_simp
    ring
  have hc : resid2 (n + 1) a = -Φ a := by simp only [resid2, hΦdef, hFa]
  rw [hc]
  refine ⟨C2 + C1, ?_⟩
  have hSc : IsOpen ((Gsing : Set ℂ)ᶜ) := Gsing.finite_toSet.isClosed.isOpen_compl
  filter_upwards [hC1, hC2, self_mem_nhdsWithin, nhdsWithin_le_nhds (hSc.mem_nhds haS),
    nhdsWithin_le_nhds hs] with z hz1 hz2 hza hzS hzs
  have hza' : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hJ : besselJC 1 z = (z - a) * F z := by
    have := sub_smul_dslope (besselJC 1) a z
    rw [smul_eq_mul, h1, sub_zero] at this
    exact this.symm
  have key : Ghol z / z ^ (2 * (n + 1) + 1) -
      (residG (n + 1) a / (z - a) ^ 1 + -Φ a / (z - a) ^ 2) =
      (pK : ℂ) / z ^ (2 * (n + 1) + 1) -
        (Φ z / (z - a) ^ 2 - (deriv Φ a / (z - a) ^ 1 + Φ a / (z - a) ^ 2)) := by
    rw [Ghol_of_notMem hzS, hderiv]
    simp only [Gfun, hJ, hΦdef]
    have hz0 : z ≠ 0 := hzs.1
    have hFz : F z ≠ 0 := hzs.2
    field_simp
    ring
  rw [key]
  exact (norm_sub_le _ _).trans (add_le_add hz2 hz1)

end Buckling
end
end ChunkedSource059
/- END SOURCE 059 -/

/- BEGIN SOURCE 060: RequestProject/Concavity/ResidueSign.lean -/
section ChunkedSource060

/-!
# The sign of the paired residues (Lemma 8.8 and Proposition 8.9 of the paper)

At `a = ±κ_n`, `n ≥ 2`, the residue of `G(ζ)/ζ^{2m+1}` is the real number
`((2m - 1) L(κ_n) - φ(κ_n) φ_r(κ_n)) / (κ_n^{2m+1} J₀(κ_n)²)`, which is positive for `m ≥ 2`
by Lemma 8.4.
-/

@[expose] public section

open Filter Topology Metric Set

namespace Buckling

lemma dLC_neg (z : ℂ) : dLC (-z) = dLC z := by
  have h1 : HasDerivAt (fun w => LC (-w)) (dLC (-z) * (-1)) z :=
    (hasDerivAt_LC (-z)).comp z (hasDerivAt_neg z)
  have h2 : HasDerivAt (fun w => LC (-w)) (-dLC z) z := by
    have : (fun w => LC (-w)) = fun w => -LC w := funext LC_neg
    rw [this]; exact (hasDerivAt_LC z).neg
  have := h1.unique h2
  linear_combination -this

lemma residG_neg (m : ℕ) (a : ℂ) : residG m (-a) = residG m a := by
  simp only [residG, LC_neg, dLC_neg, besselJC_neg, pow_zero, one_mul]
  rw [Odd.neg_pow ⟨m, rfl⟩, ← neg_div_neg_eq]
  congr 1 <;> ring

/-- The residue at a real nonzero zero `x` of `J₁`. -/
lemma residG_ofReal (m : ℕ) {x : ℝ} (hx : x ≠ 0) (hJ : besselJ 1 x = 0) :
    residG m (x : ℂ) = ((((2 * m - 1) * LR x +
      pAlpha * (besselJ 0 (pAlpha * x) * besselJ 1 (pAlpha * x))) /
        (x ^ (2 * m + 1) * besselJ 0 x ^ 2) : ℝ) : ℂ) := by
  have h1 : (x : ℂ) * dBC (x : ℂ) = 0 := by
    rw [mul_dBC, besselJC_ofReal, besselJC_ofReal, hJ]; simp
  have h2 : ((pAlpha : ℂ) * x) * dBC ((pAlpha : ℂ) * x) =
      ((besselJ 0 (pAlpha * x) * besselJ 1 (pAlpha * x) : ℝ) : ℂ) := by
    rw [mul_dBC, show (pAlpha : ℂ) * (x : ℂ) = ((pAlpha * x : ℝ) : ℂ) by push_cast; ring,
      besselJC_ofReal, besselJC_ofReal]
    push_cast; ring
  have hxd : (x : ℂ) * dLC x = -((pAlpha * (besselJ 0 (pAlpha * x) * besselJ 1 (pAlpha * x)) : ℝ)
      : ℂ) := by
    unfold dLC
    have : (x : ℂ) * ((pK : ℂ) * dBC x - (pAlpha : ℂ) * ((pAlpha : ℂ) * dBC ((pAlpha : ℂ) * x))) =
        (pK : ℂ) * ((x : ℂ) * dBC x) - (pAlpha : ℂ) * (((pAlpha : ℂ) * x) * dBC ((pAlpha : ℂ) * x))
      := by ring
    rw [this, h1, h2]; push_cast; ring
  unfold residG
  rw [hxd, LC_ofReal, besselJC_ofReal]
  simp only [LR]
  push_cast
  ring

/-- `J₀(κ_n) ≠ 0` (the zeros of `J₁` are simple). -/
lemma besselJ_zero_besselZero_one_ne (hZ : ExtZeros) {n : ℕ} (hn : 1 ≤ n) :
    besselJ 0 (besselZero 1 n) ≠ 0 := by
  have hpos := besselZero_pos hZ 1 n hn
  obtain ⟨hz, hd⟩ := (hZ 1 (by norm_num)).2.2.1 n hn
  rwa [(hasDerivAt_besselJ_one _ hpos.ne').deriv, hz, zero_div, sub_zero] at hd

/-- **Positivity of the residues**: for `n ≥ 2` and `m ≥ 2`, the residue of `G(ζ)/ζ^{2m+1}` at
`±κ_n` is a positive real number. -/
theorem residG_pos (hZ : ExtZeros) (hI : ExtIntegral) {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    0 < (residG m (besselZero 1 n : ℂ)).re ∧ 0 < (residG m (-(besselZero 1 n : ℂ))).re := by
  rw [residG_neg]
  refine ⟨?_, ?_⟩ <;>
  · have hpos := besselZero_pos hZ 1 n (by omega)
    rw [residG_ofReal m hpos.ne' ((hZ 1 (by norm_num)).2.2.1 n (by omega)).1, Complex.ofReal_re]
    obtain ⟨hL, h3⟩ := residue_numerator_pos hZ hI hn
    have hJ0 := besselJ_zero_besselZero_one_ne hZ (show 1 ≤ n by omega)
    have hden : 0 < besselZero 1 n ^ (2 * m + 1) * besselJ 0 (besselZero 1 n) ^ 2 := by
      have := pow_pos hpos (2 * m + 1)
      positivity
    apply div_pos _ hden
    have hm' : (3 : ℝ) ≤ 2 * m - 1 := by
      have : (2 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    nlinarith

end Buckling
end
end ChunkedSource060
/- END SOURCE 060 -/

