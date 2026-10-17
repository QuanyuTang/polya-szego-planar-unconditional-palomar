module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/
public import RequestProject.Core3

/- CONDITIONAL, UNCOMPILED structural experiment. See README.md. -/

/- BEGIN SOURCE 088: RequestProject/Disk/Eigenspace.lean -/
section ChunkedSource088

/-!
# The first buckling eigenspace of a disk and strict monotonicity (Lemmas 11.6, 12.1)

From the spectral gap `disk_gap` we derive
* every minimizer of the buckling quotient on `B_R(a)` is a multiple of `U_{R,a}`
  (second part of Lemma 11.6);
* `Λ₁(W) > Λ₁(B)` for a nonempty proper open subset `W` of a disk `B` (Lemma 12.1).

For the second statement we do not need the existence of minimizers on `W`: a minimizing
sequence of test functions on `W` converges, by the spectral gap, in `H²` to a nonzero
multiple of `U`; by the Sobolev embedding (E9) the convergence is uniform, and the uniform
limit vanishes at a point of `B \ W`, where `U` is positive.
-/

@[expose] public section

open MeasureTheory Real Set Filter Topology Metric

namespace Buckling

/-! ### Elementary facts about `U` -/

lemma continuous_pderiv_diskU (a : Plane) (R : ℝ) (i : Fin 2) :
    Continuous (pderiv i (diskU a R)) :=
  (contDiff_pderiv_of_smooth (contDiff_clampG _ a) i).continuous

lemma memLp_restrict_ball_of_continuous {f : Plane → ℝ} (hf : Continuous f) (a : Plane) (R : ℝ) :
    MemLp f 2 (volume.restrict (ball a R)) := by
  haveI : IsFiniteMeasure (volume.restrict (ball a R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  obtain ⟨C, hC⟩ := (isCompact_closedBall a R).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_ball]
  exact ae_of_all _ fun x hx => hC x (ball_subset_closedBall hx)

/-- `∂ᵢU` as an element of `L²(B_R(a))`. -/
noncomputable def gU (a : Plane) (R : ℝ) (i : Fin 2) : L2 (ball a R) :=
  (memLp_restrict_ball_of_continuous (continuous_pderiv_diskU a R i) a R).toLp _

/-- `E₁(U) = ∫_B |∇U|²`. -/
noncomputable def E1U (a : Plane) (R : ℝ) : ℝ :=
  ∫ x in ball a R, ‖fderiv ℝ (diskU a R) x‖ ^ 2

lemma sum_norm_gU_sq (a : Plane) (R : ℝ) : ∑ i, ‖gU a R i‖ ^ 2 = E1U a R := by
  simp only [gU, norm_toLp_sq, Fin.sum_univ_two, E1U]
  rw [← integral_add ((memLp_restrict_ball_of_continuous (continuous_pderiv_diskU a R 0) a R).integrable_sq)
    ((memLp_restrict_ball_of_continuous (continuous_pderiv_diskU a R 1) a R).integrable_sq)]
  simp only [sum_pderiv_sq]

lemma E1U_pos (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R) : 0 < E1U a R := by
  have hk := jk_pos hZ
  set f : Plane → ℝ := fun x => ‖fderiv ℝ (diskU a R) x‖ ^ 2 with hf
  have hfeq : f = fun x => pderiv 0 (diskU a R) x ^ 2 + pderiv 1 (diskU a R) x ^ 2 := by
    ext x; simp only [f, sum_pderiv_sq]
  have hfc : Continuous f := by
    rw [hfeq]; exact ((continuous_pderiv_diskU a R 0).pow 2).add ((continuous_pderiv_diskU a R 1).pow 2)
  have hint : IntegrableOn f (ball a R) := by
    rw [hfeq]
    exact ((memLp_restrict_ball_of_continuous (continuous_pderiv_diskU a R 0) a R).integrable_sq).add
      ((memLp_restrict_ball_of_continuous (continuous_pderiv_diskU a R 1) a R).integrable_sq)
  unfold E1U
  rw [setIntegral_pos_iff_support_of_nonneg_ae (ae_of_all _ fun x => sq_nonneg _) hint]
  set x0 : Plane := a + EuclideanSpace.single 0 (R / 2)
  have hx0 : ‖x0 - a‖ = R / 2 := by
    simp [x0, EuclideanSpace.norm_single, abs_of_pos hR]
  have hfx0 : f x0 ≠ 0 := by
    simp only [f, diskU, fderiv_clampG, norm_fderiv_radJ0_sq, hx0]
    have : jk / R * (R / 2) = jk / 2 := by field_simp
    rw [this]
    have := besselJ_one_pos_of_lt_jk hZ (jk / 2) (by positivity) (by linarith)
    positivity
  have hopen : IsOpen (Function.support f ∩ ball a R) := hfc.isOpen_support.inter isOpen_ball
  refine hopen.measure_pos volume ⟨x0, hfx0, ?_⟩
  rw [mem_ball, dist_eq_norm, hx0]; linarith

lemma inner_toLp_toLp {Ω : Set Plane} {f g : Plane → ℝ} (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp g 2 (volume.restrict Ω)) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x in Ω, f x * g x := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  simp [hx, hy, mul_comm]

/-- For a test function in the disk, `Σᵢ ⟨∂ᵢφ, ∂ᵢU⟩_{L²(B)} = ∫ ∇φ·∇U`. -/
lemma sum_inner_gU {a : Plane} {R : ℝ} {φ : Plane → ℝ} (hφ : IsTestFn (ball a R) φ) :
    ∑ i, inner ℝ (hφ.pderiv i).toL2 (gU a R i) = gradPair φ (diskU a R) := by
  have hint : ∀ i, Integrable (fun x => pderiv i φ x * pderiv i (diskU a R) x) := fun i =>
    ((hφ.pderiv i).1.continuous.mul (continuous_pderiv_diskU a R i)).integrable_of_hasCompactSupport
      (hφ.pderiv i).2.1.mul_right
  simp only [Fin.sum_univ_two, gU, IsTestFn.toL2, inner_toLp_toLp, gradPair]
  rw [integral_add (hint 0) (hint 1), ← integral_add (hint 0).integrableOn (hint 1).integrableOn]
  rw [← integral_add (hint 0) (hint 1)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp [(hφ.pderiv 0).eq_zero_of_notMem hx, (hφ.pderiv 1).eq_zero_of_notMem hx]

/-! ### The zero extension of `U` -/

/-- `U_{R,a}` on the closed disk, `0` outside. -/
noncomputable abbrev diskUg (a : Plane) (R : ℝ) : Plane → ℝ := ballGlue a R (diskU a R)

lemma diskU_sphere (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R) :
    ∀ x, ‖x - a‖ = R → diskU a R x = 0 ∧ fderiv ℝ (diskU a R) x = 0 :=
  clampG_sphere hZ a hR

lemma diskUg_lipschitz (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R) :
    ∃ L, LipschitzWith L (diskUg a R) :=
  ballGlue_lipschitz a ((contDiff_clampG _ a).of_le (by simp))
    (fun x hx => (diskU_sphere hZ a hR x hx).1)

lemma tsupport_diskUg (a : Plane) (R : ℝ) : tsupport (diskUg a R) ⊆ closedBall a R := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  rw [mem_closedBall, dist_eq_norm]
  by_contra h
  exact hx (by simp [diskUg, ballGlue, h])

lemma hasCompactSupport_diskUg (a : Plane) (R : ℝ) : HasCompactSupport (diskUg a R) :=
  (isCompact_closedBall a R).of_isClosed_subset (isClosed_tsupport _) (tsupport_diskUg a R)

lemma diskUg_eq_of_mem {a : Plane} {R : ℝ} {x : Plane} (hx : x ∈ ball a R) :
    diskUg a R x = diskU a R x := by
  rw [mem_ball, dist_eq_norm] at hx
  simp [diskUg, ballGlue, hx.le]

lemma diskUg_eq_zero_of_notMem {a : Plane} {R : ℝ} {x : Plane} (hx : x ∉ closedBall a R) :
    diskUg a R x = 0 := by
  rw [mem_closedBall, dist_eq_norm, not_le] at hx
  simp [diskUg, ballGlue, not_le.mpr hx]

/-- The weak derivative of the zero extension of `U` is the zero extension of `∇U`. -/
lemma integral_diskUg_mul_pderiv (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) (i : Fin 2) :
    ∫ x, diskUg a R x * pderiv i ψ x = -∫ x in ball a R, pderiv i (diskU a R) x * ψ x := by
  obtain ⟨L, hL⟩ := diskUg_lipschitz hZ a hR
  have h := lipschitz_hasWeakGradient hL ψ hψ i
  rw [h]
  congr 1
  have hgd : Differentiable ℝ (diskU a R) := (contDiff_clampG _ a).differentiable (by simp)
  have hp := pderiv_ballGlue a hgd (diskU_sphere hZ a hR) i
  have hsph : ∀ᵐ x ∂(volume : Measure Plane), x ∉ sphere a R :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume a R)
  rw [← integral_indicator measurableSet_ball]
  refine integral_congr_ae ?_
  filter_upwards [hsph] with x hx
  have h1 : fderiv ℝ (diskUg a R) x (EuclideanSpace.single i 1) = pderiv i (diskUg a R) x := rfl
  rw [h1, hp]
  rw [mem_sphere, dist_eq_norm] at hx
  by_cases hb : ‖x - a‖ < R
  · have hxb : x ∈ ball a R := by rw [mem_ball, dist_eq_norm]; exact hb
    simp [ballGlue, hb.le, hxb]
  · have hgt : R < ‖x - a‖ := lt_of_le_of_ne (not_lt.mp hb) (Ne.symm hx)
    have hxb : x ∉ ball a R := by rw [mem_ball, dist_eq_norm]; exact hb
    simp [ballGlue, not_le.mpr hgt, hxb]

/-! ### Closure-level facts -/

/-- Elements of `H₀²(Ω)` satisfy the weak-derivative relation for their first component. -/
lemma H02_weak_gradient {Ω : Set Plane} {v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)}
    (hv : v ∈ H02 Ω) {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) (i : Fin 2) :
    ∫ x in Ω, v.1 x * pderiv i ψ x = -∫ x in Ω, v.2.1 i x * ψ x := by
  have hm : ∀ {g : Plane → ℝ}, IsTestFn univ g → MemLp g 2 (volume.restrict Ω) := fun hg =>
    (hg.1.continuous.memLp_of_hasCompactSupport hg.2.1).restrict Ω
  set g1 : L2 Ω := (hm (hψ.pderiv i)).toLp _
  set g0 : L2 Ω := (hm hψ).toLp _
  have key : ∀ w ∈ H02 Ω, inner ℝ w.1 g1 + inner ℝ (w.2.1 i) g0 = 0 := by
    intro w hw
    refine closure_minimal (s := Set.range (graphH2 (Ω := Ω)))
      (t := {w | inner ℝ w.1 g1 + inner ℝ (w.2.1 i) g0 = 0}) ?_ ?_ hw
    · rintro _ ⟨φ, rfl⟩
      simp only [mem_setOf_eq, graphH2, IsTestFn.toL2, g1, g0, inner_toLp_toLp]
      have hc : ∀ {f g : Plane → ℝ}, Continuous f → IsTestFn Ω g →
          Integrable (fun x => g x * f x) := fun hf hg =>
        (hg.1.continuous.mul hf).integrable_of_hasCompactSupport hg.2.1.mul_right
      have e1 : ∫ x in Ω, φ.1 x * pderiv i ψ x = ∫ x, φ.1 x * pderiv i ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          simp [φ.2.eq_zero_of_notMem hx]
      have e2 : ∫ x in Ω, pderiv i φ.1 x * ψ x = ∫ x, pderiv i φ.1 x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          simp [(φ.2.pderiv i).eq_zero_of_notMem hx]
      rw [e1, e2]
      have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Plane))
        (f := φ.1) (g := ψ) (v := EuclideanSpace.single i 1)
        (hc hψ.1.continuous (φ.2.pderiv i)) (hc (hψ.pderiv i).1.continuous φ.2)
        (hc hψ.1.continuous φ.2)
        (fun x _ => φ.2.1.differentiable (by simp) x)
        (fun x _ => hψ.1.differentiable (by simp) x)
      simp only [pderiv] at this ⊢
      linarith
    · exact isClosed_eq (by fun_prop) continuous_const
  have h := key v hv
  have c1 : inner ℝ v.1 g1 = ∫ x in Ω, v.1 x * pderiv i ψ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hm (hψ.pderiv i)).coeFn_toLp] with x hx
    simp [g1, hx, mul_comm]
  have c2 : inner ℝ (v.2.1 i) g0 = ∫ x in Ω, v.2.1 i x * ψ x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hm hψ).coeFn_toLp] with x hx
    simp [g0, hx, mul_comm]
  linarith

/-- An `L²` function with zero weak gradient, vanishing outside a compact set, is zero. -/
lemma ae_eq_zero_of_weakGradient_zero (hM : ExtMollification) {F : Plane → ℝ}
    (hF : MemLp F 2 volume) {K : Set Plane} (hK : IsCompact K) (hFK : ∀ᵐ x, x ∉ K → F x = 0)
    (hw : ∀ ψ, IsTestFn univ ψ → ∀ i, ∫ x, F x * pderiv i ψ x = 0) : F =ᵐ[volume] 0 := by
  have hweak : HasWeakGradient F (fun _ _ => 0) := by
    intro ψ hψ i; simp [hw ψ hψ i]
  have hlt : ∀ ε > 0, eLpNorm F 2 volume < ENNReal.ofReal ε := by
    intro ε hε
    obtain ⟨ψ, hψs, hψsupp, hψ0, -, hψd⟩ := hM F (fun _ _ => 0) K hF (fun _ => MemLp.zero)
      hweak hK.isClosed hFK ε hε
    have hd := hψd (fun _ => ae_of_all _ fun _ => rfl)
    have hfd : ∀ x, fderiv ℝ ψ x = 0 := fun x => clm_eq_zero_of_pderiv _ (hd 0 x) (hd 1 x)
    have hconst := is_const_of_fderiv_eq_zero (hψs.differentiable (by simp)) hfd
    obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem _).mp
      (hK.cthickening (r := ε)).ne_univ
    have hψz : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hψsupp h))
    have : (fun x => ψ x - F x) = fun x => -F x := by
      ext x; rw [hconst x z, hψz]; ring
    rw [this] at hψ0
    have e : (fun x => -F x) = -F := rfl
    rwa [e, eLpNorm_neg] at hψ0
  have h0 : eLpNorm F 2 volume = 0 := by
    by_contra hne
    have htop : eLpNorm F 2 volume ≠ ⊤ := hF.ne
    have hpos : 0 < (eLpNorm F 2 volume).toReal := ENNReal.toReal_pos hne htop
    have := hlt _ hpos
    rw [ENNReal.ofReal_toReal htop] at this
    exact lt_irrefl _ this
  exact (eLpNorm_eq_zero_iff (f := F) (p := 2) (μ := volume) (by norm_num)).mp h0

/-- The spectral gap, extended to `H₀²(B)`. -/
lemma disk_gap_H02 (a : Plane) {R : ℝ} (hR : 0 < R) :
    ∃ δ > 0, ∀ v ∈ H02 (ball a R),
      δ * (energy1' v * E1U a R - (∑ i, inner ℝ (v.2.1 i) (gU a R i)) ^ 2)
        ≤ E1U a R * (energy2 v - jk ^ 2 / R ^ 2 * energy1' v) := by
  obtain ⟨δ, hδ, hgap⟩ := disk_gap a hR
  refine ⟨δ, hδ, fun v hv => ?_⟩
  refine closure_minimal (s := Set.range (graphH2 (Ω := ball a R)))
    (t := {v | δ * (energy1' v * E1U a R - (∑ i, inner ℝ (v.2.1 i) (gU a R i)) ^ 2)
        ≤ E1U a R * (energy2 v - jk ^ 2 / R ^ 2 * energy1' v)}) ?_ ?_ hv
  · rintro _ ⟨φ, rfl⟩
    simp only [mem_setOf_eq, energy1'_graphH2, energy2_graphH2]
    have := sum_inner_gU φ.2
    simp only [graphH2]
    rw [this]
    exact hgap φ.1 φ.2
  · refine isClosed_le ?_ ?_
    · unfold energy1'; fun_prop
    · unfold energy1' energy2; fun_prop

/-- If the gradient of `v ∈ H₀²(B)` is `c ∇U`, then `v = cU`. -/
lemma eq_smul_diskU_of_grad (a : Plane) {R : ℝ} (hR : 0 < R)
    (v : L2 (ball a R) × (Fin 2 → L2 (ball a R)) × (Fin 2 → Fin 2 → L2 (ball a R)))
    (hv : v ∈ H02 (ball a R)) (c : ℝ)
    (hgrad_ae : ∀ i, ∀ᵐ x ∂(volume.restrict (ball a R)), v.2.1 i x = c * pderiv i (diskU a R) x) :
    ∀ᵐ x ∂(volume.restrict (ball a R)), v.1 x = c * diskU a R x := by
  have hZ := extZeros_holds
  have hvL : MemLp ((ball a R).indicator (fun y => v.1 y)) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp v.1)
  obtain ⟨L, hL⟩ := diskUg_lipschitz hZ a hR
  have hUL : MemLp (diskUg a R) 2 volume :=
    hL.continuous.memLp_of_hasCompactSupport (hasCompactSupport_diskUg a R)
  have hFL : MemLp (fun x => (ball a R).indicator (fun y => v.1 y) x - c * diskUg a R x) 2 volume :=
    hvL.sub (hUL.const_mul c)
  have hweak : ∀ ψ, IsTestFn univ ψ → ∀ i,
      ∫ x, ((ball a R).indicator (fun y => v.1 y) x - c * diskUg a R x) * pderiv i ψ x = 0 := by
    intro ψ hψ i
    have hpL : MemLp (pderiv i ψ) 2 volume :=
      (hψ.pderiv i).1.continuous.memLp_of_hasCompactSupport (hψ.pderiv i).2.1
    have hi1 : Integrable fun x => (ball a R).indicator (fun y => v.1 y) x * pderiv i ψ x :=
      hvL.integrable_mul hpL
    have hi2 : Integrable fun x => c * diskUg a R x * pderiv i ψ x :=
      ((hUL.const_mul c).integrable_mul hpL)
    have e1 : ∫ x, (ball a R).indicator (fun y => v.1 y) x * pderiv i ψ x =
        ∫ x in ball a R, v.1 x * pderiv i ψ x := by
      rw [← integral_indicator measurableSet_ball]
      congr 1; ext x
      by_cases hx : x ∈ ball a R <;> simp [hx]
    have e2 : ∫ x in ball a R, v.2.1 i x * ψ x =
        c * ∫ x in ball a R, pderiv i (diskU a R) x * ψ x := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hgrad_ae i] with x hx
      rw [hx]; ring
    have e3 : ∫ x, c * diskUg a R x * pderiv i ψ x = c * ∫ x, diskUg a R x * pderiv i ψ x := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    simp only [sub_mul]
    rw [integral_sub hi1 hi2, e1, H02_weak_gradient hv hψ i, e2, e3,
      integral_diskUg_mul_pderiv hZ a hR hψ i]
    ring
  have hF0 := ae_eq_zero_of_weakGradient_zero extMollification_holds hFL (isCompact_closedBall a R)
    (ae_of_all _ fun x hx => by
      have hxb : x ∉ ball a R := fun h => hx (ball_subset_closedBall h)
      simp [hxb, diskUg_eq_zero_of_notMem hx]) hweak
  rw [ae_restrict_iff' measurableSet_ball]
  filter_upwards [hF0] with x hx hxb
  simp only [Pi.zero_apply, indicator_of_mem hxb, diskUg_eq_of_mem hxb] at hx
  linarith

/-- Equality in the Cauchy–Schwarz inequality for the gradient pairing. -/
lemma grad_eq_smul_of_le {Ω : Set Plane} (u g : Fin 2 → L2 Ω) (hg : 0 < ∑ i, ‖g i‖ ^ 2)
    (hle : (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖g i‖ ^ 2) ≤ (∑ i, inner ℝ (u i) (g i)) ^ 2) :
    ∀ i, u i = ((∑ i, inner ℝ (u i) (g i)) / ∑ i, ‖g i‖ ^ 2) • g i := by
  set P := ∑ i, inner ℝ (u i) (g i) with hP
  set G := ∑ i, ‖g i‖ ^ 2 with hG
  set c := P / G with hc
  have hexp : ∑ i, ‖u i - c • g i‖ ^ 2 = (∑ i, ‖u i‖ ^ 2) - 2 * c * P + c ^ 2 * G := by
    simp only [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, Finset.sum_add_distrib, Finset.sum_sub_distrib, hP, hG, Finset.mul_sum]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hzero : ∑ i, ‖u i - c • g i‖ ^ 2 ≤ 0 := by
    rw [hexp, hc]
    have : (∑ i, ‖u i‖ ^ 2) - 2 * (P / G) * P + (P / G) ^ 2 * G =
        ((∑ i, ‖u i‖ ^ 2) * G - P ^ 2) / G := by field_simp; ring
    rw [this]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hg.le
  intro i
  have hi : ‖u i - c • g i‖ ^ 2 ≤ 0 :=
    le_trans (Finset.single_le_sum (f := fun j => ‖u j - c • g j‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)) hzero
  have : ‖u i - c • g i‖ = 0 := by nlinarith [norm_nonneg (u i - c • g i)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- **Lemma 11.6 (second part), quotient form.**  An element of `H₀²(B_R(a))` whose
buckling quotient is `k²/R²` is a multiple of `U_{R,a}`. -/
theorem minimizer_eq_smul_diskU (a : Plane) {R : ℝ} (hR : 0 < R)
    (v : L2 (ball a R) × (Fin 2 → L2 (ball a R)) × (Fin 2 → Fin 2 → L2 (ball a R)))
    (hv : v ∈ H02 (ball a R)) (hq : energy2 v = jk ^ 2 / R ^ 2 * energy1' v) :
    ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (ball a R)), v.1 x = C * diskU a R x := by
  have hZ := extZeros_holds
  obtain ⟨δ, hδ, hgap⟩ := disk_gap_H02 a hR
  have hE1U := E1U_pos hZ a hR
  have hle : energy1' v * E1U a R ≤ (∑ i, inner ℝ (v.2.1 i) (gU a R i)) ^ 2 := by
    have := hgap v hv
    rw [hq, sub_self, mul_zero] at this
    nlinarith
  rw [← sum_norm_gU_sq] at hle hE1U
  have hgrad := grad_eq_smul_of_le v.2.1 (gU a R) hE1U hle
  set c := (∑ i, inner ℝ (v.2.1 i) (gU a R i)) / ∑ i, ‖gU a R i‖ ^ 2
  refine ⟨c, eq_smul_diskU_of_grad a hR v hv c fun i => ?_⟩
  rw [hgrad i]
  filter_upwards [Lp.coeFn_smul c (gU a R i),
    (memLp_restrict_ball_of_continuous (continuous_pderiv_diskU a R i) a R).coeFn_toLp]
    with x h1 h2
  rw [h1, Pi.smul_apply, smul_eq_mul, gU, h2]

/-! ### Auxiliary facts for Lemma 12.1 -/

/-- `J₀` is strictly decreasing on `[0, k]`. -/
lemma besselJ_zero_strictAntiOn (hZ : ExtZeros) : StrictAntiOn (besselJ 0) (Set.Icc 0 jk) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 jk) (continuous_besselJ 0).continuousOn
  intro x hx
  rw [interior_Icc] at hx
  rw [deriv_besselJ_zero]
  linarith [besselJ_one_pos_of_lt_jk hZ x hx.1 hx.2]

lemma diskU_pos (hZ : ExtZeros) (a : Plane) {R : ℝ} (hR : 0 < R) {x : Plane}
    (hx : x ∈ ball a R) : 0 < diskU a R x := by
  have hk := jk_pos hZ
  have hx' : ‖x - a‖ < R := by rw [mem_ball, dist_eq_norm] at hx; exact hx
  have ht0 : 0 ≤ jk / R * ‖x - a‖ := by positivity
  have ht1 : jk / R * ‖x - a‖ < jk := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hR]; exact mul_lt_mul_of_pos_left hx' hk
  have := besselJ_zero_strictAntiOn hZ ⟨ht0, ht1.le⟩ ⟨by linarith, le_rfl⟩ ht1
  simp only [diskU, clampG, radJ0_eq]
  linarith

lemma energy1'_smul {Ω : Set Plane} (s : ℝ) (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) :
    energy1' (s • v) = s ^ 2 * energy1' v := by
  simp [energy1', norm_smul, mul_pow]
  ring

lemma energy2_smul {Ω : Set Plane} (s : ℝ) (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) :
    energy2 (s • v) = s ^ 2 * energy2 v := by
  simp only [energy2, Prod.smul_snd, Pi.smul_apply, ← smul_add, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]

lemma energy1'_parallelogram {Ω : Set Plane}
    (v w : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) :
    energy1' (v - w) + energy1' (v + w) = 2 * energy1' v + 2 * energy1' w := by
  simp only [energy1', Prod.snd_sub, Prod.fst_sub, Prod.snd_add, Prod.fst_add, Pi.sub_apply,
    Pi.add_apply, Fin.sum_univ_two, norm_sub_sq_real, norm_add_sq_real]
  ring

lemma energy2_parallelogram {Ω : Set Plane}
    (v w : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) :
    energy2 (v - w) + energy2 (v + w) = 2 * energy2 v + 2 * energy2 w := by
  simp only [energy2, Prod.snd_sub, Prod.snd_add, Pi.sub_apply, Pi.add_apply]
  have e1 : v.2.2 0 0 - w.2.2 0 0 + (v.2.2 1 1 - w.2.2 1 1) =
      (v.2.2 0 0 + v.2.2 1 1) - (w.2.2 0 0 + w.2.2 1 1) := by abel
  have e2 : v.2.2 0 0 + w.2.2 0 0 + (v.2.2 1 1 + w.2.2 1 1) =
      (v.2.2 0 0 + v.2.2 1 1) + (w.2.2 0 0 + w.2.2 1 1) := by abel
  rw [e1, e2]
  have := parallelogram_law_with_norm ℝ (v.2.2 0 0 + v.2.2 1 1) (w.2.2 0 0 + w.2.2 1 1)
  simp only [sq]
  linarith

/-- On `H₀²(B)` the buckling form `E₂ - μE₁` is nonnegative. -/
lemma quotient_nonneg_H02 (a : Plane) {R : ℝ} (hR : 0 < R)
    {v : L2 (ball a R) × (Fin 2 → L2 (ball a R)) × (Fin 2 → Fin 2 → L2 (ball a R))}
    (hv : v ∈ H02 (ball a R)) : jk ^ 2 / R ^ 2 * energy1' v ≤ energy2 v := by
  obtain ⟨δ, hδ, hgap⟩ := disk_gap_H02 a hR
  have h := hgap v hv
  have hcs := sum_inner_sq_le v.2.1 (gU a R)
  rw [sum_norm_gU_sq] at hcs
  have hE1U := E1U_pos extZeros_holds a hR
  have h1 : 0 ≤ E1U a R * (energy2 v - jk ^ 2 / R ^ 2 * energy1' v) :=
    le_trans (mul_nonneg hδ.le (by simp only [energy1'] at hcs ⊢; linarith)) h
  have := (mul_nonneg_iff_of_pos_left hE1U).mp h1
  linarith

/-- The Sobolev embedding (E9) for test functions in the disk, with the `L²` part
controlled by the Dirichlet eigenvalue. -/
lemma sup_bound_of_energies (a : Plane) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : Plane → ℝ) (hψ : IsTestFn (ball a R) ψ) (x : Plane),
      |ψ x| ≤ C * Real.sqrt ((R ^ 2 / jq ^ 2 + 1) * energy1' (graphH2 ⟨ψ, hψ⟩)
        + energy2 (graphH2 ⟨ψ, hψ⟩)) := by
  obtain ⟨C, hC⟩ := extEmbedding_holds
  have hq := (parameter_signs extZeros_holds).1
  refine ⟨max C 0, le_max_right _ _, fun ψ hψ x => ?_⟩
  have hψ' : IsTestFn univ ψ := hψ.mono (subset_univ _)
  have h := hC ψ hψ' x
  rw [energy1'_graphH2, energy2_graphH2]
  have e0 : ‖hψ'.toL2‖ ^ 2 = ∫ y, ψ y ^ 2 := hψ'.integral_sq
  have e1 : ∑ i, ‖(hψ'.pderiv i).toL2‖ ^ 2 = ∫ y, ‖fderiv ℝ ψ y‖ ^ 2 := by
    simp only [Fin.sum_univ_two, IsTestFn.integral_sq]
    rw [← integral_add (hψ.pderiv 0).integrable_sq (hψ.pderiv 1).integrable_sq]
    simp only [sum_pderiv_sq]
  have e2 : ∑ i, ∑ j, ‖((hψ'.pderiv j).pderiv i).toL2‖ ^ 2 = ∫ y, laplacian ψ y ^ 2 := by
    simp only [IsTestFn.integral_sq]
    exact sum_integral_hessian_sq hψ
  rw [e0, e1, e2] at h
  have hD : ∫ y, ψ y ^ 2 ≤ R ^ 2 / jq ^ 2 * ∫ y, ‖fderiv ℝ ψ y‖ ^ 2 := by
    by_cases h0 : ∫ y, ψ y ^ 2 = 0
    · rw [h0]; positivity
    · have hle := dirichletEig_le (graphH1 ⟨ψ, hψ⟩) (subset_closure ⟨_, rfl⟩)
        (by rwa [energy0_graphH1])
      rw [dirichletEig_ball' a R hR, energy0_graphH1, energy1_graphH1] at hle
      have hpos : 0 < ∫ y, ψ y ^ 2 :=
        lt_of_le_of_ne (integral_nonneg fun y => sq_nonneg _) (Ne.symm h0)
      rw [le_div_iff₀ hpos] at hle
      have hle' : jq ^ 2 / R ^ 2 * ∫ y, ψ y ^ 2 ≤ ∫ y, ‖fderiv ℝ ψ y‖ ^ 2 := hle
      have h2 : jq ^ 2 / R ^ 2 * (∫ y, ψ y ^ 2) * R ^ 2 = jq ^ 2 * ∫ y, ψ y ^ 2 := by
        field_simp
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hle' (sq_nonneg R)]
  calc |ψ x| ≤ C * Real.sqrt ((∫ y, ψ y ^ 2) + (∫ y, ‖fderiv ℝ ψ y‖ ^ 2) +
        ∫ y, laplacian ψ y ^ 2) := h
    _ ≤ max C 0 * Real.sqrt ((∫ y, ψ y ^ 2) + (∫ y, ‖fderiv ℝ ψ y‖ ^ 2) +
        ∫ y, laplacian ψ y ^ 2) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        apply Real.sqrt_le_sqrt
        nlinarith

/-- A normalized almost-minimizing test function on `W ⊆ B`, with nonnegative pairing with `U`. -/
lemma exists_normalized_test (a : Plane) {R : ℝ} {W : Set Plane} (hW : IsOpen W)
    (hne : W.Nonempty) (hsub : W ⊆ ball a R) {c : ℝ} (hc : bucklingEig W < c) :
    ∃ (φ : Plane → ℝ) (hφ : IsTestFn (ball a R) φ), tsupport φ ⊆ W ∧
      energy1' (graphH2 ⟨φ, hφ⟩) = 1 ∧ energy2 (graphH2 ⟨φ, hφ⟩) < c ∧
      0 ≤ ∑ i, inner ℝ ((graphH2 ⟨φ, hφ⟩).2.1 i) (gU a R i) := by
  obtain ⟨φ, hφ1, hφ2⟩ : ∃ φ : {φ // IsTestFn W φ}, ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 ≠ 0 ∧
      (∫ x, laplacian φ.1 x ^ 2) / ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 < c := by
    by_contra hcon
    push_neg at hcon
    exact absurd (le_bucklingEig_of_test hW hne c hcon) (not_le.mpr hc)
  have hB : IsTestFn (ball a R) φ.1 := φ.2.mono hsub
  set E := ∫ x, ‖fderiv ℝ φ.1 x‖ ^ 2 with hEdef
  have hEpos : 0 < E := lt_of_le_of_ne (integral_nonneg fun x => sq_nonneg _) (Ne.symm hφ1)
  set P0 := ∑ i, inner ℝ ((graphH2 ⟨φ.1, hB⟩).2.1 i) (gU a R i)
  set σ : ℝ := if 0 ≤ P0 then 1 else -1 with hσ
  have hσ2 : σ ^ 2 = 1 := by rw [hσ]; split_ifs <;> norm_num
  have hσP : 0 ≤ σ * P0 := by
    rw [hσ]; split_ifs with h
    · linarith
    · push_neg at h; linarith
  set s := σ / Real.sqrt E
  have hs2 : s ^ 2 = 1 / E := by
    simp only [s, div_pow, hσ2, Real.sq_sqrt hEpos.le]
  have hψ := hB.lincomb hB s 0
  have hgr := graphH2_lincomb hB hB s 0
  simp only [zero_smul, add_zero] at hgr
  refine ⟨_, hψ, ?_, ?_, ?_, ?_⟩
  · exact (φ.2.lincomb φ.2 s 0).2.2
  · rw [hgr, energy1'_smul, energy1'_graphH2, hs2]
    change 1 / E * E = 1
    field_simp
  · rw [hgr, energy2_smul, energy2_graphH2, hs2]
    rw [one_div, ← div_eq_inv_mul]
    exact hφ2
  · rw [hgr]
    simp only [Prod.smul_snd, Prod.smul_fst, Pi.smul_apply, real_inner_smul_left]
    rw [← Finset.mul_sum]
    have : s * P0 = (σ * P0) / Real.sqrt E := by simp only [s]; ring
    change 0 ≤ s * P0
    rw [this]
    exact div_nonneg hσP (Real.sqrt_nonneg _)

lemma sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

lemma sum_norm_sub_smul_sq {Ω : Set Plane} (u g : Fin 2 → L2 Ω) (c : ℝ) :
    ∑ i, ‖u i - c • g i‖ ^ 2 =
      (∑ i, ‖u i‖ ^ 2) - 2 * c * (∑ i, inner ℝ (u i) (g i)) + c ^ 2 * ∑ i, ‖g i‖ ^ 2 := by
  simp only [Fin.sum_univ_two, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

/-- Along a normalized minimizing sequence in `H₀²(B)` with nonnegative pairing with `U`,
the gradients converge in `L²` to `∇U/‖∇U‖`. -/
lemma gradient_tendsto (a : Plane) {R : ℝ} (hR : 0 < R)
    (w : ℕ → L2 (ball a R) × (Fin 2 → L2 (ball a R)) × (Fin 2 → Fin 2 → L2 (ball a R)))
    (hw : ∀ n, w n ∈ H02 (ball a R)) (h1 : ∀ n, energy1' (w n) = 1)
    (h2 : ∀ n, energy2 (w n) < jk ^ 2 / R ^ 2 + 1 / ((n : ℝ) + 1))
    (hP : ∀ n, 0 ≤ ∑ i, inner ℝ ((w n).2.1 i) (gU a R i)) :
    Tendsto (fun n => ∑ i, ‖(w n).2.1 i - (1 / Real.sqrt (E1U a R)) • gU a R i‖ ^ 2)
      atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hgap⟩ := disk_gap_H02 a hR
  have hE1U := E1U_pos extZeros_holds a hR
  set S := Real.sqrt (E1U a R) with hSdef
  have hS : 0 < S := Real.sqrt_pos.mpr hE1U
  have hS2 : S ^ 2 = E1U a R := Real.sq_sqrt hE1U.le
  set P : ℕ → ℝ := fun n => ∑ i, inner ℝ ((w n).2.1 i) (gU a R i) with hPdef
  have hD : ∀ n, ∑ i, ‖(w n).2.1 i - (1 / S) • gU a R i‖ ^ 2 = 2 - 2 * (P n / S) := by
    intro n
    rw [sum_norm_sub_smul_sq, sum_norm_gU_sq]
    have : ∑ i, ‖(w n).2.1 i‖ ^ 2 = 1 := h1 n
    rw [this, ← hS2]
    field_simp
    ring
  -- bounds on `(P n / S)²`
  have hup : ∀ n, (P n / S) ^ 2 ≤ 1 := by
    intro n
    have hcs := sum_inner_sq_le (w n).2.1 (gU a R)
    rw [sum_norm_gU_sq] at hcs
    have : ∑ i, ‖(w n).2.1 i‖ ^ 2 = 1 := h1 n
    rw [this, one_mul] at hcs
    rw [div_pow, hS2, div_le_one hE1U]
    exact hcs
  have hlow : ∀ n : ℕ, 1 - 1 / (δ * ((n : ℝ) + 1)) ≤ (P n / S) ^ 2 := by
    intro n
    have hg := hgap (w n) (hw n)
    rw [h1 n, one_mul] at hg
    have hq : energy2 (w n) - jk ^ 2 / R ^ 2 * 1 ≤ 1 / ((n : ℝ) + 1) := by linarith [h2 n]
    have hb : δ * (E1U a R - P n ^ 2) ≤ E1U a R * (1 / ((n : ℝ) + 1)) :=
      hg.trans (mul_le_mul_of_nonneg_left hq hE1U.le)
    rw [div_pow, hS2]
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [le_div_iff₀ hE1U]
    have : E1U a R - P n ^ 2 ≤ E1U a R / (δ * ((n : ℝ) + 1)) := by
      rw [le_div_iff₀ (by positivity)]
      calc (E1U a R - P n ^ 2) * (δ * ((n : ℝ) + 1)) = δ * (E1U a R - P n ^ 2) * ((n : ℝ) + 1) := by
            ring
        _ ≤ E1U a R * (1 / ((n : ℝ) + 1)) * ((n : ℝ) + 1) := by gcongr
        _ = E1U a R := by field_simp
    have e : (1 - 1 / (δ * ((n : ℝ) + 1))) * E1U a R = E1U a R - E1U a R / (δ * ((n : ℝ) + 1)) := by
      ring
    rw [e]; linarith
  have hsq : Tendsto (fun n => (P n / S) ^ 2) atTop (𝓝 1) := by
    have hl : Tendsto (fun n : ℕ => 1 - 1 / (δ * ((n : ℝ) + 1))) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 / (δ * ((n : ℝ) + 1))) atTop (𝓝 0) := by
        have h' : Tendsto (fun n : ℕ => δ * ((n : ℝ) + 1)) atTop atTop :=
          Tendsto.const_mul_atTop hδ (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
        exact h'.inv_tendsto_atTop.congr fun n => by rw [Pi.inv_apply, one_div]
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow hup
  have hlin : Tendsto (fun n => P n / S) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto 1).comp hsq
    simp only [Real.sqrt_one] at this
    refine this.congr fun n => ?_
    simp only [Function.comp_apply]
    exact Real.sqrt_sq (div_nonneg (hP n) hS.le)
  have : Tendsto (fun n => 2 - 2 * (P n / S)) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := (2 : ℝ))).sub (hlin.const_mul 2)
    simpa using this
  exact this.congr fun n => (hD n).symm

lemma tendsto_two_div_nat : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 : ℝ)
  rw [mul_zero] at this
  exact this.congr fun n => by ring

lemma aux_energy_ineq {K μ A B : ℝ} {D : ℕ → ℝ} {n m : ℕ} (hK : 0 ≤ K) (hμ : 0 ≤ μ)
    (hA : A ≤ 2 * D n + 2 * D m) (hB : B ≤ 2 / ((n : ℝ) + 1) + 2 / ((m : ℝ) + 1) + μ * A) :
    K * A + B ≤ (fun n : ℕ => 2 * (K + μ) * D n + 2 / ((n : ℝ) + 1)) n +
      (fun n : ℕ => 2 * (K + μ) * D n + 2 / ((n : ℝ) + 1)) m := by
  simp only
  nlinarith

/-- Uniform Cauchy bound for a normalized minimizing sequence whose gradients converge. -/
lemma diff_sup_bound (a : Plane) {R : ℝ} (hR : 0 < R)
    (φ : ℕ → Plane → ℝ) (hφ : ∀ n, IsTestFn (ball a R) (φ n))
    (h1 : ∀ n, energy1' (graphH2 ⟨φ n, hφ n⟩) = 1)
    (h2 : ∀ n, energy2 (graphH2 ⟨φ n, hφ n⟩) < jk ^ 2 / R ^ 2 + 1 / ((n : ℝ) + 1))
    (T : Fin 2 → L2 (ball a R))
    (hD : Tendsto (fun n => ∑ i, ‖(graphH2 ⟨φ n, hφ n⟩).2.1 i - T i‖ ^ 2) atTop (𝓝 0)) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧ ∀ n m x, |φ n x - φ m x| ≤ b n + b m := by
  obtain ⟨C, hC0, hC⟩ := sup_bound_of_energies a hR
  set μ := jk ^ 2 / R ^ 2 with hμ
  have hμ0 : 0 ≤ μ := by positivity
  set K := R ^ 2 / jq ^ 2 + 1 with hK
  have hK0 : 0 ≤ K := by positivity
  set w := fun n => graphH2 ⟨φ n, hφ n⟩ with hwdef
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ → ℝ, D = fun n => ∑ i, ‖(w n).2.1 i - T i‖ ^ 2 := ⟨_, rfl⟩
  have hD0 : ∀ n, 0 ≤ D n := fun n => by
    rw [hDdef]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  obtain ⟨e, hedef⟩ : ∃ e : ℕ → ℝ, e = fun n => 2 * (K + μ) * D n + 2 / ((n : ℝ) + 1) :=
    ⟨_, rfl⟩
  have he0 : ∀ n, 0 ≤ e n := fun n => by rw [hedef]; have := hD0 n; positivity
  have hdiff : ∀ n m, graphH2 ⟨_, (hφ n).lincomb (hφ m) 1 (-1)⟩ = w n - w m := by
    intro n m
    rw [graphH2_lincomb, one_smul, neg_one_smul, ← sub_eq_add_neg]
  have hsum : ∀ n m, graphH2 ⟨_, (hφ n).lincomb (hφ m) 1 1⟩ = w n + w m := by
    intro n m
    rw [graphH2_lincomb, one_smul, one_smul]
  have hE1d : ∀ n m, energy1' (w n - w m) ≤ 2 * D n + 2 * D m := by
    intro n m
    rw [hDdef]
    simp only [energy1', Prod.snd_sub, Prod.fst_sub, Pi.sub_apply, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := norm_sub_le ((w n).2.1 i - T i) ((w m).2.1 i - T i)
    rw [sub_sub_sub_cancel_right] at h
    have := norm_nonneg ((w n).2.1 i - (w m).2.1 i)
    nlinarith [norm_nonneg ((w n).2.1 i - T i), norm_nonneg ((w m).2.1 i - T i),
      sq_nonneg (‖(w n).2.1 i - T i‖ - ‖(w m).2.1 i - T i‖)]
  have hE2d : ∀ n m, energy2 (w n - w m) ≤
      2 / ((n : ℝ) + 1) + 2 / ((m : ℝ) + 1) + μ * energy1' (w n - w m) := by
    intro n m
    have hp2 := energy2_parallelogram (w n) (w m)
    have hp1 := energy1'_parallelogram (w n) (w m)
    have hq := quotient_nonneg_H02 a hR (v := w n + w m)
      (by rw [← hsum n m]; exact subset_closure ⟨_, rfl⟩)
    have hn := h2 n; have hm := h2 m; have h1n := h1 n; have h1m := h1 m
    have hmul := congrArg (fun t => μ * t) hp1
    have e1 : 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) := by ring
    have e2 : 2 / ((m : ℝ) + 1) = 2 * (1 / ((m : ℝ) + 1)) := by ring
    change energy1' (w n) = 1 at h1n
    change energy1' (w m) = 1 at h1m
    change energy2 (w n) < μ + 1 / ((n : ℝ) + 1) at hn
    change energy2 (w m) < μ + 1 / ((m : ℝ) + 1) at hm
    rw [h1n, h1m] at hmul
    rw [e1, e2]
    nlinarith
  refine ⟨fun n => C * Real.sqrt (e n), ?_, fun n m x => ?_⟩
  · have hD' : Tendsto D atTop (𝓝 0) := by rw [hDdef]; exact hD
    have he : Tendsto e atTop (𝓝 0) := by
      have h1' := tendsto_two_div_nat
      have := (hD'.const_mul (2 * (K + μ))).add h1'
      rw [mul_zero, zero_add] at this
      rw [hedef]; exact this
    have := ((Real.continuous_sqrt.tendsto 0).comp he).const_mul C
    rw [Real.sqrt_zero, mul_zero] at this
    exact this
  · have hb := hC _ ((hφ n).lincomb (hφ m) 1 (-1)) x
    rw [hdiff n m] at hb
    have hx : 1 * φ n x + -1 * φ m x = φ n x - φ m x := by ring
    rw [hx] at hb
    show |φ n x - φ m x| ≤ C * Real.sqrt (e n) + C * Real.sqrt (e m)
    calc |φ n x - φ m x| ≤ C * Real.sqrt (K * energy1' (w n - w m) + energy2 (w n - w m)) := hb
      _ ≤ C * Real.sqrt (e n + e m) := by
          apply mul_le_mul_of_nonneg_left _ hC0
          apply Real.sqrt_le_sqrt
          have hA := hE1d n m
          have hB := hE2d n m
          rw [hedef]
          exact aux_energy_ineq hK0 hμ0 hA hB
      _ ≤ C * (Real.sqrt (e n) + Real.sqrt (e m)) :=
          mul_le_mul_of_nonneg_left (sqrt_add_le_add_sqrt' (he0 n) (he0 m)) hC0
      _ = C * Real.sqrt (e n) + C * Real.sqrt (e m) := by ring

/-- A sequence of continuous functions with a summable-type uniform Cauchy bound converges
uniformly to a continuous function. -/
lemma uniform_limit_of_cauchy_bound (f : ℕ → Plane → ℝ) (hf : ∀ n, Continuous (f n))
    (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0)) (h : ∀ n m x, |f n x - f m x| ≤ b n + b m) :
    ∃ Φ : Plane → ℝ, Continuous Φ ∧ (∀ x, Tendsto (fun n => f n x) atTop (𝓝 (Φ x))) ∧
      ∀ n x, |f n x - Φ x| ≤ b n := by
  have hcauchy : ∀ x, CauchySeq (fun n => f n x) := by
    intro x
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := (hb.eventually (gt_mem_nhds (half_pos hε))).exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq]
    have := h n N x
    have h1 := hN n hn; have h2 := hN N le_rfl
    linarith
  choose Φ hΦ using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hbound : ∀ n x, |f n x - Φ x| ≤ b n := by
    intro n x
    have hl : Tendsto (fun m => |f n x - f m x|) atTop (𝓝 (|f n x - Φ x|)) :=
      ((tendsto_const_nhds.sub (hΦ x)).abs)
    have hr : Tendsto (fun m => b n + b m) atTop (𝓝 (b n)) := by
      simpa using (tendsto_const_nhds (x := b n)).add hb
    exact le_of_tendsto_of_tendsto' hl hr fun m => h n m x
  refine ⟨Φ, ?_, hΦ, hbound⟩
  have hu : TendstoUniformly f Φ atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hn x
    rw [Real.dist_eq, abs_sub_comm]
    exact lt_of_le_of_lt (hbound n x) hn
  exact hu.continuous (Frequently.of_forall hf)

/-- The uniform limit of the minimizing sequence has the weak gradient given by the
`L²` limit of the gradients. -/
lemma limit_weak_identity (a : Plane) {R : ℝ}
    (φ : ℕ → Plane → ℝ) (hφ : ∀ n, IsTestFn (ball a R) (φ n)) (T : Fin 2 → L2 (ball a R))
    (hD : Tendsto (fun n => ∑ i, ‖(graphH2 ⟨φ n, hφ n⟩).2.1 i - T i‖ ^ 2) atTop (𝓝 0))
    (Φ : Plane → ℝ) (hΦ : Continuous Φ) (b : ℕ → ℝ) (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n x, |φ n x - Φ x| ≤ b n)
    {ψ : Plane → ℝ} (hψ : IsTestFn univ ψ) (i : Fin 2) :
    ∫ x, Φ x * pderiv i ψ x =
      -inner ℝ (T i) (((hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1).restrict
        (ball a R)).toLp ψ) := by
  set ψB : L2 (ball a R) :=
    ((hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1).restrict (ball a R)).toLp ψ
  have hpc : Continuous (pderiv i ψ) := (hψ.pderiv i).1.continuous
  have hps : HasCompactSupport (pderiv i ψ) := (hψ.pderiv i).2.1
  -- (a) convergence of the integrals
  have ha : Tendsto (fun n => ∫ x, φ n x * pderiv i ψ x) atTop (𝓝 (∫ x, Φ x * pderiv i ψ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hI : Integrable fun x => |pderiv i ψ x| := (hpc.abs).integrable_of_hasCompactSupport hps.abs
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      ((hb.mul_const (∫ x, |pderiv i ψ x|)).trans (by rw [zero_mul]))
    have h1 : Integrable fun x => φ n x * pderiv i ψ x :=
      ((hφ n).1.continuous.mul hpc).integrable_of_hasCompactSupport hps.mul_left
    have h2 : Integrable fun x => Φ x * pderiv i ψ x :=
      (hΦ.mul hpc).integrable_of_hasCompactSupport hps.mul_left
    rw [← integral_sub h1 h2, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hI.const_mul _) (ae_of_all _ fun x => ?_)
    rw [← sub_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound n x) (abs_nonneg _)
  -- (b) integration by parts
  have hb' : ∀ n, ∫ x, φ n x * pderiv i ψ x = -inner ℝ ((graphH2 ⟨φ n, hφ n⟩).2.1 i) ψB := by
    intro n
    simp only [graphH2, IsTestFn.toL2, ψB, inner_toLp_toLp]
    have hc : ∀ {f g : Plane → ℝ}, Continuous f → IsTestFn (ball a R) g →
        Integrable (fun x => g x * f x) := fun hf hg =>
      (hg.1.continuous.mul hf).integrable_of_hasCompactSupport hg.2.1.mul_right
    have e2 : ∫ x in ball a R, pderiv i (φ n) x * ψ x = ∫ x, pderiv i (φ n) x * ψ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        simp [((hφ n).pderiv i).eq_zero_of_notMem hx]
    rw [e2]
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure Plane))
      (f := φ n) (g := ψ) (v := EuclideanSpace.single i 1)
      (hc hψ.1.continuous ((hφ n).pderiv i)) (hc hpc (hφ n))
      (hc hψ.1.continuous (hφ n))
      (fun x _ => (hφ n).1.differentiable (by simp) x)
      (fun x _ => hψ.1.differentiable (by simp) x)
    simpa only [pderiv] using this
  -- (c) convergence of the gradients
  have hc : Tendsto (fun n => (graphH2 ⟨φ n, hφ n⟩).2.1 i) atTop (𝓝 (T i)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : Tendsto (fun n => ‖(graphH2 ⟨φ n, hφ n⟩).2.1 i - T i‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) (fun n => Finset.single_le_sum
        (f := fun j => ‖(graphH2 ⟨φ n, hφ n⟩).2.1 j - T j‖ ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)) hD
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    rw [Real.sqrt_zero] at this
    exact this.congr fun n => by simp [Real.sqrt_sq (norm_nonneg _)]
  have hlim : Tendsto (fun n => -inner ℝ ((graphH2 ⟨φ n, hφ n⟩).2.1 i) ψB) atTop
      (𝓝 (-inner ℝ (T i) ψB)) := (hc.inner tendsto_const_nhds).neg
  exact tendsto_nhds_unique ha (hlim.congr fun n => (hb' n).symm)

/-- **Lemma 12.1, quantitative form.**  For a nonempty proper open subset `W` of
`B_R(a)`, `Λ₁(W) > k²/R²`. -/
theorem bucklingEig_gt_of_ssubset_ball (a : Plane) {R : ℝ} (hR : 0 < R)
    (W : Set Plane) (hW : IsOpen W) (hne : W.Nonempty) (hsub : W ⊆ ball a R)
    (hne' : W ≠ ball a R) : jk ^ 2 / R ^ 2 < bucklingEig W := by
  have hZ := extZeros_holds
  by_contra hle
  push_neg at hle
  obtain ⟨x0, hx0B, hx0W⟩ : ∃ x0 ∈ ball a R, x0 ∉ W := by
    by_contra h
    push_neg at h
    exact hne' (Subset.antisymm hsub h)
  have hseq : ∀ n : ℕ, ∃ (φ : Plane → ℝ) (hφ : IsTestFn (ball a R) φ), tsupport φ ⊆ W ∧
      energy1' (graphH2 ⟨φ, hφ⟩) = 1 ∧
      energy2 (graphH2 ⟨φ, hφ⟩) < jk ^ 2 / R ^ 2 + 1 / ((n : ℝ) + 1) ∧
      0 ≤ ∑ i, inner ℝ ((graphH2 ⟨φ, hφ⟩).2.1 i) (gU a R i) := fun n =>
    exists_normalized_test a hW hne hsub (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
  choose φ hφ hφW hφ1 hφ2 hφP using hseq
  have hD := gradient_tendsto a hR (fun n => graphH2 ⟨φ n, hφ n⟩)
    (fun n => subset_closure ⟨_, rfl⟩) hφ1 hφ2 hφP
  obtain ⟨S, hSdef⟩ : ∃ S, S = Real.sqrt (E1U a R) := ⟨_, rfl⟩
  have hS : 0 < S := hSdef ▸ Real.sqrt_pos.mpr (E1U_pos hZ a hR)
  obtain ⟨T, hTdef⟩ : ∃ T : Fin 2 → L2 (ball a R), T = fun i => (1 / S) • gU a R i := ⟨_, rfl⟩
  replace hD : Tendsto (fun n => ∑ i, ‖(graphH2 ⟨φ n, hφ n⟩).2.1 i - T i‖ ^ 2) atTop (𝓝 0) := by
    rw [hTdef, hSdef]; exact hD
  obtain ⟨b, hb, hbd⟩ := diff_sup_bound a hR φ hφ hφ1 hφ2 T hD
  obtain ⟨Φ, hΦc, hΦlim, hΦb⟩ :=
    uniform_limit_of_cauchy_bound φ (fun n => (hφ n).1.continuous) b hb hbd
  have hΦW : ∀ x, x ∉ W → Φ x = 0 := by
    intro x hx
    have : (fun n => φ n x) = fun _ => 0 :=
      funext fun n => image_eq_zero_of_notMem_tsupport (fun h => hx (hφW n h))
    have h := hΦlim x
    rw [this] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  obtain ⟨L, hL⟩ := diskUg_lipschitz hZ a hR
  obtain ⟨F, hFdef⟩ : ∃ F : Plane → ℝ, F = fun x => Φ x - (1 / S) * diskUg a R x := ⟨_, rfl⟩
  have hFc : Continuous F := hFdef ▸ hΦc.sub (continuous_const.mul hL.continuous)
  have hFK : ∀ x, x ∉ closedBall a R → F x = 0 := by
    intro x hx
    simp only [hFdef, diskUg_eq_zero_of_notMem hx,
      hΦW x (fun h => hx (ball_subset_closedBall (hsub h))), mul_zero, sub_zero]
  have hFcs : HasCompactSupport F := HasCompactSupport.intro (isCompact_closedBall a R) hFK
  have hFL : MemLp F 2 volume := hFc.memLp_of_hasCompactSupport hFcs
  have hweak : ∀ ψ, IsTestFn univ ψ → ∀ i, ∫ x, F x * pderiv i ψ x = 0 := by
    intro ψ hψ i
    have h1 := limit_weak_identity a φ hφ T hD Φ hΦc b hb hΦb hψ i
    have h2 := integral_diskUg_mul_pderiv hZ a hR hψ i
    have hT : inner ℝ (T i) (((hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1).restrict
        (ball a R)).toLp ψ) = (1 / S) * ∫ x in ball a R, pderiv i (diskU a R) x * ψ x := by
      simp only [hTdef, real_inner_smul_left, gU, inner_toLp_toLp]
    have hpc : Continuous (pderiv i ψ) := (hψ.pderiv i).1.continuous
    have hps : HasCompactSupport (pderiv i ψ) := (hψ.pderiv i).2.1
    have i1 : Integrable fun x => Φ x * pderiv i ψ x :=
      (hΦc.mul hpc).integrable_of_hasCompactSupport hps.mul_left
    have i2 : Integrable fun x => (1 / S) * diskUg a R x * pderiv i ψ x :=
      ((continuous_const.mul hL.continuous).mul hpc).integrable_of_hasCompactSupport hps.mul_left
    have e3 : ∫ x, (1 / S) * diskUg a R x * pderiv i ψ x =
        (1 / S) * ∫ x, diskUg a R x * pderiv i ψ x := by
      rw [← integral_const_mul]; congr 1; ext x; ring
    simp only [hFdef, sub_mul]
    rw [integral_sub i1 i2, e3, h1, hT, h2]
    ring
  have hF0 := ae_eq_zero_of_weakGradient_zero extMollification_holds hFL (isCompact_closedBall a R)
    (ae_of_all _ hFK) hweak
  have hFzero : F = fun _ => 0 := (Continuous.ae_eq_iff_eq volume hFc continuous_const).mp hF0
  have hx := congrFun hFzero x0
  simp only [hFdef, hΦW x0 hx0W, diskUg_eq_of_mem hx0B, zero_sub, neg_eq_zero] at hx
  have hU := diskU_pos hZ a hR hx0B
  have : 0 < 1 / S * diskU a R x0 := by positivity
  linarith

end Buckling
end
end ChunkedSource088
/- END SOURCE 088 -/

/- BEGIN SOURCE 089: RequestProject/MainResults.lean -/
section ChunkedSource089

/-!
# Main results of the paper

* Theorem 9.21 (functional inequality),
* Theorem 10.7 (buckling–Dirichlet comparison) `Λ₁(Ω) ≥ (k²/q²) λ₁ᴰ(Ω)`,
* Lemmas 11.2 and 11.6 (the disk eigenvalues and the buckling eigenspace),
* Corollary 11.7 (optimality of the constant),
* Theorem 12.3 (the planar buckling area inequality `|Ω| Λ₁(Ω) ≥ π j_{1,1}²`, with
  equality exactly for disks).

The area inequality, its equality case and the Pólya–Szegő buckling inequality are
conditional on the Faber–Krahn inequality with equality case (E12, the only field of
`PaperExternals`); the other results are unconditional.
-/

@[expose] public section

open MeasureTheory Real Filter Topology

namespace Buckling

/-- **Sections 5–8 of the paper** (strict convexity, the quadratic estimate, the lower bound
for `z`, concavity of `G`): the inequality `d² + 4Kg² ≤ 4K²` of Proposition 4.10 on `(0, k)`. -/
theorem remaining_positivity : RemainingPositivity :=
  remaining_positivity_of_estimates

/-- **Lemma 9.3**: the even extension of `f` is `C¹` on `ℝ`. -/
theorem fExt_contDiff : ContDiff ℝ 1 fExt :=
  fExt_contDiff' extZeros_holds

/-- **Lemma 9.3**: the odd extension of `b` is `C¹` on `ℝ`. -/
theorem bExt_contDiff : ContDiff ℝ 1 bExt :=
  bExt_contDiff' extZeros_holds

/-- **Lemma 9.3**: the even extension of `G` is globally Lipschitz. -/
theorem GExt_lipschitz : ∃ L, LipschitzWith L GExt :=
  GExt_lipschitz' extZeros_holds

/-- **Lemma 9.3**: the even extension of `G` is differentiable away from `0`. -/
theorem GExt_differentiableAt (s : ℝ) (hs : s ≠ 0) :
    DifferentiableAt ℝ GExt s := by
  rcases lt_or_gt_of_ne hs with h | h
  · exact (hasDerivAt_GExt_neg extZeros_holds h).differentiableAt
  · exact (hasDerivAt_GExt_pos extZeros_holds h).differentiableAt

/-- **Lemmas 9.1, 9.3**: `f_s` and `f - s f_s` are bounded. -/
theorem fExt_bounds :
    ∃ C, ∀ s, |deriv fExt s| ≤ C ∧ |fExt s - s * deriv fExt s| ≤ C :=
  fExt_bounds' extZeros_holds

/-- **Lemmas 9.1, 9.3**: `b_s` and `b - s b_s` are bounded. -/
theorem bExt_bounds :
    ∃ C, ∀ s, |deriv bExt s| ≤ C ∧ |bExt s - s * deriv bExt s| ≤ C :=
  bExt_bounds' extZeros_holds

/-- **Lemmas 9.1, 9.3**: `G` and `s G_s` are bounded. -/
theorem GExt_bounds :
    ∃ C, ∀ s, |GExt s| ≤ C ∧ |s * deriv GExt s| ≤ C :=
  GExt_bounds' extZeros_holds

/-- **Sections 4–8 and Lemmas 9.1, 9.3 of the paper**: the one-variable profiles `f, b, G`
(parity-extended) have the regularity, boundedness, asymptotics and matrix-positivity
properties collected in `ProfileFacts`.  The matrix positivity and coupling conditions are
derived from `remaining_positivity` via the kernel identities (Propositions 4.9, 4.10). -/
theorem profile_facts : ProfileFacts := by
  obtain ⟨hM, hC⟩ := matrix_coupling_of_remaining extZeros_holds (remaining_positivity)
  exact ⟨fExt_contDiff, bExt_contDiff, GExt_lipschitz, GExt_differentiableAt,
    fExt_bounds, bExt_bounds, GExt_bounds, tendsto_fExt_div_atTop extZeros_holds,
    tendsto_fExt_div_atBot extZeros_holds, tendsto_bExt_div_atTop extZeros_holds,
    tendsto_bExt_div_atBot extZeros_holds, hM, hC⟩

/-- **Theorem 9.21 (functional inequality).**  For every real `U ∈ C_c^∞(ℝ²)`, the
function `F = 𝓕(U, |∇U|)` is compactly supported and Lipschitz, and
`∫|∇F|² - λ∫F² ≤ K(∫|ΔU|² - ∫|∇U|²)`. -/
theorem functional_inequality (U : Plane → ℝ)
    (hU : IsTestFn Set.univ U) :
    (∃ L, LipschitzWith L (transformF U)) ∧ HasCompactSupport (transformF U) ∧
      (∫ x, ‖fderiv ℝ (transformF U) x‖ ^ 2) - pLam * ∫ x, transformF U x ^ 2
        ≤ pK * ((∫ x, laplacian U x ^ 2) - ∫ x, ‖fderiv ℝ U x‖ ^ 2) :=
  functionalInequality_of_profileFacts profile_facts U hU


/-- A disk with prescribed finite positive area. -/
lemma exists_ball_volume_eq (Ω : Set Plane) (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    ∃ R : ℝ, 0 < R ∧ volume (Metric.ball (0 : Plane) R) = volume Ω ∧
      π * R ^ 2 = (volume Ω).toReal := by
  have hA : 0 < (volume Ω).toReal := ENNReal.toReal_pos h0.ne' hfin.ne
  refine ⟨Real.sqrt ((volume Ω).toReal / π), Real.sqrt_pos.mpr (div_pos hA pi_pos), ?_, ?_⟩
  · rw [EuclideanSpace.volume_ball_fin_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_pos hA pi_pos).le, ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ pi_pos.ne', ENNReal.ofReal_toReal hfin.ne]
  · rw [Real.sq_sqrt (div_pos hA pi_pos).le]; field_simp

/-- **Lemma 12.2.**  An open set equal almost everywhere to an open disk is contained
in it. -/
theorem subset_ball_of_ae_eq {Ω : Set Plane} (hΩ : IsOpen Ω) (a : Plane) {R : ℝ} (hR : 0 < R)
    (h : volume (symmDiff Ω (Metric.ball a R)) = 0) : Ω ⊆ Metric.ball a R := by
  have h1 : Ω ⊆ Metric.closedBall a R := by
    have hopen : IsOpen (Ω \ Metric.closedBall a R) := hΩ.sdiff Metric.isClosed_closedBall
    have hz : volume (Ω \ Metric.closedBall a R) = 0 := by
      apply measure_mono_null _ h
      intro x hx
      exact Or.inl ⟨hx.1, fun hb => hx.2 (Metric.ball_subset_closedBall hb)⟩
    have := (hopen.measure_eq_zero_iff volume).mp hz
    intro x hx
    by_contra hc
    have : x ∈ Ω \ Metric.closedBall a R := ⟨hx, hc⟩
    simp_all
  have := interior_mono h1
  rw [hΩ.interior_eq, interior_closedBall a hR.ne'] at this
  exact this

/-- **Lemma 10.4 (inclusion).**  If `Ω ⊆ D` with `Ω` nonempty and open, then
`Λ₁(Ω) ≥ Λ₁(D)`. -/
theorem bucklingEig_mono {Ω D : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hsub : Ω ⊆ D) :
    bucklingEig D ≤ bucklingEig Ω := by
  refine le_bucklingEig_of_test hΩ hne _ fun φ hφ => ?_
  have hD : IsTestFn D φ.1 := ⟨φ.2.1, φ.2.2.1, φ.2.2.2.trans hsub⟩
  have := bucklingEig_le (graphH2 ⟨φ.1, hD⟩) (subset_closure ⟨_, rfl⟩)
    (by rwa [energy1'_graphH2])
  rwa [energy2_graphH2, energy1'_graphH2] at this

/-- **Lemma 12.1 (strict inclusion inside a disk).**  If `W` is a nonempty proper open
subset of a disk `B`, then `Λ₁(W) > Λ₁(B)`. -/
theorem bucklingEig_lt_of_ssubset_ball (a : Plane) (R : ℝ) (hR : 0 < R)
    (W : Set Plane) (hW : IsOpen W) (hne : W.Nonempty) (hsub : W ⊆ Metric.ball a R)
    (hne' : W ≠ Metric.ball a R) :
    bucklingEig (Metric.ball a R) < bucklingEig W :=
  (bucklingEig_ball_le a hR).trans_lt
    (bucklingEig_gt_of_ssubset_ball a hR W hW hne hsub hne')

/-- **Theorem 10.7 (buckling–Dirichlet comparison).**  For every nonempty open
`Ω ⊆ ℝ²`, `Λ₁(Ω) ≥ (k²/q²) λ₁ᴰ(Ω)`, where `q = j_{0,1}` and `k = j_{1,1}`. -/
theorem buckling_ge_dirichlet (Ω : Set Plane) (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) :
    jk ^ 2 / jq ^ 2 * dirichletEig Ω ≤ bucklingEig Ω :=
  buckling_ge_dirichlet_of_functional (fun U hU => functional_inequality U hU) Ω hΩ hne

/-- **Lemma 11.2.**  `λ₁ᴰ(B_R(a)) = q²/R²`. -/
theorem dirichletEig_ball (a : Plane) (R : ℝ) (hR : 0 < R) :
    dirichletEig (Metric.ball a R) = jq ^ 2 / R ^ 2 :=
  dirichletEig_ball' a R hR

/-- **Lemma 11.6 (first part).**  `Λ₁(B_R(a)) = k²/R²`. -/
theorem bucklingEig_ball (a : Plane) (R : ℝ) (hR : 0 < R) :
    bucklingEig (Metric.ball a R) = jk ^ 2 / R ^ 2 := by
  refine le_antisymm (bucklingEig_ball_le a hR) ?_
  have hq := (parameter_signs extZeros_holds).1
  have h := buckling_ge_dirichlet (Metric.ball a R) Metric.isOpen_ball
    ⟨a, Metric.mem_ball_self hR⟩
  rw [dirichletEig_ball a R hR] at h
  calc jk ^ 2 / R ^ 2 = jk ^ 2 / jq ^ 2 * (jq ^ 2 / R ^ 2) := by field_simp
    _ ≤ _ := h

/-- **Lemma 11.6 (second part).**  Every nonzero minimizer of the buckling quotient on
`B_R(a)` is a scalar multiple of `U_{R,a}(x) = J₀(k|x-a|/R) - J₀(k)`. -/
theorem buckling_minimizer_ball (a : Plane) (R : ℝ) (hR : 0 < R)
    (v : L2 (Metric.ball a R) × (Fin 2 → L2 (Metric.ball a R)) ×
      (Fin 2 → Fin 2 → L2 (Metric.ball a R)))
    (hv : v ∈ H02 (Metric.ball a R)) (hv1 : energy1' v ≠ 0)
    (hmin : energy2 v / energy1' v = bucklingEig (Metric.ball a R)) :
    ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict (Metric.ball a R)),
      v.1 x = C * (besselJ 0 (jk * ‖x - a‖ / R) - besselJ 0 jk) := by
  rw [bucklingEig_ball a R hR, div_eq_iff hv1] at hmin
  obtain ⟨C, hC⟩ := minimizer_eq_smul_diskU a hR v hv hmin
  refine ⟨C, hC.mono fun x hx => ?_⟩
  rw [hx, diskU, clampG, radJ0_eq, div_mul_eq_mul_div]

/-- **Lemma 11.6 (third part).**  `U_{R,a}` is strictly positive in `B_R(a)`. -/
theorem buckling_eigenfunction_pos (a : Plane) (R : ℝ) (hR : 0 < R)
    (x : Plane) (hx : x ∈ Metric.ball a R) :
    0 < besselJ 0 (jk * ‖x - a‖ / R) - besselJ 0 jk := by
  have hk := (parameter_signs extZeros_holds).2.1
  have hq := (parameter_signs extZeros_holds).1
  have hx' : ‖x - a‖ < R := by rw [Metric.mem_ball, dist_eq_norm] at hx; exact hx
  have ht0 : 0 ≤ jk * ‖x - a‖ / R :=
    div_nonneg (mul_nonneg (by linarith) (norm_nonneg _)) hR.le
  have ht1 : jk * ‖x - a‖ / R < jk := by
    rw [div_lt_iff₀ hR]; exact mul_lt_mul_of_pos_left hx' (by linarith)
  have := besselJ_zero_strictAntiOn extZeros_holds ⟨ht0, ht1.le⟩ ⟨by linarith, le_rfl⟩ ht1
  linarith

/-- **Corollary 11.7 (optimality).**  The constant `k²/q²` in Theorem 10.7 cannot be
increased. -/
theorem comparison_constant_optimal (C : ℝ) (hC : jk ^ 2 / jq ^ 2 < C) :
    ∃ Ω : Set Plane, IsOpen Ω ∧ Ω.Nonempty ∧ bucklingEig Ω < C * dirichletEig Ω := by
  have hq := (parameter_signs extZeros_holds).1
  refine ⟨Metric.ball 0 1, Metric.isOpen_ball, ⟨0, Metric.mem_ball_self one_pos⟩, ?_⟩
  rw [dirichletEig_ball 0 1 one_pos]
  have hle := bucklingEig_ball_le (0 : Plane) one_pos
  have hq2 : 0 < jq ^ 2 := by positivity
  have := mul_lt_mul_of_pos_right hC hq2
  rw [div_mul_cancel₀ _ hq2.ne'] at this
  simp only [one_pow, div_one] at hle ⊢
  linarith

/-- **Theorem 12.3 (the planar buckling area inequality).**  For every open
`Ω ⊆ ℝ²` with `0 < |Ω| < ∞`, `|Ω| Λ₁(Ω) ≥ π j_{1,1}²`. -/
theorem area_inequality (hE : PaperExternals) (Ω : Set Plane) (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    π * jk ^ 2 ≤ (volume Ω).toReal * bucklingEig Ω := by
  have hq := (parameter_signs extZeros_holds).1
  have hne : Ω.Nonempty := Set.nonempty_iff_ne_empty.mpr (by rintro rfl; simp at h0)
  obtain ⟨R, hR, hvol, hA⟩ := exists_ball_volume_eq Ω h0 hfin
  have hFK := (hE.faberKrahn Ω hΩ h0 hfin R hR hvol).1
  rw [dirichletEig_ball 0 R hR] at hFK
  have hmain := buckling_ge_dirichlet Ω hΩ hne
  have hA0 : 0 ≤ (volume Ω).toReal := ENNReal.toReal_nonneg
  have hk2 : 0 ≤ jk ^ 2 / jq ^ 2 := by positivity
  calc π * jk ^ 2 = (volume Ω).toReal * (jk ^ 2 / jq ^ 2 * (jq ^ 2 / R ^ 2)) := by
        rw [← hA]; field_simp
    _ ≤ (volume Ω).toReal * (jk ^ 2 / jq ^ 2 * dirichletEig Ω) := by gcongr
    _ ≤ (volume Ω).toReal * bucklingEig Ω := by gcongr

/-- **Theorem 12.3 (equality case).**  Equality holds in the area inequality if and
only if `Ω` is an open disk `B_R(a)`. -/
theorem area_equality_iff (hE : PaperExternals) (Ω : Set Plane) (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    (volume Ω).toReal * bucklingEig Ω = π * jk ^ 2 ↔
      ∃ (a : Plane) (R : ℝ), 0 < R ∧ Ω = Metric.ball a R := by
  have hq := (parameter_signs extZeros_holds).1
  have hne : Ω.Nonempty := Set.nonempty_iff_ne_empty.mpr (by rintro rfl; simp at h0)
  have hA : 0 < (volume Ω).toReal := ENNReal.toReal_pos h0.ne' hfin.ne
  constructor
  · intro heq
    obtain ⟨R, hR, hvol, hAR⟩ := exists_ball_volume_eq Ω h0 hfin
    have hFK := hE.faberKrahn Ω hΩ h0 hfin R hR hvol
    have hball := dirichletEig_ball 0 R hR
    have hmain := buckling_ge_dirichlet Ω hΩ hne
    have hk2 : 0 < jk ^ 2 / jq ^ 2 := by
      have := (parameter_signs extZeros_holds).2.1
      exact div_pos (pow_pos (by linarith) 2) (pow_pos hq 2)
    -- equality forces `λ₁ᴰ(Ω) = q²/R²`
    have hD : dirichletEig Ω = jq ^ 2 / R ^ 2 := by
      apply le_antisymm _ (hball ▸ hFK.1)
      have h1 : (volume Ω).toReal * (jk ^ 2 / jq ^ 2 * dirichletEig Ω) ≤
          (volume Ω).toReal * (jk ^ 2 / jq ^ 2 * (jq ^ 2 / R ^ 2)) := by
        calc _ ≤ (volume Ω).toReal * bucklingEig Ω := by gcongr
          _ = _ := by rw [heq, ← hAR]; field_simp
      have h2 := le_of_mul_le_mul_left h1 hA
      exact le_of_mul_le_mul_left h2 hk2
    obtain ⟨a, ha⟩ := hFK.2 (hD.trans hball.symm)
    have hsub := subset_ball_of_ae_eq hΩ a hR ha
    refine ⟨a, R, hR, ?_⟩
    by_contra hne'
    have hlt := bucklingEig_lt_of_ssubset_ball a R hR Ω hΩ hne hsub hne'
    rw [bucklingEig_ball a R hR] at hlt
    have : bucklingEig Ω = jk ^ 2 / R ^ 2 := by
      rw [← hAR] at heq
      have hR2 : 0 < π * R ^ 2 := by positivity
      field_simp
      nlinarith [heq]
    linarith
  · rintro ⟨a, R, hR, rfl⟩
    rw [bucklingEig_ball a R hR, EuclideanSpace.volume_ball_fin_two,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
      ENNReal.toReal_ofReal pi_pos.le]
    field_simp

/-- **`conj:PS` in dimension two (Pólya–Szegő buckling inequality)**, deduced from
Theorem 12.3 and Lemma 11.6.  If `Ω ⊆ ℝ²` is open with `0 < |Ω| < ∞` and `πR² = |Ω|`, then
`Λ₁(Ω) ≥ Λ₁(B_R(0))`, with equality iff `Ω` is a disk of radius `R`. -/
theorem polya_szego_buckling (hE : PaperExternals) (Ω : Set Plane) (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) (R : ℝ) (hR : 0 < R)
    (hvol : π * R ^ 2 = (volume Ω).toReal) :
    bucklingEig (Metric.ball (0 : Plane) R) ≤ bucklingEig Ω ∧
      (bucklingEig Ω = bucklingEig (Metric.ball (0 : Plane) R) ↔
        ∃ a : Plane, Ω = Metric.ball a R) := by
  have hR2 : 0 < π * R ^ 2 := by positivity
  have hball := bucklingEig_ball 0 R hR
  have hineq := area_inequality hE Ω hΩ h0 hfin
  have hiff := area_equality_iff hE Ω hΩ h0 hfin
  rw [← hvol] at hineq hiff
  rw [hball]
  refine ⟨?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]; nlinarith
  · constructor
    · intro heq
      obtain ⟨a, R', hR', rfl⟩ := hiff.mp (by rw [heq]; field_simp)
      refine ⟨a, ?_⟩
      have hv : (volume (Metric.ball a R')).toReal = π * R' ^ 2 := by
        rw [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul, ENNReal.toReal_pow,
          ENNReal.toReal_ofReal hR'.le, ENNReal.toReal_ofReal pi_pos.le]; ring
      have : R' ^ 2 = R ^ 2 := by
        have := hvol.trans hv
        have hp := pi_pos
        nlinarith
      have : R' = R := by nlinarith
      rw [this]
    · rintro ⟨a, rfl⟩
      rw [bucklingEig_ball a R hR]

end Buckling
end
end ChunkedSource089
/- END SOURCE 089 -/

