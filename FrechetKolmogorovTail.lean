module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EllipticPdes.Analysis.FrechetKolmogorov

/-!
# Finite-grid approximation with an L2 tail

SOURCE_DRAFT, Lean 4.35-rc3 only; NOT compiled.
The dependency is EllipticPDE commit
ec784093f30308ef770ff855ce624725adf6f870, lean/ subdirectory.

This extends the pinned library's finite-grid estimates to functions without
bounded support. The generic criterion below consumes uniform L2 tails; it
does not assert or assume finite-area H01 compactness.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter
open EllipticPdes.Analysis.FrechetKolmogorov
open scoped ENNReal RealInnerProductSpace

namespace FaberKrahnDevelopment.FrechetKolmogorovTail

variable {n : ℕ}

/-- The grid approximation error includes the actual square-integral tail
outside the selected cubes. No support condition is imposed on `g`. -/
theorem norm_sq_sub_avg_eq_add_tail {η : ℝ} (hη : 0 < η)
    {K : Finset (Fin n → ℤ)} {g : EucL2 n} :
    ‖g - avg η K g‖ ^ 2 =
      (∑ k ∈ K, ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2) +
        ∫ x in (⋃ k ∈ K, cube η k)ᶜ, (g x) ^ 2 := by
  classical
  let U : Set (EuclideanSpace ℝ (Fin n)) := ⋃ k ∈ K, cube η k
  have hU : MeasurableSet U :=
    Finset.measurableSet_biUnion K (fun k _ => measurableSet_cube η k)
  have hf : Integrable (fun x => ((g - avg η K g) x) ^ 2) volume :=
    (Lp.memLp (g - avg η K g)).integrable_sq
  have hpart : (∫ x in U, ((g - avg η K g) x) ^ 2) =
      ∑ k ∈ K, ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2 := by
    change (∫ x in ⋃ k ∈ K, cube η k, ((g - avg η K g) x) ^ 2) = _
    rw [integral_biUnion_finset K (fun k _ => measurableSet_cube η k)
      (fun i _ j _ hij => cube_disjoint hη hij) (fun _ _ => hf.integrableOn)]
    refine Finset.sum_congr rfl (fun k hk => integral_congr_ae ?_)
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub g (avg η K g)),
      ae_restrict_of_ae (coeFn_avg η K g),
      ae_restrict_mem (measurableSet_cube η k)] with x hsub havg hx
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [havg, stepFun_eq_on_cube hη hk hx]
  have htail : (∫ x in Uᶜ, ((g - avg η K g) x) ^ 2) =
      ∫ x in Uᶜ, (g x) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub g (avg η K g)),
      ae_restrict_of_ae (coeFn_avg η K g),
      ae_restrict_mem hU.compl] with x hsub havg hx
    have hstep : stepFun η K g x = 0 := by
      unfold stepFun
      refine Finset.sum_eq_zero (fun k hk => ?_)
      rw [Set.indicator_of_notMem
        (fun hxk => hx (Set.mem_iUnion₂.mpr ⟨k, hk, hxk⟩)), mul_zero]
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [havg, hstep, sub_zero]
  calc
    ‖g - avg η K g‖ ^ 2 =
        (∫ x in U, ((g - avg η K g) x) ^ 2) +
          ∫ x in Uᶜ, ((g - avg η K g) x) ^ 2 := by
      rw [norm_sq_eq_integral_sq]
      exact (integral_add_compl hU hf).symm
    _ = _ := by rw [hpart, htail]

/-- Existing per-cube variance and translation estimates apply to the
untruncated function; its omitted tail remains explicit. -/
theorem norm_sq_sub_avg_le_translation_add_tail {η : ℝ} (hη : 0 < η)
    {K : Finset (Fin n → ℤ)} {g : EucL2 n} :
    ‖g - avg η K g‖ ^ 2 ≤
      (η ^ n)⁻¹ * (∫ w in dbox η, ‖transL2 w g - g‖ ^ 2) +
        ∫ x in (⋃ k ∈ K, cube η k)ᶜ, (g x) ^ 2 := by
  rw [norm_sq_sub_avg_eq_add_tail hη]
  refine add_le_add ?_ le_rfl
  calc
    (∑ k ∈ K, ∫ x in cube η k, (g x - cubeCoef η k g) ^ 2) ≤
        ∑ k ∈ K, (η ^ n)⁻¹ * ∫ x in cube η k,
          ∫ y in cube η k, (g x - g y) ^ 2 :=
      Finset.sum_le_sum (fun k _ => cube_variance_le hη k g)
    _ = (η ^ n)⁻¹ * ∑ k ∈ K, ∫ x in cube η k,
        ∫ y in cube η k, (g x - g y) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (η ^ n)⁻¹ * ∫ w in dbox η, ‖transL2 w g - g‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (sum_cube_double_le_translation hη K g)
        (inv_nonneg.mpr (pow_nonneg hη.le n))

/-- A grid covering a ball has error controlled by the translation modulus
and the actual tail outside that ball. -/
theorem norm_sq_sub_avg_le_const_add_ball_tail {η : ℝ} (hη : 0 < η)
    {K : Finset (Fin n → ℤ)} {g : EucL2 n} {Λ R : ℝ}
    (hcover : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆
      ⋃ k ∈ K, cube η k)
    (hmod : ∀ h, ‖transL2 h g - g‖ ≤ Λ * ‖h‖) :
    ‖g - avg η K g‖ ^ 2 ≤ 2 ^ n * n * Λ ^ 2 * η ^ 2 +
      ∫ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, (g x) ^ 2 := by
  have hne : (η : ℝ) ^ n ≠ 0 := (pow_pos hη n).ne'
  have hbound : (∫ w in dbox η, ‖transL2 w g - g‖ ^ 2) ≤
      (2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2)) := by
    have hpt : ∀ w ∈ dbox η, ‖transL2 w g - g‖ ^ 2 ≤ Λ ^ 2 * (n * η ^ 2) := by
      intro w hw
      have h1 : ‖transL2 w g - g‖ ^ 2 ≤ (Λ * ‖w‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hmod w) 2
      have h2 : ‖w‖ ^ 2 ≤ n * η ^ 2 := normSq_le_of_mem_dbox hw
      nlinarith [norm_nonneg w, sq_nonneg Λ]
    calc
      (∫ w in dbox η, ‖transL2 w g - g‖ ^ 2) ≤
          ∫ _w in dbox η, Λ ^ 2 * (n * η ^ 2) :=
        setIntegral_mono_on (integrableOn_dbox_translation_modulus g)
          (integrableOn_const (volume_dbox_ne_top η)) (measurableSet_dbox η) hpt
      _ = (2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2)) := by
        rw [setIntegral_const, smul_eq_mul, volume_real_dbox hη.le]
  have htail : (∫ x in (⋃ k ∈ K, cube η k)ᶜ, (g x) ^ 2) ≤
      ∫ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, (g x) ^ 2 := by
    exact setIntegral_mono_set (Lp.memLp g).integrable_sq.integrableOn
      (Filter.Eventually.of_forall fun x => sq_nonneg (g x))
      (Filter.Eventually.of_forall fun x hx hxball => hx (hcover hxball))
  have halgebra : (η ^ n)⁻¹ * ((2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2))) =
      2 ^ n * n * Λ ^ 2 * η ^ 2 := by rw [mul_pow]; field_simp
  calc
    ‖g - avg η K g‖ ^ 2 ≤
        (η ^ n)⁻¹ * (∫ w in dbox η, ‖transL2 w g - g‖ ^ 2) +
          ∫ x in (⋃ k ∈ K, cube η k)ᶜ, (g x) ^ 2 :=
      norm_sq_sub_avg_le_translation_add_tail hη
    _ ≤ (η ^ n)⁻¹ * ((2 * η) ^ n * (Λ ^ 2 * (n * η ^ 2))) +
        ∫ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, (g x) ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_left hbound
        (inv_nonneg.mpr (pow_nonneg hη.le n))) htail
    _ = _ := by rw [halgebra]

/-- Uniformly bounded L2 functions with a uniform Lipschitz translation
modulus and uniformly vanishing L2 tails form a totally bounded set.
This is a generic criterion; the three hypotheses must be produced for
any subsequent Sobolev application. -/
theorem totallyBounded_of_lipschitz_translation_uniform_tails
    (S : Set (EucL2 n)) {M Λ : ℝ}
    (hbdd : ∀ g ∈ S, ‖g‖ ≤ M)
    (hmod : ∀ g ∈ S, ∀ h, ‖transL2 h g - g‖ ≤ Λ * ‖h‖)
    (htail : ∀ ε > 0, ∃ R : ℝ, ∀ g ∈ S,
      (∫ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, (g x) ^ 2) < ε) :
    TotallyBounded S := by
  classical
  apply totallyBounded_of_approx
  intro ε hε
  have hεhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨R, hR⟩ := htail ((ε / 2) ^ 2) (pow_pos hεhalf 2)
  set D : ℝ := 2 ^ n * n * Λ ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt D := Real.sqrt_nonneg _
  have hden : 0 < Real.sqrt D + 1 := by linarith
  set η : ℝ := (ε / 2) / (Real.sqrt D + 1) with hη_def
  have hη : 0 < η := div_pos hεhalf hden
  set K : Finset (Fin n → ℤ) :=
    Fintype.piFinset (fun _ : Fin n => Finset.Icc (-(⌈R / η⌉ + 1)) (⌈R / η⌉ + 1))
  have hDη : D * η ^ 2 < (ε / 2) ^ 2 := by
    have hs : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0
    have hη2 : η ^ 2 * (Real.sqrt D + 1) ^ 2 = (ε / 2) ^ 2 := by
      rw [hη_def, div_pow]; field_simp
    have key : D * η ^ 2 * (Real.sqrt D + 1) ^ 2 <
        (ε / 2) ^ 2 * (Real.sqrt D + 1) ^ 2 := by
      calc
        D * η ^ 2 * (Real.sqrt D + 1) ^ 2 = D * (ε / 2) ^ 2 := by
          rw [mul_assoc, hη2]
        _ < (ε / 2) ^ 2 * (Real.sqrt D + 1) ^ 2 := by
          nlinarith [hs, mul_nonneg (sq_nonneg (ε / 2)) hsqrt0,
            mul_pos hεhalf hεhalf]
    exact lt_of_mul_lt_mul_right key (by positivity)
  have happrox : ∀ g ∈ S, ‖g - avg η K g‖ < ε := by
    intro g hg
    have hb : ‖g - avg η K g‖ ^ 2 ≤ D * η ^ 2 +
        ∫ x in (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ, (g x) ^ 2 := by
      rw [hD]
      exact norm_sq_sub_avg_le_const_add_ball_tail hη
        (closedBall_subset_iUnion_cube hη R) (hmod g hg)
    have hlt : ‖g - avg η K g‖ ^ 2 < ε ^ 2 := by nlinarith [hR g hg]
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  refine ⟨avg η K '' S, ?_, ?_⟩
  · have : FiniteDimensional ℝ
        (Submodule.span ℝ (cubeIndicator η '' (K : Set (Fin n → ℤ)))) :=
      FiniteDimensional.span_of_finite ℝ (K.finite_toSet.image _)
    refine totallyBounded_of_finiteDimensional_bounded
      (Submodule.span ℝ (cubeIndicator η '' (K : Set (Fin n → ℤ)))) ?_ ?_
    · rintro _ ⟨g, _, rfl⟩
      exact avg_mem_span η K g
    · apply (Metric.isBounded_closedBall (x := (0 : EucL2 n)) (r := M + ε)).subset
      rintro _ ⟨g, hg, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      have htri : ‖avg η K g‖ ≤ ‖g‖ + ‖g - avg η K g‖ :=
        calc
          ‖avg η K g‖ = ‖g - (g - avg η K g)‖ := by congr 1; abel
          _ ≤ ‖g‖ + ‖g - avg η K g‖ := norm_sub_le _ _
      linarith [hbdd g hg, (happrox g hg).le]
  · intro g hg
    refine ⟨avg η K g, ⟨g, hg, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    exact happrox g hg

end FaberKrahnDevelopment.FrechetKolmogorovTail

end

end
