module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPLogTest
public import PositiveCompactWeakTesting
public import WeakSMPCaccioppoliAlgebra

/-!
# A real integrated logarithmic Caccioppoli estimate

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The input is the original nonnegative smooth-test supersolution inequality,
actual full-space L2 weak-gradient data, and nonnegativity only almost
everywhere in the open test domain. The nonlinear compact weak test is
produced by WeakSMPLogTest and justified by positive L2 approximation.

All real-integral densities below are proved integrable. In particular the
uncut reciprocal R_delta(w), whose value at zero is nonzero, is never
asserted to be globally L2. The weighted energy is a sum of genuine L2
pairings. No Poincare inequality or strong maximum principle is asserted.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.WeakSMPIntegratedCaccioppoli

open EllipticPdes EllipticPdes.Embedding WeakSMPRegularizers

def firstTerm (δ : ℝ) (χ w : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  2 * χ x * pderiv i χ x * reciprocal δ (w x)

def weightedGradient (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  χ x ^ 2 * (reciprocal δ (w x) / radius δ (w x)) * g i x

def weightedEnergy (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (x : Plane) : ℝ :=
  χ x ^ 2 * (reciprocal δ (w x) / radius δ (w x)) * (∑ i, g i x ^ 2)

def crossDensity (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (x : Plane) : ℝ :=
  2 * χ x * reciprocal δ (w x) * (∑ i, g i x * pderiv i χ x)

def cutoffEnergy (χ : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i, pderiv i χ x ^ 2

def logGradient (δ : ℝ) (w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  g i x / radius δ (w x)

def logEnergy (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (x : Plane) : ℝ :=
  χ x ^ 2 * (∑ i, logGradient δ w g i x ^ 2)

lemma memLp_firstTerm {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    (i : Fin 2) : MemLp (firstTerm δ χ w i) 2 volume := by
  exact WeakSMPLogTest.memLp_compact_mul_reciprocal hδ
    ((continuous_const.mul hχ.1.continuous).mul (hχ.pderiv i).1.continuous)
    ((hχ.2.1.comp_left (g := fun t : ℝ => 2 * t) (by simp)).mul_right) hw

/-- The weighted factor is really L2: it is the difference of the two
already produced L2 parts of the nonlinear test gradient. -/
lemma memLp_weightedGradient {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume) (i : Fin 2) :
    MemLp (weightedGradient δ χ w g i) 2 volume := by
  have heq : weightedGradient δ χ w g i =
      firstTerm δ χ w i - WeakSMPLogTest.testGradient δ χ w g i := by
    funext x
    simp only [weightedGradient, firstTerm, WeakSMPLogTest.testGradient, Pi.sub_apply]
    ring
  rw [heq]
  exact (memLp_firstTerm hχ hδ hw i).sub
    (WeakSMPLogTest.memLp_testGradient hχ hδ hw hg i)

lemma weightedEnergy_eq_sum (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (x : Plane) :
    weightedEnergy δ χ w g x = ∑ i, g i x * weightedGradient δ χ w g i x := by
  unfold weightedEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold weightedGradient
  ring

lemma crossDensity_eq_sum (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (x : Plane) :
    crossDensity δ χ w g x = ∑ i, g i x * firstTerm δ χ w i x := by
  unfold crossDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold firstTerm
  ring

lemma integrable_weightedEnergy {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume) :
    Integrable (weightedEnergy δ χ w g) volume := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    (hg i).integrable_mul (memLp_weightedGradient hχ hδ hw hg i))
  simpa only [Pi.mul_apply, ← weightedEnergy_eq_sum] using! hsum

lemma integrable_crossDensity {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume) :
    Integrable (crossDensity δ χ w g) volume := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    (hg i).integrable_mul (memLp_firstTerm hχ hδ hw i))
  simpa only [Pi.mul_apply, ← crossDensity_eq_sum] using! hsum

lemma integrable_cutoffEnergy {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ) :
    Integrable (cutoffEnergy χ) volume := by
  exact integrable_finsetSum Finset.univ (fun i _ =>
    (((hχ.pderiv i).1.continuous.memLp_of_hasCompactSupport
      (hχ.pderiv i).2.1 : MemLp (pderiv i χ) 2 volume)).integrable_sq)

lemma test_pairing_eq_cross_sub_energy (δ : ℝ) (χ w : Plane → ℝ)
    (g : Fin 2 → Plane → ℝ) (x : Plane) :
    (∑ i, g i x * WeakSMPLogTest.testGradient δ χ w g i x) =
      crossDensity δ χ w g x - weightedEnergy δ χ w g x := by
  rw [crossDensity_eq_sum, weightedEnergy_eq_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [WeakSMPLogTest.testGradient, firstTerm, weightedGradient]
  ring

/-- The original smooth-test inequality is actually evaluated on the
nonlinear weak test, using its produced data and positive mollification. -/
theorem integral_weightedEnergy_le_crossDensity {D : Set Plane} (hD : IsOpen D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) {δ : ℝ} (hδ : 0 < δ)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    (∫ x, weightedEnergy δ χ w g x) ≤ ∫ x, crossDensity δ χ w g x := by
  obtain ⟨hp, hc, hs, hψ, hξ, hψweak⟩ :=
    WeakSMPLogTest.nonlinear_test_data hχ hδ hw hg hweak
  have htest := PositiveCompactWeakTesting.extend_nonnegative_compact_weak_test
    hD hg hsuper hp hc hs hψ hξ hψweak
  have hpair : ∀ i, Integrable
      (fun x => g i x * WeakSMPLogTest.testGradient δ χ w g i x) volume :=
    fun i => (hg i).integrable_mul (hξ i)
  have heq : (fun x => ∑ i, g i x * WeakSMPLogTest.testGradient δ χ w g i x) =
      (fun x => crossDensity δ χ w g x - weightedEnergy δ χ w g x) :=
    funext (test_pairing_eq_cross_sub_energy δ χ w g)
  rw [← integral_finsetSum Finset.univ (fun i _ => hpair i), heq,
    integral_sub (integrable_crossDensity hχ hδ hw hg)
      (integrable_weightedEnergy hχ hδ hw hg)] at htest
  linarith

lemma cutoff_and_derivatives_zero_outside {D : Set Plane} {χ : Plane → ℝ}
    (hχ : IsTestFn D χ) {x : Plane} (hx : x ∉ D) :
    χ x = 0 ∧ ∀ i, pderiv i χ x = 0 := by
  refine ⟨image_eq_zero_of_notMem_tsupport (fun h => hx (hχ.2.2 h)), ?_⟩
  intro i
  exact image_eq_zero_of_notMem_tsupport (fun h => hx ((hχ.pderiv i).2.2 h))

lemma crossDensity_le_half_energy_ae {D : Set Plane} (hD : IsOpen D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) {δ : ℝ} (hδ : 0 < δ)
    {w : Plane → ℝ} (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (g : Fin 2 → Plane → ℝ) :
    ∀ᵐ x ∂volume, crossDensity δ χ w g x ≤
      weightedEnergy δ χ w g x / 2 + 2 * cutoffEnergy χ x := by
  have hcond := (ae_restrict_iff' hD.measurableSet).mp hw0
  filter_upwards [hcond] with x hx
  by_cases hxD : x ∈ D
  · exact reciprocal_cross_sum_le_half_energy hδ (hx hxD) (χ x)
      (fun i => g i x) (fun i => pderiv i χ x)
  · obtain ⟨hχ0, hd0⟩ := cutoff_and_derivatives_zero_outside hχ hxD
    simp only [crossDensity, weightedEnergy, cutoffEnergy, hχ0, hd0,
      zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Finset.sum_const_zero,
      zero_div, zero_add, le_refl]

/-- The weighted reciprocal energy is bounded by four times the cutoff
energy. Nonnegativity of w is needed only almost everywhere in D. -/
theorem integral_weightedEnergy_le_four_cutoff {D : Set Plane} (hD : IsOpen D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) {δ : ℝ} (hδ : 0 < δ)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    (∫ x, weightedEnergy δ χ w g x) ≤ 4 * ∫ x, cutoffEnergy χ x := by
  have hF := integrable_weightedEnergy hχ hδ hw hg
  have hG := integrable_crossDensity hχ hδ hw hg
  have hC := integrable_cutoffEnergy hχ
  have hFG := integral_weightedEnergy_le_crossDensity hD hχ hδ hw hg hweak hsuper
  have hYoung := integral_mono_ae hG ((hF.div_const 2).add (hC.const_mul 2))
    (crossDensity_le_half_energy_ae hD hχ hδ hw0 g)
  change (∫ x, crossDensity δ χ w g x) ≤
    ∫ x, weightedEnergy δ χ w g x / 2 + 2 * cutoffEnergy χ x at hYoung
  rw [integral_add (hF.div_const 2) (hC.const_mul 2), integral_div,
    integral_const_mul] at hYoung
  linarith

lemma memLp_logGradient {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ}
    (hw : MemLp w 2 volume) {g : Fin 2 → Plane → ℝ}
    (hg : ∀ i, MemLp (g i) 2 volume) (i : Fin 2) :
    MemLp (logGradient δ w g i) 2 volume := by
  have hq : Continuous (fun t : ℝ => 1 / radius δ t) :=
    continuous_const.div (contDiff_radius hδ).continuous (fun t => (radius_pos hδ t).ne')
  have h := WeakSMPLogTest.memLp_bounded_mul
    (hq.comp_aestronglyMeasurable hw.aestronglyMeasurable) (hg i) (1 / δ) (fun x => by
      rw [abs_of_pos (one_div_pos.mpr (radius_pos hδ (w x)))]
      exact one_div_le_one_div_of_le hδ (delta_le_radius hδ (w x)))
  simpa only [logGradient, one_div_mul_eq_div] using! h

lemma integrable_logEnergy {D : Set Plane} {χ : Plane → ℝ} (hχ : IsTestFn D χ)
    {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume) :
    Integrable (logEnergy δ χ w g) volume := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ =>
    (WeakSMPLogTest.memLp_compact_continuous_mul hχ.1.continuous hχ.2.1
      (memLp_logGradient hδ hw hg i)).integrable_sq)
  have heq : (fun x => ∑ i, (χ x * logGradient δ w g i x) ^ 2) =
      logEnergy δ χ w g := by
    funext x
    simp only [logEnergy, mul_pow, Finset.mul_sum]
  rw [heq] at hsum
  exact hsum

lemma square_div_radius_le {δ : ℝ} (hδ : 0 < δ) (t a : ℝ) :
    (a / radius δ t) ^ 2 ≤ 2 * (reciprocal δ t / radius δ t) * a ^ 2 := by
  have h := mul_le_mul_of_nonneg_right
    (one_div_radius_sq_le_two_reciprocal_div_radius hδ t) (sq_nonneg a)
  calc
    (a / radius δ t) ^ 2 = (1 / radius δ t ^ 2) * a ^ 2 := by
      rw [div_pow]
      ring
    _ ≤ (2 * reciprocal δ t / radius δ t) * a ^ 2 := h
    _ = 2 * (reciprocal δ t / radius δ t) * a ^ 2 := by ring

lemma logEnergy_le_two_weightedEnergy {δ : ℝ} (hδ : 0 < δ)
    (χ w : Plane → ℝ) (g : Fin 2 → Plane → ℝ) (x : Plane) :
    logEnergy δ χ w g x ≤ 2 * weightedEnergy δ χ w g x := by
  have hsum : (∑ i, logGradient δ w g i x ^ 2) ≤
      ∑ i, 2 * (reciprocal δ (w x) / radius δ (w x)) * g i x ^ 2 :=
    Finset.sum_le_sum fun i _ => square_div_radius_le hδ (w x) (g i x)
  have h := mul_le_mul_of_nonneg_left hsum (sq_nonneg (χ x))
  simpa only [logEnergy, weightedEnergy, ← Finset.mul_sum, ← Finset.sum_mul, mul_assoc, mul_left_comm,
    mul_comm] using! h

/-- The actual logarithmic gradient density has the uniform Caccioppoli
bound. No nonlinear-test admissibility or energy integrability is assumed. -/
theorem integral_logEnergy_le_eight_cutoff {D : Set Plane} (hD : IsOpen D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) {δ : ℝ} (hδ : 0 < δ)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    (∫ x, logEnergy δ χ w g x) ≤ 8 * ∫ x, cutoffEnergy χ x := by
  have hF := integrable_weightedEnergy hχ hδ hw hg
  have hB := integrable_logEnergy hχ hδ hw hg
  have hBF := integral_mono hB (hF.const_mul 2)
    (logEnergy_le_two_weightedEnergy hδ χ w g)
  rw [integral_const_mul] at hBF
  have hFC := integral_weightedEnergy_le_four_cutoff hD hχ hδ hw hg hweak hw0 hsuper
  linarith

/-- The bounded scalar derivative gives the actual global L2 logarithm. -/
def logarithmDerivativeBound (δ : ℝ) : ℝ≥0 := ⟨|1 / δ|, abs_nonneg _⟩

lemma nnnorm_deriv_logarithm_le {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    ‖deriv (logarithm δ) t‖₊ ≤ logarithmDerivativeBound δ := by
  apply NNReal.coe_le_coe.mp
  simpa only [logarithmDerivativeBound, NNReal.coe_mk, coe_nnnorm, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hδ)] using! abs_deriv_logarithm_le hδ t

lemma memLp_logarithm {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ}
    (hw : MemLp w 2 volume) : MemLp (fun x => logarithm δ (w x)) 2 volume := by
  have hLip : LipschitzWith (logarithmDerivativeBound δ) (logarithm δ) :=
    lipschitzWith_of_nnnorm_deriv_le
      ((contDiff_logarithm δ).differentiable (by simp))
      (nnnorm_deriv_logarithm_le hδ)
  simpa only [Function.comp_def] using hLip.comp_memLp (logarithm_zero δ) hw

/-- The density controlled above is the square of the actual weak
gradient of the actual global logarithm, rather than a formal expression. -/
theorem hasWeakGradOn_logarithm {δ : ℝ} (hδ : 0 < δ) {w : Plane → ℝ}
    (hw : MemLp w 2 volume) {g : Fin 2 → Plane → ℝ}
    (hg : ∀ i, MemLp (g i) 2 volume) (hweak : HasWeakGradOn univ w g) :
    HasWeakGradOn univ (fun x => logarithm δ (w x)) (logGradient δ w g) := by
  have hL1 : ContDiff ℝ 1 (logarithm δ) :=
    (contDiff_logarithm δ).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  have h := hasWeakGradOn_comp isOpen_univ
    ((hw.locallyIntegrable one_le_two).locallyIntegrableOn _)
    (fun i => ((hg i).locallyIntegrable one_le_two).locallyIntegrableOn _)
    hweak hL1 (nnnorm_deriv_logarithm_le hδ)
  have hgrad : (fun i x => deriv (logarithm δ) (w x) * g i x) =
      logGradient δ w g := by
    funext i x
    rw [(hasDerivAt_logarithm hδ (w x)).deriv]
    simp only [logGradient, one_div_mul_eq_div]
  rw [hgrad] at h
  exact h

/-- A single consumer interface: actual logarithm L2 data, actual weak
gradient, actual real integrability, and its integrated energy bound. -/
theorem logarithmic_caccioppoli_data {D : Set Plane} (hD : IsOpen D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) {δ : ℝ} (hδ : 0 < δ)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    MemLp (fun x => logarithm δ (w x)) 2 volume ∧
      (∀ i, MemLp (logGradient δ w g i) 2 volume) ∧
      HasWeakGradOn univ (fun x => logarithm δ (w x)) (logGradient δ w g) ∧
      Integrable (logEnergy δ χ w g) volume ∧
      (∫ x, logEnergy δ χ w g x) ≤ 8 * ∫ x, cutoffEnergy χ x :=
  ⟨memLp_logarithm hδ hw, memLp_logGradient hδ hw hg,
    hasWeakGradOn_logarithm hδ hw hg hweak, integrable_logEnergy hχ hδ hw hg,
    integral_logEnergy_le_eight_cutoff hD hχ hδ hw hg hweak hw0 hsuper⟩

end Buckling.WeakSMPIntegratedCaccioppoli

end

end
