module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import CutoffEnergyEstimate
public import FiniteOrbitEnergies
public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Finite actual cutoff Rayleigh and real derivative-energy bounds

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.
The original project's proved compact-Lipschitz integrability, mollification,
and disk ground-state theorems are consumed through its separately built
MainResults import. The actual cutoff gives global Lipschitz multiplication,
compact support strictly inside the larger open disk, and H01 admissibility.
No nonzero-mass hypothesis is needed for the lower bound.

All three gradient-square integrability facts are produced: the input `f`
from its literal common support, the actual smooth cutoff from its compact
support, and `χf` from its constructed Lipschitz regularity and compact support.
The real integral estimate then follows from the proved a.e. cutoff estimate.
No energy bound, integrability, gradient convergence, spectral inequality, or
good limit is supplied as an input. This is a finite-function consumer only;
no limit in ε or δ is taken here. Actual compilation and axiom inspection of
this module and its dependency chain remain required.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped NNReal

namespace FaberKrahnDevelopment.EuclideanReflection

/-- The literal smooth compact cutoff is a global Lipschitz function. -/
lemma spectralCutoff_lipschitz (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ L : ℝ≥0, LipschitzWith L (spectralCutoff R ε hR hε : Plane → ℝ) := by
  have htest : Buckling.IsTestFn Set.univ
      (spectralCutoff R ε hR hε : Plane → ℝ) :=
    ⟨(spectralCutoff R ε hR hε).contDiff,
      (spectralCutoff R ε hR hε).hasCompactSupport, Set.subset_univ _⟩
  exact htest.lipschitz

/-- The product Lipschitz bound is produced from actual bounded factors. -/
lemma spectralCutoff_mul_lipschitz {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x => spectralCutoff R ε hR hε x * f x) := by
  obtain ⟨Lχ, hχ⟩ := spectralCutoff_lipschitz R ε hR hε
  apply Buckling.lipschitz_mul_bdd (Cf := (1 : ℝ)) (Cg := ‖f‖) hχ hf
  · intro x
    rw [abs_of_nonneg (spectralCutoff_mem_Icc R ε hR hε x).1]
    exact (spectralCutoff_mem_Icc R ε hR hε x).2
  · intro x
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x

/-- A genuinely finite cutoff-gradient integral, not an assumed constant. -/
def spectralCutoffEnergy (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) : ℝ :=
  ∫ x, ‖fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x‖ ^ 2 ∂volume

lemma integrable_derivativeEnergy_spectralCutoff
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    Integrable (fun x => ‖fderiv ℝ
      (spectralCutoff R ε hR hε : Plane → ℝ) x‖ ^ 2) volume := by
  obtain ⟨Lχ, hχ⟩ := spectralCutoff_lipschitz R ε hR hε
  exact Buckling.integrable_norm_fderiv_sq_of_lipschitz hχ
    (spectralCutoff R ε hR hε).hasCompactSupport

lemma spectralCutoffEnergy_nonneg (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    0 ≤ spectralCutoffEnergy R ε hR hε :=
  integral_nonneg fun x => sq_nonneg _

lemma integrable_derivativeEnergy_spectralCutoff_mul
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Integrable (fun x => ‖fderiv ℝ
      (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2) volume := by
  obtain ⟨L, hL⟩ := spectralCutoff_mul_lipschitz hR hε hf
  exact Buckling.integrable_norm_fderiv_sq_of_lipschitz hL
    (hasCompactSupport_spectralCutoff_mul R ε hR hε (f : Plane → ℝ))

lemma integrable_mass_spectralCutoff_mul
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Integrable (fun x => (spectralCutoff R ε hR hε x * f x) ^ 2) volume := by
  obtain ⟨L, hL⟩ := spectralCutoff_mul_lipschitz hR hε hf
  have hC : Continuous (fun x : Plane => (spectralCutoff R ε hR hε x * f x) ^ 2) :=
    hL.continuous.fun_pow 2
  have hK : HasCompactSupport (fun x : Plane => spectralCutoff R ε hR hε x * f x) :=
    hasCompactSupport_spectralCutoff_mul R ε hR hε (f : Plane → ℝ)
  have hSq : HasCompactSupport
      (fun x : Plane => (spectralCutoff R ε hR hε x * f x) ^ 2) := by
    simpa only [Function.comp_apply] using!
      hK.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact hC.integrable_of_hasCompactSupport hSq

/-- Actual H01 admissibility and the proved disk ground state give this
spectral inequality even when the cutoff function is identically zero. -/
lemma spectralCutoff_dirichlet_lower
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 *
        (∫ x, (spectralCutoff R ε hR hε x * f x) ^ 2 ∂volume) ≤
      ∫ x, ‖fderiv ℝ (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2 ∂volume := by
  obtain ⟨L, hL⟩ := spectralCutoff_mul_lipschitz hR hε hf
  have hc := hasCompactSupport_spectralCutoff_mul R ε hR hε (f : Plane → ℝ)
  have hs := tsupport_spectralCutoff_mul_subset R ε hR hε (f : Plane → ℝ)
  obtain ⟨u, hu, h0, h1⟩ := Buckling.lipschitz_mem_H01 Buckling.extMollification_holds
    (Ω := Metric.ball (0 : Plane) (R + 2 * ε)) Metric.isOpen_ball hL hc hs
  have hρ : 0 < R + 2 * ε := by linarith
  have hSpectral := Buckling.dirichlet_lower Buckling.extZeros_holds (0 : Plane) hρ u hu
  rw [h0, h1] at hSpectral
  exact hSpectral

/-- Integrate the actual a.e. estimate using independently produced finite
real gradient integrals. Compact support of `f` is used only for its own energy. -/
lemma integral_derivativeEnergy_spectralCutoff_mul_le
    {R ε δ S : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hδ : 0 < δ)
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hvZ : ∀ x, R < ‖x‖ → v x = 0) :
    (∫ x, ‖fderiv ℝ (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2 ∂volume) ≤
      (1 + δ) * (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume) +
        (1 + δ⁻¹) * (dist f v) ^ 2 * spectralCutoffEnergy R ε hR hε := by
  have hfI := integrable_derivativeEnergy_of_lipschitz_zero_outside_ball hf hfZ
  have hχI := integrable_derivativeEnergy_spectralCutoff R ε hR hε
  have hpI := integrable_derivativeEnergy_spectralCutoff_mul hR hε hf
  have hfirst := hfI.const_mul (1 + δ)
  have hsecond := hχI.const_mul ((1 + δ⁻¹) * (dist f v) ^ 2)
  have hBound := integral_mono_ae hpI (hfirst.add hsecond)
    (ae_norm_fderiv_spectralCutoff_mul_sq_le hR hε hδ hf hvZ)
  change (∫ x, ‖fderiv ℝ (fun y => spectralCutoff R ε hR hε y * f y) x‖ ^ 2 ∂volume) ≤
    ∫ x, (1 + δ) * ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 +
      ((1 + δ⁻¹) * (dist f v) ^ 2) *
        ‖fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x‖ ^ 2 ∂volume at hBound
  rw [integral_add hfirst hsecond, integral_const_mul, integral_const_mul] at hBound
  exact hBound

/-- The complete finite-function spectral-plus-energy consumer. The two
literature inputs invoked here have actual proofs in the original project;
there is no Faber--Krahn or PaperExternals premise. -/
lemma spectralCutoff_rayleigh_energy_le
    {R ε δ S : ℝ} (hR : 0 ≤ R) (hε : 0 < ε) (hδ : 0 < δ)
    {f v : Plane →ᵇ ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hvZ : ∀ x, R < ‖x‖ → v x = 0) :
    Buckling.jq ^ 2 / (R + 2 * ε) ^ 2 *
        (∫ x, (spectralCutoff R ε hR hε x * f x) ^ 2 ∂volume) ≤
      (1 + δ) * (∫ x, ‖fderiv ℝ (f : Plane → ℝ) x‖ ^ 2 ∂volume) +
        (1 + δ⁻¹) * (dist f v) ^ 2 * spectralCutoffEnergy R ε hR hε :=
  (spectralCutoff_dirichlet_lower hR hε hf).trans
    (integral_derivativeEnergy_spectralCutoff_mul_le hR hε hδ hf hfZ hvZ)

end FaberKrahnDevelopment.EuclideanReflection

end

end
