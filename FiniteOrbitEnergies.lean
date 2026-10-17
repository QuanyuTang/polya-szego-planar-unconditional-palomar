module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.MainResults
public import FinitePolarizationOrbit
public import PolarizationEnergyTransport
public import AbsoluteValueEnergy
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Actual real mass and derivative energy of finite polarization orbits

SOURCE_DRAFT (2026-10-17). This isolated module has not been compiled and
is not imported by production. The project import is intended to use the
separately verified chunked artifacts. Its `Buckling.Plane` and the imported
`EuclideanReflection.Plane` are the same Euclidean space by definition.

For a nonnegative Lipschitz function zero outside a common centered ball,
every literal finite polarization has the same real square integral and
real squared-derivative integral. Actual integrability is produced at each
step from the common compact support, using the original project's proved
`integrable_norm_fderiv_sq_of_lipschitz` for derivative energy. The real
transport proof cancels two equal finite real integrals, without converting
an infinite ENNReal energy or using a default-zero integral as a bound.

Mass transport comes directly from the literal max/min squared pair. Energy
transport uses the actual reflection derivative-pair theorem. Neither
equimeasurability/layer cake nor an energy identity is an input to the orbit
theorems. Absolute-value starting functions are covered at the end.

This proves no statement about a uniform limit's derivative, cutoff energy,
the disk Rayleigh quotient, Faber--Krahn, or the equality case.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- Scalar max/min sorting preserves the sum of the actual squares. -/
lemma sorted_square_pair (a b : ℝ) :
    max a b ^ 2 + min a b ^ 2 = a ^ 2 + b ^ 2 := by
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab, min_eq_left hab]
    exact add_comm _ _
  · rw [max_eq_left hba, min_eq_right hba]

/-- The literal two-point polarization preserves the square sum at a pair
whenever that pair swaps sides. No measure or distribution premise is used. -/
lemma square_twoPointPolarization_pair {α : Type*} {H : Set α} {τ : α → α}
    {f : α → ℝ} (hInv : Function.Involutive τ) {x : α}
    (hSwap : τ x ∈ H ↔ x ∉ H) :
    twoPointPolarization H τ f x ^ 2 + twoPointPolarization H τ f (τ x) ^ 2 =
      f x ^ 2 + f (τ x) ^ 2 := by
  classical
  by_cases hx : x ∈ H
  · have hτx : τ x ∉ H := fun hτx => (hSwap.mp hτx) hx
    simp only [twoPointPolarization, if_pos hx, if_neg hτx, hInv x]
    rw [min_comm (f (τ x)) (f x)]
    exact sorted_square_pair (f x) (f (τ x))
  · have hτx : τ x ∈ H := hSwap.mpr hx
    simp only [twoPointPolarization, if_neg hx, if_pos hτx, hInv x]
    simpa only [min_comm, add_comm] using sorted_square_pair (f (τ x)) (f x)

/-- A measure-theoretic transport fact for arbitrary integrable densities.
The applications below produce the paired equality from actual max/min or
derivative geometry, rather than taking energy conservation as an input. -/
lemma integral_eq_of_ae_involution_pair_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {τ : α → α}
    (hτ : MeasurePreserving τ μ μ) (hInv : Function.Involutive τ)
    {p q : α → ℝ} (hp : Integrable p μ) (hq : Integrable q μ)
    (hPair : ∀ᵐ x ∂μ, p x + p (τ x) = q x + q (τ x)) :
    (∫ x, p x ∂μ) = ∫ x, q x ∂μ := by
  let e : α ≃ᵐ α := MeasurableEquiv.ofInvolutive τ hInv hτ.measurable
  have hpτ : Integrable (fun x => p (τ x)) μ := hτ.integrable_comp_of_integrable hp
  have hqτ : Integrable (fun x => q (τ x)) μ := hτ.integrable_comp_of_integrable hq
  have hip : (∫ x, p (τ x) ∂μ) = ∫ x, p x ∂μ :=
    hτ.integral_comp e.measurableEmbedding p
  have hiq : (∫ x, q (τ x) ∂μ) = ∫ x, q x ∂μ :=
    hτ.integral_comp e.measurableEmbedding q
  have hIntegral := integral_congr_ae hPair
  rw [integral_add hp hpτ, integral_add hq hqτ, hip, hiq] at hIntegral
  linarith

/-- Literal zero values outside a closed ball bound the topological support. -/
lemma tsupport_subset_closedBall_of_zero_outside_ball {f : Plane → ℝ} {S : ℝ}
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    tsupport f ⊆ Metric.closedBall (0 : Plane) S := by
  apply closure_minimal ?_ Metric.isClosed_closedBall
  intro x hx
  by_contra hxBall
  have hxR : S < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hxBall
  exact hx (hfZ x hxR)

lemma hasCompactSupport_of_zero_outside_ball {f : Plane → ℝ} {S : ℝ}
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) : HasCompactSupport f :=
  (isCompact_closedBall (0 : Plane) S).of_isClosed_subset (isClosed_tsupport f)
    (tsupport_subset_closedBall_of_zero_outside_ball hfZ)

/-- Ordinary square-mass integrability, independently of a preservation law. -/
lemma integrable_sq_of_lipschitz_zero_outside_ball {f : Plane → ℝ}
    {K : ℝ≥0} {S : ℝ} (hfL : LipschitzWith K f)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    Integrable (fun x => f x ^ 2) volume := by
  have hC : Continuous (fun x : Plane => f x ^ 2) := hfL.continuous.fun_pow 2
  have hK : HasCompactSupport f := hasCompactSupport_of_zero_outside_ball hfZ
  have hSq : HasCompactSupport (fun x : Plane => f x ^ 2) := by
    simpa only [Function.comp_apply] using!
      hK.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact hC.integrable_of_hasCompactSupport hSq

/-- Ordinary derivative-energy integrability, using the actual project
theorem on the definitionally identical Euclidean plane. -/
lemma integrable_derivativeEnergy_of_lipschitz_zero_outside_ball {f : Plane → ℝ}
    {K : ℝ≥0} {S : ℝ} (hfL : LipschitzWith K f)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    Integrable (fun x => ‖fderiv ℝ f x‖ ^ 2) volume :=
  Buckling.integrable_norm_fderiv_sq_of_lipschitz hfL
    (hasCompactSupport_of_zero_outside_ball hfZ)

namespace OriginHalfspace

/-- A single actual step preserves real squared mass. All integrability
data and the paired square equality are produced from the initial bounds. -/
lemma integral_sq_step (s : OriginHalfspace) {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ}
    (hfL : LipschitzWith K f) (hfN : ∀ x, 0 ≤ f x)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, s.step f x ^ 2) = ∫ x, f x ^ 2 := by
  have hpZ : ∀ x, S < ‖x‖ → s.step f x = 0 :=
    fun x hx => s.step_eq_zero_of_radius_lt hfN hfZ hx
  have hpI := integrable_sq_of_lipschitz_zero_outside_ball (s.lipschitzWith_step hfL) hpZ
  have hfI := integrable_sq_of_lipschitz_zero_outside_ball hfL hfZ
  apply integral_eq_of_ae_involution_pair_eq
    (reflection_measurePreserving s.normal s.offset)
    (reflection_involutive s.normal s.offset) hpI hfI
  filter_upwards [reflection_ae_swap s.normal s.offset] with x hx
  exact square_twoPointPolarization_pair (reflection_involutive s.normal s.offset) hx

/-- A single actual step preserves the real squared derivative integral.
The a.e. pair law is the previously constructed reflection theorem. -/
lemma integral_derivativeEnergy_step (s : OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ}
    (hfL : LipschitzWith K f) (hfN : ∀ x, 0 ≤ f x)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, ‖fderiv ℝ (s.step f) x‖ ^ 2) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hpZ : ∀ x, S < ‖x‖ → s.step f x = 0 :=
    fun x hx => s.step_eq_zero_of_radius_lt hfN hfZ hx
  have hpI := integrable_derivativeEnergy_of_lipschitz_zero_outside_ball
    (s.lipschitzWith_step hfL) hpZ
  have hfI := integrable_derivativeEnergy_of_lipschitz_zero_outside_ball hfL hfZ
  exact integral_eq_of_ae_involution_pair_eq
    (reflection_measurePreserving s.normal s.offset)
    (reflection_involutive s.normal s.offset) hpI hfI
    (ae_norm_fderiv_polarization_pair s.normal s.offset hfL)

end OriginHalfspace

/-- Every finite-list output has a genuinely integrable square and squared
derivative; this conclusion does not rely on a conservation identity. -/
lemma integrable_finitePolarization_energies (ss : List OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ}
    (hfL : LipschitzWith K f) (hfN : ∀ x, 0 ≤ f x)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    Integrable (fun x => finitePolarization ss f x ^ 2) volume ∧
      Integrable (fun x => ‖fderiv ℝ (finitePolarization ss f) x‖ ^ 2) volume := by
  have hL := lipschitzWith_finitePolarization ss hfL
  have hZ := finitePolarization_eq_zero_of_radius_lt ss hfN hfZ
  exact ⟨integrable_sq_of_lipschitz_zero_outside_ball hL hZ,
    integrable_derivativeEnergy_of_lipschitz_zero_outside_ball hL hZ⟩

lemma integral_sq_finitePolarization (ss : List OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ}
    (hfL : LipschitzWith K f) (hfN : ∀ x, 0 ≤ f x)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, finitePolarization ss f x ^ 2) = ∫ x, f x ^ 2 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      exact (s.integral_sq_step (lipschitzWith_finitePolarization ss hfL)
        (finitePolarization_nonneg ss hfN)
        (finitePolarization_eq_zero_of_radius_lt ss hfN hfZ)).trans ih

lemma integral_derivativeEnergy_finitePolarization (ss : List OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ}
    (hfL : LipschitzWith K f) (hfN : ∀ x, 0 ≤ f x)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, ‖fderiv ℝ (finitePolarization ss f) x‖ ^ 2) =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      exact (s.integral_derivativeEnergy_step (lipschitzWith_finitePolarization ss hfL)
        (finitePolarization_nonneg ss hfN)
        (finitePolarization_eq_zero_of_radius_lt ss hfN hfZ)).trans ih

/-- Both exact real-integral identities for any member of the literal orbit. -/
lemma energies_of_mem_finitePolarizationOrbit {f g : Plane → ℝ} {K : ℝ≥0} {S : ℝ}
    (hfL : LipschitzWith K f) (hfN : ∀ x, 0 ≤ f x)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hg : g ∈ finitePolarizationOrbit f) :
    (∫ x, g x ^ 2) = (∫ x, f x ^ 2) ∧
      (∫ x, ‖fderiv ℝ g x‖ ^ 2) = ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  obtain ⟨ss, rfl⟩ := hg
  exact ⟨integral_sq_finitePolarization ss hfL hfN hfZ,
    integral_derivativeEnergy_finitePolarization ss hfL hfN hfZ⟩

/-- Literal absolute-value initialization retains the original signed
function's real mass after every finite sequence. -/
lemma integral_sq_finitePolarization_absoluteValue (ss : List OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ} (hfL : LipschitzWith K f)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, finitePolarization ss (fun y => |f y|) x ^ 2) = ∫ x, f x ^ 2 := by
  have hAbsZ : ∀ x, S < ‖x‖ → |f x| = 0 := fun x hx => by rw [hfZ x hx, abs_zero]
  exact (integral_sq_finitePolarization ss (lipschitzWith_absoluteValue hfL)
    (fun x => abs_nonneg _) hAbsZ).trans (integral_absoluteValue_sq volume f)

/-- Literal absolute-value initialization also retains the original signed
function's real derivative energy after every finite sequence. -/
lemma integral_derivativeEnergy_finitePolarization_absoluteValue (ss : List OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} {S : ℝ} (hfL : LipschitzWith K f)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    (∫ x, ‖fderiv ℝ (finitePolarization ss (fun y => |f y|)) x‖ ^ 2) =
      ∫ x, ‖fderiv ℝ f x‖ ^ 2 := by
  have hAbsZ : ∀ x, S < ‖x‖ → |f x| = 0 := fun x hx => by rw [hfZ x hx, abs_zero]
  exact (integral_derivativeEnergy_finitePolarization ss (lipschitzWith_absoluteValue hfL)
    (fun x => abs_nonneg _) hAbsZ).trans (integral_norm_fderiv_absoluteValue_sq (μ := volume) hfL)

end FaberKrahnDevelopment
