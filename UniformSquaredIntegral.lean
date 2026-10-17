module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import PolarizationMoment
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Square integrals under global uniform convergence with common support

SOURCE_DRAFT (2026-10-17), awaiting compilation and axiom inspection.
This module is not imported by the production buckling project.

Multiplication is continuous in the actual bounded-continuous-function
normed algebra. Apply the already constructed continuous weighted moment to
the literal square f*f and the integrable indicator of a finite-measure set.
On functions vanishing outside that set, this functional is exactly the full
square integral. This gives convergence without any weak derivative, layer
cake formula, square-integral convergence assumption, or a fixed pointwise
amplitude bound.
-/

@[expose] public section

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology

namespace FaberKrahnDevelopment

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] {μ : Measure X}

noncomputable def clippedSquaredIntegral (μ : Measure X) (S : Set X)
    (f : X →ᵇ ℝ) : ℝ :=
  weightedMoment μ (S.indicator (fun _ => (1 : ℝ))) (f * f)

lemma continuous_clippedSquaredIntegral {S : Set X}
    (hS : MeasurableSet S) (hfin : μ S ≠ ⊤) :
    Continuous (clippedSquaredIntegral μ S) := by
  have hw : Integrable (S.indicator (fun _ => (1 : ℝ))) μ :=
    (integrableOn_const hfin).integrable_indicator hS
  exact (continuous_weightedMoment hw).comp (continuous_id.mul continuous_id)

/-- The finite-set functional agrees pointwise with the actual whole-domain
square integral when the omitted values vanish. -/
lemma clippedSquaredIntegral_eq_integral {S : Set X} {f : X →ᵇ ℝ}
    (hf : ∀ x, x ∉ S → f x = 0) :
    clippedSquaredIntegral μ S f = ∫ x, f x ^ 2 ∂μ := by
  classical
  unfold clippedSquaredIntegral weightedMoment
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ S
    · simp only [indicator_of_mem hx, one_mul, coe_mul, Pi.mul_apply, pow_two]
    · simp only [indicator_of_notMem hx, zero_mul, hf x hx, zero_pow (by decide : 2 ≠ 0)]

/-- A genuine uniform limit with common finite-measure support has convergent
full square integrals, for an arbitrary filter (not just a sequence). -/
lemma tendsto_integral_sq_of_uniform_commonSupport
    {ι : Type*} {l : Filter ι} {S : Set X}
    (hS : MeasurableSet S) (hfin : μ S ≠ ⊤)
    {F : ι → (X →ᵇ ℝ)} {v : X →ᵇ ℝ}
    (hF : Tendsto F l (𝓝 v))
    (hFS : ∀ i x, x ∉ S → F i x = 0) (hvS : ∀ x, x ∉ S → v x = 0) :
    Tendsto (fun i => ∫ x, F i x ^ 2 ∂μ) l (𝓝 (∫ x, v x ^ 2 ∂μ)) := by
  have hJ := ((continuous_clippedSquaredIntegral hS hfin).tendsto v).comp hF
  change Tendsto (fun i => clippedSquaredIntegral μ S (F i)) l
    (𝓝 (clippedSquaredIntegral μ S v)) at hJ
  have hEq : (fun i => clippedSquaredIntegral μ S (F i)) =
      (fun i => ∫ x, F i x ^ 2 ∂μ) :=
    funext fun i => clippedSquaredIntegral_eq_integral (hFS i)
  rw [hEq, clippedSquaredIntegral_eq_integral hvS] at hJ
  exact hJ

end FaberKrahnDevelopment
