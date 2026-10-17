module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPBallLogBound
public import WeakSMPLogBoundDecay
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# The local almost-everywhere zero-or-positive alternative on a ball

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The actual uniform logarithm bound and its finite-measure decay consumer
first show that a positive-measure zero set forces zero almost everywhere
on a ball. An actual smooth bump removes the cutoff from the local root.
The zero set of an L2 representative is treated as null-measurable.

The original domain is an arbitrary open planar set. The only local
geometric condition is that the closed doubled ball lies in the domain.
No cutoff, Poincare, nonlinear test, or zero-set conclusion is an input to
the zero-or-positive alternative. Global connected propagation and the
final rigidity theorem are outside this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal InnerProductSpace RealInnerProductSpace

namespace Buckling.WeakSMPBallZero

open EllipticPdes EllipticPdes.Embedding

/-- The fixed-cutoff version consumes the actual uniform bound, not a
new logarithmic integrability or boundedness hypothesis. -/
theorem ae_eq_zero_on_ball_of_zero_set_with_cutoff {D : Set Plane} (hD : IsOpen D)
    {p : Plane} {r : ℝ} (hr : 0 < r) (hBD : ball p r ⊆ D)
    {χ : Plane → ℝ} (hχ : IsTestFn D χ) (hχone : ∀ x ∈ ball p r, χ x = 1)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x)
    {E : Set Plane} (hEB : E ⊆ ball p r) (hE : 0 < volume E)
    (hwE : ∀ᵐ x ∂volume.restrict E, w x = 0) :
    w =ᵐ[volume.restrict (ball p r)] 0 := by
  letI : IsFiniteMeasure (volume.restrict (ball p r)) :=
    isFiniteMeasure_restrict_of_isBounded isBounded_ball
  obtain ⟨hn, C, _hC0, hbound⟩ :=
    WeakSMPBallLogBound.exists_uniform_ball_log_bound hD hr hBD hχ hχone
      hw hg hweak hw0 hsuper hEB hE hwE
  exact WeakSMPLogBoundDecay.ae_eq_zero_of_uniform_log_bound
    (hw.restrict (ball p r)).aestronglyMeasurable hn C
    (fun δ hδ => (hbound δ hδ).1) (fun δ hδ => (hbound δ hδ).2)

/-- The smooth cutoff is actually constructed from the two radii. Its
support is the closed doubled ball, not merely an unspecified compact set. -/
theorem exists_test_cutoff_ball {D : Set Plane} {p : Plane} {r : ℝ}
    (hr : 0 < r) (hclosed : closedBall p (2 * r) ⊆ D) :
    ∃ χ : Plane → ℝ, IsTestFn D χ ∧ ∀ x ∈ ball p r, χ x = 1 := by
  let b : ContDiffBump p := ⟨r, 2 * r, hr, by linarith⟩
  have hb : IsTestFn D b := by
    refine ⟨b.contDiff, b.hasCompactSupport, ?_⟩
    rw [b.tsupport_eq]
    exact hclosed
  refine ⟨b, hb, ?_⟩
  intro x hx
  exact b.one_of_mem_closedBall (ball_subset_closedBall hx)

lemma ball_subset_of_closed_doubled_ball {D : Set Plane} {p : Plane} {r : ℝ}
    (hr : 0 < r) (hclosed : closedBall p (2 * r) ⊆ D) : ball p r ⊆ D :=
  (ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith : r ≤ 2 * r))).trans hclosed

/-- No cutoff is supplied by the caller: the actual smooth bump produces
it from the closed doubled ball inclusion. -/
theorem ae_eq_zero_on_ball_of_zero_set {D : Set Plane} (hD : IsOpen D)
    {p : Plane} {r : ℝ} (hr : 0 < r) (hclosed : closedBall p (2 * r) ⊆ D)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x)
    {E : Set Plane} (hEB : E ⊆ ball p r) (hE : 0 < volume E)
    (hwE : ∀ᵐ x ∂volume.restrict E, w x = 0) :
    w =ᵐ[volume.restrict (ball p r)] 0 := by
  obtain ⟨χ, hχ, hχone⟩ := exists_test_cutoff_ball hr hclosed
  exact ae_eq_zero_on_ball_of_zero_set_with_cutoff hD hr
    (ball_subset_of_closed_doubled_ball hr hclosed) hχ hχone
    hw hg hweak hw0 hsuper hEB hE hwE

/-- The local a.e. zero-or-strictly-positive alternative for the actual
full-space weak-H1 supersolution on an arbitrary open domain. -/
theorem ball_zero_or_pos {D : Set Plane} (hD : IsOpen D)
    {p : Plane} {r : ℝ} (hr : 0 < r) (hclosed : closedBall p (2 * r) ⊆ D)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    (w =ᵐ[volume.restrict (ball p r)] 0) ∨
      (∀ᵐ x ∂volume.restrict (ball p r), 0 < w x) := by
  let E : Set Plane := {x | x ∈ ball p r ∧ w x = 0}
  have hEB : E ⊆ ball p r := fun _ hx => hx.1
  have hzeroMeas : NullMeasurableSet {x | w x = 0} volume :=
    hw.aestronglyMeasurable.aemeasurable.nullMeasurableSet_preimage
      (measurableSet_singleton (0 : ℝ))
  have hEm : NullMeasurableSet E volume :=
    measurableSet_ball.nullMeasurableSet.inter hzeroMeas
  by_cases hE : volume E = 0
  · right
    have hnotE : ∀ᵐ x ∂volume, x ∉ E :=
      measure_eq_zero_iff_ae_notMem.mp hE
    have hn := WeakSMPBallLogBound.nonneg_ae_ball hD
      (ball_subset_of_closed_doubled_ball hr hclosed) hw0
    filter_upwards [hn, ae_restrict_of_ae hnotE,
      ae_restrict_mem measurableSet_ball] with x hx0 hxE hxB
    by_contra hpos
    have hxzero : w x = 0 := le_antisymm (le_of_not_gt hpos) hx0
    exact hxE ⟨hxB, hxzero⟩
  · left
    have hwE : ∀ᵐ x ∂volume.restrict E, w x = 0 :=
      (ae_restrict_mem₀ hEm).mono fun _ hx => hx.2
    exact ae_eq_zero_on_ball_of_zero_set hD hr hclosed hw hg hweak hw0 hsuper
      hEB (pos_iff_ne_zero.mpr hE) hwE

end Buckling.WeakSMPBallZero

end

end
