module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPBallZero
public import ConnectedLocalAEDichotomy

/-!
# The weak strong maximum principle on an arbitrary connected open domain

SOURCE_DRAFT: not registered or native checked.
The local zero-or-positive alternative is actually produced from smooth
positive tests, nonlinear weak testing, logarithmic Caccioppoli, ball
Poincare and anchoring. Countable open unions and preconnectedness then
propagate that alternative across the domain. No boundedness, regular
boundary, classical derivative or preselected positive representative is
assumed. This is still not Faber-Krahn equality rigidity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace Buckling.WeakSMPConnected

open EllipticPdes.Embedding

/-- An actual H1 supersolution which is nonnegative almost everywhere
on a preconnected open planar domain is either zero almost everywhere
or strictly positive almost everywhere there. -/
theorem zero_or_pos_ae {D : Set Plane} (hD : IsOpen D) (hconn : IsPreconnected D)
    {w : Plane → ℝ} (hw : MemLp w 2 volume)
    {g : Fin 2 → Plane → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hweak : HasWeakGradOn univ w g)
    (hw0 : ∀ᵐ x ∂volume.restrict D, 0 ≤ w x)
    (hsuper : ∀ ψ : Plane → ℝ, IsTestFn D ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, g i x * pderiv i ψ x) :
    (w =ᵐ[volume.restrict D] 0) ∨
      (∀ᵐ x ∂volume.restrict D, 0 < w x) := by
  apply ConnectedLocalAEDichotomy.zero_or_pos_ae_of_local hD hconn w
  intro p hp
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD p hp
  let r : ℝ := ε / 4
  have hr : 0 < r := div_pos hε (by norm_num)
  have hclosed : closedBall p (2 * r) ⊆ D := by
    intro x hx
    apply hεD
    apply lt_of_le_of_lt (mem_closedBall.mp hx)
    dsimp [r]
    linarith
  refine ⟨ball p r, isOpen_ball,
    WeakSMPBallZero.ball_subset_of_closed_doubled_ball hr hclosed,
    mem_ball_self hr, ?_⟩
  exact WeakSMPBallZero.ball_zero_or_pos hD hr hclosed hw hg hweak hw0 hsuper

end Buckling.WeakSMPConnected

end

end
