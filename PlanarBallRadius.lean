module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.Tactic.Linarith

/-!
# Actual planar ball volume determines a nonnegative radius

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

This is a canonical-Mathlib-only helper, independent of Core1..Core4.
It uses the actual EuclideanSpace.volume_ball_fin_two formula. Applying
toReal computes the actual finite real squared radii times pi; pi is
nonzero, and nonnegative radii exclude the negative square-root branch.

The final helper transports an already-produced AE ball to a prescribed
radius with the same actual domain volume, returning the actual null
symmetric difference used by the original ExtFaberKrahn interface.
No AE ball or equality rigidity is produced from a spectral input here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal symmDiff

namespace Buckling.PlanarBallRadius

abbrev Space := EuclideanSpace ℝ (Fin 2)

/-- The centers may be completely unrelated. Nonnegative actual radii are
uniquely determined by the actual planar ball volumes. -/
theorem radius_eq_of_volume_ball_eq (a b : Space) {r s : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hVolume : volume (ball a r) = volume (ball b s)) : r = s := by
  have hReal : r ^ 2 * Real.pi = s ^ 2 * Real.pi := by
    simpa only [EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal hs,
      ENNReal.toReal_ofReal Real.pi_pos.le] using congrArg ENNReal.toReal hVolume
  have hSq : r ^ 2 = s ^ 2 := mul_right_cancel₀ Real.pi_ne_zero hReal
  nlinarith

/-- Replace the actual AE-ball radius by the prescribed equal-volume
radius. The given volume equality has the original interface's direction. -/
theorem ae_eq_prescribed_ball {Ω : Set Space} (a : Space) {s R : ℝ}
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hAE : Ω =ᵐ[volume] ball a s)
    (hVolume : volume (ball (0 : Space) R) = volume Ω) :
    Ω =ᵐ[volume] ball a R := by
  have hBalls : volume (ball a s) = volume (ball (0 : Space) R) :=
    (measure_congr hAE).symm.trans hVolume.symm
  have hRadius : s = R := radius_eq_of_volume_ball_eq a 0 hs hR hBalls
  simpa only [hRadius] using hAE

/-- The exact null-symmetric-difference conclusion requested by the
original equality interface, once an actual AE ball has been produced. -/
theorem symmDiff_prescribed_ball_eq_zero {Ω : Set Space} (a : Space) {s R : ℝ}
    (hs : 0 ≤ s) (hR : 0 ≤ R) (hAE : Ω =ᵐ[volume] ball a s)
    (hVolume : volume (ball (0 : Space) R) = volume Ω) :
    volume (Ω ∆ ball a R) = 0 :=
  measure_symmDiff_eq_zero_iff.mpr (ae_eq_prescribed_ball a hs hR hAE hVolume)

end Buckling.PlanarBallRadius

end

end
