module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RadialPotentialCenter
public import RadialPotentialPolarization
public import ReflectionOrderPositiveBall
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Order.MinMax

/-!
# Actual global polarization branches produce an AE ball

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

For a nonnegative actual L1 density of positive mass, the actual radial
potential produces its own global maximizing center. For every affine
reflection whose chosen strict side contains that center, the supplied
literal polarization branch and actual potential maximality produce the
actual AE reflection order. Actual good-point comparison and finite actual
positive-set volume then produce an AE ball of strictly positive radius.

The signed-density wrapper applies this actual argument to max(U,0).
The actual literal max/min polarization commutes with positive part, so
the original actual branch family produces the required positive-part
branches. Actual integral monotonicity supplies positive positive-part
mass. Its positive set is exactly that of U. Thus the signed root also
has no external center, potential maximum, reflection order or ball input.

The branch family itself remains a premise to be supplied by the actual
SMP/equality argument. These consumers do not assert that missing theorem
or the manuscript's complete equality/area corollary.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal MeasureTheory InnerProductSpace RealInnerProductSpace

namespace Buckling.ReflectionBranchPositiveBall

open FaberKrahnDevelopment FaberKrahnDevelopment.EuclideanReflection
open RadialPotentialCenter RadialPotentialPolarization ReflectionOrderPositiveBall

/-- Positive actual integral forces actual positive-set measure to be
positive, even when the integrable density is signed. -/
lemma positiveSet_measure_pos {U : Plane → ℝ} (hMass : 0 < ∫ x, U x) :
    0 < volume {x | 0 < U x} := by
  by_contra h
  have hZero : volume {x | 0 < U x} = 0 := le_antisymm (le_of_not_gt h) bot_le
  have hNonpos : ∀ᵐ x ∂volume, U x ≤ 0 :=
    (measure_eq_zero_iff_ae_notMem.mp hZero).mono fun x hx => not_lt.mp hx
  exact (not_le_of_gt hMass) (integral_nonpos_of_ae hNonpos)

/-- The actual center is produced by the actual potential; the actual
orders are produced from the actual global branches at that center. -/
theorem exists_pos_ball_ae_eq_of_nonneg_branches {U : Plane → ℝ}
    (hU : Integrable U volume) (hUN : ∀ᵐ x ∂volume, 0 ≤ U x)
    (hMass : 0 < ∫ x, U x) (hfin : volume {x | 0 < U x} < ⊤)
    (hBranches : ∀ (ν : UnitNormal) (c : ℝ),
      (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume] U) ∨
      (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume]
        fun x => U (reflection ν c x))) :
    ∃ (p : Plane) (R : ℝ), 0 < R ∧ {x | 0 < U x} =ᵐ[volume] ball p R := by
  obtain ⟨p, hpPositive, hpMax⟩ := exists_positive_global_maximum hU hUN hMass
  have hOrder : ∀ (ν : UnitNormal) (c : ℝ), c < inner ℝ (ν : Plane) p →
      ∀ᵐ x ∂(volume.restrict (halfspace ν c)), U (reflection ν c x) ≤ U x := by
    intro ν c hp
    exact ae_reflection_order_of_global_maximum_and_branch ν c hU hp hpMax
      (hBranches ν c)
  obtain ⟨R, hR, hAE⟩ := exists_pos_ball_ae_eq_of_reflection_order hU p hOrder
    (positiveSet_measure_pos hMass) hfin
  exact ⟨p, R, hR, hAE⟩

/-- Actual pointwise polarization commutes with positive part; no AE
composition, representative choice or additional geometry is used here. -/
lemma polarization_positivePart {α : Type*} (H : Set α) (τ : α → α) (U : α → ℝ) :
    twoPointPolarization H τ (fun x => max (U x) 0) =
      fun x => max (twoPointPolarization H τ U x) 0 := by
  classical
  funext x
  unfold twoPointPolarization
  split_ifs
  · simpa only [max_self] using max_max_max_comm (U x) 0 (U (τ x)) 0
  · exact (max_min_distrib_right (U x) (U (τ x)) 0).symm

/-- Signed actual L1 densities also work: their actual positive part has
positive mass, inherits the actual branches and has the same positive set. -/
theorem exists_pos_ball_ae_eq_of_integrable_branches {U : Plane → ℝ}
    (hU : Integrable U volume) (hMass : 0 < ∫ x, U x)
    (hfin : volume {x | 0 < U x} < ⊤)
    (hBranches : ∀ (ν : UnitNormal) (c : ℝ),
      (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume] U) ∨
      (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume]
        fun x => U (reflection ν c x))) :
    ∃ (p : Plane) (R : ℝ), 0 < R ∧ {x | 0 < U x} =ᵐ[volume] ball p R := by
  have hPart : Integrable (fun x => max (U x) 0) volume := hU.pos_part
  have hPartN : ∀ᵐ x ∂volume, 0 ≤ max (U x) 0 :=
    Eventually.of_forall fun x => le_max_right _ _
  have hPartMass : 0 < ∫ x, max (U x) 0 :=
    lt_of_lt_of_le hMass (integral_mono hU hPart fun x => le_max_left _ _)
  have hPositiveSet : {x | 0 < max (U x) 0} = {x | 0 < U x} := by
    ext x
    simp only [mem_setOf_eq, lt_max_iff, lt_self_iff_false, or_false]
  have hPartBranches : ∀ (ν : UnitNormal) (c : ℝ),
      (twoPointPolarization (halfspace ν c) (reflection ν c)
        (fun x => max (U x) 0) =ᵐ[volume] fun x => max (U x) 0) ∨
      (twoPointPolarization (halfspace ν c) (reflection ν c)
        (fun x => max (U x) 0) =ᵐ[volume] fun x => max (U (reflection ν c x)) 0) := by
    intro ν c
    rcases hBranches ν c with h | h
    · left
      filter_upwards [h] with x hx
      rw [polarization_positivePart]
      exact congrArg (fun t : ℝ => max t 0) hx
    · right
      filter_upwards [h] with x hx
      rw [polarization_positivePart]
      exact congrArg (fun t : ℝ => max t 0) hx
  have hPartFin : volume {x | 0 < max (U x) 0} < ⊤ := by
    rw [hPositiveSet]
    exact hfin
  obtain ⟨p, R, hR, hAE⟩ := exists_pos_ball_ae_eq_of_nonneg_branches hPart hPartN
    hPartMass hPartFin hPartBranches
  exact ⟨p, R, hR, by simpa only [hPositiveSet] using hAE⟩

end Buckling.ReflectionBranchPositiveBall

end

end
