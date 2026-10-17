module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import ReflectionOrderGoodPoints
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The actual finite positive set is almost everywhere a centered ball

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The radii below are the actual distances of positive Lebesgue good points.
If they were unbounded, the actual good-point radial comparison would make
every good point positive. That contradicts finite positive-set measure,
because actual Euclidean volume of the whole plane is infinite.

For the bounded nonempty set of radii, its actual real supremum is the
radius. Every good point strictly inside has a farther positive good point
and hence is positive. Every positive good point has radius at most that
supremum. Removing the single null sphere proves the AE set identity.
The null positive-set case is the ball of radius zero.

Only the single Lebesgue good-point exceptional set and one actual sphere
are discarded. No uncountable intersection of reflection AE predicates is
taken. The final roots consume the actual reflection-order family through
ReflectionOrderGoodPoints.radial_order_at_goodPoints; radial order and a
ball-shaped set are not extra premises of those roots.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal MeasureTheory InnerProductSpace RealInnerProductSpace

namespace Buckling.ReflectionOrderPositiveBall

open FaberKrahnDevelopment.EuclideanReflection
open Buckling.ReflectionOrderGoodPoints

/-- Actual distances of the positive points in the one produced good set. -/
def positiveGoodRadii (U : Plane → ℝ) (p : Plane) : Set ℝ :=
  (fun x => dist p x) '' {x | GoodPoint U x ∧ 0 < U x}

lemma positiveGoodRadii_nonneg {U : Plane → ℝ} {p : Plane} {r : ℝ}
    (hr : r ∈ positiveGoodRadii U p) : 0 ≤ r := by
  rcases hr with ⟨x, hx, rfl⟩
  exact dist_nonneg

/-- Finite positive-set measure forces the actual positive good radii to
be bounded. Otherwise all good points would be positive, contradicting
the actual infinite volume of the plane. -/
theorem positiveGoodRadii_bddAbove {U : Plane → ℝ} (hU : Integrable U volume)
    (p : Plane)
    (hRadial : ∀ {x y : Plane}, GoodPoint U x → GoodPoint U y →
      dist p x < dist p y → U y ≤ U x)
    (hfin : volume {x | 0 < U x} < ⊤) : BddAbove (positiveGoodRadii U p) := by
  by_contra hUnbdd
  have hPositive : ∀ᵐ x ∂volume, 0 < U x := by
    filter_upwards [ae_goodPoint hU] with x hx
    obtain ⟨r, hr, hDist⟩ := (not_bddAbove_iff.mp hUnbdd) (dist p x)
    rcases hr with ⟨y, hy, rfl⟩
    exact lt_of_lt_of_le hy.2 (hRadial hx hy.1 hDist)
  have hAE : {x | 0 < U x} =ᵐ[volume] (univ : Set Plane) := by
    filter_upwards [hPositive] with x hx
    change (0 < U x) = True
    exact propext ⟨fun _ => trivial, fun _ => hx⟩
  have hInfinite : volume {x | 0 < U x} = ⊤ :=
    (measure_congr hAE).trans
      (measure_univ_of_isAddLeftInvariant (volume : Measure Plane))
  exact (ne_of_lt hfin) hInfinite

lemma positiveGoodRadii_nonempty {U : Plane → ℝ} (hU : Integrable U volume)
    (p : Plane) (hpos : volume {x | 0 < U x} ≠ 0) :
    (positiveGoodRadii U p).Nonempty := by
  by_contra hEmpty
  have hNotPos : ∀ᵐ x ∂volume, x ∉ {x | 0 < U x} := by
    filter_upwards [ae_goodPoint hU] with x hx
    intro hPositive
    exact hEmpty ⟨dist p x, x, ⟨hx, hPositive⟩, rfl⟩
  exact hpos (measure_eq_zero_iff_ae_notMem.mpr hNotPos)

/-- The supremum property supplies an actual farther positive good point;
its comparison produces positivity at this actual interior good point. -/
lemma positive_of_goodPoint_dist_lt_sSup {U : Plane → ℝ} {p : Plane}
    (hRadial : ∀ {x y : Plane}, GoodPoint U x → GoodPoint U y →
      dist p x < dist p y → U y ≤ U x)
    (hne : (positiveGoodRadii U p).Nonempty) {x : Plane}
    (hx : GoodPoint U x) (hDist : dist p x < sSup (positiveGoodRadii U p)) :
    0 < U x := by
  obtain ⟨r, hr, hFarther⟩ := exists_lt_of_lt_csSup hne hDist
  rcases hr with ⟨y, hy, rfl⟩
  exact lt_of_lt_of_le hy.2 (hRadial hx hy.1 hFarther)

/-- A pure measure-theoretic consumer of the actual good-point radial order.
The later reflection root supplies this order from the actual AE family. -/
theorem exists_ball_ae_eq_of_goodPoint_radial_order {U : Plane → ℝ}
    (hU : Integrable U volume) (p : Plane)
    (hRadial : ∀ {x y : Plane}, GoodPoint U x → GoodPoint U y →
      dist p x < dist p y → U y ≤ U x)
    (hfin : volume {x | 0 < U x} < ⊤) :
    ∃ R : ℝ, 0 ≤ R ∧ {x | 0 < U x} =ᵐ[volume] ball p R := by
  by_cases hzero : volume {x | 0 < U x} = 0
  · refine ⟨0, le_rfl, ?_⟩
    simpa only [ball_zero] using
      (ae_eq_empty.mpr hzero : {x | 0 < U x} =ᵐ[volume] (∅ : Set Plane))
  have hBdd := positiveGoodRadii_bddAbove hU p hRadial hfin
  have hne := positiveGoodRadii_nonempty hU p hzero
  let R : ℝ := sSup (positiveGoodRadii U p)
  have hR : 0 ≤ R := by
    obtain ⟨r, hr⟩ := hne
    exact (positiveGoodRadii_nonneg hr).trans (le_csSup hBdd hr)
  refine ⟨R, hR, ?_⟩
  have hSphere : ∀ᵐ x ∂volume, x ∉ sphere p R :=
    measure_eq_zero_iff_ae_notMem.mp (Measure.addHaar_sphere volume p R)
  filter_upwards [ae_goodPoint hU, hSphere] with x hx hxSphere
  change (0 < U x) = (dist x p < R)
  apply propext
  constructor
  · intro hPositive
    have hLe : dist p x ≤ R :=
      le_csSup hBdd ⟨x, ⟨hx, hPositive⟩, rfl⟩
    have hNe : dist p x ≠ R := by
      intro hEq
      apply hxSphere
      change dist x p = R
      exact (dist_comm x p).trans hEq
    rw [dist_comm x p]
    exact lt_of_le_of_ne hLe hNe
  · intro hDist
    have hDist' : dist p x < sSup (positiveGoodRadii U p) := by
      change dist p x < R
      rw [dist_comm p x]
      exact hDist
    exact positive_of_goodPoint_dist_lt_sSup hRadial hne hx hDist'

/-- Actual reflection order towards a center and finite actual positive-set
measure produce an actual AE ball. Signed integrable U is sufficient. -/
theorem exists_ball_ae_eq_of_reflection_order {U : Plane → ℝ}
    (hU : Integrable U volume) (p : Plane)
    (hOrder : ∀ (ν : UnitNormal) (c : ℝ), c < inner ℝ (ν : Plane) p →
      ∀ᵐ z ∂(volume.restrict (halfspace ν c)), U (reflection ν c z) ≤ U z)
    (hfin : volume {x | 0 < U x} < ⊤) :
    ∃ R : ℝ, 0 ≤ R ∧ {x | 0 < U x} =ᵐ[volume] ball p R :=
  exists_ball_ae_eq_of_goodPoint_radial_order hU p
    (radial_order_at_goodPoints hU p hOrder) hfin

/-- If the actual positive set has positive measure, the produced ball has
strictly positive radius, without prescribing a radius or a volume formula. -/
theorem exists_pos_ball_ae_eq_of_reflection_order {U : Plane → ℝ}
    (hU : Integrable U volume) (p : Plane)
    (hOrder : ∀ (ν : UnitNormal) (c : ℝ), c < inner ℝ (ν : Plane) p →
      ∀ᵐ z ∂(volume.restrict (halfspace ν c)), U (reflection ν c z) ≤ U z)
    (hpos : 0 < volume {x | 0 < U x}) (hfin : volume {x | 0 < U x} < ⊤) :
    ∃ R : ℝ, 0 < R ∧ {x | 0 < U x} =ᵐ[volume] ball p R := by
  obtain ⟨R, hR, hAE⟩ := exists_ball_ae_eq_of_reflection_order hU p hOrder hfin
  have hBall : volume (ball p R) ≠ 0 := by
    rw [← measure_congr hAE]
    exact ne_of_gt hpos
  exact ⟨R, nonempty_ball.mp (nonempty_of_measure_ne_zero hBall), hAE⟩

end Buckling.ReflectionOrderPositiveBall

end

end
