module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FinitePolarizationOrbit
public import GlobalLipschitzCompactness
public import PolarizationMoment
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Global bounded-continuous finite polarization orbits

SOURCE_DRAFT (2026-10-17), not compiled and isolated from production.
Every finite polarization is explicitly packaged as a bounded continuous
function, using its proved Lipschitz continuity and literal range `[0, M]`.
The resulting actual orbit has compact closure in the GLOBAL uniform metric,
with the original Lipschitz/range/support bounds. An integrable weight gives
a continuous actual weighted-moment functional, which attains its minimum.

This does not assume or assert a radial decreasing limit, an energy-controlled
limit, Sobolev convergence, Faber--Krahn, or its equality case. The new closure
members are functions on the whole plane, not only the support ball.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- Two real values in `[0, M]` have distance at most `M`. -/
lemma dist_le_of_mem_Icc_zero {a b M : ℝ} (ha : a ∈ Icc 0 M) (hb : b ∈ Icc 0 M) :
    dist a b ≤ M := by
  rw [Real.dist_eq]
  exact abs_le.mpr ⟨by linarith [ha.1, hb.2], by linarith [ha.2, hb.1]⟩

/-- Actual BCF construction from continuity and a literal diameter bound. -/
def boundedOfLipschitzRange (f : Plane → ℝ) {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M) : Plane →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound ⟨f, hfL.continuous⟩ M
    (fun x y => dist_le_of_mem_Icc_zero (hfR x) (hfR y))

@[simp] lemma boundedOfLipschitzRange_coe (f : Plane → ℝ) {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M) :
    (boundedOfLipschitzRange f hfL hfR : Plane → ℝ) = f := rfl

/-- Every literal finite polarization, rather than only an intersection with
the BCF space, has a concrete bounded-continuous representative. -/
def boundedFinitePolarization (ss : List OriginHalfspace) (f : Plane → ℝ)
    {K : ℝ≥0} {M : ℝ} (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M) :
    Plane →ᵇ ℝ :=
  boundedOfLipschitzRange (finitePolarization ss f)
    (lipschitzWith_finitePolarization ss hfL) (finitePolarization_mem_Icc ss hfR)

@[simp] lemma boundedFinitePolarization_coe (ss : List OriginHalfspace)
    (f : Plane → ℝ) {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M) :
    (boundedFinitePolarization ss f hfL hfR : Plane → ℝ) = finitePolarization ss f := rfl

/-- The actual finite-list orbit in the whole-plane bounded continuous space. -/
def boundedPolarizationOrbit (f : Plane →ᵇ ℝ) : Set (Plane →ᵇ ℝ) :=
  {g | (g : Plane → ℝ) ∈ finitePolarizationOrbit (f : Plane → ℝ)}

lemma boundedFinitePolarization_mem_orbit (ss : List OriginHalfspace)
    (f : Plane →ᵇ ℝ) {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M) :
    boundedFinitePolarization ss f hfL hfR ∈ boundedPolarizationOrbit f :=
  ⟨ss, rfl⟩

/-- No finite sequence is lost by the BCF realization of the orbit. -/
lemma mem_boundedPolarizationOrbit_iff {f g : Plane →ᵇ ℝ} {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M) :
    g ∈ boundedPolarizationOrbit f ↔
      ∃ ss : List OriginHalfspace, boundedFinitePolarization ss f hfL hfR = g := by
  constructor
  · rintro ⟨ss, hss⟩
    refine ⟨ss, ?_⟩
    apply BoundedContinuousFunction.ext
    intro x
    exact congrFun hss x
  · rintro ⟨ss, rfl⟩
    exact boundedFinitePolarization_mem_orbit ss f hfL hfR

lemma self_mem_boundedPolarizationOrbit (f : Plane →ᵇ ℝ) :
    f ∈ boundedPolarizationOrbit f := self_mem_finitePolarizationOrbit f

lemma boundedPolarizationOrbit_nonempty (f : Plane →ᵇ ℝ) :
    (boundedPolarizationOrbit f).Nonempty := ⟨f, self_mem_boundedPolarizationOrbit f⟩

/-- The real finite orbit satisfies the global common-support family bounds. -/
lemma boundedPolarizationOrbit_subset_commonSupport {f : Plane →ᵇ ℝ}
    {K : ℝ≥0} {M S : ℝ} (hfL : LipschitzWith K f)
    (hfR : ∀ x, f x ∈ Icc 0 M) (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    boundedPolarizationOrbit f ⊆
      commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M := by
  intro g hg
  refine ⟨lipschitzWith_of_mem_finitePolarizationOrbit hfL hg,
    mem_Icc_of_mem_finitePolarizationOrbit hfR hg, ?_⟩
  intro x hx
  have hxR : S < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact eq_zero_of_radius_lt_of_mem_finitePolarizationOrbit
    (fun z => (hfR z).1) hfZ hg x hxR

lemma closure_boundedPolarizationOrbit_subset_commonSupport {f : Plane →ᵇ ℝ}
    {K : ℝ≥0} {M S : ℝ} (hfL : LipschitzWith K f)
    (hfR : ∀ x, f x ∈ Icc 0 M) (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    closure (boundedPolarizationOrbit f) ⊆
      commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M :=
  closure_subset_commonSupportLipschitzFamily
    (boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ)

/-- Compactness is for the original full-plane uniform distance. -/
lemma isCompact_closure_boundedPolarizationOrbit {f : Plane →ᵇ ℝ}
    {K : ℝ≥0} {M S : ℝ} (hfL : LipschitzWith K f)
    (hfR : ∀ x, f x ∈ Icc 0 M) (hfZ : ∀ x, S < ‖x‖ → f x = 0) :
    IsCompact (closure (boundedPolarizationOrbit f)) :=
  isCompact_closure_of_commonSupport_lipschitz
    (isCompact_closedBall (0 : Plane) S)
    (boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ)

/-- A genuine integrable weight gives a genuine minimizing orbit-closure
member. Continuity of the moment is produced from integrability. -/
lemma exists_min_weightedMoment_on_boundedPolarizationOrbit
    {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ} {w : Plane → ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) (hw : Integrable w volume) :
    ∃ g ∈ closure (boundedPolarizationOrbit f),
      LipschitzWith K g ∧ (∀ x, g x ∈ Icc 0 M) ∧
        (∀ x, x ∉ Metric.closedBall (0 : Plane) S → g x = 0) ∧
        IsMinOn (weightedMoment volume w) (closure (boundedPolarizationOrbit f)) g :=
  exists_min_on_closure_of_commonSupport_lipschitz
    (isCompact_closedBall (0 : Plane) S)
    (boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ)
    (boundedPolarizationOrbit_nonempty f) (weightedMoment volume w)
    (continuous_weightedMoment hw).continuousOn

namespace OriginHalfspace

/-- A single actual step packaged globally using its proved bounds. -/
def boundedStep (s : OriginHalfspace) (g : Plane →ᵇ ℝ) {K : ℝ≥0} {M : ℝ}
    (hgL : LipschitzWith K g) (hgR : ∀ x, g x ∈ Icc 0 M) : Plane →ᵇ ℝ :=
  boundedOfLipschitzRange (s.step g) (s.lipschitzWith_step hgL) (s.step_mem_Icc hgR)

@[simp] lemma boundedStep_coe (s : OriginHalfspace) (g : Plane →ᵇ ℝ)
    {K : ℝ≥0} {M : ℝ} (hgL : LipschitzWith K g) (hgR : ∀ x, g x ∈ Icc 0 M) :
    (s.boundedStep g hgL hgR : Plane → ℝ) = s.step g := rfl

lemma boundedStep_mem_orbit (s : OriginHalfspace) {f g : Plane →ᵇ ℝ}
    {K : ℝ≥0} {M : ℝ} (hgL : LipschitzWith K g) (hgR : ∀ x, g x ∈ Icc 0 M)
    (hg : g ∈ boundedPolarizationOrbit f) :
    s.boundedStep g hgL hgR ∈ boundedPolarizationOrbit f :=
  step_mem_finitePolarizationOrbit s hg

/-- Uniform nonexpansiveness comes from literal max/min stability. -/
lemma dist_boundedStep_le (s : OriginHalfspace) (f g : Plane →ᵇ ℝ)
    {K : ℝ≥0} {M : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hgL : LipschitzWith K g) (hgR : ∀ x, g x ∈ Icc 0 M) :
    dist (s.boundedStep f hfL hfR) (s.boundedStep g hgL hgR) ≤ dist f g := by
  apply (BoundedContinuousFunction.dist_le dist_nonneg).2
  intro x
  exact dist_twoPointPolarization_le_of_forall
    (fun z => BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) z) x

lemma boundedStep_mem_commonSupport (s : OriginHalfspace) {g : Plane →ᵇ ℝ}
    {K : ℝ≥0} {M S : ℝ}
    (hg : g ∈ commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M) :
    s.boundedStep g hg.1 hg.2.1 ∈
      commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M := by
  refine ⟨s.lipschitzWith_step hg.1, s.step_mem_Icc hg.2.1, ?_⟩
  intro x hx
  have hxR : S < ‖x‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx
  apply s.step_eq_zero_of_radius_lt (fun z => (hg.2.1 z).1) ?_ hxR
  intro z hz
  apply hg.2.2 z
  simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz

/-- Actual endomap on the closed common-support family. -/
def familyStep (s : OriginHalfspace) (S : ℝ) (K : ℝ≥0) (M : ℝ) :
    commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M →
      commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M :=
  fun g => ⟨s.boundedStep g.val g.property.1 g.property.2.1,
    s.boundedStep_mem_commonSupport g.property⟩

lemma lipschitzWith_familyStep (s : OriginHalfspace) (S : ℝ) (K : ℝ≥0) (M : ℝ) :
    LipschitzWith 1 (s.familyStep S K M) := by
  apply LipschitzWith.mk_one
  intro f g
  exact s.dist_boundedStep_le f.val g.val
    f.property.1 f.property.2.1 g.property.1 g.property.2.1

lemma continuous_familyStep (s : OriginHalfspace) (S : ℝ) (K : ℝ≥0) (M : ℝ) :
    Continuous (s.familyStep S K M) :=
  (s.lipschitzWith_familyStep S K M).continuous

end OriginHalfspace

/-- Closure stability is derived from the actual nonexpansive step endomap,
without assuming a pre-existing radial or energy-controlled limit. -/
lemma exists_step_mem_closure_boundedPolarizationOrbit
    (s : OriginHalfspace) {f : Plane →ᵇ ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfL : LipschitzWith K f) (hfR : ∀ x, f x ∈ Icc 0 M)
    (hfZ : ∀ x, S < ‖x‖ → f x = 0) {g : Plane →ᵇ ℝ}
    (hg : g ∈ closure (boundedPolarizationOrbit f)) :
    ∃ g' ∈ closure (boundedPolarizationOrbit f),
      (g' : Plane → ℝ) = s.step (g : Plane → ℝ) := by
  let F := commonSupportLipschitzFamily (Metric.closedBall (0 : Plane) S) K M
  let T : Set F := {q | q.val ∈ boundedPolarizationOrbit f}
  have hA : boundedPolarizationOrbit f ⊆ F :=
    boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ
  have hG : g ∈ F :=
    closure_boundedPolarizationOrbit_subset_commonSupport hfL hfR hfZ hg
  let q : F := ⟨g, hG⟩
  have hImage : (Subtype.val : F → (Plane →ᵇ ℝ)) '' T = boundedPolarizationOrbit f := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hu
      exact ⟨⟨u, hA hu⟩, hu, rfl⟩
  have hq : q ∈ closure T := by
    apply closure_subtype.mpr
    rw [hImage]
    exact hg
  have hMap : Set.MapsTo (s.familyStep S K M) T T := by
    intro v hv
    exact s.boundedStep_mem_orbit v.property.1 v.property.2.1 hv
  have hout := hMap.closure (s.continuous_familyStep S K M) hq
  have hout' := closure_subtype.mp hout
  rw [hImage] at hout'
  exact ⟨(s.familyStep S K M q).val, hout', rfl⟩

end FaberKrahnDevelopment

end

end
