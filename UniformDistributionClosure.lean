module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Tactic.Linarith

/-!
# Strict superlevel distributions are closed for global uniform distance

SOURCE_DRAFT (2026-10-17). This isolated file has not yet been compiled.
It is not imported by the buckling project.

For every measure, a family of bounded continuous real functions having the
same strict-superlevel measures retains those measures at every point of its
global uniform closure. Every real threshold is covered, including a level
at which the reference function has a positive-measure plateau.

The proof uses countable directed unions over rational thresholds strictly
above the given threshold, followed by two uniform-distance sandwiches. It
does not subtract infinite measures, impose finiteness of the measure, use
continuity from above, or exclude exceptional thresholds. Mathlib's measure
continuity from below even applies to sets that are not assumed measurable;
thus no compatibility between the domain topology and measurable structure
is needed for this outer-measure statement. In the intended Borel-space
application the functions and all these superlevel sets are measurable.

This is only an equimeasurability closure step. No radial limit, Sobolev
convergence, energy inequality, or Faber--Krahn theorem is asserted.
-/

@[expose] public section

open Set MeasureTheory BoundedContinuousFunction
open scoped Topology ENNReal

namespace FaberKrahnDevelopment

section Superlevels

variable {E : Type*} [MeasurableSpace E]

/-- A strict superlevel measure is the supremum of the superlevel measures
at rational thresholds strictly above it. No measurability or finiteness
hypothesis is needed for this continuity-from-below identity. -/
lemma measure_strictSuperlevel_eq_iSup_rat (μ : Measure E) (u : E → ℝ) (t : ℝ) :
    μ {x | t < u x} =
      ⨆ q : {q : ℚ // t < (q : ℝ)}, μ {x | (q.val : ℝ) < u x} := by
  let Q := {q : ℚ // t < (q : ℝ)}
  let S : Q → Set E := fun q => {x | (q.val : ℝ) < u x}
  have hUnion : (⋃ q : Q, S q) = {x | t < u x} := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
      exact q.property.trans hq
    · intro hx
      change t < u x at hx
      obtain ⟨q, htq, hqu⟩ := exists_rat_btwn hx
      exact Set.mem_iUnion.mpr ⟨⟨q, htq⟩, hqu⟩
  have hDirected : Directed (· ⊆ ·) S := by
    intro a b
    by_cases hab : (a.val : ℝ) ≤ (b.val : ℝ)
    · refine ⟨a, Set.Subset.rfl, ?_⟩
      intro x hx
      exact lt_of_le_of_lt hab hx
    · refine ⟨b, ?_, Set.Subset.rfl⟩
      intro x hx
      exact lt_of_le_of_lt (not_le.mp hab).le hx
  rw [← hUnion]
  exact hDirected.measure_iUnion

end Superlevels

section UniformClosure

variable {E : Type*} [TopologicalSpace E] [MeasurableSpace E]

/-- A uniform-distance bound moves one strict superlevel into another.
The strict inequality on the distance supplies the strict threshold result. -/
lemma strictSuperlevel_subset_of_dist_lt
    {f g : E →ᵇ ℝ} {s t : ℝ} (hfg : dist f g < s - t) :
    {x | s < f x} ⊆ {x | t < g x} := by
  intro x hx
  have hPoint : dist (f x) (g x) < s - t :=
    (BoundedContinuousFunction.dist_coe_le_dist x).trans_lt hfg
  have hAbs : |f x - g x| < s - t := by
    simpa only [Real.dist_eq] using hPoint
  have hDiff : f x - g x < s - t := (abs_lt.mp hAbs).2
  change t < g x
  change s < f x at hx
  linarith

/-- Uniform closure preserves the entire strict-superlevel distribution
relative to any fixed reference function. The reference need not itself be
bounded or continuous. Equality holds at every real threshold. -/
lemma strictSuperlevel_measure_eq_of_mem_uniform_closure
    (μ : Measure E) (u : E → ℝ) {A : Set (E →ᵇ ℝ)}
    (hA : ∀ g ∈ A, ∀ t : ℝ, μ {x | t < g x} = μ {x | t < u x})
    {f : E →ᵇ ℝ} (hf : f ∈ closure A) (t : ℝ) :
    μ {x | t < f x} = μ {x | t < u x} := by
  apply le_antisymm
  · rw [measure_strictSuperlevel_eq_iSup_rat μ (f : E → ℝ) t]
    apply iSup_le
    intro q
    obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf
      ((q.val : ℝ) - t) (sub_pos.mpr q.property)
    calc
      μ {x | (q.val : ℝ) < f x} ≤ μ {x | t < g x} :=
        measure_mono (strictSuperlevel_subset_of_dist_lt hfg)
      _ = μ {x | t < u x} := hA g hg t
  · rw [measure_strictSuperlevel_eq_iSup_rat μ u t]
    apply iSup_le
    intro q
    obtain ⟨g, hg, hfg⟩ := Metric.mem_closure_iff.mp hf
      ((q.val : ℝ) - t) (sub_pos.mpr q.property)
    have hgf : dist g f < (q.val : ℝ) - t := by
      simpa only [dist_comm] using hfg
    calc
      μ {x | (q.val : ℝ) < u x} = μ {x | (q.val : ℝ) < g x} :=
        (hA g hg (q.val : ℝ)).symm
      _ ≤ μ {x | t < f x} :=
        measure_mono (strictSuperlevel_subset_of_dist_lt hgf)

/-- A prescribed strict-superlevel distribution in the full BCF space. -/
def prescribedSuperlevelFamily (μ : Measure E) (D : ℝ → ℝ≥0∞) : Set (E →ᵇ ℝ) :=
  {f | ∀ t : ℝ, μ {x | t < f x} = D t}

/-- The global uniform closure of any family with one prescribed strict
superlevel distribution still has exactly that distribution at all levels.
If the original family is empty the assertion is vacuous. -/
lemma closure_subset_prescribedSuperlevelFamily
    (μ : Measure E) (D : ℝ → ℝ≥0∞) {A : Set (E →ᵇ ℝ)}
    (hA : A ⊆ prescribedSuperlevelFamily μ D) :
    closure A ⊆ prescribedSuperlevelFamily μ D := by
  intro f hf
  obtain ⟨g₀, hg₀, _⟩ := Metric.mem_closure_iff.mp hf 1 zero_lt_one
  have hReference : ∀ g ∈ A, ∀ t : ℝ,
      μ {x | t < g x} = μ {x | t < g₀ x} := by
    intro g hg t
    exact (hA hg t).trans (hA hg₀ t).symm
  intro t
  exact (strictSuperlevel_measure_eq_of_mem_uniform_closure μ (g₀ : E → ℝ)
    hReference hf t).trans (hA hg₀ t)

/-- The functions with a prescribed strict-superlevel distribution form a
closed subset for the global uniform topology. -/
lemma isClosed_prescribedSuperlevelFamily (μ : Measure E) (D : ℝ → ℝ≥0∞) :
    IsClosed (prescribedSuperlevelFamily μ D) :=
  isClosed_of_closure_subset (closure_subset_prescribedSuperlevelFamily μ D
    (A := prescribedSuperlevelFamily μ D) Set.Subset.rfl)

/-- Taking global uniform closure of the complete distribution class does
not enlarge it. -/
lemma closure_prescribedSuperlevelFamily (μ : Measure E) (D : ℝ → ℝ≥0∞) :
    closure (prescribedSuperlevelFamily μ D) = prescribedSuperlevelFamily μ D :=
  (isClosed_prescribedSuperlevelFamily μ D).closure_eq

end UniformClosure

end FaberKrahnDevelopment
