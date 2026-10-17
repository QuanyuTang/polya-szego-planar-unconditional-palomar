module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Dynamics.Ergodic.MeasurePreserving
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# Two-point polarization and superlevel-set measure

Development status (2026-10-17): source drafted against the local Mathlib v4.28
API, not yet compiled. This file is quarantined from the production project.
Its mathematical scope is equimeasurability of two-point sorting only. It does
not assert a Sobolev energy estimate, convergence to Schwarz rearrangement,
Faber--Krahn, or a completed proof of any manuscript root.

The swapping condition is almost everywhere. Requiring an actual Euclidean
reflection to interchange a halfspace with its complement at every point
would fail on the fixed hyperplane. A separate elementary lemma below turns
an exact off-boundary swapping statement and a null boundary into this a.e.
condition. A concrete Euclidean halfspace instantiation is still pending.

No nonnegativity, compact support, or finite-measure assumption is needed for
the superlevel-set identity itself; therefore the result also covers the
nonnegative measurable compactly supported functions needed subsequently.
The proof uses addition in ENNReal, without subtraction or cancellation at
infinity.
-/

@[expose] public section

open MeasureTheory Set

namespace FaberKrahnDevelopment

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Split the measure of a set between a measurable side and its complement. -/
lemma measure_inter_add_compl_inter {H : Set α} (hH : MeasurableSet H)
    (A : Set α) : μ (H ∩ A) + μ (Hᶜ ∩ A) = μ A := by
  simpa only [Set.diff_eq, Set.inter_comm] using
    (measure_inter_add_diff (μ := μ) A hH)

/-- Inclusion--exclusion localized to a measurable side, with no finiteness
assumption and hence no ENNReal subtraction. -/
lemma measure_inter_union_add_inter_inter {H A B : Set α}
    (hH : MeasurableSet H) (hB : MeasurableSet B) :
    μ (H ∩ (A ∪ B)) + μ (H ∩ (A ∩ B)) = μ (H ∩ A) + μ (H ∩ B) := by
  rw [Set.inter_union_distrib_left H A B, Set.inter_inter_distrib_left H A B]
  exact measure_union_add_inter (μ := μ) (H ∩ A) (hH.inter hB)

/-- A direct max/min superlevel identity. Measurability of the second
function suffices for the underlying inclusion--exclusion identity. -/
lemma measure_superlevel_max_add_min {f g : α → ℝ}
    (hg : Measurable g) (t : ℝ) :
    μ {x | t < max (f x) (g x)} + μ {x | t < min (f x) (g x)} =
      μ {x | t < f x} + μ {x | t < g x} := by
  have hmax : {x | t < max (f x) (g x)} = {x | t < f x} ∪ {x | t < g x} := by
    apply Set.ext
    intro x
    simp only [Set.mem_setOf_eq, Set.mem_union, lt_max_iff]
  have hmin : {x | t < min (f x) (g x)} = {x | t < f x} ∩ {x | t < g x} := by
    apply Set.ext
    intro x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, lt_min_iff]
  rw [hmax, hmin]
  exact measure_union_add_inter (μ := μ) {x | t < f x}
    (measurableSet_lt measurable_const hg)

/-- An exact swapping statement away from a null exceptional set yields the
a.e. swapping hypothesis used by the polarization theorem. In the Euclidean
application the exceptional set will be the reflecting hyperplane. -/
lemma ae_swap_of_null_exception {H N : Set α} {τ : α → α}
    (hN : μ N = 0)
    (hSwap : ∀ x, x ∉ N → (τ x ∈ H ↔ x ∉ H)) :
    ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H :=
  (measure_eq_zero_iff_ae_notMem.mp hN).mono fun x hx => hSwap x hx

/-- Transport the complementary-side part of a measurable set to the chosen
side by a measure-preserving map that swaps the sides a.e. -/
lemma measure_compl_inter_eq_inter_preimage {H A : Set α} {τ : α → α}
    (hH : MeasurableSet H) (hA : MeasurableSet A)
    (hτ : MeasurePreserving τ μ μ)
    (hSwap : ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H) :
    μ (Hᶜ ∩ A) = μ (H ∩ τ ⁻¹' A) := by
  calc
    μ (Hᶜ ∩ A) = μ (τ ⁻¹' (Hᶜ ∩ A)) :=
      (hτ.measure_preimage (hH.compl.inter hA).nullMeasurableSet).symm
    _ = μ (H ∩ τ ⁻¹' A) := by
      apply measure_congr
      apply hSwap.mono
      intro x hx
      change (τ x ∉ H ∧ τ x ∈ A) = (x ∈ H ∧ τ x ∈ A)
      apply propext
      constructor
      · intro h
        refine ⟨?_, h.2⟩
        by_contra hn
        exact h.1 (hx.mpr hn)
      · intro h
        refine ⟨?_, h.2⟩
        intro hτH
        exact (hx.mp hτH) h.1

/-- Sort membership in each two-point orbit: put the union on the chosen side
and the intersection on the complementary side. The resulting set has the
same measure as the original measurable set. -/
lemma measure_twoPointSorted_set {H A : Set α} {τ : α → α}
    (hH : MeasurableSet H) (hA : MeasurableSet A)
    (hτ : MeasurePreserving τ μ μ) (hInv : Function.Involutive τ)
    (hSwap : ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H) :
    μ ((H ∩ (A ∪ τ ⁻¹' A)) ∪ (Hᶜ ∩ (A ∩ τ ⁻¹' A))) = μ A := by
  have hAτ : MeasurableSet (τ ⁻¹' A) := hA.preimage hτ.measurable
  have hI : MeasurableSet (A ∩ τ ⁻¹' A) := hA.inter hAτ
  have hIInv : τ ⁻¹' (A ∩ τ ⁻¹' A) = A ∩ τ ⁻¹' A := by
    apply Set.ext
    intro x
    change (τ x ∈ A ∧ τ (τ x) ∈ A) ↔ (x ∈ A ∧ τ x ∈ A)
    rw [hInv x]
    exact and_comm
  have hIHalf : μ (Hᶜ ∩ (A ∩ τ ⁻¹' A)) = μ (H ∩ (A ∩ τ ⁻¹' A)) := by
    calc
      μ (Hᶜ ∩ (A ∩ τ ⁻¹' A)) = μ (H ∩ τ ⁻¹' (A ∩ τ ⁻¹' A)) :=
        measure_compl_inter_eq_inter_preimage hH hI hτ hSwap
      _ = μ (H ∩ (A ∩ τ ⁻¹' A)) := by rw [hIInv]
  have hDisjoint :
      Disjoint (H ∩ (A ∪ τ ⁻¹' A)) (Hᶜ ∩ (A ∩ τ ⁻¹' A)) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hy.1 hx.1
  calc
    μ ((H ∩ (A ∪ τ ⁻¹' A)) ∪ (Hᶜ ∩ (A ∩ τ ⁻¹' A))) =
        μ (H ∩ (A ∪ τ ⁻¹' A)) + μ (Hᶜ ∩ (A ∩ τ ⁻¹' A)) :=
      measure_union hDisjoint (hH.compl.inter hI)
    _ = μ (H ∩ (A ∪ τ ⁻¹' A)) + μ (H ∩ (A ∩ τ ⁻¹' A)) := by rw [hIHalf]
    _ = μ (H ∩ A) + μ (H ∩ τ ⁻¹' A) :=
      measure_inter_union_add_inter_inter hH hAτ
    _ = μ (H ∩ A) + μ (Hᶜ ∩ A) := by
      rw [← measure_compl_inter_eq_inter_preimage hH hA hτ hSwap]
    _ = μ A := measure_inter_add_compl_inter hH A

open Classical in
/-- Two-point polarization: larger value on `H`, smaller value on its
complement. This literal definition has no fallback approximation. -/
noncomputable def twoPointPolarization (H : Set α) (τ : α → α)
    (f : α → ℝ) (x : α) : ℝ :=
  if x ∈ H then max (f x) (f (τ x)) else min (f x) (f (τ x))

/-- Measurability of the explicit two-point polarization. -/
lemma measurable_twoPointPolarization {H : Set α} {τ : α → α} {f : α → ℝ}
    (hH : MeasurableSet H) (hτ : Measurable τ) (hf : Measurable f) :
    Measurable (twoPointPolarization H τ f) := by
  classical
  unfold twoPointPolarization
  exact Measurable.ite hH (hf.max (hf.comp hτ)) (hf.min (hf.comp hτ))

/-- Two-point polarization preserves the measure of every strict superlevel
set. The abstract hypotheses are the natural measurable reflection data,
including a.e. side swapping so that a null reflecting boundary is allowed. -/
lemma measure_superlevel_twoPointPolarization {H : Set α} {τ : α → α}
    {f : α → ℝ} (hH : MeasurableSet H) (hf : Measurable f)
    (hτ : MeasurePreserving τ μ μ) (hInv : Function.Involutive τ)
    (hSwap : ∀ᵐ x ∂μ, τ x ∈ H ↔ x ∉ H) (t : ℝ) :
    μ {x | t < twoPointPolarization H τ f x} = μ {x | t < f x} := by
  classical
  let A : Set α := {x | t < f x}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hf
  have hLevel : {x | t < twoPointPolarization H τ f x} =
      (H ∩ (A ∪ τ ⁻¹' A)) ∪ (Hᶜ ∩ (A ∩ τ ⁻¹' A)) := by
    apply Set.ext
    intro x
    by_cases hx : x ∈ H
    · simp [twoPointPolarization, hx, A, lt_max_iff]
    · simp [twoPointPolarization, hx, A, lt_min_iff]
  rw [hLevel]
  exact measure_twoPointSorted_set hH hA hτ hInv hSwap

end FaberKrahnDevelopment
