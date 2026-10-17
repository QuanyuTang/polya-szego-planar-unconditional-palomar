module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import LipschitzCompactness
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Compactness with common support in the global uniform metric

SOURCE_DRAFT (2026-10-17). This isolated file has not yet been compiled.
It is not imported by the buckling project.

The domain need not be compact, complete, or locally compact. The functions
are actual bounded continuous real functions on the whole domain. They share
a Lipschitz constant, a pointwise interval bound, and a compact set outside
which they vanish. Restriction to that compact set is an isometry on this
family, because both functions vanish at every omitted point. The family is
closed in the complete space of bounded continuous functions; hence this
isometry is a closed embedding. Compactness on the compact domain then gives
compactness for the original global uniform distance.

No limiting function is defined merely on the compact support. The closure
and minimizer statements below concern functions on the whole original
space. No assertion about energy, radial symmetry, rearrangement, or
Faber--Krahn is made here.
-/

@[expose] public section

open Set BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

variable {E : Type*} [PseudoMetricSpace E]

/-- Full-domain functions with common bounds and literal zero values outside
the specified support set. Compactness of that set is required only later. -/
def commonSupportLipschitzFamily (S : Set E) (K : ℝ≥0) (M : ℝ) :
    Set (E →ᵇ ℝ) :=
  {f | LipschitzWith K f ∧ (∀ x, f x ∈ Icc 0 M) ∧ ∀ x, x ∉ S → f x = 0}

/-- Every defining condition is closed for the global uniform topology.
This lemma does not require the support set to be closed or compact. -/
lemma isClosed_commonSupportLipschitzFamily (S : Set E) (K : ℝ≥0) (M : ℝ) :
    IsClosed (commonSupportLipschitzFamily S K M) := by
  have hLip : IsClosed {f : E →ᵇ ℝ | LipschitzWith K f} :=
    (isClosed_setOf_lipschitzWith (α := E) (β := ℝ) K).preimage
      BoundedContinuousFunction.continuous_coe
  have hRange : IsClosed {f : E →ᵇ ℝ | ∀ x, f x ∈ Icc 0 M} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)
  have hZero : IsClosed {f : E →ᵇ ℝ | ∀ x, x ∉ S → f x = 0} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun x => isClosed_iInter fun _ =>
      isClosed_eq (continuous_eval_const x) continuous_const
  exact hLip.inter (hRange.inter hZero)

/-- Restriction preserves the full uniform distance when the omitted values
of every member are all zero. This includes an empty support set. -/
lemma isometry_restrict_commonSupportLipschitzFamily
    (S : Set E) (K : ℝ≥0) (M : ℝ) :
    Isometry (fun f : commonSupportLipschitzFamily S K M => f.val.restrict S) := by
  apply Isometry.of_dist_eq
  intro f g
  change dist (f.val.restrict S) (g.val.restrict S) = dist f.val g.val
  apply le_antisymm
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).2
    intro x
    exact BoundedContinuousFunction.dist_coe_le_dist (f := f.val) (g := g.val)
      (x : E)
  · apply (BoundedContinuousFunction.dist_le dist_nonneg).2
    intro x
    by_cases hx : x ∈ S
    · exact BoundedContinuousFunction.dist_coe_le_dist
        (f := f.val.restrict S) (g := g.val.restrict S) (⟨x, hx⟩ : S)
    · rw [f.property.2.2 x hx, g.property.2.2 x hx, dist_self]
      exact dist_nonneg

/-- The family is compact in the uniform metric on all of `E`.
Neither `E` nor the support set is required to be nonempty, and no sign
condition on the upper bound `M` is needed. -/
lemma isCompact_commonSupportLipschitzFamily
    {S : Set E} (hS : IsCompact S) (K : ℝ≥0) (M : ℝ) :
    IsCompact (commonSupportLipschitzFamily S K M) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : CompleteSpace (commonSupportLipschitzFamily S K M) :=
    (isClosed_commonSupportLipschitzFamily S K M).isComplete.completeSpace_coe
  let R : commonSupportLipschitzFamily S K M → (S →ᵇ ℝ) :=
    fun f => f.val.restrict S
  have hR : Isometry R := isometry_restrict_commonSupportLipschitzFamily S K M
  have hImage : ∀ f : commonSupportLipschitzFamily S K M,
      R f ∈ boundedLipschitzFamily (X := S) K M := by
    intro f
    refine ⟨?_, ?_⟩
    · apply LipschitzWith.of_dist_le_mul
      intro x y
      exact f.property.1.dist_le_mul (x : E) (y : E)
    · intro x
      exact f.property.2.1 (x : E)
  have hPreimage : R ⁻¹' boundedLipschitzFamily (X := S) K M = Set.univ :=
    Set.eq_univ_of_forall hImage
  have hCompact : IsCompact (R ⁻¹' boundedLipschitzFamily (X := S) K M) :=
    hR.isClosedEmbedding.isCompact_preimage (isCompact_boundedLipschitzFamily K M)
  rw [hPreimage] at hCompact
  exact isCompact_iff_isCompact_univ.mpr hCompact

/-- Uniform closure retains the pointwise bounds and zero values on the
complement of the original common support set. -/
lemma closure_subset_commonSupportLipschitzFamily
    {A : Set (E →ᵇ ℝ)} {S : Set E} {K : ℝ≥0} {M : ℝ}
    (hA : A ⊆ commonSupportLipschitzFamily S K M) :
    closure A ⊆ commonSupportLipschitzFamily S K M :=
  closure_minimal hA (isClosed_commonSupportLipschitzFamily S K M)

/-- The global uniform closure of any family with the common bounds and
compact support is compact in the original full-domain function space. -/
lemma isCompact_closure_of_commonSupport_lipschitz
    {A : Set (E →ᵇ ℝ)} {S : Set E} {K : ℝ≥0} {M : ℝ}
    (hS : IsCompact S) (hA : A ⊆ commonSupportLipschitzFamily S K M) :
    IsCompact (closure A) :=
  (isCompact_commonSupportLipschitzFamily hS K M).of_isClosed_subset isClosed_closure
    (closure_subset_commonSupportLipschitzFamily hA)

/-- A continuous real functional attains its minimum in the global uniform
closure of a nonempty family, with the original bounds and support retained. -/
lemma exists_min_on_closure_of_commonSupport_lipschitz
    {A : Set (E →ᵇ ℝ)} {S : Set E} {K : ℝ≥0} {M : ℝ}
    (hS : IsCompact S) (hA : A ⊆ commonSupportLipschitzFamily S K M)
    (hne : A.Nonempty) (J : (E →ᵇ ℝ) → ℝ) (hJ : ContinuousOn J (closure A)) :
    ∃ f ∈ closure A, LipschitzWith K f ∧ (∀ x, f x ∈ Icc 0 M) ∧
      (∀ x, x ∉ S → f x = 0) ∧ IsMinOn J (closure A) f := by
  obtain ⟨f, hf, hmin⟩ :=
    (isCompact_closure_of_commonSupport_lipschitz hS hA).exists_isMinOn
      (hne.mono subset_closure) hJ
  have hb := closure_subset_commonSupportLipschitzFamily hA hf
  exact ⟨f, hf, hb.1, hb.2.1, hb.2.2, hmin⟩

end FaberKrahnDevelopment
