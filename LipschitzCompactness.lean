module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Compactness of a uniformly bounded Lipschitz family

SOURCE_DRAFT (2026-10-17). This isolated development has not yet been compiled.
It is not imported by the buckling project.

This is the compactness step intended for restrictions of finite polarization
orbits to a fixed closed Euclidean ball. It uses the uniform metric on actual
bounded continuous functions. Common Lipschitz and pointwise interval bounds
give a closed compact family; consequently the uniform closure of any such
orbit is compact and a continuous real functional attains a minimum there.

No assertion about symmetrization, the existence of an energy-controlled
radial limit, a Sobolev limit, or Faber--Krahn is made here. The actual orbit
must still be constructed and shown to satisfy these elementary bounds;
continuity of the intended moment functional is a separate obligation.
-/

@[expose] public section

open Set Filter BoundedContinuousFunction
open scoped Topology NNReal

namespace FaberKrahnDevelopment

variable {X : Type*} [PseudoMetricSpace X] [CompactSpace X]

/-- A common Lipschitz constant and an actual pointwise interval bound. -/
def boundedLipschitzFamily (K : ℝ≥0) (M : ℝ) : Set (X →ᵇ ℝ) :=
  {f | LipschitzWith K f ∧ ∀ x, f x ∈ Icc 0 M}

lemma isClosed_boundedLipschitzFamily (K : ℝ≥0) (M : ℝ) :
    IsClosed (boundedLipschitzFamily (X := X) K M) := by
  have hLip : IsClosed {f : X →ᵇ ℝ | LipschitzWith K f} :=
    (isClosed_setOf_lipschitzWith (α := X) (β := ℝ) K).preimage
      BoundedContinuousFunction.continuous_coe
  have hRange : IsClosed {f : X →ᵇ ℝ | ∀ x, f x ∈ Icc 0 M} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun x => isClosed_Icc.preimage (continuous_eval_const x)
  exact hLip.inter hRange

/-- The whole family is compact in the uniform metric, with no condition on
the sign of `M` needed (a negative bound can simply give an empty family). -/
lemma isCompact_boundedLipschitzFamily (K : ℝ≥0) (M : ℝ) :
    IsCompact (boundedLipschitzFamily (X := X) K M) := by
  refine BoundedContinuousFunction.arzela_ascoli₂ (Icc 0 M) isCompact_Icc
    (boundedLipschitzFamily K M) (isClosed_boundedLipschitzFamily K M) ?_ ?_
  · intro f x hf
    exact hf.2 x
  · refine Metric.equicontinuous_of_continuity_modulus
      (fun t : ℝ => (K : ℝ) * t) ?_ _ ?_
    · have hlim : Tendsto (fun t : ℝ => (K : ℝ) * t) (𝓝 0)
          (𝓝 ((K : ℝ) * 0)) := tendsto_const_nhds.mul tendsto_id
      simpa only [mul_zero] using hlim
    · rintro x y ⟨f, hf⟩
      exact hf.1.dist_le_mul x y

/-- Uniform closure retains the literal Lipschitz and range bounds. -/
lemma closure_subset_boundedLipschitzFamily {A : Set (X →ᵇ ℝ)}
    {K : ℝ≥0} {M : ℝ} (hA : A ⊆ boundedLipschitzFamily K M) :
    closure A ⊆ boundedLipschitzFamily K M :=
  closure_minimal hA (isClosed_boundedLipschitzFamily K M)

/-- A family satisfying the common bounds has compact uniform closure. -/
lemma isCompact_closure_of_bounded_lipschitz {A : Set (X →ᵇ ℝ)}
    {K : ℝ≥0} {M : ℝ} (hA : A ⊆ boundedLipschitzFamily K M) :
    IsCompact (closure A) :=
  (isCompact_boundedLipschitzFamily K M).of_isClosed_subset isClosed_closure
    (closure_subset_boundedLipschitzFamily hA)

/-- A continuous real functional has an actual minimizer in a nonempty
bounded Lipschitz family's uniform closure. Its bounds are retained. -/
lemma exists_min_on_closure_of_bounded_lipschitz {A : Set (X →ᵇ ℝ)}
    {K : ℝ≥0} {M : ℝ} (hA : A ⊆ boundedLipschitzFamily K M)
    (hne : A.Nonempty) (J : (X →ᵇ ℝ) → ℝ)
    (hJ : ContinuousOn J (closure A)) :
    ∃ f ∈ closure A, LipschitzWith K f ∧ (∀ x, f x ∈ Icc 0 M) ∧
      IsMinOn J (closure A) f := by
  obtain ⟨f, hf, hmin⟩ := (isCompact_closure_of_bounded_lipschitz hA).exists_isMinOn
    (hne.mono subset_closure) hJ
  have hb := closure_subset_boundedLipschitzFamily hA hf
  exact ⟨f, hf, hb.1, hb.2, hmin⟩

end FaberKrahnDevelopment
