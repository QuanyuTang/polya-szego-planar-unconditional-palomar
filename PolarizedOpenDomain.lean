module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EuclideanReflectionContraction
public import PolarizationMeasure

/-!
# Actual open domains and compact supports under affine polarization

SOURCE_DRAFT: not registered or native checked. The chosen halfspace is
the original closed side `c <= inner normal x`. The domain is expressed
using a strict side and a two-sided intersection, which is genuinely open.
On the reflecting boundary the reflection fixes the point, so the usual
sorted-set definition agrees pointwise, including the boundary. No domain
boundedness, energy preservation, or H01 admissibility is assumed here.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace InnerProductSpace

namespace FaberKrahnDevelopment
namespace PolarizedOpenDomain

open EuclideanReflection

def strictSide (ν : UnitNormal) (c : ℝ) : Set Plane :=
  {x | c < ⟪(ν : Plane), x⟫_ℝ}

def domain (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) : Set Plane :=
  ((Ω ∪ reflection ν c ⁻¹' Ω) ∩ strictSide ν c) ∪
    (Ω ∩ reflection ν c ⁻¹' Ω)

def supportSet (ν : UnitNormal) (c : ℝ) (K : Set Plane) : Set Plane :=
  ((K ∪ reflection ν c ⁻¹' K) ∩ halfspace ν c) ∪
    (K ∩ reflection ν c ⁻¹' K)

lemma reflection_eq_self_of_boundary (ν : UnitNormal) (c : ℝ) {x : Plane}
    (hx : ⟪(ν : Plane), x⟫_ℝ = c) : reflection ν c x = x := by
  simp only [reflection_eq_add_smul, hx, sub_self, mul_zero, zero_smul, add_zero]

lemma strictSide_isOpen (ν : UnitNormal) (c : ℝ) : IsOpen (strictSide ν c) :=
  isOpen_lt continuous_const (continuous_const.inner continuous_id)

lemma domain_isOpen (ν : UnitNormal) (c : ℝ) {Ω : Set Plane} (hΩ : IsOpen Ω) :
    IsOpen (domain ν c Ω) := by
  have hpre := hΩ.preimage (reflection_isometry ν c).continuous
  exact ((hΩ.union hpre).inter (strictSide_isOpen ν c)).union (hΩ.inter hpre)

attribute [local instance] Classical.propDecidable

lemma mem_domain_iff (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) (x : Plane) :
    x ∈ domain ν c Ω ↔ if x ∈ halfspace ν c then
      x ∈ Ω ∨ reflection ν c x ∈ Ω else x ∈ Ω ∧ reflection ν c x ∈ Ω := by
  classical
  by_cases hH : x ∈ halfspace ν c
  · rw [if_pos hH]
    change c ≤ ⟪(ν : Plane), x⟫_ℝ at hH
    by_cases hs : c < ⟪(ν : Plane), x⟫_ℝ
    · simp only [domain, mem_union, mem_inter_iff, mem_preimage, strictSide, mem_setOf_eq, hs,
        and_true]
      constructor
      · rintro (h | h)
        · exact h
        · exact Or.inl h.1
      · intro h
        exact Or.inl h
    · have hb : ⟪(ν : Plane), x⟫_ℝ = c := le_antisymm (not_lt.mp hs) hH
      have hf := reflection_eq_self_of_boundary ν c hb
      simp only [domain, mem_union, mem_inter_iff, mem_preimage, strictSide, mem_setOf_eq, hs,
        and_false, false_or, hf, and_self, or_self]
  · rw [if_neg hH]
    have hs : ¬ c < ⟪(ν : Plane), x⟫_ℝ := fun h => hH h.le
    simp only [domain, mem_union, mem_inter_iff, mem_preimage, strictSide, mem_setOf_eq, hs,
      and_false, false_or]

lemma domain_eq_sorted_set (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) :
    domain ν c Ω =
      ((halfspace ν c ∩ (Ω ∪ reflection ν c ⁻¹' Ω)) ∪
        ((halfspace ν c)ᶜ ∩ (Ω ∩ reflection ν c ⁻¹' Ω))) := by
  classical
  ext x
  rw [mem_domain_iff]
  by_cases hH : x ∈ halfspace ν c <;> simp only [hH, if_pos, if_neg, mem_union,
    mem_inter_iff, mem_compl_iff, mem_preimage, true_and, false_and, or_false, false_or,
    not_true_eq_false, not_false_eq_true]

lemma volume_domain (ν : UnitNormal) (c : ℝ) {Ω : Set Plane} (hΩ : MeasurableSet Ω) :
    volume (domain ν c Ω) = volume Ω := by
  rw [domain_eq_sorted_set]
  exact measure_twoPointSorted_set (halfspace_measurableSet ν c) hΩ
    (reflection_measurePreserving ν c) (reflection_involutive ν c) (reflection_ae_swap ν c)

lemma reflection_preimage_eq_image (ν : UnitNormal) (c : ℝ) (K : Set Plane) :
    reflection ν c ⁻¹' K = reflection ν c '' K := by
  ext x
  constructor
  · intro hx
    exact ⟨reflection ν c x, hx, reflection_reflection ν c x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa only [mem_preimage, reflection_reflection] using hy

lemma supportSet_isCompact (ν : UnitNormal) (c : ℝ) {K : Set Plane} (hK : IsCompact K) :
    IsCompact (supportSet ν c K) := by
  have hpre : IsCompact (reflection ν c ⁻¹' K) := by
    rw [reflection_preimage_eq_image]
    exact hK.image (reflection_isometry ν c).continuous
  exact ((hK.union hpre).inter_right (halfspace_isClosed ν c)).union
    (hK.inter_right hpre.isClosed)

lemma supportSet_subset_domain (ν : UnitNormal) (c : ℝ) {K Ω : Set Plane} (hKΩ : K ⊆ Ω) :
    supportSet ν c K ⊆ domain ν c Ω := by
  rintro x (⟨hxU, hxH⟩ | ⟨hxK, hxpre⟩)
  · by_cases hs : c < ⟪(ν : Plane), x⟫_ℝ
    · apply Or.inl
      refine ⟨?_, hs⟩
      rcases hxU with hx | hx
      · exact Or.inl (hKΩ hx)
      · exact Or.inr (hKΩ hx)
    · have hb : ⟪(ν : Plane), x⟫_ℝ = c :=
        le_antisymm (not_lt.mp hs) hxH
      have hf := reflection_eq_self_of_boundary ν c hb
      have hx : x ∈ K := by
        rcases hxU with h | h
        · exact h
        · simpa only [mem_preimage, hf] using h
      exact Or.inr ⟨hKΩ hx, by simpa only [mem_preimage, hf] using hKΩ hx⟩
  · exact Or.inr ⟨hKΩ hxK, hKΩ hxpre⟩

lemma support_polarization_subset (ν : UnitNormal) (c : ℝ) {f : Plane → ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    Function.support (twoPointPolarization (halfspace ν c) (reflection ν c) f) ⊆
      supportSet ν c (tsupport f) := by
  classical
  intro x hx
  change twoPointPolarization (halfspace ν c) (reflection ν c) f x ≠ 0 at hx
  by_cases hH : x ∈ halfspace ν c
  · apply Or.inl
    refine ⟨?_, hH⟩
    by_contra hn
    have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hn (Or.inl h))
    have hτ0 : f (reflection ν c x) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hn (Or.inr h))
    exact hx (by simp only [twoPointPolarization, if_pos hH, hx0, hτ0, max_self])
  · apply Or.inr
    constructor
    · by_contra hn
      have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport hn
      exact hx (by simp only [twoPointPolarization, if_neg hH, hx0,
        min_eq_left (hf (reflection ν c x))])
    · by_contra hn
      have hτ0 : f (reflection ν c x) = 0 := image_eq_zero_of_notMem_tsupport hn
      exact hx (by simp only [twoPointPolarization, if_neg hH, hτ0,
        min_eq_right (hf x)])

lemma tsupport_polarization_subset (ν : UnitNormal) (c : ℝ) {f : Plane → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hc : HasCompactSupport f) :
    tsupport (twoPointPolarization (halfspace ν c) (reflection ν c) f) ⊆
      supportSet ν c (tsupport f) :=
  closure_minimal (support_polarization_subset ν c hf) (supportSet_isCompact ν c hc).isClosed

theorem polarization_hasCompactSupport_inside (ν : UnitNormal) (c : ℝ)
    {Ω : Set Plane} {f : Plane → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ Ω) :
    HasCompactSupport (twoPointPolarization (halfspace ν c) (reflection ν c) f) ∧
      tsupport (twoPointPolarization (halfspace ν c) (reflection ν c) f) ⊆ domain ν c Ω := by
  have hsub := tsupport_polarization_subset ν c hf hc
  exact ⟨(supportSet_isCompact ν c hc).of_isClosed_subset (isClosed_tsupport _) hsub,
    hsub.trans (supportSet_subset_domain ν c hs)⟩

end PolarizedOpenDomain
end FaberKrahnDevelopment

end

end
