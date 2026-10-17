module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FoldedDomainNonempty
public import Mathlib.MeasureTheory.Measure.Restrict

/-!
# Extending a strict folded-domain polarization branch to full volume

SOURCE_DRAFT: not compiled or registered. The zero extension outside the
actual original domain, actual reflection measure preservation and actual
side swapping supply all exceptional-set transports. The reflecting
boundary is fixed pointwise. No positivity or boundary regularity of U
is needed; a strict-domain branch is explicitly an intermediate input.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped InnerProductSpace RealInnerProductSpace

namespace FaberKrahnDevelopment.PolarizationBranchExtension

open EuclideanReflection PolarizedOpenDomain FoldedDomainConnected

lemma ae_first_branch_of_closed_side (ν : UnitNormal) (c : ℝ) (U : Plane → ℝ)
    (hSide : ∀ᵐ x ∂volume, x ∈ halfspace ν c →
      twoPointPolarization (halfspace ν c) (reflection ν c) U x = U x) :
    twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume] U := by
  have hRef := (reflection_measurePreserving ν c).quasiMeasurePreserving.ae hSide
  filter_upwards [hSide, hRef, reflection_ae_swap ν c] with x hx hr hs
  by_cases hxH : x ∈ halfspace ν c
  · exact hx hxH
  · have hxR : reflection ν c x ∈ halfspace ν c := hs.mpr hxH
    have hm := hr hxR
    simp only [twoPointPolarization, if_pos hxR, reflection_reflection] at hm
    have hOrder : U x ≤ U (reflection ν c x) := (le_max_right _ _).trans hm.le
    simp only [twoPointPolarization, if_neg hxH, min_eq_left hOrder]

lemma ae_second_branch_of_closed_side (ν : UnitNormal) (c : ℝ) (U : Plane → ℝ)
    (hSide : ∀ᵐ x ∂volume, x ∈ halfspace ν c →
      twoPointPolarization (halfspace ν c) (reflection ν c) U x = U (reflection ν c x)) :
    twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume]
      fun x => U (reflection ν c x) := by
  have hRef := (reflection_measurePreserving ν c).quasiMeasurePreserving.ae hSide
  filter_upwards [hSide, hRef, reflection_ae_swap ν c] with x hx hr hs
  by_cases hxH : x ∈ halfspace ν c
  · exact hx hxH
  · have hxR : reflection ν c x ∈ halfspace ν c := hs.mpr hxH
    have hm := hr hxR
    simp only [twoPointPolarization, if_pos hxR, reflection_reflection] at hm
    have hOrder : U (reflection ν c x) ≤ U x := (le_max_left _ _).trans hm.le
    simp only [twoPointPolarization, if_neg hxH, min_eq_right hOrder]

theorem ae_global_branch_of_folded_branch (ν : UnitNormal) (c : ℝ)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (U : Plane → ℝ)
    (hOff : ∀ᵐ x ∂volume, x ∉ Ω → U x = 0)
    (hBranch :
      (twoPointPolarization (halfspace ν c) (reflection ν c) U
          =ᵐ[volume.restrict (foldedDomain ν c Ω)] U) ∨
      (twoPointPolarization (halfspace ν c) (reflection ν c) U
          =ᵐ[volume.restrict (foldedDomain ν c Ω)] fun x => U (reflection ν c x))) :
    (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume] U) ∨
      (twoPointPolarization (halfspace ν c) (reflection ν c) U =ᵐ[volume]
        fun x => U (reflection ν c x)) := by
  have hD : MeasurableSet (foldedDomain ν c Ω) :=
    ((hΩ.union (hΩ.preimage (reflection_isometry ν c).continuous)).inter
      (strictSide_isOpen ν c)).measurableSet
  have hOffR := (reflection_measurePreserving ν c).quasiMeasurePreserving.ae hOff
  have hSide : ∀ target : Plane → ℝ,
      (twoPointPolarization (halfspace ν c) (reflection ν c) U
          =ᵐ[volume.restrict (foldedDomain ν c Ω)] target) →
      (∀ x, inner ℝ (ν : Plane) x = c → target x = U x) →
      (∀ᵐ x ∂volume, x ∉ Ω → reflection ν c x ∉ Ω → target x = 0) →
      ∀ᵐ x ∂volume, x ∈ halfspace ν c →
        twoPointPolarization (halfspace ν c) (reflection ν c) U x = target x := by
    intro target hLocal hBoundary hTargetOff
    have hLocal' := (ae_restrict_iff' hD).mp hLocal
    filter_upwards [hLocal', hOff, hOffR, hTargetOff] with x hx hox hor htx hxH
    by_cases hxS : c < inner ℝ (ν : Plane) x
    · by_cases hxUnion : x ∈ Ω ∪ reflection ν c ⁻¹' Ω
      · exact hx ⟨hxUnion, hxS⟩
      · have hxΩ : x ∉ Ω := fun h => hxUnion (Or.inl h)
        have hxRΩ : reflection ν c x ∉ Ω := fun h => hxUnion (Or.inr h)
        simp only [twoPointPolarization, if_pos hxH, hox hxΩ, hor hxRΩ,
          max_self, htx hxΩ hxRΩ]
    · have hb : inner ℝ (ν : Plane) x = c := le_antisymm (not_lt.mp hxS) hxH
      rw [hBoundary x hb]
      simp only [twoPointPolarization, if_pos hxH,
        reflection_eq_self_of_boundary ν c hb, max_self]
  rcases hBranch with hFirst | hSecond
  · apply Or.inl
    apply ae_first_branch_of_closed_side ν c U
    exact hSide U hFirst (fun _ _ => rfl) (hOff.mono fun x hx hxΩ _ => hx hxΩ)
  · apply Or.inr
    apply ae_second_branch_of_closed_side ν c U
    apply hSide (fun x => U (reflection ν c x)) hSecond
    · intro x hx
      rw [reflection_eq_self_of_boundary ν c hx]
    · exact hOffR.mono fun x hx _ hxRΩ => hx hxRΩ

end FaberKrahnDevelopment.PolarizationBranchExtension
end
end
