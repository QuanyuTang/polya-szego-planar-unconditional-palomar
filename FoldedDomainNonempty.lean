module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FoldedDomainConnected

/-!
SOURCE_DRAFT: not registered or native checked. A nonempty open original
domain gives a nonempty strict folded domain for every affine halfspace.
The actual normal push handles a point on the reflecting boundary.
-/

@[expose] public section

noncomputable section

open Set Metric
open scoped InnerProductSpace RealInnerProductSpace

namespace FaberKrahnDevelopment.FoldedDomainConnected

open EuclideanReflection PolarizedOpenDomain AffineHalfspaceFold

theorem foldedDomain_nonempty (ν : UnitNormal) (c : ℝ) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) : (foldedDomain ν c Ω).Nonempty := by
  obtain ⟨a, ha⟩ := hne
  let G : Set Plane := Ω ∪ reflection ν c ⁻¹' Ω
  let x : Plane := fold ν c a
  have hG : IsOpen G := hΩ.union (hΩ.preimage (reflection_isometry ν c).continuous)
  have hx : x ∈ G := fold_mem_union ν c Ω ha
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hG x hx
  refine ⟨x + (δ / 2) • (ν : Plane), ?_, ?_⟩
  · apply hball
    change dist (x + (δ / 2) • (ν : Plane)) x < δ
    rw [dist_normal_push, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  · exact normal_push_mem_strictSide ν c (fold_mem_halfspace ν c a) (half_pos hδ)

lemma foldedDomain_subset_domain (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) :
    foldedDomain ν c Ω ⊆ domain ν c Ω := fun _ hx => Or.inl hx

lemma domain_inter_strictSide (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) :
    domain ν c Ω ∩ strictSide ν c = foldedDomain ν c Ω := by
  ext x
  constructor
  · rintro ⟨hx, hxS⟩
    rcases hx with hx | hx
    · exact hx
    · exact ⟨Or.inl hx.1, hxS⟩
  · intro hx
    exact ⟨Or.inl hx, hx.2⟩

end FaberKrahnDevelopment.FoldedDomainConnected

end

end
