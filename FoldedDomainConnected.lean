module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import AffineHalfspaceFold
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Connected.LocallyPathConnected
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Connectedness of the actual strictly folded domain

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
For an arbitrary open preconnected planar set Omega, the chosen strict
half of Omega union its actual reflected preimage is preconnected.

An actual path inside Omega is folded into the closed chosen halfspace.
Its compact image has an actual uniform positive neighborhood inside the
open reflected union. A single small positive normal push moves the whole
folded path into the strict side. Actual short convex endpoint paths join
the original endpoints to their pushed endpoints.

No path, compactness margin, offset sign, boundedness, boundary regularity
or connectedness of the target is assumed. The result concerns only the
strict chosen-side part, not the whole polarized open domain.
-/

@[expose] public section

noncomputable section

open Set Metric Filter Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace FaberKrahnDevelopment.FoldedDomainConnected

open EuclideanReflection PolarizedOpenDomain AffineHalfspaceFold

def foldedDomain (ν : UnitNormal) (c : ℝ) (Ω : Set Plane) : Set Plane :=
  (Ω ∪ reflection ν c ⁻¹' Ω) ∩ strictSide ν c

lemma foldedDomain_isOpen (ν : UnitNormal) (c : ℝ) {Ω : Set Plane} (hΩ : IsOpen Ω) :
    IsOpen (foldedDomain ν c Ω) :=
  (hΩ.union (hΩ.preimage (reflection_isometry ν c).continuous)).inter
    (strictSide_isOpen ν c)

lemma strictSide_convex (ν : UnitNormal) (c : ℝ) : Convex ℝ (strictSide ν c) := by
  exact (convex_Ioi c).linear_preimage (innerSL ℝ (ν : Plane)).toLinearMap

/-- The local path-connected structure is actually produced from convex
metric balls, rather than added as an assumption on the domain. -/
lemma isPathConnected_of_open_preconnected {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hne : Ω.Nonempty) : IsPathConnected Ω := by
  letI : LocallyPathConnectedSpace Plane :=
    LocallyPathConnectedSpace.of_bases (fun _ => Metric.nhds_basis_ball)
      (fun p r hr => (convex_ball p r).isPathConnected (nonempty_ball.mpr hr))
  exact hΩ.isConnected_iff_isPathConnected.mp ⟨hne, hconn⟩

/-- The endpoint join is an actual segment in the convex intersection of
a small ball and the strict halfspace. Its containing ball lies in G. -/
lemma joinedIn_normal_push (ν : UnitNormal) (c : ℝ) {G : Set Plane} {x : Plane}
    (hx : x ∈ strictSide ν c) {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t) (htδ : t < δ)
    (hball : ball x δ ⊆ G) :
    JoinedIn (G ∩ strictSide ν c) x (x + t • (ν : Plane)) := by
  have hxH : x ∈ halfspace ν c := by
    change c ≤ ⟪(ν : Plane), x⟫_ℝ
    exact (show c < ⟪(ν : Plane), x⟫_ℝ from hx).le
  have hpush : x + t • (ν : Plane) ∈ ball x δ := by
    change dist (x + t • (ν : Plane)) x < δ
    rw [dist_normal_push, abs_of_pos ht]
    exact htδ
  have hcv : Convex ℝ (ball x δ ∩ strictSide ν c) :=
    (convex_ball x δ).inter (strictSide_convex ν c)
  have hleft : x ∈ ball x δ ∩ strictSide ν c := ⟨mem_ball_self hδ, hx⟩
  have hright : x + t • (ν : Plane) ∈ ball x δ ∩ strictSide ν c :=
    ⟨hpush, normal_push_mem_strictSide ν c hxH ht⟩
  exact ((hcv.isPathConnected ⟨x, hleft⟩).joinedIn x hleft _ hright).mono
    (fun _ hy => ⟨hball hy.1, hy.2⟩)

/-- The actual uniform normal push produces a path in the strict folded
domain for any two of its points, from only the original open connected set. -/
theorem joinedIn_foldedDomain (ν : UnitNormal) (c : ℝ) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) {p q : Plane}
    (hp : p ∈ foldedDomain ν c Ω) (hq : q ∈ foldedDomain ν c Ω) :
    JoinedIn (foldedDomain ν c Ω) p q := by
  have hpH : p ∈ halfspace ν c := by
    change c ≤ ⟪(ν : Plane), p⟫_ℝ
    exact (show c < ⟪(ν : Plane), p⟫_ℝ from hp.2).le
  have hqH : q ∈ halfspace ν c := by
    change c ≤ ⟪(ν : Plane), q⟫_ℝ
    exact (show c < ⟪(ν : Plane), q⟫_ℝ from hq.2).le
  obtain ⟨a, ha, rfl⟩ := exists_fold_preimage ν c Ω hp.1 hpH
  obtain ⟨b, hb, rfl⟩ := exists_fold_preimage ν c Ω hq.1 hqH
  have hΩpath := isPathConnected_of_open_preconnected hΩ hconn ⟨a, ha⟩
  have hγ : JoinedIn Ω a b := hΩpath.joinedIn a ha b hb
  let α : Path (fold ν c a) (fold ν c b) := hγ.somePath.map (continuous_fold ν c)
  let G : Set Plane := Ω ∪ reflection ν c ⁻¹' Ω
  let K : Set Plane := Set.range α
  have hG : IsOpen G := hΩ.union (hΩ.preimage (reflection_isometry ν c).continuous)
  have hK : IsCompact K := isCompact_range α.continuous
  have hKG : K ⊆ G := by
    rintro x ⟨s, rfl⟩
    exact fold_mem_union ν c Ω (hγ.somePath_mem s)
  have hKH : K ⊆ halfspace ν c := by
    rintro x ⟨s, rfl⟩
    exact fold_mem_halfspace ν c (hγ.somePath s)
  obtain ⟨δ, hδ, hTube⟩ := hK.exists_thickening_subset_open hG hKG
  let t : ℝ := δ / 2
  have ht : 0 < t := half_pos hδ
  have htδ : t < δ := half_lt_self hδ
  have hPush : ∀ x ∈ K, x + t • (ν : Plane) ∈ foldedDomain ν c Ω := by
    intro x hx
    refine ⟨?_, normal_push_mem_strictSide ν c (hKH hx) ht⟩
    apply hTube
    apply mem_thickening_iff.mpr
    refine ⟨x, hx, ?_⟩
    rw [dist_normal_push, abs_of_pos ht]
    exact htδ
  have hMiddle : JoinedIn (foldedDomain ν c Ω)
      (fold ν c a + t • (ν : Plane)) (fold ν c b + t • (ν : Plane)) := by
    refine ⟨α.map (continuous_normal_push ν t), ?_⟩
    intro s
    change α s + t • (ν : Plane) ∈ foldedDomain ν c Ω
    exact hPush (α s) ⟨s, rfl⟩
  have haK : fold ν c a ∈ K := ⟨0, α.source⟩
  have hbK : fold ν c b ∈ K := ⟨1, α.target⟩
  have hLeft : JoinedIn (foldedDomain ν c Ω)
      (fold ν c a) (fold ν c a + t • (ν : Plane)) :=
    joinedIn_normal_push ν c hp.2 hδ ht htδ
      ((ball_subset_thickening haK δ).trans hTube)
  have hRight : JoinedIn (foldedDomain ν c Ω)
      (fold ν c b) (fold ν c b + t • (ν : Plane)) :=
    joinedIn_normal_push ν c hq.2 hδ ht htδ
      ((ball_subset_thickening hbK δ).trans hTube)
  exact hLeft.trans (hMiddle.trans hRight.symm)

theorem isPathConnected_foldedDomain (ν : UnitNormal) (c : ℝ) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hne : (foldedDomain ν c Ω).Nonempty) : IsPathConnected (foldedDomain ν c Ω) := by
  obtain ⟨p, hp⟩ := hne
  refine ⟨p, hp, ?_⟩
  intro q hq
  exact joinedIn_foldedDomain ν c hΩ hconn hp hq

/-- Empty sets are included: no nonemptiness assumption is added to the
natural open/preconnected source-domain statement. -/
theorem isPreconnected_foldedDomain (ν : UnitNormal) (c : ℝ) {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω) :
    IsPreconnected (foldedDomain ν c Ω) := by
  rcases (foldedDomain ν c Ω).eq_empty_or_nonempty with hEmpty | hne
  · rw [hEmpty]
    exact isPreconnected_empty
  · exact (isPathConnected_foldedDomain ν c hΩ hconn hne).isConnected.isPreconnected

end FaberKrahnDevelopment.FoldedDomainConnected

end

end
