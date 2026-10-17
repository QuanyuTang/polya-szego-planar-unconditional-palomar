module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FaberKrahnEqualityGroundStateData
public import ReflectionBranchPositiveBall
public import PlanarBallRadius

/-!
# Actual AE disk rigidity at equality in the original FK product bound

SOURCE_DRAFT: not compiled or registered. The genuine FK inequality is
still an explicit intermediate input. All groundstate, weak PDE, SMP,
reflection branch, maximizing center and good-point radial order data
are produced by the preceding sources. The final consumer also matches
the prescribed equal-area radius in the original E12 equality interface.
This source is not an assertion of successful native or external replay.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal symmDiff

namespace Buckling.FaberKrahnEqualityAeDisk

theorem exists_ae_disk_of_area_product_equality {k : ℝ} (hk : 0 < k)
    (hFK : ∀ A : Set Plane, IsOpen A → 0 < volume A → volume A < ⊤ →
      k ≤ (volume A).toReal * dirichletEig A)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k) :
    ∃ (a : Plane) (R : ℝ), 0 < R ∧ Ω =ᵐ[volume] ball a R := by
  obtain ⟨U, _hU2, hI, hN, hIP, hPosSet, _hOff, hBranches⟩ :=
    FaberKrahnEqualityGroundStateData.exists_density_with_global_branches
      hk hFK hΩ hne hfin heq
  have hPosFin : volume {x | 0 < U x} < ⊤ := by
    rw [measure_congr hPosSet]
    exact hfin
  obtain ⟨a, R, hR, hBall⟩ :=
    ReflectionBranchPositiveBall.exists_pos_ball_ae_eq_of_nonneg_branches
      hI hN hIP hPosFin hBranches
  exact ⟨a, R, hR, hPosSet.symm.trans hBall⟩

theorem exists_prescribed_ae_disk_of_area_product_equality {k : ℝ} (hk : 0 < k)
    (hFK : ∀ A : Set Plane, IsOpen A → 0 < volume A → volume A < ⊤ →
      k ≤ (volume A).toReal * dirichletEig A)
    {Ω : Set Plane} (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤)
    (heq : (volume Ω).toReal * dirichletEig Ω = k)
    {R : ℝ} (hR : 0 < R) (hVolume : volume (ball (0 : Plane) R) = volume Ω) :
    ∃ a : Plane, volume (Ω ∆ ball a R) = 0 := by
  obtain ⟨a, s, hs, hAE⟩ :=
    exists_ae_disk_of_area_product_equality hk hFK hΩ hne hfin heq
  exact ⟨a, PlanarBallRadius.symmDiff_prescribed_ball_eq_zero a hs.le hR.le hAE hVolume⟩

end Buckling.FaberKrahnEqualityAeDisk
end
end
