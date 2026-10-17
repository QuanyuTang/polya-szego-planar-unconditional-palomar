module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EuclideanReflection
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Algebra.Support

/-!
# An actual smooth cutoff with a strict disk-support margin

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.

The inner radius is R+ε/2, the outer radius R+ε, and the consumer is the open
disk of radius R+2ε. Thus the cutoff equals one near the whole closed ball R,
and its compact support lies strictly inside the consumer domain. A function
vanishing outside closedBall R is unchanged by the cutoff, and its value
times the cutoff derivative is zero everywhere. No weak derivative limit or
energy convergence is assumed.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace FaberKrahnDevelopment.EuclideanReflection

def spectralCutoff (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    ContDiffBump (0 : Plane) where
  rIn := R + ε / 2
  rOut := R + ε
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

lemma spectralCutoff_mem_Icc (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) (x : Plane) :
    spectralCutoff R ε hR hε x ∈ Icc (0 : ℝ) 1 :=
  ⟨(spectralCutoff R ε hR hε).nonneg, (spectralCutoff R ε hR hε).le_one⟩

lemma spectralCutoff_one_of_norm_le {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {x : Plane} (hx : ‖x‖ ≤ R) : spectralCutoff R ε hR hε x = 1 := by
  apply (spectralCutoff R ε hR hε).one_of_mem_closedBall
  change dist x (0 : Plane) ≤ R + ε / 2
  rw [dist_zero_right]
  linarith

lemma fderiv_spectralCutoff_eq_zero {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {x : Plane} (hx : ‖x‖ ≤ R) :
    fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x = 0 := by
  have hmem : x ∈ Metric.ball (0 : Plane) (spectralCutoff R ε hR hε).rIn := by
    change dist x (0 : Plane) < R + ε / 2
    rw [dist_zero_right]
    linarith
  have hlocal : (spectralCutoff R ε hR hε : Plane → ℝ) =ᶠ[𝓝 x]
      (fun _ => (1 : ℝ)) :=
    (spectralCutoff R ε hR hε).eventuallyEq_one_of_mem_ball hmem
  rw [hlocal.fderiv_eq]
  simp

lemma tsupport_spectralCutoff_subset (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    tsupport (spectralCutoff R ε hR hε : Plane → ℝ) ⊆
      Metric.ball (0 : Plane) (R + 2 * ε) := by
  rw [(spectralCutoff R ε hR hε).tsupport_eq]
  exact Metric.closedBall_subset_ball (by change R + ε < R + 2 * ε; linarith)

lemma tsupport_spectralCutoff_mul_subset (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (u : Plane → ℝ) :
    tsupport (fun x => spectralCutoff R ε hR hε x * u x) ⊆
      Metric.ball (0 : Plane) (R + 2 * ε) :=
  tsupport_mul_subset_left.trans (tsupport_spectralCutoff_subset R ε hR hε)

lemma hasCompactSupport_spectralCutoff_mul (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (u : Plane → ℝ) :
    HasCompactSupport (fun x => spectralCutoff R ε hR hε x * u x) :=
  (spectralCutoff R ε hR hε).hasCompactSupport.of_isClosed_subset
    (isClosed_tsupport _) tsupport_mul_subset_left

lemma spectralCutoff_mul_eq_self {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    {v : Plane → ℝ} (hv : ∀ x, R < ‖x‖ → v x = 0) (x : Plane) :
    spectralCutoff R ε hR hε x * v x = v x := by
  by_cases hx : ‖x‖ ≤ R
  · rw [spectralCutoff_one_of_norm_le hR hε hx, one_mul]
  · rw [hv x (not_le.mp hx), mul_zero]

lemma value_smul_fderiv_spectralCutoff_eq_zero {R ε : ℝ}
    (hR : 0 ≤ R) (hε : 0 < ε) {v : Plane → ℝ}
    (hv : ∀ x, R < ‖x‖ → v x = 0) (x : Plane) :
    v x • fderiv ℝ (spectralCutoff R ε hR hε : Plane → ℝ) x = 0 := by
  by_cases hx : ‖x‖ ≤ R
  · rw [fderiv_spectralCutoff_eq_zero hR hε hx, smul_zero]
  · rw [hv x (not_le.mp hx), zero_smul]

end FaberKrahnDevelopment.EuclideanReflection

end

end
