module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FixedInitialFaberKrahn
public import DirichletTestDensity
public import Mathlib.Topology.ContinuousMap.CompactlySupported

/-!
# The inequality node for the original Dirichlet eigenvalue

SOURCE_DRAFT (2026-10-17), uncompiled and isolated from production.
The literal absolute value of a smooth test function is packaged as a
bounded continuous function. Its Lipschitz bound, compact support, actual
mass and derivative-energy identities are produced from the test function.
The fixed-initial-function inequality then applies with only the natural
domain-area bound. The density bridge uses the project's original H01,
energy and dirichletEig definitions.

This file proves no equality characterization. In particular its proposed
inequality root cannot construct the full original ExtFaberKrahn structure.
All dependencies and these proofs still require native compilation and
axiom inspection; source text alone is not verification evidence.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory BoundedContinuousFunction
open scoped NNReal CompactlySupported

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- The signed original smooth test function has the sharp disk bound.
Its absolute value is an actual function, with unchanged mass and energy. -/
lemma testFunction_faberKrahn {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : Buckling.IsTestFn Ω φ) {R : ℝ} (hR : 0 < R)
    (hArea : volume Ω ≤ volume (Metric.ball (0 : Plane) R)) :
    Buckling.jq ^ 2 / R ^ 2 * (∫ x, φ x ^ 2) ≤
      ∫ x, ‖fderiv ℝ φ x‖ ^ 2 := by
  obtain ⟨K, hK⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hφ.2.1 hφ.1 (by simp)
  let g : C_c(Plane, ℝ) :=
    { toFun := fun x => |φ x|
      continuous_toFun := hφ.1.continuous.abs
      hasCompactSupport' := hφ.2.1.comp_left (g := fun t : ℝ => |t|) (by simp) }
  let f : Plane →ᵇ ℝ := g.toBoundedContinuousFunction
  have hfL : LipschitzWith K f := lipschitzWith_absoluteValue hK
  have hfR : ∀ x, f x ∈ Icc 0 ‖f‖ := by
    intro x
    exact ⟨abs_nonneg (φ x), f.apply_le_norm x⟩
  obtain ⟨S, hS⟩ := hφ.2.1.isCompact.isBounded.subset_closedBall (0 : Plane)
  have hfZ : ∀ x, S < ‖x‖ → f x = 0 := by
    intro x hx
    have hxT : x ∉ tsupport φ := by
      intro hxT
      have hxS : ‖x‖ ≤ S := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hS hxT
      exact (not_le_of_gt hx) hxS
    change |φ x| = 0
    rw [image_eq_zero_of_notMem_tsupport hxT, abs_zero]
  have hfArea : volume {x | 0 < f x} ≤ volume (Metric.ball (0 : Plane) R) := by
    apply (measure_mono (show {x | 0 < f x} ⊆ Ω from ?_)).trans hArea
    intro x hx
    by_contra hxΩ
    have hx0 := hφ.eq_zero_of_notMem hxΩ
    have hxPos : 0 < |φ x| := hx
    rw [hx0, abs_zero] at hxPos
    exact (lt_irrefl (0 : ℝ)) hxPos
  have h := fixedInitial_faberKrahn hfL hfR hfZ hR hfArea
  change Buckling.jq ^ 2 / R ^ 2 * (∫ x, |φ x| ^ 2) ≤
    ∫ x, ‖fderiv ℝ (fun y => |φ y|) x‖ ^ 2 at h
  rw [integral_absoluteValue_sq volume φ,
    integral_norm_fderiv_absoluteValue_sq (μ := volume) hK] at h
  exact h

/-- The inequality half of E12 for the original graph-closure Dirichlet
eigenvalue. No additional theorem package, good limit or nonempty admissible
class is assumed; the density bridge produces the latter from the domain. -/
theorem dirichlet_faberKrahn_inequality {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) {R : ℝ} (hR : 0 < R)
    (hArea : volume Ω ≤ volume (Metric.ball (0 : Plane) R)) :
    Buckling.dirichletEig (Metric.ball (0 : Plane) R) ≤
      Buckling.dirichletEig Ω := by
  rw [Buckling.dirichletEig_ball (0 : Plane) R hR]
  apply Buckling.le_dirichletEig_of_test hΩ hne
  intro φ hMass
  have hMassNonneg : 0 ≤ ∫ x, φ.1 x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hMassPos : 0 < ∫ x, φ.1 x ^ 2 :=
    lt_of_le_of_ne hMassNonneg (Ne.symm hMass)
  exact (le_div_iff₀ hMassPos).2 (testFunction_faberKrahn φ.2 hR hArea)

end FaberKrahnDevelopment

end

end
