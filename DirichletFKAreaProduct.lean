module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import TestFunctionFaberKrahn
public import RequestProject.Core2
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# The actual original Dirichlet FK area product, with no FK premise

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The original inequality producer dirichlet_faberKrahn_inequality was
actually checked under Lean 4.28. Its current 4.35 port and this new file
still require native compilation: no 4.28 result is a 4.35 verification.

The constant is pi * jq^2 (the Dirichlet constant), not pi * jk^2 (the
buckling constant). Positivity uses the actual proved Bessel-zero package.
The disk formula is the original Core2 dirichletEig_ball' theorem, with
the unchanged original dirichletEig. The elementary prescribed-area disk
construction is repeated in a fresh namespace, without importing
MainResults just for that construction. The existing inequality producer
currently has a transitive MainResults/Core4 dependency, recorded in NOTES.

No global FK lower bound, equality-rigidity statement, external E12
package, positivity of an eigenvalue, or boundedness of Omega is an input.
-/

@[expose] public section

noncomputable section

open MeasureTheory Real Set
open scoped ENNReal

namespace Buckling.DirichletFKAreaProduct

/-- The sharp Dirichlet area constant. It deliberately uses jq, not jk. -/
def sharpConstant : ℝ := π * jq ^ 2

theorem sharpConstant_pos : 0 < sharpConstant := by
  have hq : 0 < jq := (parameter_signs extZeros_holds).1
  exact mul_pos pi_pos (sq_pos_of_pos hq)

/-- Pure planar-area algebra, independent of any spectral or equality
hypothesis. No regularity of the measured set is required. -/
lemma exists_disk_of_area (Ω : Set Plane) (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    ∃ R : ℝ, 0 < R ∧ volume (Metric.ball (0 : Plane) R) = volume Ω ∧
      π * R ^ 2 = (volume Ω).toReal := by
  have hA : 0 < (volume Ω).toReal := ENNReal.toReal_pos h0.ne' hfin.ne
  refine ⟨Real.sqrt ((volume Ω).toReal / π), Real.sqrt_pos.mpr (div_pos hA pi_pos),
    ?_, ?_⟩
  · rw [EuclideanSpace.volume_ball_fin_two,
      ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
      Real.sq_sqrt (div_pos hA pi_pos).le,
      ← ENNReal.ofReal_mul (by positivity),
      div_mul_cancel₀ _ pi_pos.ne', ENNReal.ofReal_toReal hfin.ne]
  · rw [Real.sq_sqrt (div_pos hA pi_pos).le]
    field_simp

/-- The original Dirichlet eigenvalue satisfies the sharp area-product
inequality with only the natural finite-positive-area open-set inputs. -/
theorem dirichlet_area_product {Ω : Set Plane} (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    π * jq ^ 2 ≤ (volume Ω).toReal * dirichletEig Ω := by
  have hne : Ω.Nonempty := Set.nonempty_iff_ne_empty.mpr (by rintro rfl; simp at h0)
  obtain ⟨R, hR, hvol, hArea⟩ := exists_disk_of_area Ω h0 hfin
  have hFK := FaberKrahnDevelopment.dirichlet_faberKrahn_inequality
    hΩ hne hR hvol.ge
  rw [dirichletEig_ball' (0 : Plane) R hR] at hFK
  calc
    π * jq ^ 2 = (volume Ω).toReal * (jq ^ 2 / R ^ 2) := by
      rw [← hArea]
      field_simp [hR.ne']
      <;> ring
    _ ≤ (volume Ω).toReal * dirichletEig Ω :=
      mul_le_mul_of_nonneg_left hFK ENNReal.toReal_nonneg

/-- The exact curried interface expected by the equality/ground-state
consumers. This is an actual producer, with no hFK argument. -/
theorem global_lower_bound :
    ∀ Ω : Set Plane, IsOpen Ω → 0 < volume Ω → volume Ω < ⊤ →
      sharpConstant ≤ (volume Ω).toReal * dirichletEig Ω := by
  intro Ω hΩ h0 hfin
  exact dirichlet_area_product hΩ h0 hfin

end Buckling.DirichletFKAreaProduct

end

end
