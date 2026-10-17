module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import FaberKrahnEqualityAeDisk
public import DirichletFKAreaProduct

/-!
# Assembly of the original E12 proposition without external hypotheses

SOURCE_DRAFT: NOT COMPILED, NOT REGISTERED, NOT SUBMISSION READY.
This source supplies the original ExtFaberKrahn proposition, including its
prescribed-radius equality conclusion, using the genuine inequality and
the actual weak-H01/polarization/measure rigidity chain. No hFK or hE is a
theorem argument here. This is an unverified source assembly, not evidence
that the new chain or its Lean 4.35 ports have successfully compiled.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace Buckling

theorem faberKrahn_holds_without_E12 : ExtFaberKrahn := by
  intro Ω hΩ h0 hfin R hR hVolume
  have hne : Ω.Nonempty := Set.nonempty_iff_ne_empty.mpr (by rintro rfl; simp at h0)
  refine ⟨FaberKrahnDevelopment.dirichlet_faberKrahn_inequality
    hΩ hne hR hVolume.ge, ?_⟩
  intro hEquality
  have hArea : (volume Ω).toReal = R ^ 2 * π := by
    rw [← hVolume, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hR.le,
      ENNReal.toReal_ofReal pi_pos.le]
  have hProduct : (volume Ω).toReal * dirichletEig Ω =
      DirichletFKAreaProduct.sharpConstant := by
    rw [hEquality, dirichletEig_ball' (0 : Plane) R hR, hArea]
    unfold DirichletFKAreaProduct.sharpConstant
    field_simp [hR.ne']
    <;> ring
  exact FaberKrahnEqualityAeDisk.exists_prescribed_ae_disk_of_area_product_equality
    DirichletFKAreaProduct.sharpConstant_pos DirichletFKAreaProduct.global_lower_bound
    hΩ hne hfin hProduct hR hVolume

/-- The original package is now supplied by the preceding proof source,
rather than accepted as a theorem input. Native checking is still pending. -/
theorem paperExternals_holds_without_E12 : PaperExternals :=
  ⟨faberKrahn_holds_without_E12⟩

end Buckling
end
end
