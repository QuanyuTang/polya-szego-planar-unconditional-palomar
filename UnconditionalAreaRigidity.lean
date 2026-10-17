module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import UnconditionalFaberKrahn
public import RequestProject.Core4

/-!
# Source assembly of the full original area corollary and planar conjecture

SOURCE_DRAFT: NOT COMPILED, NOT REGISTERED, NOT SUBMISSION READY.
The actual original Core4 equality theorem upgrades AE FK disk rigidity
to equality with the exact open disk by its original H02 strict-inclusion
argument. The supplied E12 package has no external theorem argument.
These source wrappers do not certify compilation or the complete goal.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace Buckling

theorem area_inequality_unconditional {Ω : Set Plane} (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    π * jk ^ 2 ≤ (volume Ω).toReal * bucklingEig Ω :=
  area_inequality paperExternals_holds_without_E12 Ω hΩ h0 hfin

theorem area_equality_iff_without_E12 {Ω : Set Plane} (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    (volume Ω).toReal * bucklingEig Ω = π * jk ^ 2 ↔
      ∃ (a : Plane) (R : ℝ), 0 < R ∧ Ω = Metric.ball a R :=
  area_equality_iff paperExternals_holds_without_E12 Ω hΩ h0 hfin

theorem polya_szego_buckling_without_E12 {Ω : Set Plane} (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) (R : ℝ) (hR : 0 < R)
    (hVolume : π * R ^ 2 = (volume Ω).toReal) :
    bucklingEig (Metric.ball (0 : Plane) R) ≤ bucklingEig Ω ∧
      (bucklingEig Ω = bucklingEig (Metric.ball (0 : Plane) R) ↔
        ∃ a : Plane, Ω = Metric.ball a R) :=
  polya_szego_buckling paperExternals_holds_without_E12 Ω hΩ h0 hfin R hR hVolume

end Buckling
end
end
