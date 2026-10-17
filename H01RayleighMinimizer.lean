module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01CompactEmbedding
public import H01NonzeroMass
public import EllipticPdes.Analysis.DirectMethodForm
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Attainment of the original Dirichlet infimum on finite-area open domains

SOURCE_DRAFT, Lean 4.35.0-rc3 only; NOT compiled or registered.
The direct-method theorem is applied to the actual Hilbert H01 submodule,
its full inner product, and the actual compact full-space value map. A real
bump supplies a unit-mass competitor. Every original nonzero-mass H01 class
is actually rescaled to unit value norm. The Hilbert norm identity then
converts full-norm minimization into the original energy1/energy0 quotient.
Both bounds for the original ciInf are proved explicitly.

No compactness, minimizing sequence, nonzero test, minimizer, Euler equation,
positivity or equality rigidity is assumed as an extra hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace Buckling
namespace H01Rayleigh

/-- Return to precisely the original product of the three restricted L2
components, without changing either original energy definition. -/
def raw (Ω : Set Plane) (W : h01HilbertSubmodule Ω) :
    L2 Ω × (Fin 2 → L2 Ω) :=
  (h1DataToHilbert Ω).symm W.1

lemma raw_mem_H01 (Ω : Set Plane) (W : h01HilbertSubmodule Ω) :
    raw Ω W ∈ H01 Ω := by
  apply (h1DataToHilbert_mem_iff Ω (raw Ω W)).mp
  simpa [raw] using W.2

lemma energy0_raw_eq {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (W : h01HilbertSubmodule Ω) :
    energy0 (raw Ω W) = ‖h01HilbertGlobalValue Ω hΩm W‖ ^ 2 := by
  have hn : ‖h01HilbertGlobalValue Ω hΩm W‖ = ‖(raw Ω W).1‖ :=
    (lpExtendByZero volume 2 Ω hΩm).norm_map (raw Ω W).1
  rw [energy0, hn]

lemma norm_sq_eq_energies (Ω : Set Plane) (W : h01HilbertSubmodule Ω) :
    ‖W‖ ^ 2 = energy0 (raw Ω W) + energy1 (raw Ω W) := by
  simpa [raw] using (norm_h1DataToHilbert_sq Ω (raw Ω W))

/-- Actual scalar rescaling in the actual Hilbert submodule. -/
def normalize (Ω : Set Plane) (hΩm : MeasurableSet Ω)
    (W : h01HilbertSubmodule Ω) : h01HilbertSubmodule Ω :=
  ‖h01HilbertGlobalValue Ω hΩm W‖⁻¹ • W

lemma normalize_value_norm {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (W : h01HilbertSubmodule Ω)
    (hW : ‖h01HilbertGlobalValue Ω hΩm W‖ ≠ 0) :
    ‖h01HilbertGlobalValue Ω hΩm (normalize Ω hΩm W)‖ = 1 := by
  rw [normalize, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀ hW]

/-- The full normalized norm is the original shifted Rayleigh quotient.
This algebraic identity even holds at zero mass with real inverse-zero
conventions; admissibility below separately produces nonzero mass. -/
lemma normalize_norm_sq {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (W : h01HilbertSubmodule Ω) :
    ‖normalize Ω hΩm W‖ ^ 2 =
      (energy0 (raw Ω W) + energy1 (raw Ω W)) / energy0 (raw Ω W) := by
  rw [normalize, norm_smul, mul_pow]
  have hs : ‖‖h01HilbertGlobalValue Ω hΩm W‖⁻¹‖ ^ 2 =
      (energy0 (raw Ω W))⁻¹ := by
    rw [Real.norm_eq_abs, sq_abs, inv_pow, ← energy0_raw_eq hΩm W]
  rw [hs, norm_sq_eq_energies]
  rw [div_eq_mul_inv]
  ring

/-- A bounded-below proof for the original energy quotient. This reproduces
the short original ciInf estimate under a fresh name, without Core2. -/
lemma original_dirichletEig_le {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) (h0 : energy0 v ≠ 0) :
    dirichletEig Ω ≤ energy1 v / energy0 v := by
  refine ciInf_le ⟨0, ?_⟩
    (⟨v, hv, h0⟩ : {v // v ∈ H01 Ω ∧ energy0 v ≠ 0})
  rintro _ ⟨w, rfl⟩
  exact div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (sq_nonneg _)

/-- The actual inner product of the completed original H01 Hilbert model. -/
def fullForm (Ω : Set Plane) :
    h01HilbertSubmodule Ω →L[ℝ] h01HilbertSubmodule Ω →L[ℝ] ℝ :=
  innerSL ℝ

lemma fullForm_self (Ω : Set Plane) (W : h01HilbertSubmodule Ω) :
    fullForm Ω W W = ‖W‖ ^ 2 := by
  change inner ℝ W W = ‖W‖ ^ 2
  exact real_inner_self_eq_norm_sq W

lemma fullForm_coercive (Ω : Set Plane) : IsCoercive (fullForm Ω) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro W
  simpa only [fullForm_self, one_mul, pow_two] using
    (le_rfl : ‖W‖ * ‖W‖ ≤ ‖W‖ * ‖W‖)

lemma fullForm_symm (Ω : Set Plane) :
    ∀ U V : h01HilbertSubmodule Ω, fullForm Ω U V = fullForm Ω V U := by
  intro U V
  change inner ℝ U V = inner ℝ V U
  exact real_inner_comm V U

/-- Any actual minimizer of the full norm at unit value norm is below the
original quotient of every original H01 class with nonzero mass. -/
lemma energy1_le_original_quotient {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (U : h01HilbertSubmodule Ω)
    (hU : ‖h01HilbertGlobalValue Ω hΩm U‖ = 1)
    (hmin : ∀ W : h01HilbertSubmodule Ω,
      ‖h01HilbertGlobalValue Ω hΩm W‖ = 1 → fullForm Ω U U ≤ fullForm Ω W W)
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) (h0 : energy0 v ≠ 0) :
    energy1 (raw Ω U) ≤ energy1 v / energy0 v := by
  let W : h01HilbertSubmodule Ω :=
    ⟨h1DataToHilbert Ω v, (h1DataToHilbert_mem_iff Ω v).mpr hv⟩
  have hraw : raw Ω W = v := by
    change (h1DataToHilbert Ω).symm (h1DataToHilbert Ω v) = v
    exact (h1DataToHilbert Ω).symm_apply_apply v
  have hm : energy0 v = ‖h01HilbertGlobalValue Ω hΩm W‖ ^ 2 := by
    simpa only [hraw] using (energy0_raw_eq hΩm W)
  have hn : ‖h01HilbertGlobalValue Ω hΩm W‖ ≠ 0 := by
    intro hz
    apply h0
    simpa only [hz, zero_pow (by decide : 2 ≠ 0)] using hm
  have hnormalized := normalize_value_norm hΩm W hn
  have hcompare := hmin (normalize Ω hΩm W) hnormalized
  have hnorm_compare : ‖U‖ ^ 2 ≤ ‖normalize Ω hΩm W‖ ^ 2 := by
    simpa only [fullForm_self] using hcompare
  rw [norm_sq_eq_energies Ω U, normalize_norm_sq hΩm W] at hnorm_compare
  have henergy_compare : energy0 (raw Ω U) + energy1 (raw Ω U) ≤
      (energy0 v + energy1 v) / energy0 v := by
    simpa only [hraw] using hnorm_compare
  have hu0 : energy0 (raw Ω U) = 1 := by
    simpa only [hU, one_pow] using (energy0_raw_eq hΩm U)
  have hquot : (energy0 v + energy1 v) / energy0 v =
      1 + energy1 v / energy0 v := by
    rw [add_div, div_self h0]
  rw [hu0, hquot] at henergy_compare
  linarith

end H01Rayleigh

/-- The original Dirichlet ciInf is attained by an original H01 class of
mass one on every nonempty open finite-area domain, without boundedness. -/
theorem exists_H01_dirichletEig_minimizer {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤) :
    ∃ v : L2 Ω × (Fin 2 → L2 Ω),
      v ∈ H01 Ω ∧ energy0 v = 1 ∧ energy1 v = dirichletEig Ω := by
  obtain ⟨U, hU, hmin⟩ := EllipticPdes.Analysis.exists_bilin_minimiser
    (B := H01Rayleigh.fullForm Ω) (H01Rayleigh.fullForm_coercive Ω)
    (H01Rayleigh.fullForm_symm Ω) (h01HilbertGlobalValue Ω hΩ.measurableSet)
    (h01HilbertGlobalValue_isCompact hΩ.measurableSet hfin)
    (exists_h01HilbertGlobalValue_norm_eq_one hΩ hne)
  have hu : H01Rayleigh.raw Ω U ∈ H01 Ω := H01Rayleigh.raw_mem_H01 Ω U
  have hu0 : energy0 (H01Rayleigh.raw Ω U) = 1 := by
    simpa only [hU, one_pow] using (H01Rayleigh.energy0_raw_eq hΩ.measurableSet U)
  have hu_ne : energy0 (H01Rayleigh.raw Ω U) ≠ 0 := by
    rw [hu0]
    norm_num
  letI : Nonempty {v // v ∈ H01 Ω ∧ energy0 v ≠ 0} :=
    ⟨⟨H01Rayleigh.raw Ω U, hu, hu_ne⟩⟩
  have h_lower : energy1 (H01Rayleigh.raw Ω U) ≤ dirichletEig Ω := by
    unfold dirichletEig
    apply le_ciInf
    intro v
    exact H01Rayleigh.energy1_le_original_quotient hΩ.measurableSet U hU hmin
      v.1 v.2.1 v.2.2
  have h_upper : dirichletEig Ω ≤ energy1 (H01Rayleigh.raw Ω U) := by
    simpa only [hu0, div_one] using
      (H01Rayleigh.original_dirichletEig_le (H01Rayleigh.raw Ω U) hu hu_ne)
  exact ⟨H01Rayleigh.raw Ω U, hu, hu0, le_antisymm h_lower h_upper⟩

end Buckling

end

end
