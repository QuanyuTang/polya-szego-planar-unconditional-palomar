module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import H01FullEuler
public import WeakSMPConnected
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Strict positivity and actual L1 of an original connected-domain ground state

SOURCE_DRAFT: not compiled or registered. Interior supersolution testing is
produced from the actual original Euler identity. The actual weak SMP
then excludes the zero branch using the unchanged original mass one.
Finite area produces genuine L1 of the actual full zero extension, without
requiring a bounded domain or a moment condition.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace Buckling.H01GroundStatePositive

open H01WeakGradientBridge

lemma fullComponent_off {Ω : Set Plane} (hΩm : MeasurableSet Ω) (f : L2 Ω) :
    ∀ᵐ x ∂volume, x ∉ Ω → fullComponent hΩm f x = 0 := by
  filter_upwards [coeFn_fullComponent hΩm f] with x hx hxΩ
  rw [hx, zeroExtend_eq_zero_of_notMem f hxΩ]

lemma fullComponent_integrable {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (hfin : volume Ω < ⊤) (f : L2 Ω) : Integrable (fullComponent hΩm f) volume := by
  letI : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hf : IntegrableOn (fun x => f x) Ω volume :=
    MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2) (Lp.memLp f)
  apply (hf.integrable_indicator hΩm).congr
  exact (coeFn_fullComponent hΩm f).symm

lemma original_value_ae_zero_of_full_restricted_zero {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (f : L2 Ω)
    (hz : (fullComponent hΩm f : Plane → ℝ) =ᵐ[volume.restrict Ω] 0) :
    (f : Plane → ℝ) =ᵐ[volume.restrict Ω] 0 := by
  filter_upwards [ae_restrict_of_ae (coeFn_fullComponent hΩm f), hz,
    ae_restrict_mem hΩm] with x hx hzx hxΩ
  rw [hx, zeroExtend, Set.indicator_of_mem hxΩ] at hzx
  exact hzx

lemma full_value_not_ae_zero_of_mass_one {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (u : L2 Ω × (Fin 2 → L2 Ω)) (hMass : energy0 u = 1) :
    ¬ (fullComponent hΩm u.1 : Plane → ℝ) =ᵐ[volume] 0 := by
  intro hz
  have hzOrig := original_value_ae_zero_of_full_restricted_zero hΩm u.1
    (ae_restrict_of_ae hz)
  have hL2 : u.1 = 0 := Lp.ext (hzOrig.trans (Lp.coeFn_zero ℝ 2 (volume.restrict Ω)).symm)
  have hZero : energy0 u = 0 := by
    simp only [energy0, hL2, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact zero_ne_one (hZero.symm.trans hMass)

lemma integral_full_value_pos {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (hfin : volume Ω < ⊤) (u : L2 Ω × (Fin 2 → L2 Ω))
    (hMass : energy0 u = 1)
    (hN : ∀ᵐ x ∂volume, 0 ≤ fullComponent hΩm u.1 x) :
    0 < ∫ x, fullComponent hΩm u.1 x := by
  have hI := fullComponent_integrable hΩm hfin u.1
  have hNE : (∫ x, fullComponent hΩm u.1 x) ≠ 0 := by
    intro hz
    exact full_value_not_ae_zero_of_mass_one hΩm u hMass
      ((integral_eq_zero_iff_of_nonneg_ae hN hI).mp hz)
  exact lt_of_le_of_ne (integral_nonneg_of_ae hN) (Ne.symm hNE)

theorem full_groundState_pos_ae {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {u : L2 Ω × (Fin 2 → L2 Ω)}
    (hu : u ∈ H01 Ω) (hMass : energy0 u = 1)
    (hEnergy : energy1 u = dirichletEig Ω * energy0 u)
    (hN : ∀ᵐ x ∂volume, 0 ≤ fullComponent hΩ.measurableSet u.1 x)
    (heigenvalue : 0 ≤ dirichletEig Ω) :
    ∀ᵐ x ∂volume.restrict Ω, 0 < fullComponent hΩ.measurableSet u.1 x := by
  have hSuper : ∀ ψ : Plane → ℝ, IsTestFn Ω ψ → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∑ i, ∫ x, fullComponent hΩ.measurableSet (u.2 i) x * pderiv i ψ x := by
    intro ψ hψ hψN
    rw [H01FullEuler.full_euler_of_energy_eq hΩ.measurableSet hu hEnergy hψ]
    apply mul_nonneg heigenvalue
    apply integral_nonneg_of_ae
    exact hN.mono fun x hx => mul_nonneg hx (hψN x)
  rcases WeakSMPConnected.zero_or_pos_ae hΩ hconn (Lp.memLp _)
      (fun i => Lp.memLp (fullComponent hΩ.measurableSet (u.2 i)))
      (H01_fullLp_hasWeakGradOn hΩ.measurableSet hu)
      (ae_restrict_of_ae hN) hSuper with hz | hp
  · have hzOrig := original_value_ae_zero_of_full_restricted_zero hΩ.measurableSet u.1 hz
    have hL2 : u.1 = 0 := Lp.ext (hzOrig.trans (Lp.coeFn_zero ℝ 2 (volume.restrict Ω)).symm)
    have hZero : energy0 u = 0 := by simp only [energy0, hL2, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact (zero_ne_one (hZero.symm.trans hMass)).elim
  · exact hp

theorem positive_set_ae_eq_domain {Ω : Set Plane} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) {u : L2 Ω × (Fin 2 → L2 Ω)}
    (hu : u ∈ H01 Ω) (hMass : energy0 u = 1)
    (hEnergy : energy1 u = dirichletEig Ω * energy0 u)
    (hN : ∀ᵐ x ∂volume, 0 ≤ fullComponent hΩ.measurableSet u.1 x)
    (heigenvalue : 0 ≤ dirichletEig Ω) :
    {x | 0 < fullComponent hΩ.measurableSet u.1 x} =ᵐ[volume] Ω := by
  have hp := (ae_restrict_iff' hΩ.measurableSet).mp
    (full_groundState_pos_ae hΩ hconn hu hMass hEnergy hN heigenvalue)
  filter_upwards [hp, fullComponent_off hΩ.measurableSet u.1] with x hpx hox
  apply propext
  change (0 < fullComponent hΩ.measurableSet u.1 x) ↔ x ∈ Ω
  constructor
  · intro hx
    by_contra hxΩ
    rw [hox hxΩ] at hx
    exact lt_irrefl (0 : ℝ) hx
  · exact hpx

end Buckling.H01GroundStatePositive
end
end
