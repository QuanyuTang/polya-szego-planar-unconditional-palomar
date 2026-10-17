module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EllipticH01Bridge
public import FiniteAreaTestLpBounds
public import EllipticPdes.Analysis.LpExtendByZero
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Uniform L2 tails of the original finite-area H01 unit ball

SOURCE_DRAFT, Lean 4.35-rc3 only; NOT compiled.
The EllipticPDE dependency is pinned to
ec784093f30308ef770ff855ce624725adf6f870, lean/ subdirectory.

The tail estimate is extended through the original strong graph closure.
No H01-to-L4 embedding, compact inclusion, minimizer, or Rellich conclusion
is assumed or asserted. The endpoint supplies only the real integral tail
hypothesis of the generic finite-grid criterion.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace Buckling

/-- Restrict the original value coordinate to the complement of a ball.
The target retains the nested restriction, avoiding transport of Lp types. -/
def h01TailRestriction (Ω : Set Plane) (R : ℝ) :
    (L2 Ω × (Fin 2 → L2 Ω)) →L[ℝ]
      Lp ℝ 2 ((volume.restrict Ω).restrict (closedBall (0 : Plane) R)ᶜ) :=
  (LpToLpRestrictCLM Plane ℝ ℝ (volume.restrict Ω) 2
    (closedBall (0 : Plane) R)ᶜ).comp
      (ContinuousLinearMap.fst ℝ (L2 Ω) (Fin 2 → L2 Ω))

/-- The actual whole-space zero extension of the original value coordinate. -/
def h01GlobalValue (Ω : Set Plane) (hΩm : MeasurableSet Ω) :
    (L2 Ω × (Fin 2 → L2 Ω)) →L[ℝ] Lp ℝ 2 (volume : Measure Plane) :=
  (lpExtendByZero volume 2 Ω hΩm).toContinuousLinearMap.comp
    (ContinuousLinearMap.fst ℝ (L2 Ω) (Fin 2 → L2 Ω))

/-- A real coefficient; its square is left uncombined to avoid additional
fractional-power identities at zero tail measure. -/
def h01TailCoefficient (Ω : Set Plane) (c R : ℝ) : ℝ :=
  c * (volume (Ω \ closedBall (0 : Plane) R)).toReal ^ (1 / 4 : ℝ)

lemma norm_h01TailRestriction_graphH1 {Ω : Set Plane} (R : ℝ)
    (φ : {φ // IsTestFn Ω φ}) :
    ‖h01TailRestriction Ω R (graphH1 φ)‖ =
      (eLpNorm φ.1 2 (volume.restrict (Ω \ closedBall (0 : Plane) R))).toReal := by
  have hrep : (h01TailRestriction Ω R (graphH1 φ) : Plane → ℝ)
      =ᵐ[(volume.restrict Ω).restrict (closedBall (0 : Plane) R)ᶜ] φ.1 :=
    (LpToLpRestrictCLM_coeFn ℝ (closedBall (0 : Plane) R)ᶜ φ.2.toL2).trans
      (ae_restrict_of_ae φ.2.memLp.coeFn_toLp)
  have hset : (closedBall (0 : Plane) R)ᶜ ∩ Ω = Ω \ closedBall (0 : Plane) R := by
    ext x
    change (x ∉ closedBall (0 : Plane) R ∧ x ∈ Ω) ↔
      (x ∈ Ω ∧ x ∉ closedBall (0 : Plane) R)
    exact and_comm
  rw [Lp.norm_def, eLpNorm_congr_ae hrep,
    Measure.restrict_restrict isClosed_closedBall.measurableSet.compl, hset]

/-- The real square-integral tail of the actual full-space function equals
the squared norm of the original restricted tail coordinate. -/
lemma integral_sq_h01GlobalValue_tail_eq {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (R : ℝ) (v : L2 Ω × (Fin 2 → L2 Ω)) :
    (∫ x in (closedBall (0 : Plane) R)ᶜ, (h01GlobalValue Ω hΩm v x) ^ 2) =
      ‖h01TailRestriction Ω R v‖ ^ 2 := by
  have hJ : (h01GlobalValue Ω hΩm v : Plane → ℝ)
      =ᵐ[volume] Ω.indicator (v.1 : Plane → ℝ) :=
    coeFn_lpExtendByZero hΩm v.1
  have hQ : (h01TailRestriction Ω R v : Plane → ℝ)
      =ᵐ[(volume.restrict Ω).restrict (closedBall (0 : Plane) R)ᶜ] v.1 :=
    LpToLpRestrictCLM_coeFn ℝ (closedBall (0 : Plane) R)ᶜ v.1
  have hleft :
      (∫ x in (closedBall (0 : Plane) R)ᶜ, (h01GlobalValue Ω hΩm v x) ^ 2) =
        ∫ x in Ω ∩ (closedBall (0 : Plane) R)ᶜ, (v.1 x) ^ 2 := by
    calc
      (∫ x in (closedBall (0 : Plane) R)ᶜ, (h01GlobalValue Ω hΩm v x) ^ 2) =
          ∫ x in (closedBall (0 : Plane) R)ᶜ,
            Ω.indicator (fun y => (v.1 y) ^ 2) x := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hJ] with x hx
        rw [hx]
        by_cases hxΩ : x ∈ Ω
        · rw [Set.indicator_of_mem hxΩ, Set.indicator_of_mem hxΩ]
        · rw [Set.indicator_of_notMem hxΩ, Set.indicator_of_notMem hxΩ,
            zero_pow (by decide : (2 : ℕ) ≠ 0)]
      _ = _ := by rw [integral_indicator hΩm, Measure.restrict_restrict hΩm]
  have hright : ‖h01TailRestriction Ω R v‖ ^ 2 =
      ∫ x in (closedBall (0 : Plane) R)ᶜ ∩ Ω, (v.1 x) ^ 2 := by
    rw [MeasureTheory.L2.norm_sq_eq_integral_sq]
    calc
      (∫ x, (h01TailRestriction Ω R v x) ^ 2
          ∂((volume.restrict Ω).restrict (closedBall (0 : Plane) R)ᶜ)) =
          ∫ x, (v.1 x) ^ 2
            ∂((volume.restrict Ω).restrict (closedBall (0 : Plane) R)ᶜ) := by
        apply integral_congr_ae
        filter_upwards [hQ] with x hx
        rw [hx]
      _ = _ := by rw [Measure.restrict_restrict isClosed_closedBall.measurableSet.compl]
  rw [hleft, hright, Set.inter_comm]

/-- The genuine test-function tail bound passes to the original H01 graph
closure. The same finite real constant works for all radii and all members. -/
theorem h01_tailRestriction_sq_bound {Ω : Set Plane} (hfin : volume Ω < ⊤) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R : ℝ) (v : L2 Ω × (Fin 2 → L2 Ω)), v ∈ H01 Ω →
      ‖h01TailRestriction Ω R v‖ ^ 2 ≤
        h01TailCoefficient Ω c R ^ 2 * energy1 v := by
  obtain ⟨C, hC, hTest⟩ := test_l4_and_tail_l2_bounds_finite_area hfin
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro R v hv
  have hclosed : IsClosed {w : L2 Ω × (Fin 2 → L2 Ω) |
      ‖h01TailRestriction Ω R w‖ ^ 2 ≤
        h01TailCoefficient Ω C.toReal R ^ 2 * energy1 w} := by
    have hE : Continuous (fun w : L2 Ω × (Fin 2 → L2 Ω) => energy1 w) := by
      unfold energy1
      fun_prop
    exact isClosed_le ((h01TailRestriction Ω R).continuous.norm.fun_pow 2)
      (hE.const_mul (h01TailCoefficient Ω C.toReal R ^ 2))
  apply (closure_minimal (s := Set.range (graphH1 (Ω := Ω))) ?_ hclosed) hv
  rintro _ ⟨φ, rfl⟩
  have hE0 : 0 ≤ energy1 (graphH1 φ) := by
    unfold energy1
    exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT : volume (Ω \ closedBall (0 : Plane) R) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.sdiff_subset) hfin
  have hRhsFin :
      (C * ENNReal.ofReal (energy1 (graphH1 φ) ^ (1 / 2 : ℝ))) *
        volume (Ω \ closedBall (0 : Plane) R) ^ (1 / 4 : ℝ) ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC ENNReal.ofReal_lt_top)
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hT.ne)).ne
  have hReal := ENNReal.toReal_mono hRhsFin
    ((hTest φ).2 (Ω \ closedBall (0 : Plane) R))
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg hE0 _),
    ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow] at hReal
  have hnorm : ‖h01TailRestriction Ω R (graphH1 φ)‖ ≤
      h01TailCoefficient Ω C.toReal R * Real.sqrt (energy1 (graphH1 φ)) := by
    rw [norm_h01TailRestriction_graphH1]
    exact hReal.trans_eq (by unfold h01TailCoefficient; ring)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  rw [mul_pow, Real.sq_sqrt hE0] at hsq
  exact hsq

/-- A full-volume real integral statement for the actual original value,
with the original derivative energy and the true domain tail measure. -/
theorem h01_integral_sq_tail_bound {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (hfin : volume Ω < ⊤) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (R : ℝ) (v : L2 Ω × (Fin 2 → L2 Ω)), v ∈ H01 Ω →
      (∫ x in (closedBall (0 : Plane) R)ᶜ, (h01GlobalValue Ω hΩm v x) ^ 2) ≤
        h01TailCoefficient Ω c R ^ 2 * energy1 v := by
  obtain ⟨c, hc, hbound⟩ := h01_tailRestriction_sq_bound hfin
  refine ⟨c, hc, fun R v hv => ?_⟩
  rw [integral_sq_h01GlobalValue_tail_eq]
  exact hbound R v hv

/-- Finite area makes the common squared tail coefficient vanish along
integer radii, even if the domain itself is unbounded. -/
lemma h01TailCoefficient_sq_tendsto {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    (hfin : volume Ω < ⊤) (c : ℝ) :
    Tendsto (fun n : ℕ => h01TailCoefficient Ω c (n : ℝ) ^ 2) atTop (𝓝 0) := by
  let T : ℕ → Set Plane := fun n => Ω \ closedBall (0 : Plane) (n : ℝ)
  have hm : Antitone T := by
    intro n m hnm x hx
    refine ⟨hx.1, fun hxn => hx.2 ?_⟩
    exact closedBall_subset_closedBall (Nat.cast_le.mpr hnm) hxn
  have hmeas : ∀ n, NullMeasurableSet (T n) volume :=
    fun n => (hΩm.diff isClosed_closedBall.measurableSet).nullMeasurableSet
  have hfinite : ∃ n, volume (T n) ≠ ⊤ :=
    ⟨0, (lt_of_le_of_lt (measure_mono Set.sdiff_subset) hfin).ne⟩
  have hInter : (⋂ n : ℕ, T n) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
    have hxN := Set.mem_iInter.mp hx n
    apply hxN.2
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn.le
  have hMeasure : Tendsto (fun n => volume (T n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop hmeas hm hfinite
    simpa only [Function.comp_def, hInter, measure_empty] using h
  have hReal : Tendsto (fun n => (volume (T n)).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hMeasure
  have hQuarter : Tendsto (fun n => (volume (T n)).toReal ^ (1 / 4 : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    have h := ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 4)).tendsto 0).comp hReal
    simpa [Function.comp_def] using h
  simpa [h01TailCoefficient, T] using (hQuarter.const_mul c).pow 2

/-- The original Hilbert H01's actual full-space value map. -/
def h01HilbertGlobalValue (Ω : Set Plane) (hΩm : MeasurableSet Ω) :
    h01HilbertSubmodule Ω →L[ℝ] Lp ℝ 2 (volume : Measure Plane) :=
  (h01GlobalValue Ω hΩm).comp
    ((h1DataToHilbert Ω).symm.toContinuousLinearMap.comp
      (h01HilbertSubmodule Ω).subtypeL)

def h01HilbertUnitValueSet (Ω : Set Plane) (hΩm : MeasurableSet Ω) :
    Set (Lp ℝ 2 (volume : Measure Plane)) :=
  h01HilbertGlobalValue Ω hΩm '' closedBall (0 : h01HilbertSubmodule Ω) 1

/-- The exact real-square-integral uniform-tail input of the generic
finite-grid criterion, now produced for the actual original H01 unit ball. -/
theorem h01HilbertUnitValueSet_uniform_tails {Ω : Set Plane}
    (hΩm : MeasurableSet Ω) (hfin : volume Ω < ⊤) :
    ∀ ε > 0, ∃ R : ℝ, ∀ g ∈ h01HilbertUnitValueSet Ω hΩm,
      (∫ x in (closedBall (0 : Plane) R)ᶜ, (g x) ^ 2) < ε := by
  obtain ⟨c, _hc, hbound⟩ := h01_integral_sq_tail_bound hΩm hfin
  intro ε hε
  have hlim := h01TailCoefficient_sq_tendsto hΩm hfin c
  have hevent : ∀ᶠ n : ℕ in atTop, h01TailCoefficient Ω c (n : ℝ) ^ 2 < ε :=
    (tendsto_order.1 hlim).2 ε hε
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨(N : ℝ), ?_⟩
  rintro g ⟨u, hu, rfl⟩
  let v : L2 Ω × (Fin 2 → L2 Ω) := (h1DataToHilbert Ω).symm u.1
  have hv : v ∈ H01 Ω := (h1DataToHilbert_mem_iff Ω v).mp (by simpa [v] using u.2)
  have hnorm : ‖h1DataToHilbert Ω v‖ ≤ 1 := by
    simpa only [v, ContinuousLinearEquiv.apply_symm_apply, Submodule.norm_coe, Metric.mem_closedBall,
      dist_zero_right] using hu
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  simp only [one_pow] at hsq
  rw [norm_h1DataToHilbert_sq] at hsq
  have hE0 : 0 ≤ energy0 v := sq_nonneg ‖v.1‖
  have hE1 : energy1 v ≤ 1 := by linarith
  change (∫ x in (closedBall (0 : Plane) (N : ℝ))ᶜ,
    (h01GlobalValue Ω hΩm v x) ^ 2) < ε
  calc
    (∫ x in (closedBall (0 : Plane) (N : ℝ))ᶜ,
        (h01GlobalValue Ω hΩm v x) ^ 2) ≤
        h01TailCoefficient Ω c (N : ℝ) ^ 2 * energy1 v := hbound _ v hv
    _ ≤ h01TailCoefficient Ω c (N : ℝ) ^ 2 := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left hE1 (sq_nonneg (h01TailCoefficient Ω c (N : ℝ)))
    _ < ε := hN N le_rfl

end Buckling

end

end
