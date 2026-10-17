/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco

The finite-coordinate transport lemmas below are adapted from lines 67--112
of EllipticPdes/Sobolev/H01Lattice.lean at commit
ec784093f30308ef770ff855ce624725adf6f870. The source copyright and Apache
attribution are retained. The remaining bridge combines those lemmas with
the original Buckling definitions and the original Lipschitz IBP proof.
-/

module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EllipticH01Bridge
public import EllipticPdes.Sobolev.GraphLattice
public import EllipticPdes.Sobolev.GraphEuclidean
public import EllipticPdes.Embedding.WeakGradient
public import EllipticPdes.Analysis.LpExtendByZero

/-!
# The actual original H01 tuple of a compactly supported Lipschitz function

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The inputs are an open set, an actual globally Lipschitz scalar function,
compact support, and support inclusion. Whole-space L2 membership and the
weak derivative identity are proved here. The pinned graph-space theorem
then constructs H01 membership by genuine mollification. Finite-coordinate
transport and EllipticH01Bridge identify the resulting literal tuple with
the original graph closure. Core2, H01Lattice, and ExtMollification are not
imported or assumed.

The roots identify both actual restricted L2 representatives and the
actual full-space zero extensions with the function and its fderiv
coordinates almost everywhere. No equality of energies substitutes for
this identification. Energy identities are left to a subsequent consumer.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution RealInnerProductSpace

namespace Buckling.CompactLipOriginalH01

open EllipticPdes EllipticPdes.Embedding

/-- The actual directional fderivative in the original coordinate basis. -/
def coordinate (G : Plane → ℝ) (i : Fin 2) (x : Plane) : ℝ :=
  fderiv ℝ G x (EuclideanSpace.single i 1)

lemma fderiv_eq_zero_of_notMem_tsupport {G : Plane → ℝ} {x : Plane}
    (hx : x ∉ tsupport G) : fderiv ℝ G x = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_fderiv_subset ℝ h))

lemma coordinate_eq_zero_of_notMem_tsupport {G : Plane → ℝ} {x : Plane}
    (hx : x ∉ tsupport G) (i : Fin 2) : coordinate G i x = 0 := by
  simp [coordinate, fderiv_eq_zero_of_notMem_tsupport hx]

/-- A bounded measurable function supported in a compact set is in L2. -/
lemma memLp_of_bdd_support {g : Plane → ℝ} {K : Set Plane} (hK : IsCompact K)
    (hg : AEStronglyMeasurable g volume) (C : ℝ) (hb : ∀ x, |g x| ≤ C)
    (hs : ∀ x ∉ K, g x = 0) : MemLp g 2 volume := by
  have he : g = K.indicator g := by
    ext x
    by_cases hx : x ∈ K <;> simp [hx, hs]
  rw [he, memLp_indicator_iff_restrict hK.measurableSet]
  haveI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact MemLp.of_bound hg.restrict C (ae_of_all _ fun x => by simpa using hb x)

lemma value_memLp {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) : MemLp G 2 volume :=
  hG.continuous.memLp_of_hasCompactSupport hc

/-- Boundedness of the actual fderivative and its support give L2 coordinates. -/
lemma coordinate_memLp {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (i : Fin 2) : MemLp (coordinate G i) 2 volume := by
  refine memLp_of_bdd_support hc ?_ L (fun x => ?_)
    (fun x hx => coordinate_eq_zero_of_notMem_tsupport hx i)
  · exact (measurable_fderiv_apply_const ℝ G _).aestronglyMeasurable
  · calc
      |coordinate G i x| = ‖fderiv ℝ G x (EuclideanSpace.single i 1)‖ :=
        (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ G x‖ * ‖(EuclideanSpace.single i 1 : Plane)‖ :=
        (fderiv ℝ G x).le_opNorm _
      _ = ‖fderiv ℝ G x‖ := by simp
      _ ≤ L := norm_fderiv_le_of_lipschitz ℝ hG

/-- Rademacher plus the actual Lipschitz integration-by-parts theorem.
This is the original short proof, in a fresh namespace, without Core2. -/
lemma lipschitz_hasWeakGradient {G : Plane → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) : HasWeakGradient G (coordinate G) := by
  intro ψ hψ i
  obtain ⟨D, hD⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hψ.2.1 hψ.1 (by simp)
  set v : Plane := EuclideanSpace.single i 1
  have key := hG.integral_lineDeriv_mul_eq hD hψ.2.1 v (μ := volume)
  have h1 : ∫ x, lineDeriv ℝ G x v * ψ x = ∫ x, coordinate G i x * ψ x := by
    refine integral_congr_ae ?_
    filter_upwards [hG.ae_differentiableAt (μ := volume)] with x hx
    change lineDeriv ℝ G x v * ψ x = fderiv ℝ G x v * ψ x
    rw [hx.lineDeriv_eq_fderiv]
  have h2 : ∀ x, lineDeriv ℝ ψ x (-v) = -pderiv i ψ x := by
    intro x
    rw [((hψ.1.differentiable (by simp)) x).lineDeriv_eq_fderiv]
    simp [pderiv, v]
  rw [← h1, key]
  simp only [h2]
  rw [← integral_neg]
  congr 1
  ext x
  ring

/-- The original and library whole-space predicates have the same literal IBP identity. -/
lemma hasWeakGradient_iff_hasWeakGradOn_univ {G : Plane → ℝ}
    {g : Fin 2 → Plane → ℝ} :
    HasWeakGradient G g ↔ EllipticPdes.Embedding.HasWeakGradOn univ G g := by
  constructor
  · intro h ψ hψ hc hs i
    simpa only [Measure.restrict_univ, pderiv, EllipticPdes.Sobolev.partialD] using
      h ψ ⟨hψ, hc, hs⟩ i
  · intro h ψ hψ i
    simpa only [Measure.restrict_univ, pderiv, EllipticPdes.Sobolev.partialD] using
      h ψ hψ.1 hψ.2.1 hψ.2.2 i

/-! The following two finite-coordinate proofs are adapted from the pinned
Apache-licensed H01Lattice source. Only the genuine graph criterion is
imported, rather than the unrelated maximum-principle modules. -/

lemma memLp_vector_of_coordinates {g : Fin 2 → Plane → ℝ}
    (hg : ∀ i, MemLp (g i) 2 (volume : Measure Plane)) :
    MemLp (fun x => (WithLp.toLp 2 fun i => g i x : Plane)) 2 volume := by
  refine (Lp.memLp (H1Graph.piLpLpₗ (volume : Measure Plane)
    (WithLp.toLp 2 fun i => (hg i).toLp (g i)))).ae_eq ?_
  filter_upwards [H1Graph.coeFn_piLpLpₗ (volume : Measure Plane)
    (WithLp.toLp 2 fun i => (hg i).toLp (g i)),
    ae_all_iff.2 fun i => (hg i).coeFn_toLp] with x hx hx'
  rw [hx]
  exact congrArg (WithLp.toLp 2) (funext hx')

/-- Actual coordinate transport of the graph-space compact-support theorem. -/
lemma coordinate_mem_ellipticH01 {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {g : Fin 2 → Plane → ℝ} (hwg : HasWeakGradOn univ G g)
    (hG : MemLp G 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) :
    WithLp.toLp 2 (Fin.cons ((hG.mono_measure Measure.restrict_le_self).toLp G)
      fun i => ((hg i).mono_measure Measure.restrict_le_self).toLp (g i)) ∈
        EllipticPdes.Sobolev.H01 Ω := by
  have hgm := memLp_vector_of_coordinates hg
  have hwg' : HasWeakFDerivOn ⊤ G
      (fun x => innerSL ℝ (WithLp.toLp 2 fun i => g i x : Plane)) volume := by
    have := (hasWeakGradOn_iff_hasWeakFDerivOn isOpen_univ
      ((hG.locallyIntegrable one_le_two).locallyIntegrableOn _)
      (fun i => ((hg i).locallyIntegrable one_le_two).locallyIntegrableOn _)).1 hwg
    convert this using 1
    funext x
    rw [gradCLM_eq_toDual]
    rfl
  have key := H1Graph.mem_H01_of_hasCompactSupport hΩ hwg' hG hgm hc hs
  set X := H1Graph.mk ((hG.mono_measure Measure.restrict_le_self).toLp G)
    ((hgm.mono_measure Measure.restrict_le_self).toLp _) with hX
  have hmem := Submodule.mem_map_of_mem
    (f := (H1Graph.h1Equiv Ω).toLinearEquiv.toLinearMap) key
  rw [H1Graph.map_h1Equiv_H01] at hmem
  convert hmem using 1
  refine (PiLp.ext fun j => ?_)
  induction j using Fin.cases with
  | zero => simp [hX]
  | succ i =>
    refine Lp.ext ?_
    simp only [Fin.cons_succ]
    have e : (H1Graph.h1Equiv Ω X) i.succ =
        (EuclideanSpace.proj (𝕜 := ℝ) i : Plane →L[ℝ] ℝ).compLp
          (H1Graph.gradL X) := H1Graph.h1Equiv_apply_succ Ω X i
    refine (((hg i).mono_measure Measure.restrict_le_self).coeFn_toLp).trans ?_
    change _ =ᵐ[volume.restrict Ω] ⇑((H1Graph.h1Equiv Ω X) i.succ)
    rw [e]
    filter_upwards [ContinuousLinearMap.coeFn_compLp
      (EuclideanSpace.proj (𝕜 := ℝ) i : Plane →L[ℝ] ℝ) (H1Graph.gradL X),
      (hgm.mono_measure Measure.restrict_le_self).coeFn_toLp] with x h1 h2
    rw [h1]
    simp only [hX, H1Graph.gradL_mk] at h2 ⊢
    rw [h2]
    rfl

/-- The literal original L2 value/coordinate tuple, not an energy surrogate. -/
def tuple (Ω : Set Plane) {G : Plane → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) (hc : HasCompactSupport G) : L2 Ω × (Fin 2 → L2 Ω) :=
  (((value_memLp hG hc).restrict Ω).toLp G,
    fun i => ((coordinate_memLp hG hc i).restrict Ω).toLp (coordinate G i))

/-- The canonical tuple belongs to the actual original H01 graph closure. -/
theorem tuple_mem_H01 {Ω : Set Plane} (hΩ : IsOpen Ω) {G : Plane → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) :
    tuple Ω hG hc ∈ H01 Ω := by
  apply (h1DataToHilbert_mem_iff Ω (tuple Ω hG hc)).mp
  rw [h01HilbertSubmodule_eq_elliptic]
  change WithLp.toLp 2 (Fin.cons (((value_memLp hG hc).restrict Ω).toLp G)
    (fun i => ((coordinate_memLp hG hc i).restrict Ω).toLp (coordinate G i)) :
      Fin 3 → L2 Ω) ∈ _
  exact coordinate_mem_ellipticH01 hΩ
    (hasWeakGradient_iff_hasWeakGradOn_univ.mp (lipschitz_hasWeakGradient hG))
    (value_memLp hG hc) (coordinate_memLp hG hc) hc hs

lemma tuple_value_ae {Ω : Set Plane} {G : Plane → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) (hc : HasCompactSupport G) :
    ((tuple Ω hG hc).1 : Plane → ℝ) =ᵐ[volume.restrict Ω] G :=
  ((value_memLp hG hc).restrict Ω).coeFn_toLp

lemma tuple_coordinate_ae {Ω : Set Plane} {G : Plane → ℝ} {L : ℝ≥0}
    (hG : LipschitzWith L G) (hc : HasCompactSupport G) (i : Fin 2) :
    ((tuple Ω hG hc).2 i : Plane → ℝ) =ᵐ[volume.restrict Ω]
      fun x => fderiv ℝ G x (EuclideanSpace.single i 1) :=
  ((coordinate_memLp hG hc i).restrict Ω).coeFn_toLp

/-- Zero extension of an actual restricted toLp class recovers a globally
supported representative; this uses the library's actual extension map. -/
lemma extend_restrict_toLp_ae {Ω : Set Plane} (hΩm : MeasurableSet Ω)
    {g : Plane → ℝ} (hg : MemLp g 2 volume) (hz : ∀ x ∉ Ω, g x = 0) :
    (lpExtendByZero volume 2 Ω hΩm ((hg.restrict Ω).toLp g) : Plane → ℝ)
      =ᵐ[volume] g := by
  have hcls : ∀ᵐ x ∂volume, x ∈ Ω → ((hg.restrict Ω).toLp g : Plane → ℝ) x = g x :=
    (ae_restrict_iff' hΩm).mp (hg.restrict Ω).coeFn_toLp
  filter_upwards [coeFn_lpExtendByZero hΩm ((hg.restrict Ω).toLp g), hcls] with x hx hc
  rw [hx]
  by_cases hxΩ : x ∈ Ω
  · rw [Set.indicator_of_mem hxΩ, hc hxΩ]
  · rw [Set.indicator_of_notMem hxΩ, hz x hxΩ]

lemma tuple_extend_value_ae {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) :
    (lpExtendByZero volume 2 Ω hΩ.measurableSet (tuple Ω hG hc).1 : Plane → ℝ)
      =ᵐ[volume] G := by
  exact extend_restrict_toLp_ae hΩ.measurableSet (value_memLp hG hc)
    (fun x hx => image_eq_zero_of_notMem_tsupport (fun h => hx (hs h)))

lemma tuple_extend_coordinate_ae {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) (i : Fin 2) :
    (lpExtendByZero volume 2 Ω hΩ.measurableSet ((tuple Ω hG hc).2 i) : Plane → ℝ)
      =ᵐ[volume] fun x => fderiv ℝ G x (EuclideanSpace.single i 1) := by
  exact extend_restrict_toLp_ae hΩ.measurableSet (coordinate_memLp hG hc i)
    (fun x hx => coordinate_eq_zero_of_notMem_tsupport (fun h => hx (hs h)) i)

/-- A concrete original H01 element with its actual value and actual
directional gradients, both before and after whole-space zero extension. -/
theorem exists_original_H01_with_representatives {Ω : Set Plane} (hΩ : IsOpen Ω)
    {G : Plane → ℝ} {L : ℝ≥0} (hG : LipschitzWith L G)
    (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ω) :
    ∃ v : L2 Ω × (Fin 2 → L2 Ω), v ∈ H01 Ω ∧
      ((v.1 : Plane → ℝ) =ᵐ[volume.restrict Ω] G) ∧
      (∀ i, (v.2 i : Plane → ℝ) =ᵐ[volume.restrict Ω]
        fun x => fderiv ℝ G x (EuclideanSpace.single i 1)) ∧
      ((lpExtendByZero volume 2 Ω hΩ.measurableSet v.1 : Plane → ℝ) =ᵐ[volume] G) ∧
      (∀ i, (lpExtendByZero volume 2 Ω hΩ.measurableSet (v.2 i) : Plane → ℝ)
        =ᵐ[volume] fun x => fderiv ℝ G x (EuclideanSpace.single i 1)) := by
  exact ⟨tuple Ω hG hc, tuple_mem_H01 hΩ hG hc hs,
    tuple_value_ae hG hc, tuple_coordinate_ae hG hc,
    tuple_extend_value_ae hΩ hG hc hs, tuple_extend_coordinate_ae hΩ hG hc hs⟩

end Buckling.CompactLipOriginalH01

end

end
