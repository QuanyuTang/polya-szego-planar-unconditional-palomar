/-
The compact-support mollification proof pattern and the short integrability
argument are adapted from EllipticPdes/Sobolev/GraphLattice.lean, pinned at
ec784093f30308ef770ff855ce624725adf6f870. The existing coordinate-convolution
and Lp-approximation theorems are used directly, without importing GraphLattice.

Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in that project's LICENSE.
Authors: Alejandro Soto Franco
-/

module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import RequestProject.Core1
public import EllipticPdes.Embedding.Morrey

/-!
# Nonnegative compact weak-H1 functions have nonnegative smooth test approximants

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.
The actual normed bump convolutions are nonnegative, have compact support
inside the given open set, and converge together with every supplied weak
derivative in full-space L2. No Lipschitz condition is imposed on the input.

The input weak-gradient and L2 hypotheses are the natural data of this
general approximation producer. They are not assumptions replacing the
original H01 model or a final weak maximum principle. This file does not
assert a weak-PDE test extension, a Caccioppoli inequality, or an SMP.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal Convolution

namespace Buckling.PositiveCompactWeakApproximation

open EllipticPdes EllipticPdes.Embedding

/-- The literal convolution, with the nonnegative normed bump on the right. -/
def mollified (ρ : ContDiffBump (0 : Plane)) (φ : Plane → ℝ) : Plane → ℝ :=
  φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.normed volume

/-- A compactly supported L2 function is genuinely globally integrable.
This is the short GraphLattice argument, specialized to the original plane. -/
lemma integrable_of_memLp_compact {φ : Plane → ℝ} (hφ : MemLp φ 2 volume)
    (hc : HasCompactSupport φ) : Integrable φ volume := by
  haveI : IsFiniteMeasure (volume.restrict (tsupport φ)) :=
    isFiniteMeasure_restrict.mpr hc.measure_lt_top.ne
  have hlocal : IntegrableOn φ (tsupport φ) volume :=
    (hφ.mono_measure Measure.restrict_le_self).integrable one_le_two
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport φ)).mp hlocal

/-- Positivity is proved for the actual convolution at every point, rather
than inferred from ordinary H01 density. -/
lemma mollified_nonneg (ρ : ContDiffBump (0 : Plane)) {φ : Plane → ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (x : Plane) : 0 ≤ mollified ρ φ x := by
  rw [mollified, convolution_def]
  exact integral_nonneg fun y => by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using!
      mul_nonneg (hφ y) (ρ.nonneg_normed (x - y))

/-- The support margin is measured by the actual bump outer radius. -/
lemma isTestFn_mollified {D : Set Plane} {φ : Plane → ℝ}
    (hφ : Integrable φ volume) (hc : HasCompactSupport φ)
    (ρ : ContDiffBump (0 : Plane))
    (hρ : cthickening ρ.rOut (tsupport φ) ⊆ D) : IsTestFn D (mollified ρ φ) := by
  refine ⟨contDiff_convolution_normed ρ hφ.locallyIntegrable,
    hasCompactSupport_convolution_normed ρ hc, ?_⟩
  change tsupport (φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ.normed volume) ⊆ D
  rw [convolution_lsmul_comm φ]
  exact (tsupport_normed_convolution_subset ρ hc).trans hρ

/-- The supplied actual weak-gradient component is mollified to the actual
original coordinate derivative. The full-space set has no boundary term. -/
lemma pderiv_mollified {φ : Plane → ℝ} {h : Fin 2 → Plane → ℝ}
    (hφ : Integrable φ volume) (hweak : HasWeakGradOn univ φ h)
    (ρ : ContDiffBump (0 : Plane)) (i : Fin 2) :
    pderiv i (mollified ρ φ) = mollified ρ (h i) := by
  funext x
  have h := partialD_convolution_eq_of_hasWeakGradOn (B := univ) (x := x)
    MeasurableSet.univ hφ.integrableOn
    hweak ρ i (subset_univ _)
  simpa only [Set.indicator_univ, mollified, pderiv, EllipticPdes.Sobolev.partialD] using h

/-- Full-space L2 convergence, with no restriction of the measure or hidden
uniform/support convergence requirement. -/
lemma tendsto_eLpNorm_mollified_sub {φ : Plane → ℝ} (hφ : MemLp φ 2 volume)
    {ρ : ℕ → ContDiffBump (0 : Plane)}
    (hr : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (mollified (ρ n) φ - φ) 2 volume) atTop (𝓝 0) := by
  simpa only [mollified, convolution_lsmul_comm φ] using
    (tendsto_eLpNorm_normed_convolution_sub (μ := volume) one_le_two
      ENNReal.ofNat_ne_top hφ hr)

/-- Actual nonnegative original compact smooth tests approximate both the
function and each actual weak coordinate derivative in full-space L2. -/
theorem exists_nonnegative_test_approximation {D : Set Plane} (hD : IsOpen D)
    {φ : Plane → ℝ} {h : Fin 2 → Plane → ℝ} (hφnonneg : ∀ x, 0 ≤ φ x)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ D)
    (hφ : MemLp φ 2 volume) (hh : ∀ i, MemLp (h i) 2 volume)
    (hweak : HasWeakGradOn univ φ h) :
    ∃ ψ : ℕ → Plane → ℝ,
      (∀ n, IsTestFn D (ψ n)) ∧ (∀ n x, 0 ≤ ψ n x) ∧
      Tendsto (fun n => eLpNorm (ψ n - φ) 2 volume) atTop (𝓝 0) ∧
      ∀ i, Tendsto (fun n => eLpNorm (pderiv i (ψ n) - h i) 2 volume) atTop (𝓝 0) := by
  obtain ⟨δ, hδ, hmargin⟩ := IsCompact.exists_cthickening_subset_open hc hD hs
  have hφint := integrable_of_memLp_compact hφ hc
  let ρ : ℕ → ContDiffBump (0 : Plane) := fun n => mollifier hδ n
  let ψ : ℕ → Plane → ℝ := fun n => mollified (ρ n) φ
  have hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0) := tendsto_rOut_mollifier hδ
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro n
    exact isTestFn_mollified hφint hc (ρ n)
      ((cthickening_mono (rOut_mollifier_le hδ n) _).trans hmargin)
  · exact fun n x => mollified_nonneg (ρ n) hφnonneg x
  · exact tendsto_eLpNorm_mollified_sub hφ hρ
  · intro i
    have hfd : ∀ n, pderiv i (ψ n) = mollified (ρ n) (h i) :=
      fun n => pderiv_mollified hφint hweak (ρ n) i
    simpa only [hfd] using tendsto_eLpNorm_mollified_sub (hh i) hρ

end Buckling.PositiveCompactWeakApproximation

end

end
