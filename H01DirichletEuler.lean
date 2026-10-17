/-
The elementary quadratic lemma and the quadratic-expansion proof pattern
are adapted from EllipticPdes/Spectrum/Variational.lean, pinned at
ec784093f30308ef770ff855ce624725adf6f870, without importing that module.

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

public import H01RayleighMinimizer

/-!
# Euler identity for the original Dirichlet graph-closure model

SOURCE_DRAFT (2026-10-17), Lean 4.35.0-rc3; NOT compiled or registered.

The original ciInf gives its denominator-free lower bound, including
zero-mass tuples. Variation is performed in the actual original closed
submodule H01, using exactly the original energy0 and energy1. Equality
in the lower bound forces the linear term of the real quadratic to vanish.

The final existence theorem consumes the actual finite-area minimizer;
it assumes only openness, nonemptiness and finite volume of the domain.
No compactness, nonzero test, minimizer, Euler equation, positivity or PDE
is introduced as an additional hypothesis.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open scoped InnerProductSpace RealInnerProductSpace

namespace Buckling
namespace H01DirichletEuler

/-- The original ciInf lower bound, with no denominator and no nonzero-mass
condition. At zero mass, nonnegativity of the actual gradient energy suffices. -/
theorem dirichletEig_mul_energy0_le {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    dirichletEig Ω * energy0 v ≤ energy1 v := by
  by_cases h0 : energy0 v = 0
  · rw [h0, mul_zero]
    exact Finset.sum_nonneg fun i _ => sq_nonneg ‖v.2 i‖
  · have hpos : 0 < energy0 v :=
      lt_of_le_of_ne (sq_nonneg ‖v.1‖) (Ne.symm h0)
    exact (le_div_iff₀ hpos).mp (H01Rayleigh.original_dirichletEig_le v hv h0)

/-- Elementary real quadratic argument, adapted from the pinned
EllipticPdes.Variational.eq_zero_of_quadratic_nonneg (Apache 2.0). -/
lemma eq_zero_of_quadratic_nonneg {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ 2 * t * b + t ^ 2 * a) : b = 0 := by
  by_contra hb
  have hb2 : 0 < b ^ 2 := by positivity
  have hεpos : (0 : ℝ) < 1 / (|a| + 1) := by positivity
  have hεa : 1 / (|a| + 1) * a < 2 := by
    have h1 : a ≤ |a| := le_abs_self a
    have h2 : (0 : ℝ) < |a| + 1 := by positivity
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ h2]
    linarith
  have hneg := h (-(1 / (|a| + 1) * b))
  nlinarith [mul_pos (mul_pos hεpos hb2)
    (show (0 : ℝ) < 2 - 1 / (|a| + 1) * a by linarith)]

/-- The real Hilbert norm expansion used coordinate by coordinate. -/
lemma norm_add_smul_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x y : H) (t : ℝ) :
    ‖x + t • y‖ ^ 2 = ‖x‖ ^ 2 + 2 * t * inner ℝ x y + t ^ 2 * ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, real_inner_add_add_self, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq]
  ring

lemma energy0_add_smul {Ω : Set Plane}
    (u v : L2 Ω × (Fin 2 → L2 Ω)) (t : ℝ) :
    energy0 (u + t • v) =
      energy0 u + 2 * t * inner ℝ u.1 v.1 + t ^ 2 * energy0 v := by
  change ‖u.1 + t • v.1‖ ^ 2 =
    ‖u.1‖ ^ 2 + 2 * t * inner ℝ u.1 v.1 + t ^ 2 * ‖v.1‖ ^ 2
  exact norm_add_smul_sq u.1 v.1 t

lemma energy1_add_smul {Ω : Set Plane}
    (u v : L2 Ω × (Fin 2 → L2 Ω)) (t : ℝ) :
    energy1 (u + t • v) = energy1 u +
      2 * t * (∑ i, inner ℝ (u.2 i) (v.2 i)) + t ^ 2 * energy1 v := by
  unfold energy1
  change (∑ i, ‖u.2 i + t • v.2 i‖ ^ 2) =
    (∑ i, ‖u.2 i‖ ^ 2) +
      2 * t * (∑ i, inner ℝ (u.2 i) (v.2 i)) + t ^ 2 * ∑ i, ‖v.2 i‖ ^ 2
  simp_rw [norm_add_smul_sq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Equality in the original global lower bound implies the actual weak
Euler identity against every original H01 tuple, including on irregular domains. -/
theorem euler_of_energy_eq {Ω : Set Plane}
    {u : L2 Ω × (Fin 2 → L2 Ω)} (hu : u ∈ H01 Ω)
    (heq : energy1 u = dirichletEig Ω * energy0 u)
    (v : L2 Ω × (Fin 2 → L2 Ω)) (hv : v ∈ H01 Ω) :
    (∑ i, inner ℝ (u.2 i) (v.2 i)) = dirichletEig Ω * inner ℝ u.1 v.1 := by
  have key : ∀ t : ℝ,
      0 ≤ 2 * t * ((∑ i, inner ℝ (u.2 i) (v.2 i)) -
          dirichletEig Ω * inner ℝ u.1 v.1) +
        t ^ 2 * (energy1 v - dirichletEig Ω * energy0 v) := by
    intro t
    have ht : u + t • v ∈ H01 Ω :=
      (h01ClosedSubmodule Ω).add_mem hu ((h01ClosedSubmodule Ω).smul_mem t hv)
    have hmain := dirichletEig_mul_energy0_le (u + t • v) ht
    rw [energy0_add_smul, energy1_add_smul, heq] at hmain
    nlinarith [hmain]
  have hb := eq_zero_of_quadratic_nonneg key
  linarith

end H01DirichletEuler

/-- A mass-one minimizer of the original Dirichlet ciInf, together with its
Euler identity, on every nonempty open domain of finite area. -/
theorem exists_H01_dirichletEig_minimizer_with_euler {Ω : Set Plane}
    (hΩ : IsOpen Ω) (hne : Ω.Nonempty) (hfin : volume Ω < ⊤) :
    ∃ u : L2 Ω × (Fin 2 → L2 Ω), u ∈ H01 Ω ∧ energy0 u = 1 ∧
      energy1 u = dirichletEig Ω ∧
      ∀ v : L2 Ω × (Fin 2 → L2 Ω), v ∈ H01 Ω →
        (∑ i, inner ℝ (u.2 i) (v.2 i)) = dirichletEig Ω * inner ℝ u.1 v.1 := by
  obtain ⟨u, hu, h0, h1⟩ := exists_H01_dirichletEig_minimizer hΩ hne hfin
  refine ⟨u, hu, h0, h1, ?_⟩
  intro v hv
  exact H01DirichletEuler.euler_of_energy_eq hu
    (by simpa only [h0, mul_one] using h1) v hv

end Buckling

end

end
