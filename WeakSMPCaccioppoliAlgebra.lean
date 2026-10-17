module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import WeakSMPRegularizers

/-!
# Pointwise weighted Young estimates for the smooth weak-SMP regularizers

SOURCE_DRAFT: not registered or native checked. These are elementary real
and finite-sum inequalities only. They do not assert weak-test admissibility
or an integrated Caccioppoli estimate or a strong maximum principle.
-/

@[expose] public section

noncomputable section

namespace Buckling.WeakSMPRegularizers

lemma weighted_cross_le_half_energy {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s)
    (hrs : r * s ≤ 1) (χ a b : ℝ) :
    2 * χ * r * a * b ≤ χ ^ 2 * (r / s) * a ^ 2 / 2 + 2 * b ^ 2 := by
  have hn : 0 ≤ r * (χ * a - 2 * s * b) ^ 2 + 4 * s * b ^ 2 * (1 - r * s) :=
    add_nonneg (mul_nonneg hr (sq_nonneg _))
      (mul_nonneg (by positivity) (sub_nonneg.mpr hrs))
  have hid : χ ^ 2 * (r / s) * a ^ 2 / 2 + 2 * b ^ 2 - 2 * χ * r * a * b =
      (r * (χ * a - 2 * s * b) ^ 2 + 4 * s * b ^ 2 * (1 - r * s)) / (2 * s) := by
    field_simp [hs.ne']
    <;> ring
  have hdiff : 0 ≤ χ ^ 2 * (r / s) * a ^ 2 / 2 + 2 * b ^ 2 - 2 * χ * r * a * b := by
    rw [hid]
    exact div_nonneg hn (by positivity)
  linarith

lemma reciprocal_cross_le_half_energy {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    (χ a b : ℝ) :
    2 * χ * reciprocal δ t * a * b ≤
      χ ^ 2 * (reciprocal δ t / radius δ t) * a ^ 2 / 2 + 2 * b ^ 2 :=
  weighted_cross_le_half_energy (reciprocal_pos hδ t).le (radius_pos hδ t)
    (reciprocal_mul_radius_le_one hδ ht) χ a b

lemma reciprocal_cross_sum_le_half_energy {n : ℕ} {δ t : ℝ}
    (hδ : 0 < δ) (ht : 0 ≤ t) (χ : ℝ) (a b : Fin n → ℝ) :
    2 * χ * reciprocal δ t * (∑ i, a i * b i) ≤
      χ ^ 2 * (reciprocal δ t / radius δ t) * (∑ i, a i ^ 2) / 2 +
        2 * (∑ i, b i ^ 2) := by
  calc
    2 * χ * reciprocal δ t * (∑ i, a i * b i) =
        ∑ i, 2 * χ * reciprocal δ t * a i * b i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, (χ ^ 2 * (reciprocal δ t / radius δ t) * a i ^ 2 / 2 + 2 * b i ^ 2) :=
      Finset.sum_le_sum fun i _ => reciprocal_cross_le_half_energy hδ ht χ (a i) (b i)
    _ = _ := by
      simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum]

end Buckling.WeakSMPRegularizers

end

end
