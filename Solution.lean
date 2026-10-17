module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/
public import Mathlib
public import UnconditionalAreaRigidity

/-!
# Solution draft: the unconditional planar buckling area inequality

Formalization authors: Quanyu Tang and Haiqi Zhang.

SOURCE_DRAFT (2026-10-17): UNCOMPILED, NOT TYPE-COMPARED, NOT SUBMISSION READY.
This standalone solution draft repeats the statement's mathematical
definitions and does not import the statement module. Every retained
Bridge proof is copied verbatim from the audited conditional solution.
The first three goals transfer the new unconditional development roots;
the disk and comparison goals retain their original Core4 transfers.

All mathematical definitions, including the toL2 fallback, H01/H02 closures,
Rayleigh infima and Bessel roots, are unchanged. The new dependency chain,
this complete literal Bridge, and comparison with the isolated statement
must still be compiled and checked separately. This directory is outside
the frozen 182-module verification phase and is not a submission release.
-/

@[expose] public section

open MeasureTheory Real Filter Topology

namespace BucklingChallenge

/-! ### Basic objects -/

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The partial derivative `∂ᵢ φ` of a function on the plane. -/
noncomputable def pderiv (i : Fin 2) (φ : Plane → ℝ) : Plane → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)

/-- `φ ∈ C_c^∞(Ω)`: `φ` is smooth and its support is a compact subset of `Ω`. -/
def IsTestFn (Ω : Set Plane) (φ : Plane → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ω

/-- The real Hilbert space `L²(Ω)`. -/
noncomputable abbrev L2 (Ω : Set Plane) := Lp ℝ 2 (volume.restrict Ω)

open Classical in
/-- The class of a function in `L²(Ω)` (zero if the function is not square integrable on
`Ω`; this case never occurs below, since it is only applied to test functions). -/
noncomputable def toL2 (Ω : Set Plane) (φ : Plane → ℝ) : L2 Ω :=
  if h : MemLp φ 2 (volume.restrict Ω) then h.toLp φ else 0

/-- The `H¹`-data `(φ, (∂ᵢφ)ᵢ)` of a function. -/
noncomputable def h1Data (Ω : Set Plane) (φ : Plane → ℝ) : L2 Ω × (Fin 2 → L2 Ω) :=
  (toL2 Ω φ, fun i => toL2 Ω (pderiv i φ))

/-- The `H²`-data `(φ, (∂ᵢφ)ᵢ, (∂ᵢ∂ⱼφ)ᵢⱼ)` of a function. -/
noncomputable def h2Data (Ω : Set Plane) (φ : Plane → ℝ) :
    L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω) :=
  (toL2 Ω φ, fun i => toL2 Ω (pderiv i φ), fun i j => toL2 Ω (pderiv i (pderiv j φ)))

/-- `H₀¹(Ω)`: the closure of `C_c^∞(Ω)` in the `H¹` norm. -/
def H01 (Ω : Set Plane) : Set (L2 Ω × (Fin 2 → L2 Ω)) :=
  closure (h1Data Ω '' {φ | IsTestFn Ω φ})

/-- `H₀²(Ω)`: the closure of `C_c^∞(Ω)` in the `H²` norm. -/
def H02 (Ω : Set Plane) : Set (L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) :=
  closure (h2Data Ω '' {φ | IsTestFn Ω φ})

/-- `E₀(v) = ∫_Ω v²` on `H₀¹(Ω)`. -/
noncomputable def energy0 {Ω : Set Plane} (v : L2 Ω × (Fin 2 → L2 Ω)) : ℝ := ‖v.1‖ ^ 2

/-- `E₁(v) = ∫_Ω |∇v|²` on `H₀¹(Ω)`. -/
noncomputable def energy1 {Ω : Set Plane} (v : L2 Ω × (Fin 2 → L2 Ω)) : ℝ :=
  ∑ i, ‖v.2 i‖ ^ 2

/-- `E₁(v) = ∫_Ω |∇v|²` on `H₀²(Ω)`. -/
noncomputable def gradEnergy {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) : ℝ :=
  ∑ i, ‖v.2.1 i‖ ^ 2

/-- `E₂(v) = ∫_Ω |Δv|²` on `H₀²(Ω)`, with `Δv = ∂₁∂₁v + ∂₂∂₂v`. -/
noncomputable def laplEnergy {Ω : Set Plane}
    (v : L2 Ω × (Fin 2 → L2 Ω) × (Fin 2 → Fin 2 → L2 Ω)) : ℝ :=
  ‖v.2.2 0 0 + v.2.2 1 1‖ ^ 2

/-- The first Dirichlet eigenvalue `λ₁ᴰ(Ω) = inf_{0 ≠ v ∈ H₀¹(Ω)} E₁(v)/E₀(v)`. -/
noncomputable def dirichletEig (Ω : Set Plane) : ℝ :=
  ⨅ v : {v // v ∈ H01 Ω ∧ energy0 v ≠ 0}, energy1 v.1 / energy0 v.1

/-- The first buckling eigenvalue `Λ₁(Ω) = inf_{0 ≠ v ∈ H₀²(Ω)} E₂(v)/E₁(v)`
(infimum of the Rayleigh quotient `∫|Δv|² / ∫|∇v|²`). -/
noncomputable def bucklingEig (Ω : Set Plane) : ℝ :=
  ⨅ v : {v // v ∈ H02 Ω ∧ gradEnergy v ≠ 0}, laplEnergy v.1 / gradEnergy v.1

/-! ### Bessel functions -/

/-- The Bessel function `J_n(x) = ∑_{m ≥ 0} (-1)^m (x/2)^{2m+n} / (m! (m+n)!)`, real argument. -/
noncomputable def besselJ (n : ℕ) (x : ℝ) : ℝ :=
  ∑' m : ℕ, (-1 : ℝ) ^ m * (x / 2) ^ (2 * m + n) / ((m.factorial : ℝ) * ((m + n).factorial : ℝ))

/-- The Bessel function `J_n(ζ)`, complex argument. -/
noncomputable def besselJC (n : ℕ) (ζ : ℂ) : ℂ :=
  ∑' m : ℕ, (-1 : ℂ) ^ m * (ζ / 2) ^ (2 * m + n) / ((m.factorial : ℂ) * ((m + n).factorial : ℂ))

/-- Enumeration of the positive zeros of `J_n`: `besselZero n 0 = 0` is a placeholder and
`besselZero n (k+1)` is the infimum of the zeros of `J_n` exceeding `besselZero n k`. -/
noncomputable def besselZero (n : ℕ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => sInf {x : ℝ | besselZero n k < x ∧ besselJ n x = 0}

/-- `j_{1,1}`, the first positive zero of `J₁` (the infimum of its positive zeros). -/
noncomputable def j11 : ℝ := sInf {x : ℝ | 0 < x ∧ besselJ 1 x = 0}

/-- `j_{0,1}`, the first positive zero of `J₀` (the infimum of its positive zeros). -/
noncomputable def j01 : ℝ := sInf {x : ℝ | 0 < x ∧ besselJ 0 x = 0}

/-! ### Bridge to the project's definitions (`RequestProject`) -/

section Bridge

lemma besselJ_eq : besselJ = Buckling.besselJ := rfl

lemma besselJC_eq : besselJC = Buckling.besselJC := rfl

lemma besselZero_eq : besselZero = Buckling.besselZero := by
  funext n k
  induction k with
  | zero => rfl
  | succ k ih => simp only [besselZero, Buckling.besselZero, ih, besselJ_eq]

lemma j11_eq : j11 = Buckling.jk := by
  simp only [j11, Buckling.jk, Buckling.besselZero, besselJ_eq]

lemma j01_eq : j01 = Buckling.jq := by
  simp only [j01, Buckling.jq, Buckling.besselZero, besselJ_eq]

lemma pderiv_eq : pderiv = Buckling.pderiv := rfl

lemma isTestFn_eq : IsTestFn = Buckling.IsTestFn := rfl

lemma toL2_eq {Ω : Set Plane} {φ : Plane → ℝ} (h : Buckling.IsTestFn Ω φ) :
    toL2 Ω φ = h.toL2 := by
  rw [toL2, dif_pos h.memLp]; rfl

lemma toL2_pderiv_eq {Ω : Set Plane} {φ : Plane → ℝ} (h : Buckling.IsTestFn Ω φ) (i : Fin 2) :
    toL2 Ω (pderiv i φ) = (Buckling.IsTestFn.pderiv h i).toL2 :=
  toL2_eq (Buckling.IsTestFn.pderiv h i)

lemma toL2_pderiv2_eq {Ω : Set Plane} {φ : Plane → ℝ} (h : Buckling.IsTestFn Ω φ)
    (i j : Fin 2) :
    toL2 Ω (pderiv i (pderiv j φ)) =
      (Buckling.IsTestFn.pderiv (Buckling.IsTestFn.pderiv h j) i).toL2 :=
  toL2_eq _

lemma h2Data_image_eq (Ω : Set Plane) :
    h2Data Ω '' {φ | IsTestFn Ω φ} = Set.range (Buckling.graphH2 (Ω := Ω)) := by
  ext v
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨⟨φ, hφ⟩, ?_⟩
    simp only [Buckling.graphH2, h2Data, toL2_eq hφ, toL2_pderiv_eq hφ,
      toL2_pderiv2_eq hφ]
  · rintro ⟨⟨φ, hφ⟩, rfl⟩
    refine ⟨φ, hφ, ?_⟩
    simp only [Buckling.graphH2, h2Data, toL2_eq hφ, toL2_pderiv_eq hφ,
      toL2_pderiv2_eq hφ]

lemma h1Data_image_eq (Ω : Set Plane) :
    h1Data Ω '' {φ | IsTestFn Ω φ} = Set.range (Buckling.graphH1 (Ω := Ω)) := by
  ext v
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨⟨φ, hφ⟩, ?_⟩
    simp only [Buckling.graphH1, h1Data, toL2_eq hφ, toL2_pderiv_eq hφ]
  · rintro ⟨⟨φ, hφ⟩, rfl⟩
    refine ⟨φ, hφ, ?_⟩
    simp only [Buckling.graphH1, h1Data, toL2_eq hφ, toL2_pderiv_eq hφ]

lemma H02_eq (Ω : Set Plane) : H02 Ω = Buckling.H02 Ω := by
  rw [H02, Buckling.H02, h2Data_image_eq]

lemma H01_eq (Ω : Set Plane) : H01 Ω = Buckling.H01 Ω := by
  rw [H01, Buckling.H01, h1Data_image_eq]

lemma bucklingEig_eq (Ω : Set Plane) : bucklingEig Ω = Buckling.bucklingEig Ω := by
  unfold bucklingEig; rw [H02_eq]; rfl

lemma dirichletEig_eq (Ω : Set Plane) : dirichletEig Ω = Buckling.dirichletEig Ω := by
  unfold dirichletEig; rw [H01_eq]; rfl

end Bridge

/-! ### Main results -/

/-- **`cor:area`, inequality.**  For every open `Ω ⊆ ℝ²` with `0 < |Ω| < ∞`,
`|Ω| Λ₁(Ω) ≥ π j_{1,1}²`. -/
theorem area_inequality (Ω : Set Plane) (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    π * j11 ^ 2 ≤ (volume Ω).toReal * bucklingEig Ω := by
  rw [j11_eq, bucklingEig_eq]
  exact Buckling.area_inequality_unconditional hΩ h0 hfin

/-- **`cor:area`, equality case.**  Equality holds iff `Ω = B_R(a)` for some `a`, `R > 0`. -/
theorem area_equality_iff (Ω : Set Plane) (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) :
    (volume Ω).toReal * bucklingEig Ω = π * j11 ^ 2 ↔
      ∃ (a : Plane) (R : ℝ), 0 < R ∧ Ω = Metric.ball a R := by
  rw [j11_eq, bucklingEig_eq]
  exact Buckling.area_equality_iff_without_E12 hΩ h0 hfin

/-- **`conj:PS` in dimension two (Pólya–Szegő buckling inequality).**  If `Ω ⊆ ℝ²` is open with
`0 < |Ω| < ∞` and `πR² = |Ω|`, then `Λ₁(Ω) ≥ Λ₁(B_R(0))`, with equality iff `Ω` is a disk of
radius `R`. -/
theorem polya_szego_buckling (Ω : Set Plane) (hΩ : IsOpen Ω)
    (h0 : 0 < volume Ω) (hfin : volume Ω < ⊤) (R : ℝ) (hR : 0 < R)
    (hvol : π * R ^ 2 = (volume Ω).toReal) :
    bucklingEig (Metric.ball (0 : Plane) R) ≤ bucklingEig Ω ∧
      (bucklingEig Ω = bucklingEig (Metric.ball (0 : Plane) R) ↔
        ∃ a : Plane, Ω = Metric.ball a R) := by
  rw [bucklingEig_eq, bucklingEig_eq]
  exact Buckling.polya_szego_buckling_without_E12 hΩ h0 hfin R hR hvol

/-- **Lemma 11.6 (disk eigenvalue).**  `Λ₁(B_R(a)) = j_{1,1}² / R²`. -/
theorem bucklingEig_ball (a : Plane) (R : ℝ) (hR : 0 < R) :
    bucklingEig (Metric.ball a R) = j11 ^ 2 / R ^ 2 := by
  rw [j11_eq, bucklingEig_eq]
  exact Buckling.bucklingEig_ball a R hR

/-- **Theorem 10.7 (buckling–Dirichlet comparison).**  For every nonempty open `Ω ⊆ ℝ²`,
`Λ₁(Ω) ≥ (j_{1,1}² / j_{0,1}²) λ₁ᴰ(Ω)`. -/
theorem buckling_ge_dirichlet (Ω : Set Plane) (hΩ : IsOpen Ω)
    (hne : Ω.Nonempty) :
    j11 ^ 2 / j01 ^ 2 * dirichletEig Ω ≤ bucklingEig Ω := by
  rw [j11_eq, j01_eq, bucklingEig_eq, dirichletEig_eq]
  exact Buckling.buckling_ge_dirichlet Ω hΩ hne

end BucklingChallenge
