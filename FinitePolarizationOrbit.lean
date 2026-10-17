module
/-
The following development-time comments preserve the original notes and their
historical status labels. See verification/README.md and GitHub Actions for the
verification record and checks of the exact commit.
-/

public import EuclideanReflectionContraction
public import PolarizationLipschitz
public import PolarizationMeasure
public import PolarizationBounds

/-!
# Literal finite orbits of origin-directed Euclidean polarization

SOURCE_DRAFT (2026-10-17): not compiled and not part of the production project.
Each admissible operation is specified by an actual unit normal and a real
offset `c ≤ 0`. Its side is the already constructed halfspace `c ≤ ⟪ν, x⟫`,
so the origin is on that side. No measure, distance, or radial conclusion is
stored as an input field: those facts come from the concrete reflection proofs.

The recursion is literal two-point max/min sorting. The orbit is the set of
functions produced by arbitrary finite lists; the orbit set itself need not
have finite cardinality. Natural common bounds are derived for every list and
every member of that actual orbit.

Energy transport, compactness of an orbit closure, Schwarz rearrangement, and
Faber--Krahn are deliberately separate obligations. No such conclusion is
assumed or asserted here. Actual compilation and axiom inspection remain due.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace FaberKrahnDevelopment

open EuclideanReflection

/-- Parameters of a literal closed affine halfspace containing the origin. -/
structure OriginHalfspace where
  normal : UnitNormal
  offset : ℝ
  offset_nonpos : offset ≤ 0

namespace OriginHalfspace

/-- An actual max/min polarization in the specified affine halfspace. -/
def step (s : OriginHalfspace) (f : Plane → ℝ) : Plane → ℝ :=
  twoPointPolarization (halfspace s.normal s.offset)
    (reflection s.normal s.offset) f

lemma zero_mem_halfspace (s : OriginHalfspace) :
    (0 : Plane) ∈ halfspace s.normal s.offset :=
  (zero_mem_halfspace_iff s.normal s.offset).2 s.offset_nonpos

lemma measurable_step (s : OriginHalfspace) {f : Plane → ℝ}
    (hf : Measurable f) : Measurable (s.step f) := by
  exact measurable_twoPointPolarization
    (halfspace_measurableSet s.normal s.offset)
    (reflection_measurable s.normal s.offset) hf

/-- Every strict superlevel measure is retained, including infinite measures. -/
lemma measure_superlevel_step (s : OriginHalfspace) {f : Plane → ℝ}
    (hf : Measurable f) (t : ℝ) :
    volume {x | t < s.step f x} = volume {x | t < f x} := by
  exact measure_superlevel_twoPointPolarization
    (halfspace_measurableSet s.normal s.offset) hf
    (reflection_measurePreserving s.normal s.offset)
    (reflection_involutive s.normal s.offset)
    (reflection_ae_swap s.normal s.offset) t

/-- The contraction input here is proved for this reflection, not assumed. -/
lemma lipschitzWith_step (s : OriginHalfspace) {f : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) : LipschitzWith K (s.step f) := by
  exact lipschitzWith_twoPointPolarization
    (reflection_isometry s.normal s.offset)
    (reflection_involutive s.normal s.offset)
    (reflection_cross_dist_le s.normal s.offset) hf

lemma step_mem_Icc (s : OriginHalfspace) {f : Plane → ℝ} {M : ℝ}
    (hf : ∀ x, f x ∈ Icc 0 M) : ∀ x, s.step f x ∈ Icc 0 M := by
  exact twoPointPolarization_mem_Icc hf

lemma step_nonneg (s : OriginHalfspace) {f : Plane → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∀ x, 0 ≤ s.step f x := by
  exact twoPointPolarization_nonneg hf

/-- The origin-containing orientation produces the radial comparison needed
to retain a common support ball for a nonnegative function. -/
lemma step_eq_zero_of_radius_lt (s : OriginHalfspace) {f : Plane → ℝ} {S : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hzero : ∀ x, S < ‖x‖ → f x = 0)
    {x : Plane} (hx : S < ‖x‖) : s.step f x = 0 := by
  exact twoPointPolarization_eq_zero_of_radius_lt hf hzero
    (fun z hz => norm_le_norm_reflection_of_mem s.normal s.offset s.offset_nonpos hz) hx

end OriginHalfspace

/-- Perform the tail first, then the head's literal polarization. -/
def finitePolarization : List OriginHalfspace → (Plane → ℝ) → Plane → ℝ
  | [], f => f
  | s :: ss, f => s.step (finitePolarization ss f)

@[simp] lemma finitePolarization_nil (f : Plane → ℝ) :
    finitePolarization [] f = f := rfl

@[simp] lemma finitePolarization_cons (s : OriginHalfspace)
    (ss : List OriginHalfspace) (f : Plane → ℝ) :
    finitePolarization (s :: ss) f = s.step (finitePolarization ss f) := rfl

lemma finitePolarization_append (ss tt : List OriginHalfspace) (f : Plane → ℝ) :
    finitePolarization (ss ++ tt) f = finitePolarization ss (finitePolarization tt f) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      simp only [List.cons_append, finitePolarization_cons, ih]

lemma measurable_finitePolarization (ss : List OriginHalfspace) {f : Plane → ℝ}
    (hf : Measurable f) : Measurable (finitePolarization ss f) := by
  induction ss with
  | nil => exact hf
  | cons s ss ih => exact s.measurable_step ih

lemma measure_superlevel_finitePolarization (ss : List OriginHalfspace)
    {f : Plane → ℝ} (hf : Measurable f) (t : ℝ) :
    volume {x | t < finitePolarization ss f x} = volume {x | t < f x} := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      exact (s.measure_superlevel_step (measurable_finitePolarization ss hf) t).trans ih

lemma lipschitzWith_finitePolarization (ss : List OriginHalfspace)
    {f : Plane → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) :
    LipschitzWith K (finitePolarization ss f) := by
  induction ss with
  | nil => exact hf
  | cons s ss ih => exact s.lipschitzWith_step ih

lemma finitePolarization_mem_Icc (ss : List OriginHalfspace)
    {f : Plane → ℝ} {M : ℝ} (hf : ∀ x, f x ∈ Icc 0 M) :
    ∀ x, finitePolarization ss f x ∈ Icc 0 M := by
  induction ss with
  | nil => exact hf
  | cons s ss ih => exact s.step_mem_Icc ih

lemma finitePolarization_nonneg (ss : List OriginHalfspace) {f : Plane → ℝ}
    (hf : ∀ x, 0 ≤ f x) : ∀ x, 0 ≤ finitePolarization ss f x := by
  induction ss with
  | nil => exact hf
  | cons s ss ih => exact s.step_nonneg ih

lemma finitePolarization_eq_zero_of_radius_lt (ss : List OriginHalfspace)
    {f : Plane → ℝ} {S : ℝ} (hf : ∀ x, 0 ≤ f x)
    (hzero : ∀ x, S < ‖x‖ → f x = 0) :
    ∀ x, S < ‖x‖ → finitePolarization ss f x = 0 := by
  induction ss with
  | nil => exact hzero
  | cons s ss ih =>
      intro x hx
      exact s.step_eq_zero_of_radius_lt (finitePolarization_nonneg ss hf) ih hx

/-- The actual finite-list orbit; this is not a finite-cardinality assertion. -/
def finitePolarizationOrbit (f : Plane → ℝ) : Set (Plane → ℝ) :=
  {g | ∃ ss : List OriginHalfspace, finitePolarization ss f = g}

@[simp] lemma mem_finitePolarizationOrbit_iff (f g : Plane → ℝ) :
    g ∈ finitePolarizationOrbit f ↔
      ∃ ss : List OriginHalfspace, finitePolarization ss f = g := Iff.rfl

lemma self_mem_finitePolarizationOrbit (f : Plane → ℝ) :
    f ∈ finitePolarizationOrbit f := ⟨[], rfl⟩

lemma finitePolarizationOrbit_nonempty (f : Plane → ℝ) :
    (finitePolarizationOrbit f).Nonempty := ⟨f, self_mem_finitePolarizationOrbit f⟩

lemma step_mem_finitePolarizationOrbit (s : OriginHalfspace)
    {f g : Plane → ℝ} (hg : g ∈ finitePolarizationOrbit f) :
    s.step g ∈ finitePolarizationOrbit f := by
  rcases hg with ⟨ss, rfl⟩
  exact ⟨s :: ss, rfl⟩

lemma finitePolarization_mem_orbit (ss : List OriginHalfspace)
    {f g : Plane → ℝ} (hg : g ∈ finitePolarizationOrbit f) :
    finitePolarization ss g ∈ finitePolarizationOrbit f := by
  rcases hg with ⟨tt, rfl⟩
  exact ⟨ss ++ tt, finitePolarization_append ss tt f⟩

lemma measurable_of_mem_finitePolarizationOrbit {f g : Plane → ℝ}
    (hf : Measurable f) (hg : g ∈ finitePolarizationOrbit f) : Measurable g := by
  rcases hg with ⟨ss, rfl⟩
  exact measurable_finitePolarization ss hf

lemma measure_superlevel_of_mem_finitePolarizationOrbit {f g : Plane → ℝ}
    (hf : Measurable f) (hg : g ∈ finitePolarizationOrbit f) (t : ℝ) :
    volume {x | t < g x} = volume {x | t < f x} := by
  rcases hg with ⟨ss, rfl⟩
  exact measure_superlevel_finitePolarization ss hf t

lemma lipschitzWith_of_mem_finitePolarizationOrbit {f g : Plane → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hg : g ∈ finitePolarizationOrbit f) :
    LipschitzWith K g := by
  rcases hg with ⟨ss, rfl⟩
  exact lipschitzWith_finitePolarization ss hf

lemma mem_Icc_of_mem_finitePolarizationOrbit {f g : Plane → ℝ} {M : ℝ}
    (hf : ∀ x, f x ∈ Icc 0 M) (hg : g ∈ finitePolarizationOrbit f) :
    ∀ x, g x ∈ Icc 0 M := by
  rcases hg with ⟨ss, rfl⟩
  exact finitePolarization_mem_Icc ss hf

lemma eq_zero_of_radius_lt_of_mem_finitePolarizationOrbit {f g : Plane → ℝ} {S : ℝ}
    (hf : ∀ x, 0 ≤ f x) (hzero : ∀ x, S < ‖x‖ → f x = 0)
    (hg : g ∈ finitePolarizationOrbit f) : ∀ x, S < ‖x‖ → g x = 0 := by
  rcases hg with ⟨ss, rfl⟩
  exact finitePolarization_eq_zero_of_radius_lt ss hf hzero

/-- Natural common bounds for this literal orbit, all deduced from the initial
function's bounds. There is no assumed energy or geometric result in the data. -/
lemma finitePolarizationOrbit_common_bounds {f : Plane → ℝ} {K : ℝ≥0} {M S : ℝ}
    (hfm : Measurable f) (hfL : LipschitzWith K f)
    (hfr : ∀ x, f x ∈ Icc 0 M) (hfz : ∀ x, S < ‖x‖ → f x = 0) :
    ∀ g ∈ finitePolarizationOrbit f,
      Measurable g ∧ LipschitzWith K g ∧ (∀ x, g x ∈ Icc 0 M) ∧
        (∀ x, S < ‖x‖ → g x = 0) ∧
        (∀ t : ℝ, volume {x | t < g x} = volume {x | t < f x}) := by
  intro g hg
  exact ⟨measurable_of_mem_finitePolarizationOrbit hfm hg,
    lipschitzWith_of_mem_finitePolarizationOrbit hfL hg,
    mem_Icc_of_mem_finitePolarizationOrbit hfr hg,
    eq_zero_of_radius_lt_of_mem_finitePolarizationOrbit (fun x => (hfr x).1) hfz hg,
    measure_superlevel_of_mem_finitePolarizationOrbit hfm hg⟩

end FaberKrahnDevelopment

end

end
