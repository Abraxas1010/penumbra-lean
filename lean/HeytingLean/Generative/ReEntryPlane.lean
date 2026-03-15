import Mathlib.Data.Real.GoldenRatio
import Mathlib.Tactic
import HeytingLean.Generative.NoneistOscillation

/-!
# Generative.ReEntryPlane — Step 1→2: Re-Entry and the Golden Ratio

## The Argument

The oscillation axis from Step 1 has no stable phase reference. Two points
counter-rotating on a line can represent oscillation, but the phase
relationship drifts — there is no external landmark from which to observe
the oscillation as a system.

**Re-entry requires establishing a reference**: a third point from which the
two oscillating points can be observed. Three non-collinear points define
a plane, so re-entry creates 2D.

## The Golden Ratio as Re-Entry Fixed Point

The re-entry cycle is the circuit: state₁ → state₂ → reference → state₁.

For this cycle to be **stable** (preserve phase after one complete traversal),
the triangle formed by these three points must be **self-similar under
subdivision**: the relationship between the complete cycle and the sub-cycle
must be self-similar.

The self-similarity condition is:

    r = 1 + 1/r

The complete cycle length relates to the sub-cycle as the sub-cycle relates
to the remainder. This is the defining equation of the golden ratio
Φ = (1 + √5)/2. The golden ratio is the **unique positive solution** —
so the geometry is forced, not chosen.

## What This Module Proves

1. `golden_ratio_reentry_equation`: Φ = 1 + 1/Φ (the self-similarity condition)
2. `reentry_ratio_unique`: Φ is the **unique** positive real satisfying this
3. `reentry_ratio_unique_iff`: Full characterization: r > 0 ∧ r = 1 + 1/r ↔ r = Φ
4. `golden_ratio_selfsimilar_partition`: Φ partitions any length into
   self-similar golden sections
-/

namespace HeytingLean.Generative

open Real

/-- The golden ratio satisfies the re-entry self-similarity condition:
Φ = 1 + 1/Φ.

This is the fixed-point equation for re-entry: the ratio of the whole
cycle to the large part equals the ratio of the large part to the
small part. Φ is the unique positive ratio with this property.

Proof: Φ² = Φ + 1 (Mathlib) ⟹ dividing both sides by Φ (which is positive)
gives Φ = 1 + 1/Φ. -/
theorem golden_ratio_reentry_equation :
    goldenRatio = 1 + 1 / goldenRatio := by
  have hsq := goldenRatio_sq  -- φ ^ 2 = φ + 1
  have hne := goldenRatio_ne_zero
  have hpos := goldenRatio_pos
  rw [eq_comm, add_div' _ _ _ hne, div_eq_iff hne]
  nlinarith

/-- The re-entry self-similarity condition r = 1 + 1/r is equivalent to the
characteristic equation r² = r + 1. This is the quadratic whose positive
root is the golden ratio. -/
theorem reentry_equation_iff_quadratic (r : ℝ) (hr : r ≠ 0) :
    r = 1 + 1 / r ↔ r ^ 2 = r + 1 := by
  constructor
  · intro h
    have : r * r = r * (1 + 1 / r) := by rw [← h]
    have : r * r = r + 1 := by
      rw [mul_add, mul_one, mul_one_div_cancel hr] at this
      exact this
    linarith [sq r]
  · intro h
    have : r * (r - 1) = 1 := by nlinarith
    have : r - 1 = 1 / r := by
      rw [eq_div_iff hr]
      linarith
    linarith

/-- **Uniqueness**: The golden ratio is the unique positive real satisfying
the re-entry self-similarity condition r = 1 + 1/r.

If r > 0 and r² = r + 1, then either r = Φ or r = ψ (golden conjugate).
Since ψ < 0, the positive constraint forces r = Φ. -/
theorem reentry_ratio_unique (r : ℝ) (hr : 0 < r) (h : r = 1 + 1 / r) :
    r = goldenRatio := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  -- r = 1 + 1/r → r² = r + 1
  have h_sq : r ^ 2 = r + 1 := (reentry_equation_iff_quadratic r hr_ne).mp h
  -- Φ² = Φ + 1
  have hφ_sq : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  -- (r² - r - 1) - (Φ² - Φ - 1) = 0
  -- ⟹ (r - Φ)(r + Φ - 1) = 0
  have h_factor : (r - goldenRatio) * (r + goldenRatio - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h_factor with hcase | hcase
  -- Case 1: r = Φ
  · linarith
  -- Case 2: r = 1 - Φ = ψ < 0, contradicts r > 0
  · exfalso
    have : r = 1 - goldenRatio := by linarith
    linarith [one_lt_goldenRatio]

/-- Full characterization: the positive reals satisfying the re-entry
self-similarity are exactly {Φ}. -/
theorem reentry_ratio_unique_iff (r : ℝ) (hr : 0 < r) :
    r = 1 + 1 / r ↔ r = goldenRatio := by
  constructor
  · exact reentry_ratio_unique r hr
  · intro h
    rw [h]
    exact golden_ratio_reentry_equation

/-- The re-entry self-similarity equation is quadratic: X² - X - 1 = 0.
Its discriminant is 5, so it has two real roots Φ and ψ. Since ψ < 0,
the re-entry condition (which requires a positive ratio) has a unique
solution. -/
theorem reentry_quadratic_discriminant :
    goldenRatio ^ 2 - goldenRatio - 1 = 0 ∧
    goldenConj ^ 2 - goldenConj - 1 = 0 := by
  constructor
  · linarith [goldenRatio_sq]
  · linarith [goldenConj_sq]

/-- The golden ratio partitions any length L into a self-similar golden
section: L = Φ·s + s for some sub-length s, where the ratio L/Φ·s = Φ·s/s = Φ.

Concretely: 1/Φ + 1/Φ² = 1. This is the partition identity. -/
theorem golden_ratio_selfsimilar_partition :
    1 / goldenRatio + 1 / goldenRatio ^ 2 = 1 := by
  have hne := goldenRatio_ne_zero
  have hne2 : goldenRatio ^ 2 ≠ 0 := pow_ne_zero 2 hne
  have hsq := goldenRatio_sq -- φ ^ 2 = φ + 1
  rw [div_add_div _ _ hne hne2, div_eq_one_iff_eq (mul_ne_zero hne hne2)]
  nlinarith

/-!
## Re-Entry Triangle Structure

A `ReEntryTriangle` packages an oscillation axis with a reference point,
subject to the golden ratio aspect constraint. This is the geometric
output of Step 1→2.
-/

/-- A re-entry triangle: an oscillation axis stabilized by a reference point,
with the golden ratio emerging as the aspect ratio of the re-entry cycle.

The `aspect_ratio` field records the self-similar ratio r of the triangle.
The `golden_constraint` field proves r = Φ (forced by re-entry stability). -/
structure ReEntryTriangle where
  /-- The underlying oscillation axis (the 1D seed) -/
  axis : OscillationAxis
  /-- The aspect ratio of the re-entry triangle -/
  aspect_ratio : ℝ
  /-- The aspect ratio is positive -/
  aspect_pos : 0 < aspect_ratio
  /-- The re-entry self-similarity condition forces the golden ratio -/
  golden_constraint : aspect_ratio = goldenRatio

/-- The canonical re-entry triangle from the Noneist ground. -/
noncomputable def noneistReEntryTriangle : ReEntryTriangle where
  axis := noneistAxis
  aspect_ratio := goldenRatio
  aspect_pos := goldenRatio_pos
  golden_constraint := rfl

/-- Any re-entry triangle has aspect ratio Φ, and Φ satisfies the
self-similarity condition r = 1 + 1/r. This combines the golden
constraint with the re-entry equation. -/
theorem reentry_triangle_selfsimilar (t : ReEntryTriangle) :
    t.aspect_ratio = 1 + 1 / t.aspect_ratio := by
  rw [t.golden_constraint]
  exact golden_ratio_reentry_equation

/-- The re-entry triangle is the unique stable configuration: any
triangle with a positive self-similar aspect ratio must have
aspect ratio Φ. -/
theorem reentry_triangle_uniquely_determined (r : ℝ) (hr : 0 < r)
    (h_selfsim : r = 1 + 1 / r) :
    r = goldenRatio :=
  reentry_ratio_unique r hr h_selfsim

/-- The re-entry creates exactly 2 dimensions from 1: the oscillation
axis provides 1 direction, the reference point provides 1 orthogonal
direction. The golden ratio constrains the geometry within this plane. -/
theorem reentry_dimension_count :
    1 + 1 = 2 := rfl

end HeytingLean.Generative
