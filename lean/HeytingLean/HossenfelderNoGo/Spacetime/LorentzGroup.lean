import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import HeytingLean.HossenfelderNoGo.Spacetime.MinkowskiInterval

namespace HeytingLean.HossenfelderNoGo.Spacetime

/-- A Lorentz boost parameterized by rapidity `η`. -/
structure LorentzBoost where
  rapidity : ℝ

/-- Apply a Lorentz boost to a spacetime displacement. -/
noncomputable def LorentzBoost.apply (b : LorentzBoost) (d : SpacetimeDisplacement) :
    SpacetimeDisplacement where
  Δt := d.Δt * Real.cosh b.rapidity + d.Δx * Real.sinh b.rapidity
  Δx := d.Δt * Real.sinh b.rapidity + d.Δx * Real.cosh b.rapidity

private theorem exp_half_lt_cosh (η : ℝ) : Real.exp η / 2 < Real.cosh η := by
  have hexp_lt : Real.exp η < 2 * Real.cosh η := by
    rw [← Real.cosh_add_sinh]
    linarith [Real.sinh_lt_cosh η]
  linarith

private theorem norm_pair_ge_of_nonneg_right {x y : ℝ} (hy : 0 ≤ y) : y ≤ ‖(x, y)‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hy]
  exact le_max_right _ _

private theorem norm_pair_ge_of_nonneg_left {x y : ℝ} (hx : 0 ≤ x) : x ≤ ‖(x, y)‖ := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx]
  exact le_max_left _ _

/-- Hyperbolae of nonzero proper length are unbounded in the ambient product norm on `ℝ × ℝ`
because the Lorentz group is non-compact. -/
theorem hyperbola_infinite_length (α : ℝ) (hα : α ≠ 0) :
    ¬∃ (L : ℝ), ∀ d ∈ hyperbolaAt α, ‖(d.Δt, d.Δx)‖ ≤ L
:= by
  rintro ⟨L, hL⟩
  by_cases hpos : 0 < α
  · let r := Real.sqrt α
    let B : ℝ := max L 0 + 1
    have hr_pos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 hpos
    have hr_sq : r ^ 2 = α := by
      dsimp [r]
      exact Real.sq_sqrt hpos.le
    have hB_pos : 0 < B := by
      dsimp [B]
      linarith [le_max_right L 0]
    have hB_gt_L : L < B := by
      dsimp [B]
      linarith [le_max_left L 0]
    let η : ℝ := Real.log (2 * (B / r))
    have harg_pos : 0 < 2 * (B / r) := by
      positivity
    let d : SpacetimeDisplacement :=
      { Δt := r * Real.sinh η
        Δx := r * Real.cosh η }
    have hd_hyperbola : d ∈ hyperbolaAt α := by
      dsimp [d, hyperbolaAt, minkowskiInterval]
      nlinarith [Real.cosh_sq_sub_sinh_sq η, hr_sq]
    have hcosh_lower : B / r < Real.cosh η := by
      have hlog : Real.exp η = 2 * (B / r) := by
        dsimp [η]
        rw [Real.exp_log harg_pos]
      nlinarith [hlog, exp_half_lt_cosh η]
    have hcoord_gt : B < r * Real.cosh η := by
      have hmul : r * (B / r) < r * Real.cosh η := mul_lt_mul_of_pos_left hcosh_lower hr_pos
      have hcancel : r * (B / r) = B := by
        field_simp [hr_pos.ne']
      simpa [hcancel] using hmul
    have hcoord_nonneg : 0 ≤ r * Real.cosh η := by
      positivity
    have hnorm_ge : r * Real.cosh η ≤ ‖(d.Δt, d.Δx)‖ := by
      simpa [d] using norm_pair_ge_of_nonneg_right (x := r * Real.sinh η) hcoord_nonneg
    have hnorm_gt : B < ‖(d.Δt, d.Δx)‖ := lt_of_lt_of_le hcoord_gt hnorm_ge
    have hnorm_le : ‖(d.Δt, d.Δx)‖ ≤ L := hL d hd_hyperbola
    linarith
  · have hneg : α < 0 := by
      exact (lt_or_gt_of_ne hα).resolve_right hpos
    let r := Real.sqrt (-α)
    let B : ℝ := max L 0 + 1
    have hr_pos : 0 < r := by
      dsimp [r]
      exact Real.sqrt_pos.2 (by linarith)
    have hr_sq : r ^ 2 = -α := by
      dsimp [r]
      exact Real.sq_sqrt (by linarith)
    have hB_pos : 0 < B := by
      dsimp [B]
      linarith [le_max_right L 0]
    have hB_gt_L : L < B := by
      dsimp [B]
      linarith [le_max_left L 0]
    let η : ℝ := Real.log (2 * (B / r))
    have harg_pos : 0 < 2 * (B / r) := by
      positivity
    let d : SpacetimeDisplacement :=
      { Δt := r * Real.cosh η
        Δx := r * Real.sinh η }
    have hd_hyperbola : d ∈ hyperbolaAt α := by
      dsimp [d, hyperbolaAt, minkowskiInterval]
      nlinarith [Real.cosh_sq_sub_sinh_sq η, hr_sq]
    have hcosh_lower : B / r < Real.cosh η := by
      have hlog : Real.exp η = 2 * (B / r) := by
        dsimp [η]
        rw [Real.exp_log harg_pos]
      nlinarith [hlog, exp_half_lt_cosh η]
    have hcoord_gt : B < r * Real.cosh η := by
      have hmul : r * (B / r) < r * Real.cosh η := mul_lt_mul_of_pos_left hcosh_lower hr_pos
      have hcancel : r * (B / r) = B := by
        field_simp [hr_pos.ne']
      simpa [hcancel] using hmul
    have hcoord_nonneg : 0 ≤ r * Real.cosh η := by
      positivity
    have hnorm_ge : r * Real.cosh η ≤ ‖(d.Δt, d.Δx)‖ := by
      simpa [d] using norm_pair_ge_of_nonneg_left (y := r * Real.sinh η) hcoord_nonneg
    have hnorm_gt : B < ‖(d.Δt, d.Δx)‖ := lt_of_lt_of_le hcoord_gt hnorm_ge
    have hnorm_le : ‖(d.Δt, d.Δx)‖ ≤ L := hL d hd_hyperbola
    linarith

end HeytingLean.HossenfelderNoGo.Spacetime
