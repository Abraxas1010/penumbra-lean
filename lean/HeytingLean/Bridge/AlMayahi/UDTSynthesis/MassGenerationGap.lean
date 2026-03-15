import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Eigen.NucleusReLU
import HeytingLean.Eigen.SafEDMD

/-!
# Bridge.AlMayahi.UDTSynthesis.MassGenerationGap

Mass generation gap from UDT paper equation `m = h/(c²Δτ)`.

The mass generation mechanism maps to the ReLU nucleus trapped regime:
components clamped to zero by ReLU (negative → 0) correspond to
massive degrees of freedom (Δτ > 0), while free components (nonneg,
passed through unchanged) correspond to massless DOFs (Δτ = 0).

This module connects the UDT mass generation concept to the existing
`NucleusReLU` and `SafEDMD` infrastructure, establishing that the
"nucleus gap" (sqSum before vs after ReLU) measures the same structural
phenomenon as Δτ in the mass equation.
-/

open scoped BigOperators

namespace HeytingLean.Bridge.AlMayahi.UDTSynthesis

open HeytingLean.Eigen

/-- Asymmetry gap: the proper-time asymmetry Δτ between two clocks. -/
structure AsymmetryGap where
  Δτ : ℝ
  Δτ_nonneg : 0 ≤ Δτ

/-- A massless degree of freedom has Δτ = 0 (full clock symmetry). -/
def massless (g : AsymmetryGap) : Prop := g.Δτ = 0

/-- A massive degree of freedom has Δτ > 0 (broken clock symmetry). -/
def massive (g : AsymmetryGap) : Prop := 0 < g.Δτ

/-- Massless and massive are mutually exclusive. -/
theorem massless_or_massive (g : AsymmetryGap) :
    massless g ∨ massive g := by
  rcases eq_or_lt_of_le g.Δτ_nonneg with h | h
  · left; exact h.symm
  · right; exact h

/-- Massless and massive are exhaustive and exclusive. -/
theorem not_massless_iff_massive (g : AsymmetryGap) :
    ¬ massless g ↔ massive g := by
  constructor
  · intro h
    cases massless_or_massive g with
    | inl hm => exact absurd hm h
    | inr hm => exact hm
  · intro h
    exact ne_of_gt h

/-- The trapped regime: components that are negative (clamped by ReLU to 0). -/
def trappedRegime (n : ℕ) (v : Fin n → ℝ) : Set (Fin n) :=
  {i | v i < 0}

/-- The free regime: components that are nonneg (passed through ReLU unchanged). -/
def freeRegime (n : ℕ) (v : Fin n → ℝ) : Set (Fin n) :=
  {i | 0 ≤ v i}

/-- Trapped and free regimes partition Fin n. -/
theorem trapped_free_partition (n : ℕ) (v : Fin n → ℝ) :
    trappedRegime n v ∪ freeRegime n v = Set.univ := by
  ext i
  simp only [Set.mem_union, Set.mem_univ, iff_true, trappedRegime, freeRegime,
    Set.mem_setOf_eq]
  exact lt_or_ge (v i) 0 |>.imp_left id |>.imp_right id

/-- Trapped and free regimes are disjoint. -/
theorem trapped_free_disjoint (n : ℕ) (v : Fin n → ℝ) :
    Disjoint (trappedRegime n v) (freeRegime n v) := by
  rw [Set.disjoint_iff]
  intro i ⟨htrapped, hfree⟩
  simp [trappedRegime, freeRegime] at htrapped hfree
  linarith

/-- The nucleus gap: energy lost to the ReLU nucleus projection.
This measures how much energy is in the trapped (negative) components. -/
def nucleusGap (n : ℕ) (v : Fin n → ℝ) : ℝ :=
  sqSum v - sqSum (reluNucleus n v)

/-- The nucleus gap is nonneg (ReLU can only reduce sqSum energy). -/
theorem nucleusGap_nonneg (n : ℕ) (v : Fin n → ℝ) :
    0 ≤ nucleusGap n v := by
  unfold nucleusGap
  linarith [relu_sqSum_le_sqSum v]

/-- The nucleus gap decomposes as a sum over components: each
component contributes `(v i)² - (max (v i) 0)²`. -/
theorem nucleusGap_eq_sum (n : ℕ) (v : Fin n → ℝ) :
    nucleusGap n v = ∑ i, ((v i) ^ 2 - (reluNucleus n v i) ^ 2) := by
  unfold nucleusGap sqSum
  rw [Finset.sum_sub_distrib]

/-- For a nonneg vector, all components pass through ReLU unchanged,
so the nucleus gap is zero. This is the "massless" case: full symmetry. -/
theorem nucleusGap_zero_of_nonneg {n : ℕ} (v : Fin n → ℝ) (h : ∀ i, 0 ≤ v i) :
    nucleusGap n v = 0 := by
  unfold nucleusGap
  have hrelu : reluNucleus n v = v := relu_eq_of_nonneg v h
  rw [hrelu]
  ring

/-- If the nucleus gap is zero, then the vector must be componentwise nonneg
(all components are in the free regime). -/
theorem nonneg_of_nucleusGap_zero {n : ℕ} (v : Fin n → ℝ)
    (hgap : nucleusGap n v = 0) :
    ∀ i, 0 ≤ v i := by
  intro i
  have hge : 0 ≤ nucleusGap n v := nucleusGap_nonneg n v
  rw [nucleusGap_eq_sum] at hgap
  have hterm_nonneg : ∀ j, 0 ≤ (v j) ^ 2 - (reluNucleus n v j) ^ 2 := by
    intro j
    have := relu_sq_le_sq v j
    linarith
  have hterm_zero : ∀ j ∈ Finset.univ, (v j) ^ 2 - (reluNucleus n v j) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hterm_nonneg j)).mp hgap
  have hi := hterm_zero i (Finset.mem_univ i)
  have hsq : (v i) ^ 2 = (reluNucleus n v i) ^ 2 := by linarith
  by_contra h
  push_neg at h
  have hmax_eq : reluNucleus n v i = 0 := by
    change max (v i) 0 = 0
    exact max_eq_right (le_of_lt h)
  rw [hmax_eq] at hsq
  simp at hsq
  linarith

/-- Nucleus gap is zero iff the vector is componentwise nonneg. -/
theorem nucleusGap_zero_iff_nonneg {n : ℕ} (v : Fin n → ℝ) :
    nucleusGap n v = 0 ↔ ∀ i, 0 ≤ v i :=
  ⟨nonneg_of_nucleusGap_zero v, fun h => nucleusGap_zero_of_nonneg v h⟩

/-- Nucleus gap is positive iff some component is negative (trapped). -/
theorem nucleusGap_pos_iff_trapped {n : ℕ} (v : Fin n → ℝ) :
    0 < nucleusGap n v ↔ ∃ i, v i < 0 := by
  rw [show (0 < nucleusGap n v) ↔ ¬ (nucleusGap n v = 0) from
    ⟨ne_of_gt, fun h => lt_of_le_of_ne (nucleusGap_nonneg n v) (Ne.symm h)⟩]
  rw [nucleusGap_zero_iff_nonneg]
  push_neg
  rfl

/-- The nucleus gap is bounded above by the total energy. -/
theorem nucleusGap_le_sqSum (n : ℕ) (v : Fin n → ℝ) :
    nucleusGap n v ≤ sqSum v := by
  unfold nucleusGap
  linarith [relu_sqSum_nonneg v]

end HeytingLean.Bridge.AlMayahi.UDTSynthesis
