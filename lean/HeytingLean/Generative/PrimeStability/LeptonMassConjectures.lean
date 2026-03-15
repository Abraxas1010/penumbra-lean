import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Generative.PrimeStability.StabilityHierarchy

open scoped BigOperators

namespace HeytingLean.Generative.PrimeStability

open Real

noncomputable def m_electron : ℝ := 0.51099895069
noncomputable def m_muon : ℝ := 105.6583755
noncomputable def m_tau : ℝ := 1776.93

noncomputable def koideQ (m₁ m₂ m₃ : ℝ) : ℝ :=
  (m₁ + m₂ + m₃) / (Real.sqrt m₁ + Real.sqrt m₂ + Real.sqrt m₃) ^ 2

noncomputable def signedKoideQ (r₁ r₂ r₃ : ℝ) : ℝ :=
  (r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2) / (r₁ + r₂ + r₃) ^ 2

noncomputable def brannenRoot (μ δ : ℝ) (n : Fin 3) : ℝ :=
  μ * (1 + Real.sqrt 2 * Real.cos (δ + 2 * Real.pi / 3 * n.val))

noncomputable def brannenMass (μ δ : ℝ) (n : Fin 3) : ℝ :=
  (brannenRoot μ δ n) ^ 2

theorem koideQ_bounds {m₁ m₂ m₃ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) (h₃ : 0 < m₃) :
    1 / 3 ≤ koideQ m₁ m₂ m₃ ∧ koideQ m₁ m₂ m₃ ≤ 1 := by
  let a := Real.sqrt m₁
  let b := Real.sqrt m₂
  let c := Real.sqrt m₃
  have ha : 0 < a := by simpa [a] using Real.sqrt_pos.mpr h₁
  have hb : 0 < b := by simpa [b] using Real.sqrt_pos.mpr h₂
  have hc : 0 < c := by simpa [c] using Real.sqrt_pos.mpr h₃
  have hsumsq : m₁ + m₂ + m₃ = a ^ 2 + b ^ 2 + c ^ 2 := by
    have hsq1 : a ^ 2 = m₁ := by
      dsimp [a]
      nlinarith [Real.sq_sqrt h₁.le]
    have hsq2 : b ^ 2 = m₂ := by
      dsimp [b]
      nlinarith [Real.sq_sqrt h₂.le]
    have hsq3 : c ^ 2 = m₃ := by
      dsimp [c]
      nlinarith [Real.sq_sqrt h₃.le]
    nlinarith [hsq1, hsq2, hsq3]
  have hupper : a ^ 2 + b ^ 2 + c ^ 2 ≤ (a + b + c) ^ 2 := by
    nlinarith [mul_nonneg ha.le hb.le, mul_nonneg hb.le hc.le, mul_nonneg hc.le ha.le]
  have hlower : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hden : 0 < (a + b + c) ^ 2 := by positivity
  have hden0 : (a + b + c) ^ 2 ≠ 0 := ne_of_gt hden
  constructor
  · unfold koideQ
    rw [hsumsq]
    field_simp [hden0]
    nlinarith [hlower]
  · unfold koideQ
    rw [hsumsq]
    field_simp [hden0]
    nlinarith [hupper]

theorem cos_two_pi_div_three :
    Real.cos (2 * Real.pi / 3) = - (1 / 2 : ℝ) := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]

theorem sin_two_pi_div_three :
    Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub,
    Real.sin_pi_div_three]

theorem cos_four_pi_div_three :
    Real.cos (4 * Real.pi / 3) = - (1 / 2 : ℝ) := by
  rw [show (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi,
    Real.cos_pi_div_three]

theorem sin_four_pi_div_three :
    Real.sin (4 * Real.pi / 3) = - Real.sqrt 3 / 2 := by
  rw [show (4 : ℝ) * Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.sin_add_pi,
    Real.sin_pi_div_three]
  ring

theorem cos_cycle_sum (δ : ℝ) :
    Real.cos δ + Real.cos (δ + 2 * Real.pi / 3) + Real.cos (δ + 4 * Real.pi / 3) = 0 := by
  rw [Real.cos_add, Real.cos_add]
  rw [cos_two_pi_div_three, sin_two_pi_div_three, cos_four_pi_div_three, sin_four_pi_div_three]
  ring

theorem cos_cycle_sq_sum (δ : ℝ) :
    Real.cos δ ^ 2 + Real.cos (δ + 2 * Real.pi / 3) ^ 2 +
      Real.cos (δ + 4 * Real.pi / 3) ^ 2 = 3 / 2 := by
  rw [Real.cos_add, Real.cos_add]
  rw [cos_two_pi_div_three, sin_two_pi_div_three, cos_four_pi_div_three, sin_four_pi_div_three]
  have hsq : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq δ
  have hsqrt3 : (Real.sqrt 3) ^ 2 = 3 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  nlinarith [hsq, hsqrt3]

theorem brannen_root_sum (μ δ : ℝ) :
    ∑ n : Fin 3, brannenRoot μ δ n = 3 * μ := by
  rw [Fin.sum_univ_three]
  unfold brannenRoot
  simp
  have hangle : δ + 2 * π / 3 * (2 : ℝ) = δ + 4 * π / 3 := by ring
  rw [hangle]
  ring_nf
  have hcyc : Real.cos δ + Real.cos (δ + π * (2 / 3 : ℝ)) + Real.cos (δ + π * (4 / 3 : ℝ)) = 0 := by
    convert cos_cycle_sum δ using 1
    ring
  have hlin : μ * √2 * (Real.cos δ + Real.cos (δ + π * (2 / 3 : ℝ)) + Real.cos (δ + π * (4 / 3 : ℝ))) = 0 := by
    rw [hcyc]
    ring
  have hlin' :
      μ * √2 * Real.cos δ + μ * √2 * Real.cos (δ + π * (2 / 3 : ℝ)) +
        μ * √2 * Real.cos (δ + π * (4 / 3 : ℝ)) = 0 := by
    nlinarith [hlin]
  nlinarith [hlin']

theorem brannen_root_sq_sum (μ δ : ℝ) :
    ∑ n : Fin 3, (brannenRoot μ δ n) ^ 2 = 6 * μ ^ 2 := by
  rw [Fin.sum_univ_three]
  unfold brannenRoot
  simp
  have hangle : δ + 2 * π / 3 * (2 : ℝ) = δ + 4 * π / 3 := by ring
  rw [hangle]
  ring_nf
  have hcyc : Real.cos δ + Real.cos (δ + π * (2 / 3 : ℝ)) + Real.cos (δ + π * (4 / 3 : ℝ)) = 0 := by
    convert cos_cycle_sum δ using 1
    ring
  have hsqcyc :
      Real.cos δ ^ 2 + Real.cos (δ + π * (2 / 3 : ℝ)) ^ 2 +
        Real.cos (δ + π * (4 / 3 : ℝ)) ^ 2 = 3 / 2 := by
    convert cos_cycle_sq_sum δ using 1
    ring
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have hlin :
      μ ^ 2 * √2 * (Real.cos δ + Real.cos (δ + π * (2 / 3 : ℝ)) + Real.cos (δ + π * (4 / 3 : ℝ))) * 2 = 0 := by
    rw [hcyc]
    ring
  have hsqterm :
      μ ^ 2 * (√2 ^ 2) *
        (Real.cos δ ^ 2 + Real.cos (δ + π * (2 / 3 : ℝ)) ^ 2 +
          Real.cos (δ + π * (4 / 3 : ℝ)) ^ 2) = μ ^ 2 * 3 := by
    rw [hsqrt, hsqcyc]
    ring
  have hlin' :
      μ ^ 2 * √2 * Real.cos δ * 2 + μ ^ 2 * √2 * Real.cos (δ + π * (2 / 3 : ℝ)) * 2 +
        μ ^ 2 * √2 * Real.cos (δ + π * (4 / 3 : ℝ)) * 2 = 0 := by
    nlinarith [hlin]
  have hsqterm' :
      μ ^ 2 * √2 ^ 2 * Real.cos δ ^ 2 +
        μ ^ 2 * √2 ^ 2 * Real.cos (δ + π * (2 / 3 : ℝ)) ^ 2 +
        μ ^ 2 * √2 ^ 2 * Real.cos (δ + π * (4 / 3 : ℝ)) ^ 2 = μ ^ 2 * 3 := by
    nlinarith [hsqterm]
  nlinarith [hlin', hsqterm']

theorem brannen_gives_signed_koide_exact (μ δ : ℝ) (hμ : 0 < μ) :
    signedKoideQ (brannenRoot μ δ 0) (brannenRoot μ δ 1) (brannenRoot μ δ 2) = 2 / 3 := by
  have hsum := brannen_root_sum μ δ
  have hsumsq := brannen_root_sq_sum μ δ
  rw [Fin.sum_univ_three] at hsum hsumsq
  unfold signedKoideQ
  rw [hsumsq, hsum]
  have hμ0 : (μ : ℝ) ≠ 0 := ne_of_gt hμ
  field_simp [hμ0]
  ring

theorem brannen_gives_koide_exact (μ δ : ℝ) (hμ : 0 < μ)
    (hnonneg : ∀ n : Fin 3, 0 ≤ brannenRoot μ δ n) :
    koideQ (brannenMass μ δ 0) (brannenMass μ δ 1) (brannenMass μ δ 2) = 2 / 3 := by
  unfold koideQ brannenMass
  have h0 : Real.sqrt ((brannenRoot μ δ 0) ^ 2) = brannenRoot μ δ 0 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg 0)]
  have h1 : Real.sqrt ((brannenRoot μ δ 1) ^ 2) = brannenRoot μ δ 1 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg 1)]
  have h2 : Real.sqrt ((brannenRoot μ δ 2) ^ 2) = brannenRoot μ δ 2 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hnonneg 2)]
  rw [h0, h1, h2]
  simpa using brannen_gives_signed_koide_exact μ δ hμ

end HeytingLean.Generative.PrimeStability
