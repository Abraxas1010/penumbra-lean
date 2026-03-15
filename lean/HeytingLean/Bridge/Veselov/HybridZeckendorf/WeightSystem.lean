import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

/-!
# Bridge.Veselov.HybridZeckendorf.WeightSystem

Weight hierarchy used by Veselov's hybrid Zeckendorf representation.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Hybrid-level weight sequence: `w₀ = 1`, `w₁ = 1000`, `wᵢ₊₂ = wᵢ₊₁²`. -/
def weight : Nat → Nat
  | 0 => 1
  | 1 => 1000
  | n + 2 => (weight (n + 1)) ^ 2

@[simp] theorem weight_zero : weight 0 = 1 := rfl
@[simp] theorem weight_one : weight 1 = 1000 := rfl

@[simp] theorem weight_succ_succ (n : Nat) : weight (n + 2) = (weight (n + 1)) ^ 2 := by
  simp [weight]

/-- Closed form for all levels above 0. -/
theorem weight_closed : ∀ i : Nat, weight (i + 1) = 1000 ^ (2 ^ i)
  | 0 => by simp [weight]
  | i + 1 => by
      have ih : weight (i + 1) = 1000 ^ (2 ^ i) := weight_closed i
      have hpow : (2 ^ i) * 2 = 2 ^ (i + 1) := by
        simp [pow_succ, Nat.mul_comm]
      calc
        weight (i + 2) = (weight (i + 1)) ^ 2 := by simp [weight]
        _ = (1000 ^ (2 ^ i)) ^ 2 := by rw [ih]
        _ = 1000 ^ ((2 ^ i) * 2) := by simp [pow_mul]
        _ = 1000 ^ (2 ^ (i + 1)) := by rw [hpow]

theorem weight_pos (i : Nat) : 0 < weight i := by
  cases i with
  | zero =>
      decide
  | succ n =>
      rw [weight_closed n]
      exact Nat.pow_pos (by decide : 0 < 1000)

theorem weight_ge_two_of_pos : ∀ i : Nat, 0 < i → 2 ≤ weight i
  | 0, h => (Nat.lt_irrefl 0 h).elim
  | 1, _ => by
      norm_num [weight]
  | i + 2, _ => by
      have hprev : 2 ≤ weight (i + 1) := weight_ge_two_of_pos (i + 1) (Nat.succ_pos _)
      have hprevPos : 0 < weight (i + 1) := lt_of_lt_of_le (by decide : 0 < 2) hprev
      calc
        2 ≤ weight (i + 1) := hprev
        _ ≤ weight (i + 1) * weight (i + 1) := Nat.le_mul_of_pos_left (weight (i + 1)) hprevPos
        _ = weight (i + 2) := by simp [weight, Nat.pow_two]

theorem weight_lt_succ : ∀ i : Nat, weight i < weight (i + 1)
  | 0 => by
      norm_num [weight]
  | i + 1 => by
      have htwo : 2 ≤ weight (i + 1) := weight_ge_two_of_pos (i + 1) (Nat.succ_pos _)
      have h1 : 1 < weight (i + 1) := lt_of_lt_of_le (by decide : 1 < 2) htwo
      have hpos : 0 < weight (i + 1) := lt_trans Nat.zero_lt_one h1
      have hmul :
          weight (i + 1) * 1 < weight (i + 1) * weight (i + 1) :=
        Nat.mul_lt_mul_of_pos_left h1 hpos
      calc
        weight (i + 1) = weight (i + 1) * 1 := by simp
        _ < weight (i + 1) * weight (i + 1) := hmul
        _ = weight (i + 2) := by simp [weight, Nat.pow_two]

theorem weight_strict_mono : StrictMono weight :=
  strictMono_nat_of_lt_succ weight_lt_succ

theorem weight_strict_mono' {i j : Nat} (h : i < j) : weight i < weight j :=
  weight_strict_mono h

end HeytingLean.Bridge.Veselov.HybridZeckendorf
