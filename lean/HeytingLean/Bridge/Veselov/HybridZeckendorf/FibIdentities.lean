import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-!
# Bridge.Veselov.HybridZeckendorf.FibIdentities

Fibonacci identities and lazy per-level evaluation helpers.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Paper identity rewritten in index-safe form:
`2 * F_{k+2} = F_{k+3} + F_k`. -/
theorem fib_double_identity (k : Nat) :
    2 * Nat.fib (k + 2) = Nat.fib (k + 3) + Nat.fib k := by
  calc
    2 * Nat.fib (k + 2) = Nat.fib (k + 2) + Nat.fib (k + 2) := by simp [two_mul]
    _ = (Nat.fib k + Nat.fib (k + 1)) + Nat.fib (k + 2) := by
      rw [Nat.fib_add_two (n := k)]
    _ = Nat.fib k + (Nat.fib (k + 1) + Nat.fib (k + 2)) := by ac_rfl
    _ = Nat.fib k + Nat.fib (k + 3) := by
      rw [← Nat.fib_add_two (n := k + 1)]
    _ = Nat.fib (k + 3) + Nat.fib k := by ac_rfl

/-- Lazy per-level Zeckendorf payload (duplicates/consecutives allowed). -/
abbrev LazyZeckendorf := List Nat

/-- Evaluates a lazy payload by summing Fibonacci values of indices. -/
def lazyEvalFib (z : LazyZeckendorf) : Nat :=
  (z.map Nat.fib).sum

@[simp] theorem lazyEvalFib_nil : lazyEvalFib [] = 0 := by
  simp [lazyEvalFib]

@[simp] theorem lazyEvalFib_cons (k : Nat) (z : LazyZeckendorf) :
    lazyEvalFib (k :: z) = Nat.fib k + lazyEvalFib z := by
  simp [lazyEvalFib]

theorem lazyEvalFib_append (z₁ z₂ : LazyZeckendorf) :
    lazyEvalFib (z₁ ++ z₂) = lazyEvalFib z₁ + lazyEvalFib z₂ := by
  simp [lazyEvalFib, List.map_append, List.sum_append]

end HeytingLean.Bridge.Veselov.HybridZeckendorf
