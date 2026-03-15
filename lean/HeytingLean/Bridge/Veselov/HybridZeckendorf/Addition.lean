import Mathlib.Data.Finsupp.Basic
import HeytingLean.Bridge.Veselov.HybridZeckendorf.Normalization

/-!
# Bridge.Veselov.HybridZeckendorf.Addition

Hybrid addition and correctness.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Lazy addition by per-level payload merge. -/
noncomputable def addLazy (A B : LazyHybridNumber) : LazyHybridNumber :=
  A + B

theorem addLazy_eval (A B : LazyHybridNumber) :
    lazyEval (addLazy A B) = lazyEval A + lazyEval B := by
  classical
  simpa [addLazy, lazyEval, lazyEvalFib_append, Nat.add_mul,
      Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Finsupp.sum_add_index
      (f := A) (g := B)
      (h := fun i z => lazyEvalFib z * weight i)
      (h_zero := by
        intro i _
        change lazyEvalFib (0 : LazyPayload) * weight i = 0
        have hz : lazyEvalFib (0 : LazyPayload) = 0 := by
          change (List.map Nat.fib ([] : List Nat)).sum = 0
          simp
        calc
          lazyEvalFib (0 : LazyPayload) * weight i = 0 * weight i := by rw [hz]
          _ = 0 := Nat.zero_mul _)
      (h_add := by
        intro i _ z₁ z₂
        change lazyEvalFib (z₁ ++ z₂) * weight i =
          lazyEvalFib z₁ * weight i + lazyEvalFib z₂ * weight i
        rw [lazyEvalFib_append]
        rw [Nat.add_mul]))

/-- Canonical addition through lazy merge + normalization. -/
noncomputable def add (A B : HybridNumber) : HybridNumber :=
  normalize (addLazy (toLazy A) (toLazy B))

theorem add_correct (A B : HybridNumber) :
    eval (add A B) = eval A + eval B := by
  simp [add, addLazy_eval, normalize_sound]

theorem add_comm_eval (A B : HybridNumber) :
    eval (add A B) = eval (add B A) := by
  simp [add_correct, Nat.add_comm]

/-- Canonical embedding preserves ordinary natural-number addition. -/
theorem add_fromNat (m n : Nat) :
    eval (add (fromNat m) (fromNat n)) = m + n := by
  simpa using add_correct (fromNat m) (fromNat n)

example : eval (add (fromNat 789) (fromNat 456)) = 1245 := by
  norm_num [add_fromNat]

end HeytingLean.Bridge.Veselov.HybridZeckendorf
