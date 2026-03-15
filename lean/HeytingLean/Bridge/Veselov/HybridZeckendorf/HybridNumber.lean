import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Fib.Zeckendorf
import Mathlib.Tactic
import HeytingLean.Bridge.Veselov.HybridZeckendorf.WeightSystem
import HeytingLean.Bridge.Veselov.HybridZeckendorf.FibIdentities

/-!
# Bridge.Veselov.HybridZeckendorf.HybridNumber

Core hybrid-number types, evaluation maps, and canonical constructors.
-/

namespace HeytingLean.Bridge.Veselov.HybridZeckendorf

/-- Canonical payload per level (represented as a list of Fibonacci indices). -/
abbrev ZeckPayload := List Nat

/-- Lazy payload per level (same shape, unconstrained). -/
abbrev LazyPayload := List Nat

instance : AddZeroClass ZeckPayload where
  add := List.append
  zero := []
  zero_add := by intro l; rfl
  add_zero := by
    intro l
    change l ++ [] = l
    simp

instance : AddZeroClass LazyPayload where
  add := List.append
  zero := []
  zero_add := by intro l; rfl
  add_zero := by
    intro l
    change l ++ [] = l
    simp

/-- Canonical hybrid number (finite-support by level). -/
abbrev HybridNumber := Nat →₀ ZeckPayload

/-- Lazy hybrid number (finite-support by level). -/
abbrev LazyHybridNumber := Nat →₀ LazyPayload

/-- Per-level semantic value. -/
def levelEval (z : ZeckPayload) : Nat :=
  lazyEvalFib z

/-- Full semantic value of a canonical hybrid number. -/
def eval (X : HybridNumber) : Nat :=
  X.sum (fun i z => levelEval z * weight i)

/-- Full semantic value of a lazy hybrid number. -/
def lazyEval (X : LazyHybridNumber) : Nat :=
  X.sum (fun i z => lazyEvalFib z * weight i)

theorem eval_add (A B : HybridNumber) :
    eval (A + B) = eval A + eval B := by
  classical
  simpa [eval, lazyEvalFib_append, Nat.add_mul, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    (Finsupp.sum_add_index
      (f := A) (g := B)
      (h := fun i z => levelEval z * weight i)
      (h_zero := by
        intro i _
        change levelEval (0 : ZeckPayload) * weight i = 0
        have hz : levelEval (0 : ZeckPayload) = 0 := by
          change (List.map Nat.fib ([] : List Nat)).sum = 0
          simp
        calc
          levelEval (0 : ZeckPayload) * weight i = 0 * weight i := by rw [hz]
          _ = 0 := Nat.zero_mul _)
      (h_add := by
        intro i _ z₁ z₂
        change levelEval (z₁ ++ z₂) * weight i =
          levelEval z₁ * weight i + levelEval z₂ * weight i
        rw [show levelEval (z₁ ++ z₂) = levelEval z₁ + levelEval z₂ by
              simpa [levelEval] using lazyEvalFib_append z₁ z₂]
        rw [Nat.add_mul]))

/-- Embed a natural number as a single-level canonical hybrid number. -/
noncomputable def fromNat (n : Nat) : HybridNumber :=
  Finsupp.single 0 (Nat.zeckendorf n)

/-- Canonical to lazy coercion (same concrete representation in this phase). -/
def toLazy (X : HybridNumber) : LazyHybridNumber :=
  X

@[simp] theorem eval_single (i : Nat) (z : ZeckPayload) :
    eval (Finsupp.single i z) = levelEval z * weight i := by
  simpa [eval] using
    (Finsupp.sum_single_index (a := i) (b := z) (h := fun j z => levelEval z * weight j)
      (by
        change levelEval (0 : ZeckPayload) * weight i = 0
        have h0 : levelEval (0 : ZeckPayload) = 0 := by
          change (List.map Nat.fib ([] : List Nat)).sum = 0
          simp
        calc
          levelEval (0 : ZeckPayload) * weight i = 0 * weight i := by rw [h0]
          _ = 0 := Nat.zero_mul _))

@[simp] theorem lazyEval_single (i : Nat) (z : LazyPayload) :
    lazyEval (Finsupp.single i z) = lazyEvalFib z * weight i := by
  simpa [lazyEval] using
    (Finsupp.sum_single_index (a := i) (b := z) (h := fun j z => lazyEvalFib z * weight j)
      (by
        change lazyEvalFib (0 : LazyPayload) * weight i = 0
        have h0 : lazyEvalFib (0 : LazyPayload) = 0 := by
          change (List.map Nat.fib ([] : List Nat)).sum = 0
          simp
        calc
          lazyEvalFib (0 : LazyPayload) * weight i = 0 * weight i := by rw [h0]
          _ = 0 := Nat.zero_mul _))

@[simp] theorem lazyEval_toLazy (X : HybridNumber) :
    lazyEval (toLazy X) = eval X := by
  rfl

@[simp] theorem eval_fromNat (n : Nat) :
    eval (fromNat n) = n := by
  calc
    eval (fromNat n) = levelEval (Nat.zeckendorf n) * weight 0 := by
      simp [fromNat]
    _ = ((Nat.zeckendorf n).map Nat.fib).sum := by
      simp [levelEval, lazyEvalFib, weight]
    _ = n := Nat.sum_zeckendorf_fib n

@[simp] theorem lazyEval_fromNat (n : Nat) :
    lazyEval (fromNat n) = n := by
  calc
    lazyEval (fromNat n) = lazyEvalFib (Nat.zeckendorf n) * weight 0 := by
      simp [fromNat]
    _ = ((Nat.zeckendorf n).map Nat.fib).sum := by
      simp [lazyEvalFib, weight]
    _ = n := Nat.sum_zeckendorf_fib n

example : eval (fromNat 123456789) = 123456789 := by
  simp

end HeytingLean.Bridge.Veselov.HybridZeckendorf
