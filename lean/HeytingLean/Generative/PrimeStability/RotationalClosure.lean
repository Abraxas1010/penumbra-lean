import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Order.Irreducible
import HeytingLean.Core.Nucleus
import HeytingLean.Generative.UDPGeometry

/-!
# Generative.PrimeStability.RotationalClosure

Core periodic-orbit definitions for the prime-stability project.

The key choice is to define the closure period by `Function.minimalPeriod`, so
all later stability theorems are forced to talk about genuine minimal
recurrence rather than an arbitrary witness period.
-/

namespace HeytingLean.Generative.PrimeStability

/-- A rotational closure is a pointed dynamical system whose basepoint is
genuinely periodic. -/
structure RotationalClosure (α : Type*) where
  /-- One-step internal evolution. -/
  F : α → α
  /-- Distinguished basepoint on the orbit. -/
  x₀ : α
  /-- The basepoint lies on a periodic orbit. -/
  periodic_mem : x₀ ∈ Function.periodicPts F

namespace RotationalClosure

/-- The closure period is the minimal period of the distinguished basepoint. -/
noncomputable def period {α : Type*} (rc : RotationalClosure α) : ℕ :=
  Function.minimalPeriod rc.F rc.x₀

/-- The distinguished basepoint is periodic at its minimal period. -/
theorem periodic {α : Type*} (rc : RotationalClosure α) :
    Function.IsPeriodicPt rc.F rc.period rc.x₀ := by
  simpa [period] using Function.isPeriodicPt_minimalPeriod rc.F rc.x₀

/-- A genuine rotational closure has positive minimal period. -/
theorem period_pos {α : Type*} (rc : RotationalClosure α) :
    0 < rc.period := by
  simpa [period] using Function.minimalPeriod_pos_of_mem_periodicPts rc.periodic_mem

/-- The minimal period is at least `1`. -/
theorem one_le_period {α : Type*} (rc : RotationalClosure α) :
    1 ≤ rc.period :=
  Nat.succ_le_of_lt rc.period_pos

end RotationalClosure

/-- Prime-period closures are the irreducible/stable ones. -/
def IrreducibleClosure {α : Type*} (rc : RotationalClosure α) : Prop :=
  Nat.Prime rc.period

/-- Composite-period closures are the decomposable/unstable ones. -/
def CompositeClosure {α : Type*} (rc : RotationalClosure α) : Prop :=
  1 < rc.period ∧ ¬ Nat.Prime rc.period

/-- Period `1` is the identity/massless regime. -/
def IdentityClosure {α : Type*} (rc : RotationalClosure α) : Prop :=
  rc.period = 1

/-- Trapped asymmetry is the structural regime `period > 1`. -/
def hasTrappedAsymmetry {α : Type*} (rc : RotationalClosure α) : Prop :=
  1 < rc.period

/-- A proper sub-cycle witnesses decomposability of the parent closure. -/
structure SubClosure {α : Type*} (rc : RotationalClosure α) where
  /-- Proper divisor period of the parent orbit. -/
  subPeriod : ℕ
  /-- The sub-period is nontrivial. -/
  subPeriod_gt_one : 1 < subPeriod
  /-- The sub-period divides the parent period. -/
  divides : subPeriod ∣ rc.period
  /-- The sub-period is strictly smaller than the parent period. -/
  strict : subPeriod < rc.period

/-- A closure is decomposable iff it admits a proper sub-cycle witness. -/
def Decomposable {α : Type*} (rc : RotationalClosure α) : Prop :=
  Nonempty (SubClosure rc)

theorem identityClosure_iff_period_one {α : Type*} (rc : RotationalClosure α) :
    IdentityClosure rc ↔ rc.period = 1 :=
  Iff.rfl

theorem trappedAsymmetry_iff_period_gt_one {α : Type*} (rc : RotationalClosure α) :
    hasTrappedAsymmetry rc ↔ 1 < rc.period :=
  Iff.rfl

end HeytingLean.Generative.PrimeStability
