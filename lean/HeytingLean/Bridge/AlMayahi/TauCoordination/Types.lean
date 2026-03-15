import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Bridge.AlMayahi.TauCoordination.Types

Core types for the τ-coordination formalization.

Paper references:
- OpenCLAW-P2P v4, Section 3 (verification state, claim graph)
- OpenCLAW-P2P v4, Section 10.1 (τ, clock time, protocol selector)
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

/-- Internal time coordinate of an agent, constrained to `ℝ≥0`. -/
structure Tau where
  val : ℝ
  nonneg : 0 ≤ val

/-- External clock time, constrained to `ℝ≥0`. -/
structure ClockTime where
  val : ℝ
  nonneg : 0 ≤ val

/-- Clock-rate field `χ = dt/dτ` (paper Eq. 2 notation). -/
noncomputable def clockRateField (dt : ClockTime) (dτ : Tau) : ℝ :=
  dt.val / dτ.val

theorem clockRateField_nonneg
    (dt : ClockTime) (dτ : Tau) (hτ : 0 < dτ.val) :
    0 ≤ clockRateField dt dτ := by
  unfold clockRateField
  exact div_nonneg dt.nonneg (le_of_lt hτ)

/-- Verification state of a claim (paper Section 3.3). -/
inductive VerificationState
  | proposed
  | underVerification
  | verified
  | refuted
  | deprecated
  deriving DecidableEq, Repr

/-- Knowledge claim in the claim graph (paper Section 3.1). -/
structure KnowledgeClaim where
  id : Nat
  state : VerificationState
  verifications : Nat
  dependencies : List Nat
  deriving Repr

/-- Coordination protocol selector. -/
inductive Protocol
  | clockBased
  | tauNormalized
  deriving DecidableEq, Repr

/-- Float helper mirroring `clockRateField` for reproducibility checks. -/
def floatClockRateField (dt dτ : Float) : Float :=
  dt / dτ

#eval ("clock-rate-smoke", floatClockRateField 10.0 5.0)

end HeytingLean.Bridge.AlMayahi.TauCoordination
