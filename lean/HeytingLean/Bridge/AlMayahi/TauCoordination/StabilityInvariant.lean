import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.Types

/-!
# Bridge.AlMayahi.TauCoordination.StabilityInvariant

MIFT stability invariant (`K_v / K_p ≥ θ`) from paper Section 8.
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

noncomputable section

/-- Stability state with threshold `θ ∈ (0,1)`. -/
structure StabilityState where
  verified_claims : Nat
  proposed_claims : Nat
  threshold : ℝ
  threshold_unit : 0 < threshold ∧ threshold < 1

/-- Verification ratio `K_v / max(K_p,1)`. -/
def verificationRatio (s : StabilityState) : ℝ :=
  (s.verified_claims : ℝ) / max (s.proposed_claims : ℝ) 1

/-- Stability predicate `K_v/K_p ≥ θ`. -/
def isStable (s : StabilityState) : Prop :=
  verificationRatio s ≥ s.threshold

/-- Corrective actions when the ratio drops below threshold. -/
inductive CorrectionAction
  | prioritizeVerification
  | throttleCheckpoints (rateMultiplier : ℝ)
  | adjustReputationWeights (verificationBoost : ℝ)

/-- MIFT monitor specification policy (paper Section 8.3).
This specification is noncomputable because it branches on `ℝ` predicates. -/
def miftMonitor (s : StabilityState) : List CorrectionAction := by
  classical
  by_cases h : isStable s
  · exact []
  · exact [.prioritizeVerification, .throttleCheckpoints 0.75, .adjustReputationWeights 1.1]

/-- Float helper for runtime monitor checks. -/
def floatVerificationRatio (verified proposed : Nat) : Float :=
  Float.ofNat verified / Float.ofNat (max proposed 1)

/-- Runtime-safe correction action payload in `Float`. -/
inductive RuntimeCorrectionAction
  | prioritizeVerification
  | throttleCheckpoints (rateMultiplier : Float)
  | adjustReputationWeights (verificationBoost : Float)
  deriving Repr

/-- Computable runtime monitor policy over float ratios. -/
def miftMonitorRuntime (verified proposed : Nat) (threshold : Float) :
    List RuntimeCorrectionAction :=
  if floatVerificationRatio verified proposed >= threshold then
    []
  else
    [.prioritizeVerification, .throttleCheckpoints 0.75, .adjustReputationWeights 1.1]

theorem verification_improves_stability
    (s : StabilityState)
    (hStable : isStable s) :
    isStable { s with verified_claims := s.verified_claims + 1 } := by
  have hDenPos : 0 < max (s.proposed_claims : ℝ) 1 := by
    have hOneNat : (1 : ℕ) ≤ max s.proposed_claims 1 := Nat.le_max_right s.proposed_claims 1
    have hOne : (1 : ℝ) ≤ max (s.proposed_claims : ℝ) 1 := by exact_mod_cast hOneNat
    exact lt_of_lt_of_le (by norm_num) hOne
  have hMono :
      verificationRatio s ≤ verificationRatio { s with verified_claims := s.verified_claims + 1 } := by
    unfold verificationRatio
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast Nat.le_succ s.verified_claims)
      (le_of_lt hDenPos)
  exact le_trans hStable hMono

theorem stability_recovery (s : StabilityState) :
    isStable { s with verified_claims := s.verified_claims + s.proposed_claims + 1 } := by
  have hDenPos : 0 < max (s.proposed_claims : ℝ) 1 := by
    have hOneNat : (1 : ℕ) ≤ max s.proposed_claims 1 := Nat.le_max_right s.proposed_claims 1
    have hOne : (1 : ℝ) ≤ max (s.proposed_claims : ℝ) 1 := by exact_mod_cast hOneNat
    exact lt_of_lt_of_le (by norm_num) hOne
  have hNumGeProposed :
      (s.proposed_claims : ℝ) ≤ (s.verified_claims + s.proposed_claims + 1 : Nat) := by
    have hNat : s.proposed_claims ≤ s.verified_claims + s.proposed_claims + 1 := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Nat.le_add_left s.proposed_claims (s.verified_claims + 1))
    exact_mod_cast hNat
  have hNumGeOne : (1 : ℝ) ≤ (s.verified_claims + s.proposed_claims + 1 : Nat) := by
    have hNat : 1 ≤ s.verified_claims + s.proposed_claims + 1 := by
      exact Nat.succ_le_succ (Nat.zero_le (s.verified_claims + s.proposed_claims))
    exact_mod_cast hNat
  have hDenLeNum :
      max (s.proposed_claims : ℝ) 1 ≤ (s.verified_claims + s.proposed_claims + 1 : Nat) := by
    exact max_le hNumGeProposed hNumGeOne
  have hRatioGeOne :
      1 ≤ verificationRatio { s with verified_claims := s.verified_claims + s.proposed_claims + 1 } := by
    unfold verificationRatio
    have hDiv :
        max (s.proposed_claims : ℝ) 1 / max (s.proposed_claims : ℝ) 1
          ≤ ((s.verified_claims + s.proposed_claims + 1 : Nat) : ℝ) /
            max (s.proposed_claims : ℝ) 1 := by
      exact div_le_div_of_nonneg_right hDenLeNum (le_of_lt hDenPos)
    simpa [hDenPos.ne'] using hDiv
  have hθ : s.threshold ≤ 1 := le_of_lt s.threshold_unit.2
  exact le_trans hθ hRatioGeOne

#eval ("mift-ratio-smoke", floatVerificationRatio 7 10)
#eval ("mift-monitor-runtime-smoke", miftMonitorRuntime 2 10 0.6)

end
