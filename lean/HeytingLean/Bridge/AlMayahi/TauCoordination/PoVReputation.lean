import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.StabilityInvariant
import HeytingLean.Bridge.AlMayahi.TauCoordination.AgentModel

/-!
# Bridge.AlMayahi.TauCoordination.PoVReputation

Proof-of-Verification reputation dynamics (paper Section 6, Eq. 6 / Appendix B).
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

noncomputable section

/-- Reputation update coefficients (`α, β, γ > 0`). -/
structure ReputationParams where
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  alpha_pos : 0 < alpha
  beta_pos : 0 < beta
  gamma_pos : 0 < gamma

/-- Reputation update rule (paper Eq. 6, expanded Eq. B.1). -/
def reputationUpdate
    (params : ReputationParams)
    (currentRep : ℝ)
    (verified failed refutedDownstream : Nat) : ℝ :=
  currentRep
    + params.alpha * (verified : ℝ)
    - params.beta * (failed : ℝ)
    - params.gamma * (refutedDownstream : ℝ) * currentRep

theorem reputationUpdate_monotone_verified
    (params : ReputationParams)
    (currentRep : ℝ)
    (failed refutedDownstream : Nat)
    {v₁ v₂ : Nat}
    (hv : v₁ ≤ v₂) :
    reputationUpdate params currentRep v₁ failed refutedDownstream
      ≤ reputationUpdate params currentRep v₂ failed refutedDownstream := by
  unfold reputationUpdate
  have hv' : (v₁ : ℝ) ≤ (v₂ : ℝ) := by exact_mod_cast hv
  nlinarith [params.alpha_pos, hv']

/-- Stationary reputation (paper Eq. B.2). -/
def stationaryReputation (params : ReputationParams) (p_v p_f : ℝ) : ℝ :=
  (params.alpha / params.beta) * (p_v / p_f)

/-- Definitional identity for the stationary-reputation closed form (Eq. B.2). -/
theorem reputation_equilibrium
    (params : ReputationParams)
    (p_v p_f : ℝ)
    (_h_pv : 0 < p_v)
    (_h_pf : 0 < p_f) :
    stationaryReputation params p_v p_f =
      (params.alpha / params.beta) * (p_v / p_f) := by
  rfl

/-- Weighted support of a claim from the verified votes. -/
def acceptedWeight {n : Nat} (agents : List (Agent n × Bool)) : ℝ :=
  ((agents.filter (fun a => a.2)).map (fun a => a.1.reputation)).sum

/-- Claim acceptance threshold (paper Eq. 7 schematic). -/
def claimAccepted {n : Nat} (agents : List (Agent n × Bool)) (threshold : ℝ) : Prop :=
  acceptedWeight agents ≥ threshold

theorem claimAccepted_of_lower_threshold
    {n : Nat}
    (agents : List (Agent n × Bool))
    {θ₁ θ₂ : ℝ}
    (h : θ₁ ≤ θ₂)
    (hAccepted : claimAccepted agents θ₂) :
    claimAccepted agents θ₁ := by
  unfold claimAccepted at *
  exact le_trans h hAccepted

/-- Float helper for runtime reputation updates. -/
def floatReputationUpdate
    (alpha beta gamma currentRep : Float)
    (verified failed refutedDownstream : Nat) : Float :=
  currentRep
    + alpha * Float.ofNat verified
    - beta * Float.ofNat failed
    - gamma * Float.ofNat refutedDownstream * currentRep

#eval ("reputation-update-smoke", floatReputationUpdate 0.2 0.1 0.05 4.0 3 1 0)

end
