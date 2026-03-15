import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.TauConsensusLimit

/-!
# Bridge.AlMayahi.TauCoordination.Corollaries

Corollaries from Theorem 1 and Theorem 2 (paper Sections 10-11).
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

noncomputable section

/-- Corollary 1 (named re-export of `tau_quality_geq`). -/
abbrev mift_steady_state
    (net : AgentNetwork)
    (hA1 : A1 net)
    (hIndep : QualityIndependentOfThroughput net) :
    expectedConsensusQuality net .tauNormalized ≥
      expectedConsensusQuality net .clockBased := by
  exact tau_quality_geq net hA1 hIndep

/-- Corollary 2 (named re-export of `tau_convergence`). -/
abbrev reputation_converges_to_quality
    (nets : ℕ → AgentNetwork)
    (hAssump : TauConsensusLimitAssumptions nets) :
    ConvergesAS (fun k => consensusQuality (nets k) .tauNormalized)
      hAssump.moments.meanQualityLimit := by
  exact tau_convergence nets hAssump

/-- Corollary 3 (named re-export of `tau_bias_leq`). -/
abbrev tau_minimizes_bias (net : AgentNetwork) (hA1 : A1 net) :
    consensusBias net .tauNormalized ≤ consensusBias net .clockBased := by
  exact tau_bias_leq net hA1

/-- Critical network size from paper Section 11.4 (`n* = rho / (muL * eps)`). -/
def criticalNetworkSize (rho muL eps : ℝ) : Nat :=
  Nat.ceil (rho / (muL * eps))

theorem criticalNetworkSize_nonneg (rho muL eps : ℝ) :
    0 ≤ criticalNetworkSize rho muL eps := by
  exact Nat.zero_le _

/-- Corollary 4 (phase-transition inequality form). -/
theorem phase_transition
    (rho muL eps n : ℝ)
    (hMu : 0 < muL)
    (hEps : 0 < eps)
    (hn : n > rho / (muL * eps)) :
    n * eps > rho / muL := by
  have hMulPos : 0 < muL * eps := mul_pos hMu hEps
  have hdiv : rho / (muL * eps) < n := hn
  have hmul : rho < n * (muL * eps) := (div_lt_iff₀ hMulPos).1 hdiv
  have hmul' : rho < (n * eps) * muL := by
    nlinarith [hmul]
  have hfinal : rho / muL < n * eps := (div_lt_iff₀ hMu).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul')
  simpa [gt_iff_lt] using hfinal

/-- Corollary 5 (definitional identity): the clock precision floor is `rho / muL`. -/
theorem clock_precision_ceiling (rho muL : ℝ) :
    precisionFloor rho muL = rho / muL := by
  rfl

/-- Corollary 6 (arithmetic positivity helper): `1/eps^2` is positive for `eps > 0`. -/
theorem universal_scaling_law (eps : ℝ) (hEps : 0 < eps) :
    0 < 1 / (eps ^ 2) := by
  have hsq : 0 < eps ^ 2 := by nlinarith
  exact one_div_pos.mpr hsq

end
