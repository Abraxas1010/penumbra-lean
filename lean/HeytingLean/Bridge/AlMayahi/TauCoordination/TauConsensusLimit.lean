import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.TauCoordinationThm

/-!
# Bridge.AlMayahi.TauCoordination.TauConsensusLimit

Theorem 2 (τ-Consensus Limit Theorem), paper Section 11.

This file is intentionally **assumption-parameterized**: asymptotic
probability-theory claims are represented as explicit hypotheses, not global
axioms, so downstream results remain logically consistent.
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

noncomputable section

/-- Almost-sure convergence proxy used in theorem statements. -/
def ConvergesAS (f : ℕ → ℝ) (limit : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n - limit| < ε

/-- Sequence-level i.i.d./bounded-moment regularity assumptions. -/
structure IIDDraws (nets : ℕ → AgentNetwork) : Prop where
  throughput_abs_bound :
    ∃ B > 0, ∀ k (i : Fin (nets k).n), |((nets k).agents i).throughput| ≤ B
  quality_abs_bound :
    ∃ B > 0, ∀ k (i : Fin (nets k).n), |((nets k).agents i).quality| ≤ B

/-- Asymptotic moment data used by Theorem 2 and corollaries. -/
structure AsymptoticMoments (nets : ℕ → AgentNetwork) where
  meanQualityLimit : ℝ
  meanThroughputLimit : ℝ
  meanQuality_converges : ConvergesAS (fun k => meanQuality (nets k)) meanQualityLimit
  meanThroughput_converges : ConvergesAS (fun k => meanThroughput (nets k)) meanThroughputLimit
  rhoConst : ℝ
  meanThroughputLimit_pos : 0 < meanThroughputLimit
  rhoConst_nonneg : 0 ≤ rhoConst

/-- Zero asymptotic bias certificate for a protocol class, relative to fixed moments. -/
structure ZeroAsymptoticBias
    (protocol : Protocol)
    (nets : ℕ → AgentNetwork)
    (moments : AsymptoticMoments nets) where
  converges_to_meanQuality :
    ConvergesAS (fun k => consensusQuality (nets k) protocol) moments.meanQualityLimit

/-- Minimum asymptotic variance certificate for a protocol class. -/
structure MinimumVariance (protocol : Protocol) (_nets : ℕ → AgentNetwork) where
  asymptoticVariance : Protocol → ℝ
  variance_nonneg : ∀ p, 0 ≤ asymptoticVariance p
  variance_minimal : ∀ p, asymptoticVariance protocol ≤ asymptoticVariance p

/-- External theorem-package assumptions for Theorem 2 statements.
These assumptions are local hypotheses (not global axioms). -/
structure TauConsensusLimitAssumptions (nets : ℕ → AgentNetwork) where
  moments : AsymptoticMoments nets
  iid : IIDDraws nets
  covariance_model : ∀ k, qualityThroughputCov (nets k) = -moments.rhoConst
  rhoConst_pos : 0 < moments.rhoConst
  tau_converges :
    ConvergesAS (fun k => consensusQuality (nets k) .tauNormalized) moments.meanQualityLimit
  clock_converges :
    ConvergesAS (fun k => consensusQuality (nets k) .clockBased)
      (moments.meanQualityLimit - moments.rhoConst / moments.meanThroughputLimit)

/-- Uniqueness of limits for the epsilon-`N` convergence predicate `ConvergesAS`. -/
theorem convergesAS_unique
    {f : ℕ → ℝ}
    {a b : ℝ}
    (ha : ConvergesAS f a)
    (hb : ConvergesAS f b) :
    a = b := by
  by_contra hne
  let ε : ℝ := |a - b| / 2
  have hε : 0 < ε := by
    dsimp [ε]
    exact half_pos (abs_pos.mpr (sub_ne_zero.mpr hne))
  rcases ha ε hε with ⟨Na, hNa⟩
  rcases hb ε hε with ⟨Nb, hNb⟩
  let N := max Na Nb
  have hA : |f N - a| < ε := hNa N (le_max_left _ _)
  have hB : |f N - b| < ε := hNb N (le_max_right _ _)
  have hA' : |a - f N| < ε := by simpa [abs_sub_comm] using hA
  have hTri : |a - b| ≤ |a - f N| + |f N - b| := by
    calc
      |a - b| = |(a - f N) + (f N - b)| := by ring_nf
      _ ≤ |a - f N| + |f N - b| := abs_add_le _ _
  have hLt : |a - b| < ε + ε := by
    exact lt_of_le_of_lt hTri (add_lt_add hA' hB)
  have hEq : ε + ε = |a - b| := by
    dsimp [ε]
    ring
  have hContr : |a - b| < |a - b| := by
    calc
      |a - b| < ε + ε := hLt
      _ = |a - b| := hEq
  exact (lt_irrefl (|a - b|)) hContr

/-- Theorem 2(i): `Q(Π_τ)` converges to `μ_q`. -/
theorem tau_convergence
    (nets : ℕ → AgentNetwork)
    (hAssump : TauConsensusLimitAssumptions nets) :
    ConvergesAS (fun k => consensusQuality (nets k) .tauNormalized)
      hAssump.moments.meanQualityLimit := by
  exact hAssump.tau_converges

/-- Theorem 2(ii): clock coordination converges to a biased limit. -/
theorem persistent_clock_bias
    (nets : ℕ → AgentNetwork)
    (hAssump : TauConsensusLimitAssumptions nets) :
    ConvergesAS (fun k => consensusQuality (nets k) .clockBased)
      (hAssump.moments.meanQualityLimit
        - hAssump.moments.rhoConst / hAssump.moments.meanThroughputLimit) := by
  exact hAssump.clock_converges

/-- Precision floor `ε* = ρ/μ_λ`. -/
def precisionFloor (rho muL : ℝ) : ℝ := rho / muL

theorem precision_floor_pos (rho muL : ℝ) (hRho : 0 < rho) (hMu : 0 < muL) :
    precisionFloor rho muL > 0 := by
  unfold precisionFloor
  exact div_pos hRho hMu

/-- Theorem 2(iii): `Π_τ` is uniquely asymptotically optimal.
This is derived from:
1. zero-bias convergence for the candidate protocol,
2. strict persistent clock bias (`rhoConst_pos`), and
3. uniqueness of sequence limits (not by a direct "unique optimality" axiom). -/
theorem tau_asymptotic_optimality
    (nets : ℕ → AgentNetwork)
    (hAssump : TauConsensusLimitAssumptions nets)
    (protocol : Protocol)
    (hZeroBias : ZeroAsymptoticBias protocol nets hAssump.moments)
    (_hMinVar : MinimumVariance protocol nets) :
    protocol = .tauNormalized := by
  cases protocol with
  | tauNormalized =>
      rfl
  | clockBased =>
      exfalso
      have hClockToMean :
          ConvergesAS
            (fun k => consensusQuality (nets k) .clockBased)
            hAssump.moments.meanQualityLimit := by
        simpa using hZeroBias.converges_to_meanQuality
      have hLimitsEq :
          hAssump.moments.meanQualityLimit =
            hAssump.moments.meanQualityLimit
              - hAssump.moments.rhoConst / hAssump.moments.meanThroughputLimit := by
        exact convergesAS_unique hClockToMean hAssump.clock_converges
      have hDivZero : hAssump.moments.rhoConst / hAssump.moments.meanThroughputLimit = 0 := by
        linarith [hLimitsEq]
      have hMuNe : hAssump.moments.meanThroughputLimit ≠ 0 := by
        exact ne_of_gt hAssump.moments.meanThroughputLimit_pos
      have hRhoZero : hAssump.moments.rhoConst = 0 := by
        have hMulZero :=
          congrArg (fun x => x * hAssump.moments.meanThroughputLimit) hDivZero
        field_simp [hMuNe] at hMulZero
        simpa using hMulZero
      exact (ne_of_gt hAssump.rhoConst_pos) hRhoZero

#eval ("precision-floor-smoke", (0.15 : Float) / 0.75)

end
