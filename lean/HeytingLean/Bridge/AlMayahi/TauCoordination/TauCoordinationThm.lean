import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.Propositions

/-!
# Bridge.AlMayahi.TauCoordination.TauCoordinationThm

Theorem 1 (τ-Coordination Theorem), paper Section 10.2 / Eq. 13.
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

open scoped BigOperators

noncomputable section

/-- Expected consensus quality surface used for theorem statements. -/
def expectedConsensusQuality (net : AgentNetwork) (protocol : Protocol) : ℝ :=
  consensusQuality net protocol

/-- Independence regime used in Theorem 1(i): no throughput-quality covariance. -/
def QualityIndependentOfThroughput (net : AgentNetwork) : Prop :=
  qualityThroughputCov net = 0

lemma tau_quality_eq_mean (net : AgentNetwork) :
    expectedConsensusQuality net .tauNormalized = meanQuality net := by
  have hn : (net.n : ℝ) ≠ 0 := by exact_mod_cast net.n_pos.ne'
  have hden : consensusDenominator net .tauNormalized = 1 := by
    simpa [consensusDenominator, protocolWeight] using tauWeight_sum net
  have hnum :
      consensusNumerator net .tauNormalized
        = (1 / (net.n : ℝ)) * (∑ i : Fin net.n, (net.agents i).quality) := by
    unfold consensusNumerator protocolWeight tauWeight uniformWeight
    simp [Finset.mul_sum]
  rw [expectedConsensusQuality, consensusQuality, hnum, hden, div_one]
  unfold meanQuality HeytingLean.Bridge.AlMayahi.TauEpoch.mean qualityVec
  field_simp [hn]

lemma clock_quality_eq_weighted (net : AgentNetwork) :
    expectedConsensusQuality net .clockBased
      = (∑ i : Fin net.n, (net.agents i).throughput * (net.agents i).quality)
          / totalThroughput net := by
  have htot : totalThroughput net ≠ 0 := ne_of_gt (totalThroughput_pos net)
  unfold expectedConsensusQuality consensusQuality consensusNumerator consensusDenominator protocolWeight
  have hnum :
      (∑ i : Fin net.n, clockWeight net i * (net.agents i).quality)
        = (∑ i : Fin net.n, (net.agents i).throughput * (net.agents i).quality)
            / totalThroughput net := by
    calc
      (∑ i : Fin net.n, clockWeight net i * (net.agents i).quality)
          = (∑ i : Fin net.n, ((net.agents i).throughput * (net.agents i).quality) / totalThroughput net) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            unfold clockWeight
            field_simp [htot]
      _ = (∑ i : Fin net.n, (net.agents i).throughput * (net.agents i).quality) / totalThroughput net := by
            simp [Finset.sum_div]
  rw [hnum]
  simp [clockWeight_sum]

lemma clock_quality_decomposition (net : AgentNetwork) :
    expectedConsensusQuality net .clockBased
      = meanQuality net + qualityThroughputCov net / meanThroughput net := by
  have hClock := clock_quality_eq_weighted net
  have htot : totalThroughput net ≠ 0 := ne_of_gt (totalThroughput_pos net)
  have hn : (net.n : ℝ) ≠ 0 := by exact_mod_cast net.n_pos.ne'
  let s_lq : ℝ := ∑ i : Fin net.n, (net.agents i).throughput * (net.agents i).quality
  let s_l : ℝ := totalThroughput net
  let sq : ℝ := ∑ i : Fin net.n, (net.agents i).quality
  have hClock' : expectedConsensusQuality net .clockBased = s_lq / s_l := by
    simpa [s_lq, s_l] using hClock
  have hs_l : s_l = totalThroughput net := by rfl
  have hMeanQ : meanQuality net = sq / (net.n : ℝ) := by
    simp [meanQuality, HeytingLean.Bridge.AlMayahi.TauEpoch.mean, qualityVec, sq]
  have hMeanT : meanThroughput net = s_l / (net.n : ℝ) := by
    simp [meanThroughput, s_l]
  have hCov :
      qualityThroughputCov net = s_lq / (net.n : ℝ) - (s_l / (net.n : ℝ)) * (sq / (net.n : ℝ)) := by
    simp [qualityThroughputCov, hMeanQ, hMeanT, s_lq, s_l, sq]
  rw [hClock', hMeanQ, hCov, hMeanT]
  rw [← hs_l] at htot
  field_simp [htot, hn]
  ring

/-- Theorem 1(i): τ-quality is at least clock-quality under independence. -/
theorem tau_quality_geq
    (net : AgentNetwork)
    (_hA1 : A1 net)
    (hIndep : QualityIndependentOfThroughput net) :
    expectedConsensusQuality net .tauNormalized ≥
      expectedConsensusQuality net .clockBased := by
  rw [tau_quality_eq_mean, clock_quality_decomposition, QualityIndependentOfThroughput] at *
  simp [hIndep]

/-- Theorem 1(ii): τ-bias is at most clock-bias. -/
theorem tau_bias_leq (net : AgentNetwork) (_hA1 : A1 net) :
    consensusBias net .tauNormalized ≤ consensusBias net .clockBased := by
  have hTauZero : consensusBias net .tauNormalized = 0 := by
    refine (consensusBias_zero_iff_uniform net .tauNormalized).2 ?_
    intro i
    rfl
  have hClockNonneg : 0 ≤ consensusBias net .clockBased :=
    consensusBias_nonneg net .clockBased
  simpa [hTauZero] using hClockNonneg

/-- Equality in Theorem 1(ii) occurs iff heterogeneity is absent. -/
theorem tau_bias_eq_iff_homogeneous (net : AgentNetwork) :
    consensusBias net .tauNormalized = consensusBias net .clockBased ↔ ¬ A1 net := by
  constructor
  · intro hEq hA1
    have hTauZero : consensusBias net .tauNormalized = 0 := by
      refine (consensusBias_zero_iff_uniform net .tauNormalized).2 ?_
      intro i
      rfl
    have hClockZero : consensusBias net .clockBased = 0 := by
      linarith [hEq, hTauZero]
    have hPos : 0 < consensusBias net .clockBased := clockBias_pos_of_heterogeneous net hA1
    linarith
  · intro hNoA1
    have hTauZero : consensusBias net .tauNormalized = 0 := by
      refine (consensusBias_zero_iff_uniform net .tauNormalized).2 ?_
      intro i
      rfl
    have hAllEq :
        ∀ i j : Fin net.n, (net.agents i).throughput = (net.agents j).throughput :=
      (not_A1_iff_all_throughputs_equal net).1 hNoA1
    let i0 : Fin net.n := ⟨0, net.n_pos⟩
    have hsum :
        totalThroughput net = (net.n : ℝ) * (net.agents i0).throughput := by
      unfold totalThroughput
      calc
        (∑ i : Fin net.n, (net.agents i).throughput)
            = ∑ _i : Fin net.n, (net.agents i0).throughput := by
                refine Finset.sum_congr rfl ?_
                intro i _
                exact hAllEq i i0
        _ = (net.n : ℝ) * (net.agents i0).throughput := by
              simp [Finset.sum_const, Finset.card_univ]
    have hClockUniform : ∀ i : Fin net.n, clockWeight net i = uniformWeight net := by
      intro i
      have hEqI : (net.agents i).throughput = (net.agents i0).throughput := hAllEq i i0
      have hti0 : (net.agents i0).throughput ≠ 0 := ne_of_gt (net.agents i0).throughput_pos
      unfold clockWeight uniformWeight
      rw [hEqI, hsum]
      have hn : (net.n : ℝ) ≠ 0 := by exact_mod_cast net.n_pos.ne'
      field_simp [hti0, hn]
    have hClockZero : consensusBias net .clockBased = 0 :=
      (consensusBias_zero_iff_uniform net .clockBased).2 hClockUniform
    linarith

/-- Theorem 1(iii): strict gain formula `Qτ - Qt = nρ/Λ` in the anti-correlated regime. -/
theorem tau_strict_quality_gain
    (net : AgentNetwork)
    (_hA1 : A1 net)
    (hA2Strict : qualityThroughputCov net < 0) :
    expectedConsensusQuality net .tauNormalized -
      expectedConsensusQuality net .clockBased
        = (net.n : ℝ) * rho net / totalThroughput net := by
  have hμ : meanThroughput net ≠ 0 := ne_of_gt (meanThroughput_pos net)
  have htot : totalThroughput net ≠ 0 := ne_of_gt (totalThroughput_pos net)
  have hn : (net.n : ℝ) ≠ 0 := by exact_mod_cast net.n_pos.ne'
  have hAbs : rho net = -qualityThroughputCov net := by
    unfold rho
    simpa using abs_of_neg hA2Strict
  calc
    expectedConsensusQuality net .tauNormalized -
      expectedConsensusQuality net .clockBased
        = meanQuality net - (meanQuality net + qualityThroughputCov net / meanThroughput net) := by
            rw [tau_quality_eq_mean, clock_quality_decomposition]
    _ = -(qualityThroughputCov net / meanThroughput net) := by ring
    _ = (-qualityThroughputCov net) / meanThroughput net := by ring
    _ = rho net / meanThroughput net := by simp [hAbs]
    _ = (net.n : ℝ) * rho net / totalThroughput net := by
      unfold meanThroughput
      field_simp [htot, hn]

/-- Strict positivity of the Theorem 1 gain term under strict A2. -/
theorem tau_quality_gain_pos
    (net : AgentNetwork)
    (_hA1 : A1 net)
    (hA2Strict : qualityThroughputCov net < 0) :
    (net.n : ℝ) * rho net / totalThroughput net > 0 := by
  have hn : 0 < (net.n : ℝ) := by exact_mod_cast net.n_pos
  have hρ : 0 < rho net := by
    unfold rho
    exact abs_pos.mpr (ne_of_lt hA2Strict)
  have hΛ : 0 < totalThroughput net := totalThroughput_pos net
  exact div_pos (mul_pos hn hρ) hΛ

#eval ("quality-gain-smoke", (100.0 : Float) * 0.15 / 50.0)

end
