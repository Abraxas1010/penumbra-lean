import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.AgentModel
import HeytingLean.Bridge.AlMayahi.TauEpoch.Stats

/-!
# Bridge.AlMayahi.TauCoordination.ConsensusQuality

Consensus quality and consensus bias definitions from OpenCLAW-P2P v4:
- Eq. 11: `Q(Π)` (protocol-weighted quality)
- Eq. 12: `B(Π)` (L² distance from uniform participation)
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

open scoped BigOperators

noncomputable section

/-- Uniform target weight `1/n`. -/
def uniformWeight (net : AgentNetwork) : ℝ :=
  1 / (net.n : ℝ)

/-- Clock-protocol participation weight `ωᵢ(Π_t) = λᵢ / Λ`. -/
def clockWeight (net : AgentNetwork) (i : Fin net.n) : ℝ :=
  (net.agents i).throughput / totalThroughput net

/-- τ-protocol idealized weight `ωᵢ(Π_τ) = 1/n`. -/
def tauWeight (net : AgentNetwork) (_i : Fin net.n) : ℝ :=
  uniformWeight net

/-- Protocol-indexed weight function. -/
def protocolWeight (net : AgentNetwork) (protocol : Protocol) : Fin net.n → ℝ :=
  match protocol with
  | .clockBased => clockWeight net
  | .tauNormalized => tauWeight net

theorem clockWeight_nonneg (net : AgentNetwork) (i : Fin net.n) :
    0 ≤ clockWeight net i := by
  unfold clockWeight
  exact div_nonneg (le_of_lt (net.agents i).throughput_pos) (le_of_lt (totalThroughput_pos net))

theorem tauWeight_nonneg (net : AgentNetwork) (i : Fin net.n) :
    0 ≤ tauWeight net i := by
  unfold tauWeight uniformWeight
  exact div_nonneg (by norm_num) (Nat.cast_nonneg net.n)

theorem clockWeight_sum (net : AgentNetwork) :
    (∑ i : Fin net.n, clockWeight net i) = 1 := by
  have htot : totalThroughput net ≠ 0 := ne_of_gt (totalThroughput_pos net)
  calc
    (∑ i : Fin net.n, clockWeight net i)
        = (∑ i : Fin net.n, (net.agents i).throughput / totalThroughput net) := by
          simp [clockWeight]
    _ = (∑ i : Fin net.n, (net.agents i).throughput) / totalThroughput net := by
          simp [Finset.sum_div]
    _ = totalThroughput net / totalThroughput net := by
          simp [totalThroughput, throughputVec]
    _ = 1 := by field_simp [htot]

theorem tauWeight_sum (net : AgentNetwork) :
    (∑ i : Fin net.n, tauWeight net i) = 1 := by
  have hn : (net.n : ℝ) ≠ 0 := by exact_mod_cast net.n_pos.ne'
  calc
    (∑ i : Fin net.n, tauWeight net i)
        = (net.n : ℝ) * uniformWeight net := by
          simp [tauWeight, uniformWeight, Finset.sum_const, Finset.card_univ]
    _ = (net.n : ℝ) * (1 / (net.n : ℝ)) := by rfl
    _ = 1 := by field_simp [hn]

/-- Numerator from Eq. 11. -/
def consensusNumerator (net : AgentNetwork) (protocol : Protocol) : ℝ :=
  ∑ i : Fin net.n, protocolWeight net protocol i * (net.agents i).quality

/-- Denominator from Eq. 11. -/
def consensusDenominator (net : AgentNetwork) (protocol : Protocol) : ℝ :=
  ∑ i : Fin net.n, protocolWeight net protocol i

/-- Consensus quality (paper Eq. 11). -/
def consensusQuality (net : AgentNetwork) (protocol : Protocol) : ℝ :=
  consensusNumerator net protocol / consensusDenominator net protocol

/-- Consensus bias (paper Eq. 12). -/
def consensusBias (net : AgentNetwork) (protocol : Protocol) : ℝ :=
  ∑ i : Fin net.n, (protocolWeight net protocol i - uniformWeight net) ^ 2

theorem consensusDenominator_pos (net : AgentNetwork) (protocol : Protocol) :
    0 < consensusDenominator net protocol := by
  cases protocol <;> simp [consensusDenominator, protocolWeight, clockWeight_sum, tauWeight_sum]

theorem consensusQuality_unit_interval (net : AgentNetwork) (protocol : Protocol) :
    0 ≤ consensusQuality net protocol ∧ consensusQuality net protocol ≤ 1 := by
  let num := consensusNumerator net protocol
  let den := consensusDenominator net protocol
  have hden : 0 < den := by
    simpa [den] using consensusDenominator_pos net protocol
  have hnum_nonneg : 0 ≤ num := by
    unfold num consensusNumerator
    refine Finset.sum_nonneg ?_
    intro i _
    exact mul_nonneg
      (by
        cases protocol <;>
          simp [protocolWeight, clockWeight_nonneg, tauWeight_nonneg])
      (net.agents i).quality_unit.1
  have hnum_le_den : num ≤ den := by
    unfold num den consensusNumerator consensusDenominator
    refine Finset.sum_le_sum ?_
    intro i _
    have hw_nonneg : 0 ≤ protocolWeight net protocol i := by
      cases protocol <;> simp [protocolWeight, clockWeight_nonneg, tauWeight_nonneg]
    have hq_le : (net.agents i).quality ≤ 1 := (net.agents i).quality_unit.2
    have : protocolWeight net protocol i * (net.agents i).quality
        ≤ protocolWeight net protocol i * 1 := by
      exact mul_le_mul_of_nonneg_left hq_le hw_nonneg
    simpa using this
  have hlow : 0 ≤ num / den := div_nonneg hnum_nonneg (le_of_lt hden)
  have hupp : num / den ≤ 1 := by
    have hdiv :
        num / den ≤ den / den := div_le_div_of_nonneg_right hnum_le_den (le_of_lt hden)
    simpa [hden.ne'] using hdiv
  exact ⟨
    by simpa [consensusQuality, num, den] using hlow,
    by simpa [consensusQuality, num, den] using hupp
  ⟩

theorem consensusBias_nonneg (net : AgentNetwork) (protocol : Protocol) :
    0 ≤ consensusBias net protocol := by
  unfold consensusBias
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem consensusBias_zero_iff_uniform (net : AgentNetwork) (protocol : Protocol) :
    consensusBias net protocol = 0 ↔
      ∀ i : Fin net.n, protocolWeight net protocol i = uniformWeight net := by
  constructor
  · intro hBias i
    have hTerms :
        ∀ j ∈ (Finset.univ : Finset (Fin net.n)),
          0 ≤ (protocolWeight net protocol j - uniformWeight net) ^ 2 := by
      intro j _
      exact sq_nonneg _
    have hZeroTerms := (Finset.sum_eq_zero_iff_of_nonneg hTerms).1 (by
      simpa [consensusBias] using hBias)
    have hSq : (protocolWeight net protocol i - uniformWeight net) ^ 2 = 0 :=
      hZeroTerms i (Finset.mem_univ i)
    have hSub : protocolWeight net protocol i - uniformWeight net = 0 := by
      nlinarith [hSq]
    exact sub_eq_zero.mp hSub
  · intro hUniform
    unfold consensusBias
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hEq : protocolWeight net protocol i = uniformWeight net := hUniform i
    nlinarith [hEq]

lemma throughput_eq_of_clock_uniform (net : AgentNetwork)
    (hUniform : ∀ i : Fin net.n, clockWeight net i = uniformWeight net) :
    ∀ i j : Fin net.n, (net.agents i).throughput = (net.agents j).throughput := by
  have hTot : totalThroughput net ≠ 0 := ne_of_gt (totalThroughput_pos net)
  intro i j
  have hiDiv : (net.agents i).throughput / totalThroughput net = uniformWeight net := by
    simpa [clockWeight] using hUniform i
  have hjDiv : (net.agents j).throughput / totalThroughput net = uniformWeight net := by
    simpa [clockWeight] using hUniform j
  have hi :
      (net.agents i).throughput = uniformWeight net * totalThroughput net := by
    exact (div_eq_iff hTot).1 hiDiv
  have hj :
      (net.agents j).throughput = uniformWeight net * totalThroughput net := by
    exact (div_eq_iff hTot).1 hjDiv
  linarith

theorem clockBias_pos_of_heterogeneous (net : AgentNetwork) (hA1 : A1 net) :
    0 < consensusBias net .clockBased := by
  have hNonneg : 0 ≤ consensusBias net .clockBased :=
    consensusBias_nonneg net .clockBased
  have hNe : consensusBias net .clockBased ≠ 0 := by
    intro hZero
    have hUniform : ∀ i : Fin net.n, clockWeight net i = uniformWeight net :=
      (consensusBias_zero_iff_uniform net .clockBased).1 hZero
    have hAllEq := throughput_eq_of_clock_uniform net hUniform
    rcases hA1 with ⟨i, j, hNeq⟩
    exact hNeq (hAllEq i j)
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Float helper for Eq. 12 style bias computation. -/
def floatConsensusBias (weights : List Float) : Float :=
  match weights.length with
  | 0 => 0
  | n + 1 =>
      let u := 1.0 / Float.ofNat (n + 1)
      weights.foldl (fun acc w => acc + (w - u) * (w - u)) 0

#eval ("bias-smoke", floatConsensusBias [0.6, 0.3, 0.1])

end
