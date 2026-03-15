import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauCoordination.ConsensusQuality

/-!
# Bridge.AlMayahi.TauCoordination.Propositions

Qualitative guarantees corresponding to paper Section 9 (+ Proposition 6 in Section 10.2).
-/

namespace HeytingLean.Bridge.AlMayahi.TauCoordination

noncomputable section

/-- Proposition 1 (definitional): under τ-coordination, participation is `1/n`. -/
theorem progress_fairness (net : AgentNetwork) :
    ∀ i : Fin net.n, tauWeight net i = uniformWeight net := by
  intro i
  rfl

/-- Expected gain for unsupported claims at step `k`. -/
def unsupportedClaimGain (reward : ℝ) (pUnsupportedAccepted : ℕ → ℝ) (k : ℕ) : ℝ :=
  reward * pUnsupportedAccepted k

/-- Elementary convergence-to-zero predicate over `ℕ`-indexed real sequences. -/
def ConvergesToZero (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |f n| < ε

/-- Proposition 2: if acceptance probability of unsupported claims converges to zero,
their expected gain converges to zero. -/
theorem spam_resistance
    (reward : ℝ)
    (rewardBound : ℝ)
    (pUnsupportedAccepted : ℕ → ℝ)
    (hBoundPos : 0 < rewardBound)
    (hReward : |reward| ≤ rewardBound)
    (hDecay : ConvergesToZero pUnsupportedAccepted) :
    ConvergesToZero (unsupportedClaimGain reward pUnsupportedAccepted) := by
  intro ε hε
  rcases hDecay (ε / rewardBound) (div_pos hε hBoundPos) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hp : |pUnsupportedAccepted n| < ε / rewardBound := hN n hn
  have hmul_le :
      |reward * pUnsupportedAccepted n| ≤ rewardBound * |pUnsupportedAccepted n| := by
    calc
      |reward * pUnsupportedAccepted n|
          = |reward| * |pUnsupportedAccepted n| := by simp [abs_mul]
      _ ≤ rewardBound * |pUnsupportedAccepted n| := by
            exact mul_le_mul_of_nonneg_right hReward (abs_nonneg _)
  have hbound_lt :
      rewardBound * |pUnsupportedAccepted n| < rewardBound * (ε / rewardBound) := by
    exact mul_lt_mul_of_pos_left hp hBoundPos
  have hbound_eval : rewardBound * (ε / rewardBound) = ε := by
    field_simp [hBoundPos.ne']
  exact lt_of_le_of_lt hmul_le (by simpa [hbound_eval] using hbound_lt)

/-- Verification ratio used in Proposition 3 statements. -/
def verificationRatioNat (verified proposed : ℕ) : ℝ :=
  (verified : ℝ) / (max proposed 1 : ℝ)

/-- Proposition 3: adding successful verification work cannot decrease stability ratio. -/
  theorem verification_stability
    (verified proposed : ℕ) (θ : ℝ)
    (hStable : θ ≤ verificationRatioNat verified proposed) :
    θ ≤ verificationRatioNat (verified + 1) proposed := by
  have hDenPos : 0 < (max proposed 1 : ℝ) := by
    have hOne : (1 : ℕ) ≤ max proposed 1 := Nat.le_max_right proposed 1
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (show (1 : ℝ) ≤ (max proposed 1 : ℝ) by exact_mod_cast hOne))
  have hMono :
      verificationRatioNat verified proposed ≤ verificationRatioNat (verified + 1) proposed := by
    unfold verificationRatioNat
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast (Nat.le_succ verified))
      (le_of_lt hDenPos)
  exact le_trans hStable hMono

/-- Critical Byzantine threshold (Supplementary S1.4). -/
def alphaCrit (m : ℝ) : ℝ :=
  (m - 1) / (2 * m - 1)

def alphaCritM3 : ℝ := alphaCrit 3

theorem alphaCritM3_eq : alphaCritM3 = (2 : ℝ) / 5 := by
  norm_num [alphaCritM3, alphaCrit]

/-- Proposition 4 (arithmetic specialization): for `m = 3`, `α_crit = 2/5`. -/
theorem adversarial_resilience (α : ℝ) (hα : α < alphaCritM3) : α < (2 : ℝ) / 5 := by
  simpa [alphaCritM3_eq] using hα

/-- Proposition 5 (Nat monotonicity helper): `verified - refuted ≤ verified`. -/
theorem monotonic_knowledge_growth (verified refuted : Nat) :
    verified - refuted ≤ verified := by
  exact Nat.sub_le _ _

/-- Proposition 6 (definitional): τ-fairness is independent of throughput values. -/
theorem progress_fairness_heterogeneous (net : AgentNetwork) :
    ∀ i : Fin net.n, tauWeight net i = 1 / (net.n : ℝ) := by
  intro i
  rfl

#eval ("alpha_crit_m3", (2.0 : Float) / 5.0)

end
