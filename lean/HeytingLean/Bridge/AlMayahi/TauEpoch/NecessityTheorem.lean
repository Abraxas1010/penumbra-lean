import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import HeytingLean.Bridge.AlMayahi.TauEpoch.ProjectionLaw
import HeytingLean.Bridge.AlMayahi.TauEpoch.TauProxy

/-!
# Bridge.AlMayahi.TauEpoch.NecessityTheorem

Structural class-exclusion theorem (Sec. 11.4 style):
under A1-A4 style assumptions plus an explicit one-clock mechanism gap,
one-clock frameworks cannot reproduce the observed invariant signature.
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Admissible one-clock framework class. -/
structure OneClockModel where
  localExplanation : DomainKind → Prop
  noSharedVariable : Prop
  /-- Post-hoc tuning of τ-proxies (forbidden by the locked-proxy rule). -/
  proxyTunable : Prop
  /-- Hidden cross-domain calibration channel (forbidden by non-communication). -/
  crossDomainCoupling : Prop

/-- Observed invariant signature across domains. -/
structure InvariantSignature where
  signConsistent : Prop
  tauOrdered : Prop
  scalingLaw : Prop
  crossDomain : Prop
  /-- Domain-level independence for the conservative 6/6 sign bound. -/
  sixDomainIndependent : Prop
  /-- Null probability attached to the directional-recurrence event. -/
  nullSignProb : ℚ

/-- A model generates the signature if it reproduces all observed components
and provides a local explanation in each domain. -/
def generates (M : OneClockModel) (S : InvariantSignature) : Prop :=
  (∀ d : DomainKind, M.localExplanation d) ∧
    S.signConsistent ∧ S.tauOrdered ∧ S.scalingLaw ∧ S.crossDomain

/-- Assumptions used in the structural exclusion argument. -/
structure TwoClockAssumptions where
  a1SignConsistency : ∀ S : InvariantSignature, S.signConsistent
  a2TauOrdered : ∀ S : InvariantSignature, S.tauOrdered
  /-- Locked proxy assignment excludes post-hoc tuning. -/
  a3LockedProxy : ∀ M : OneClockModel, ¬ M.proxyTunable
  /-- Domain non-communication excludes hidden calibration channels. -/
  a4NonCommunication : ∀ M : OneClockModel, M.noSharedVariable → ¬ M.crossDomainCoupling
  /-- Independence implies the conservative 6/6 directional-recurrence null bound. -/
  a5DirectionalNullBound : ∀ S : InvariantSignature,
      S.sixDomainIndependent → S.nullSignProb = (1 : ℚ) / 64
  /-- In one-clock models, matching the signature under this bound requires either
  proxy tuning or hidden cross-domain coupling. -/
  a6OneClockMechanismGap : ∀ M : OneClockModel, ∀ S : InvariantSignature,
      generates M S → S.nullSignProb ≤ (1 : ℚ) / 64 →
        M.proxyTunable ∨ M.crossDomainCoupling

/-- Step 1: Domain locality + non-communication excludes hidden calibration channels. -/
lemma domain_locality_constraint
    (assumptions : TwoClockAssumptions)
    (M : OneClockModel)
    (hNoShared : M.noSharedVariable) :
    ¬ M.crossDomainCoupling :=
  assumptions.a4NonCommunication M hNoShared

/-- Step 2a: conservative six-domain recurrence constant. -/
lemma directional_recurrence_constant : ((1 : ℚ) / 2) ^ 6 = (1 : ℚ) / 64 := by
  norm_num

/-- Step 2b: domain independence induces the null recurrence bound. -/
lemma directional_recurrence_constraint
    (assumptions : TwoClockAssumptions)
    (S : InvariantSignature)
    (hIndep : S.sixDomainIndependent) :
    S.nullSignProb = (1 : ℚ) / 64 :=
  assumptions.a5DirectionalNullBound S hIndep

/-- Step 3: Locked proxy monotonicity excludes one-clock proxy tuning. -/
lemma locked_tau_monotonicity_constraint
    (assumptions : TwoClockAssumptions)
    (M : OneClockModel) :
    ¬ M.proxyTunable :=
  assumptions.a3LockedProxy M

/-- Step 4: No calibration channel in admissible no-shared-variable one-clock models. -/
lemma no_calibration_channel_constraint
    (assumptions : TwoClockAssumptions)
    (M : OneClockModel)
    (hNoShared : M.noSharedVariable) :
    ¬ M.crossDomainCoupling :=
  domain_locality_constraint assumptions M hNoShared

/-- Two-Clock Necessity Theorem (structural class exclusion). -/
  theorem two_clock_necessity
    (assumptions : TwoClockAssumptions)
    (S : InvariantSignature)
    (hIndep : S.sixDomainIndependent) :
    ∀ (M : OneClockModel), M.noSharedVariable → generates M S → False := by
  intro M hNoShared hGenerates
  have hNullEq : S.nullSignProb = (1 : ℚ) / 64 :=
    directional_recurrence_constraint assumptions S hIndep
  have hNullLe : S.nullSignProb ≤ (1 : ℚ) / 64 := by
    simp [hNullEq]
  have hNoTune : ¬ M.proxyTunable :=
    locked_tau_monotonicity_constraint assumptions M
  have hNoChannel : ¬ M.crossDomainCoupling :=
    no_calibration_channel_constraint assumptions M hNoShared
  have hGap : M.proxyTunable ∨ M.crossDomainCoupling :=
    assumptions.a6OneClockMechanismGap M S hGenerates hNullLe
  have _hUseStep2 : ((1 : ℚ) / 2) ^ 6 = (1 : ℚ) / 64 :=
    directional_recurrence_constant
  cases hGap with
  | inl hTune => exact hNoTune hTune
  | inr hChannel => exact hNoChannel hChannel

end HeytingLean.Bridge.AlMayahi.TauEpoch
