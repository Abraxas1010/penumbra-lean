import HeytingLean.Bridge.AlMayahi.TauEpoch.NecessityTheorem
import HeytingLean.Bridge.AlMayahi.TauEpoch.Predictions
import HeytingLean.Bridge.AlMayahi.TauEpoch.TauProxy

/-!
# Bridge.AlMayahi.UDTSynthesis.FalsifiabilityPredicates

Upgrade the existing `Predictions.lean` from String-based falsifiability to
Prop-based formal falsifiability predicates, per UDT paper Section 4,
Appendix F, and Section 7.1.

The key structural insight: a null result in prediction P falsifies only
P's mechanism level, not the full UDT programme. Different predictions
operate at different mechanism levels (ontological, temporal, reconstruction,
empirical_risk), and falsification at one level does not propagate to others.
-/

namespace HeytingLean.Bridge.AlMayahi.UDTSynthesis

open HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Mechanism level at which a prediction operates. Different levels
are independently falsifiable. -/
inductive MechanismLevel
  | ontological      -- clock asymmetry exists at all
  | temporal         -- specific two-clock temporal structure
  | reconstruction   -- τ can be reconstructed from t-measurements
  | empirical_risk   -- specific observable thresholds are met
  deriving DecidableEq, Repr

/-- Formal prediction with Prop-based pass/falsification criteria. -/
structure FormalPrediction where
  id : String
  domain : DomainKind
  description : String
  mechanismLevel : MechanismLevel
  /-- Proposition that is true when the prediction passes. -/
  passCriterion : Prop
  /-- Proposition that is true when the prediction is falsified. -/
  falsificationCondition : Prop

/-- Two predictions at different mechanism levels are independently falsifiable:
falsification of one cannot logically entail falsification of the other
(without additional bridging assumptions). This is formalized as the statement
that the mechanism levels are distinct.

This is weaker than full logical independence (which would require a model)
but captures the key structural property: the UDT programme survives
individual prediction failures at specific mechanism levels. -/
def mechanismIndependent (P Q : FormalPrediction) : Prop :=
  P.mechanismLevel ≠ Q.mechanismLevel

/-- Mechanism independence is symmetric. -/
theorem mechanismIndependent_symm {P Q : FormalPrediction}
    (h : mechanismIndependent P Q) :
    mechanismIndependent Q P :=
  Ne.symm h

/-- Mechanism independence is irreflexive. -/
theorem not_mechanismIndependent_self (P : FormalPrediction) :
    ¬ mechanismIndependent P P := by
  simp [mechanismIndependent]

/-- All four mechanism levels are distinct. -/
theorem mechanism_levels_distinct :
    MechanismLevel.ontological ≠ MechanismLevel.temporal ∧
    MechanismLevel.ontological ≠ MechanismLevel.reconstruction ∧
    MechanismLevel.ontological ≠ MechanismLevel.empirical_risk ∧
    MechanismLevel.temporal ≠ MechanismLevel.reconstruction ∧
    MechanismLevel.temporal ≠ MechanismLevel.empirical_risk ∧
    MechanismLevel.reconstruction ≠ MechanismLevel.empirical_risk := by
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Discriminator record: a specific experimental test that can falsify
at a given mechanism level. From UDT Appendix F. -/
structure Discriminator where
  id : String
  description : String
  mechanismLevel : MechanismLevel
  /-- The observable quantity to test. -/
  observable : String

/-- The five experimental discriminators from UDT Appendix F. -/
def discriminatorD1 : Discriminator :=
  { id := "D1"
    description := "Sign-recurrence directional test (6-domain, locked τ-proxy)"
    mechanismLevel := .temporal
    observable := "sign consistency across 6 domains at p < 1/64" }

def discriminatorD2 : Discriminator :=
  { id := "D2"
    description := "LHC Run-3/4 κ-offset persistence"
    mechanismLevel := .empirical_risk
    observable := "all Δκ_i > 0 across channels" }

def discriminatorD3 : Discriminator :=
  { id := "D3"
    description := "Proton radius method ordering"
    mechanismLevel := .reconstruction
    observable := "Pearson r(log₁₀ τ_proxy, r_p) > 0.4 at p < 0.10" }

def discriminatorD4 : Discriminator :=
  { id := "D4"
    description := "Neutron lifetime bottle-vs-beam stratification"
    mechanismLevel := .temporal
    observable := "weighted mean bottle < weighted mean beam" }

def discriminatorD5 : Discriminator :=
  { id := "D5"
    description := "Muon g-2 lattice-spacing τ-proxy ordering"
    mechanismLevel := .empirical_risk
    observable := "Pearson r(log₁₀ τ_proxy, a_μ theory) < -0.4 at p < 0.10" }

/-- All five discriminators. -/
def allDiscriminators : List Discriminator :=
  [discriminatorD1, discriminatorD2, discriminatorD3, discriminatorD4, discriminatorD5]

/-- The discriminators span at least 3 distinct mechanism levels. -/
theorem discriminators_span_mechanism_levels :
    discriminatorD1.mechanismLevel ≠ discriminatorD2.mechanismLevel ∧
    discriminatorD1.mechanismLevel ≠ discriminatorD3.mechanismLevel ∧
    discriminatorD2.mechanismLevel ≠ discriminatorD3.mechanismLevel := by
  exact ⟨by decide, by decide, by decide⟩

/-- The two-clock necessity theorem (from NecessityTheorem.lean) extends:
each mechanism level that a null result falsifies is specific, not global.
This is a wrapper connecting the existing `two_clock_necessity` to the
mechanism-level stratification. -/
theorem structural_exclusion_is_mechanism_specific
    (assumptions : TwoClockAssumptions)
    (S : InvariantSignature)
    (hIndep : S.sixDomainIndependent) :
    -- The exclusion applies to a specific class (one-clock models),
    -- not to the UDT programme as a whole.
    ∀ (M : OneClockModel), M.noSharedVariable → generates M S → False :=
  two_clock_necessity assumptions S hIndep

end HeytingLean.Bridge.AlMayahi.UDTSynthesis
