import HeytingLean.WPP.Wolfram.ConfluenceCausalInvariance
import HeytingLean.WPP.Wolfram.ConfluenceCausalInvarianceGC

/-!
# Bridge.Wolfram.CausalInvariance

Compatibility bridge exposing the Wolfram confluence/causal-invariance results
under the legacy `Bridge/Wolfram` path.
-/

namespace HeytingLean.Bridge.Wolfram

/-- CE1 witness: confluent normal forms. -/
theorem ce1_confluentNF :
    HeytingLean.WPP.Wolfram.Properties.ConfluentNF
      (sys := HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys) :=
  HeytingLean.WPP.Wolfram.Counterexamples.CE1.confluentNF

/-- CE1 witness: not causally invariant. -/
theorem ce1_not_causalInvariant :
    ¬ HeytingLean.WPP.Wolfram.Properties.CausalInvariant
      (sys := HeytingLean.WPP.Wolfram.Counterexamples.CE1.sys) :=
  HeytingLean.WPP.Wolfram.Counterexamples.CE1.not_causalInvariant

/-- CE2 witness: causally invariant. -/
theorem ce2_causalInvariant :
    HeytingLean.WPP.Wolfram.Properties.CausalInvariant
      (sys := HeytingLean.WPP.Wolfram.Counterexamples.CE2.sys) :=
  HeytingLean.WPP.Wolfram.Counterexamples.CE2.causalInvariant

/-- CE2 witness: not confluent normal forms. -/
theorem ce2_not_confluentNF :
    ¬ HeytingLean.WPP.Wolfram.Properties.ConfluentNF
      (sys := HeytingLean.WPP.Wolfram.Counterexamples.CE2.sys) :=
  HeytingLean.WPP.Wolfram.Counterexamples.CE2.not_confluentNF

/-- Global independence theorem. -/
theorem confluence_causal_invariance_independent :
    (¬ (∀ {V P : Type} (sys : HeytingLean.WPP.Wolfram.System V P) [DecidableEq V],
        HeytingLean.WPP.Wolfram.Properties.ConfluentNF (sys := sys) →
          HeytingLean.WPP.Wolfram.Properties.CausalInvariant (sys := sys))) ∧
    (¬ (∀ {V P : Type} (sys : HeytingLean.WPP.Wolfram.System V P) [DecidableEq V],
        HeytingLean.WPP.Wolfram.Properties.CausalInvariant (sys := sys) →
          HeytingLean.WPP.Wolfram.Properties.ConfluentNF (sys := sys))) :=
  HeytingLean.WPP.Wolfram.Counterexamples.confluence_causal_invariance_independent

end HeytingLean.Bridge.Wolfram
