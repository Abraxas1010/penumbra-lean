import Mathlib.Logic.Relation
import HeytingLean.WPP.Wolfram.Rewrite

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Rewriting theory layer for Wolfram systems

The independence result in `ConfluenceCausalInvariance` uses *terminating* notions:
unique normal forms (up to vertex renaming) and isomorphism of causal graphs.

This module adds the standard relation-theoretic scaffolding:

- one-step relation `Step`,
- reflexive–transitive closure `StepStar`,
- (semi-)confluence / Church–Rosser style statements,
- a simple bounded-termination predicate for evolutions from a given start state.

It is designed to interface with Mathlib's `Relation` utilities (`ReflTransGen`, `Join`, …)
without changing the SetReplace-faithful Wolfram semantics.
-/

universe u v

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)
variable [DecidableEq V]

/-- One-step relation on states: apply some applicable event. -/
def Step (s t : HGraph V) : Prop :=
  ∃ e : sys.Event, e.Applicable (sys := sys) s ∧ e.apply (sys := sys) s = t

/-- Reflexive–transitive closure of `Step`. -/
abbrev StepStar : HGraph V → HGraph V → Prop :=
  Relation.ReflTransGen (Step (sys := sys))

/-- `Step`-normal form: no outgoing `Step` edges. -/
def NormalFormStep (s : HGraph V) : Prop :=
  ∀ t, ¬ Step (sys := sys) s t

lemma normalForm_iff_normalFormStep (s : HGraph V) :
    sys.NormalForm s ↔ NormalFormStep (sys := sys) s := by
  constructor
  · intro hn t hstep
    rcases hstep with ⟨e, happ, _ht⟩
    exact (hn e) happ
  · intro hn e happ
    have : Step (sys := sys) s (e.apply (sys := sys) s) := ⟨e, happ, rfl⟩
    exact (hn _ this).elim

/-! ## `Evolves` vs `StepStar` -/

theorem Evolves.toStepStar {s : HGraph V} {es : List sys.Event} {t : HGraph V} :
    sys.Evolves s es t → StepStar (sys := sys) s t := by
  intro hev
  induction hev with
  | nil s =>
      exact Relation.ReflTransGen.refl
  | cons e happ hrest ih =>
      refine Relation.ReflTransGen.head (hab := ⟨e, happ, rfl⟩) ih

theorem Evolves.append {s : HGraph V} {es₁ es₂ : List sys.Event} {m t : HGraph V} :
    sys.Evolves s es₁ m → sys.Evolves m es₂ t → sys.Evolves s (es₁ ++ es₂) t := by
  intro h₁ h₂
  induction h₁ with
  | nil s =>
      simpa using h₂
  | cons e happ hrest ih =>
      simpa [List.cons_append] using System.Evolves.cons (sys := sys) (e := e) happ (ih h₂)

theorem StepStar.exists_evolves {s t : HGraph V} :
    StepStar (sys := sys) s t → ∃ es : List sys.Event, System.Evolves (sys := sys) s es t := by
  intro h
  induction h with
  | refl =>
      refine ⟨[], ?_⟩
      exact System.Evolves.nil (sys := sys) s
  | tail _hab hstep ih =>
      rename_i m t'
      rcases ih with ⟨es, hes⟩
      rcases hstep with ⟨e, happ, hEq⟩
      refine ⟨es ++ [e], ?_⟩
      have hlast : System.Evolves (sys := sys) m [e] (e.apply (sys := sys) m) :=
        System.Evolves.cons (sys := sys) (e := e) happ (System.Evolves.nil (sys := sys) _)
      have hconcat : System.Evolves (sys := sys) s (es ++ [e]) (e.apply (sys := sys) m) :=
        Evolves.append (sys := sys) hes hlast
      simpa [hEq] using hconcat

/-! ## Confluence / Church–Rosser style predicates -/

/-- Joinability of two states under `StepStar`. -/
def Joinable (b c : HGraph V) : Prop :=
  Relation.Join (StepStar (sys := sys)) b c

/-- Confluence (Church–Rosser): any fork under `StepStar` is joinable. -/
def Confluent : Prop :=
  ∀ a b c, StepStar (sys := sys) a b → StepStar (sys := sys) a c → Joinable (sys := sys) b c

/-- A sufficient condition for confluence, matching `Relation.church_rosser`. -/
def SemiConfluent : Prop :=
  ∀ a b c, Step (sys := sys) a b → Step (sys := sys) a c →
    ∃ d, Relation.ReflGen (Step (sys := sys)) b d ∧ StepStar (sys := sys) c d

theorem semiConfluent_confluent (h : SemiConfluent (sys := sys)) : Confluent (sys := sys) := by
  intro a b c hab hac
  -- Use Mathlib's `Relation.church_rosser` lemma.
  exact Relation.church_rosser (r := Step (sys := sys)) h hab hac

/-! ## A simple bounded termination predicate (from a start state) -/

/-- Boundedness of evolutions from a start state: no execution list longer than `n`. -/
def BoundedFrom (s : HGraph V) (n : Nat) : Prop :=
  ∀ es t, sys.Evolves s es t → es.length ≤ n

/-- Termination-from-`s` (strong form): there exists a uniform bound on evolution lengths. -/
def TerminatingFrom (s : HGraph V) : Prop :=
  ∃ n, BoundedFrom (sys := sys) s n

end System

end Wolfram
end WPP
end HeytingLean
