import Mathlib.Data.Fin.Basic
import Mathlib.Data.Multiset.Basic
import HeytingLean.WPP.Wolfram.Hypergraph

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Rewrite semantics (SetReplace-style core)

We implement the minimal ingredient needed for Piskunov-style counterexamples:
- A rule schema is a pair of hypergraphs over a *pattern* vertex type.
- A system has a **list** of rules (SetReplace-style).
- An event chooses a rule index and a substitution for that rule (not assumed injective).
- Applicability is submultiset membership of the instantiated LHS in the current state.
- Application replaces LHS by RHS via multiset subtraction/addition.
 -/

universe u v

/-- Rewrite rule schema over pattern vertices `P`. -/
structure Rule (P : Type u) where
  lhs : HGraph P
  rhs : HGraph P

namespace Rule

/-- Instantiate a rule's expressions by mapping vertices through `σ`. -/
@[simp] def inst {P : Type u} {V : Type v} (σ : P → V) : HGraph P → HGraph V :=
  HGraph.rename σ

@[simp] def instLhs {P : Type u} {V : Type v} (r : Rule P) (σ : P → V) : HGraph V :=
  inst σ r.lhs

@[simp] def instRhs {P : Type u} {V : Type v} (r : Rule P) (σ : P → V) : HGraph V :=
  inst σ r.rhs

end Rule

/-- A Wolfram-model system with a list of rules (SetReplace-style). -/
structure System (V : Type u) (P : Type v) where
  rules : List (Rule P)
  init : HGraph V

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)

/-- A rule-application event is a substitution of pattern vertices into concrete ones. -/
structure Event (sys : System V P) where
  idx : Fin sys.rules.length
  σ : P → V

namespace Event

variable {sys : System V P}

/-- The multiset of input expressions destroyed by this event. -/
@[simp] def input (e : sys.Event) : HGraph V :=
  (sys.rules.get e.idx).instLhs e.σ

/-- The multiset of output expressions created by this event. -/
@[simp] def output (e : sys.Event) : HGraph V :=
  (sys.rules.get e.idx).instRhs e.σ

/-- Applicability: inputs are available as a submultiset of the current state. -/
def Applicable (e : sys.Event) (s : HGraph V) : Prop :=
  e.input ≤ s

instance decidableApplicable [DecidableEq V] (e : sys.Event) (s : HGraph V) :
    Decidable (e.Applicable (sys := sys) s) := by
  dsimp [Applicable]
  infer_instance

variable [DecidableEq V]

/-- Apply the event to a state: replace input expressions with output expressions. -/
def apply (e : sys.Event) (s : HGraph V) : HGraph V :=
  s - e.input + e.output

/-- Causal dependency (SetReplace): `e₁` causes `e₂` if some expression is created by `e₁`
and destroyed by `e₂`. -/
def Causes (e₁ e₂ : sys.Event) : Prop :=
  ∃ x, x ∈ e₁.output ∧ x ∈ e₂.input

end Event

variable [DecidableEq V]

/-- Execution relation: starting at `s`, apply a list of events to reach `t`. -/
inductive Evolves : HGraph V → List sys.Event → HGraph V → Prop
| nil (s : HGraph V) : Evolves s [] s
| cons {s : HGraph V} {es : List sys.Event} {t : HGraph V}
    (e : sys.Event) :
    e.Applicable (sys := sys) s →
    Evolves (e.apply (sys := sys) s) es t →
    Evolves s (e :: es) t

/-- Reachability from the system initial state. -/
def Reachable (t : HGraph V) : Prop :=
  ∃ es, sys.Evolves sys.init es t

/-- A normal form is a state with no applicable events. -/
def NormalForm (s : HGraph V) : Prop :=
  ∀ e : sys.Event, ¬ e.Applicable (sys := sys) s

end System

end Wolfram
end WPP
end HeytingLean
