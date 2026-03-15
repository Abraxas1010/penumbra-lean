import Mathlib.Data.Multiset.Fold
import HeytingLean.WPP.Wolfram.CausalGraph

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# "Garbage-collected" causal graphs (observable-event coarse-graining)

The SetReplace-style causal graph (`HeytingLean.WPP.Wolfram.System.causalGraphOf`) uses **all**
event steps in a chosen evolution as vertices.

For comparisons that should ignore transient bookkeeping steps, we define a coarse-grained causal
graph whose vertices are only those events that create at least one expression that is present in
the endpoint state. Intuitively, we "garbage-collect" events whose created expressions do not
survive to the endpoint.

This is **not** the SetReplace definition; it is an "observable-event" abstraction.
-/

universe u v

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)
variable [DecidableEq V]

open System

namespace Multiset

lemma fold_or_eq_true_of_mem_true :
    ∀ {s : Multiset Bool}, true ∈ s → s.fold (· || ·) false = true := by
  intro s h
  induction s using Multiset.induction_on with
  | empty =>
      simp at h
  | @cons a s ih =>
      have h' : true = a ∨ true ∈ s := (Multiset.mem_cons).1 h
      cases h' with
      | inl ha =>
          -- Head is `true`.
          cases a <;> cases ha
          simp [Multiset.fold_cons_left]
      | inr htailMem =>
          -- `true` is in the tail.
          have htail : s.fold (· || ·) false = true := ih htailMem
          cases a <;> simp [Multiset.fold_cons_left, htail]

end Multiset

namespace Event

/-- `x` is *created (nontrivially)* by an event `e` if it appears in the output and not in the input. -/
def Created (e : sys.Event) (x : Expr V) : Prop :=
  x ∈ e.output (sys := sys) ∧ x ∉ e.input (sys := sys)

/-- Boolean test: the event creates some expression that survives in `t`. -/
def observableB (e : sys.Event) (t : HGraph V) : Bool :=
  let createdInT : Expr V → Bool :=
    fun x => decide (x ∉ e.input (sys := sys) ∧ x ∈ t)
  ((e.output (sys := sys)).map createdInT).fold (· || ·) false

/-- An event is *observable* w.r.t. an endpoint state `t` if it creates some expression present in `t`. -/
def Observable (e : sys.Event) (t : HGraph V) : Prop :=
  observableB (sys := sys) e t = true

end Event

/-- The (sorted) list of indices of events in `es` that are observable w.r.t. endpoint `t`. -/
def observableIdxs (es : List sys.Event) (t : HGraph V) : List (Fin es.length) :=
  (List.finRange es.length).filter (fun i => Event.observableB (sys := sys) (es.get i) t)

/-- Observable-event causal graph of an evolution ending in `t` (a "garbage-collected" abstraction). -/
def causalGraphGCOf (es : List sys.Event) (t : HGraph V) : CausalGraph :=
  let idxs := observableIdxs (sys := sys) es t
  { n := idxs.length
    edge := fun i j =>
      let ii : Fin es.length := idxs.get i
      let jj : Fin es.length := idxs.get j
      ii.1 < jj.1 ∧ (es.get ii).Causes (sys := sys) (es.get jj) }

end System

namespace Properties

variable {V : Type u} {P : Type v} (sys : System V P)
variable [DecidableEq V]

/-- Observable-event ("GC") causal invariance for terminating systems. -/
def GCausalInvariant : Prop :=
  ∀ ⦃es₁ es₂ : List sys.Event⦄ ⦃t₁ t₂ : HGraph V⦄,
    sys.Evolves sys.init es₁ t₁ → sys.NormalForm t₁ →
    sys.Evolves sys.init es₂ t₂ → sys.NormalForm t₂ →
    CausalGraph.Iso (sys.causalGraphGCOf es₁ t₁) (sys.causalGraphGCOf es₂ t₂)

end Properties

end Wolfram
end WPP
end HeytingLean
