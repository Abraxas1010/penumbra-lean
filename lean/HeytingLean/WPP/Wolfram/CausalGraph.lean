import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import HeytingLean.WPP.Wolfram.Rewrite

namespace HeytingLean
namespace WPP
namespace Wolfram

/-!
# Causal graphs (SetReplace-style)

Following SetReplace documentation:

> An event A causes an event B if there exists an expression created by A and destroyed by B.

We model a causal graph as a finite directed graph on `Fin n` (events indexed by time/order).
Edges are unlabeled; multiplicity is irrelevant for the independence counterexamples.
-/

universe u v

/-- A finite directed graph on `n` vertices. -/
structure CausalGraph where
  n : Nat
  edge : Fin n → Fin n → Prop

namespace CausalGraph

/-- Graph isomorphism. -/
def Iso (g₁ g₂ : CausalGraph) : Prop :=
  ∃ e : Fin g₁.n ≃ Fin g₂.n, ∀ i j, g₁.edge i j ↔ g₂.edge (e i) (e j)

lemma Iso.n_eq {g₁ g₂ : CausalGraph} : Iso g₁ g₂ → g₁.n = g₂.n := by
  intro h
  rcases h with ⟨e, _⟩
  -- Cardinalities of finite types agree under an equivalence.
  simpa [Fintype.card_fin] using (Fintype.card_congr e)

lemma not_Iso_of_n_ne {g₁ g₂ : CausalGraph} (h : g₁.n ≠ g₂.n) : ¬ Iso g₁ g₂ := by
  intro hiso
  exact h (Iso.n_eq hiso)

end CausalGraph

namespace System

variable {V : Type u} {P : Type v} (sys : System V P)
variable [DecidableEq V]

open System

/-- Build the causal graph of a singleway evolution.

Vertices are event indices `Fin es.length`. There is an edge `i → j` (with `i<j`)
iff some expression is created by `es[i]` and destroyed by `es[j]`. -/
def causalGraphOf (es : List sys.Event) : CausalGraph where
  n := es.length
  edge := fun i j =>
    i.1 < j.1 ∧ (es.get i).Causes (sys := sys) (es.get j)

end System

end Wolfram
end WPP
end HeytingLean
