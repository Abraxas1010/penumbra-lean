import Mathlib.Computability.Halting

/-!
# MirandaDynamics.Undecidability: transfer lemmas (Lean spine)

Miranda-style “dynamical computation” results (TKFT / billiards / fluids) are typically used in the
following *logical* way:

1. show a physical/dynamical predicate `P` (e.g. “has a periodic orbit”, “reaches a region”) is
   expressive enough to encode halting, and
2. conclude `P` is not computable.

The deep analytic geometry supplies Step (1). Lean can (and should) mechanize Step (2).

This file provides a small, reusable reduction framework around Mathlib’s `halting_problem`.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Undecidability

open Nat.Partrec
open Nat.Partrec.Code
open ComputablePred

universe u v

/-- A (many-one) computable reduction between predicates. -/
structure ManyOne {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]
    (p : α → Prop) (q : β → Prop) : Type (max u v) where
  f : α → β
  computable_f : Computable f
  correct : ∀ a, p a ↔ q (f a)

namespace ManyOne

variable {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]
variable {p : α → Prop} {q : β → Prop}

/-- If `p` many-one reduces to `q` and `q` is computable, then `p` is computable. -/
theorem computable_of_reduces (hred : ManyOne (p := p) (q := q)) (hq : ComputablePred q) :
    ComputablePred p := by
  classical
  -- Obtain a computable Boolean witness for `q`, then compose with the reduction function.
  rcases ComputablePred.computable_iff.1 hq with ⟨bq, hbq, hqEq⟩
  have hb : Computable (fun a => bq (hred.f a)) := hbq.comp hred.computable_f
  refine ComputablePred.computable_iff.2 ⟨fun a => bq (hred.f a), hb, ?_⟩
  funext a
  apply propext
  -- `hqEq` gives `q = fun b => (bq b : Prop)`.
  have hqAt : q (hred.f a) ↔ (bq (hred.f a) : Prop) := by
    simp [hqEq]
  exact (hred.correct a).trans hqAt

/-- If `p` reduces to `q` and `p` is not computable, then `q` is not computable. -/
theorem not_computable_of_reduces (hred : ManyOne (p := p) (q := q)) (hp : ¬ComputablePred p) :
    ¬ComputablePred q := by
  intro hq
  exact hp (computable_of_reduces (p := p) (q := q) hred hq)

end ManyOne

/-! ## Specialization: the halting problem -/

namespace Halting

/-- The standard (code) halting predicate at fixed input `n`. -/
def Halts (n : ℕ) : Code → Prop :=
  fun c => (eval c n).Dom

theorem not_computable (n : ℕ) : ¬ComputablePred (Halts n) :=
  halting_problem n

/-- Generic transfer principle: any predicate that the halting problem many-one reduces to
is not computable. -/
theorem not_computable_of_halting_reduces
    {β : Type v} [Primcodable β] {q : β → Prop} (n : ℕ)
    (hred : ManyOne (p := Halts n) (q := q)) :
    ¬ComputablePred q :=
  ManyOne.not_computable_of_reduces (p := Halts n) (q := q) hred (not_computable n)

end Halting

end Undecidability
end MirandaDynamics
end HeytingLean
