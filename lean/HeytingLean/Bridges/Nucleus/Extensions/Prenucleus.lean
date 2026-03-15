import Mathlib.Order.Nucleus
import HeytingLean.Core.Nucleus

namespace HeytingLean
namespace Bridges
namespace Nucleus
namespace Extensions

/-- A prenucleus keeps the extensive + meet-preserving laws and may fail idempotence. -/
structure Prenucleus (L : Type*) [SemilatticeInf L] [OrderBot L] where
  act : L → L
  extensive : ∀ a, a ≤ act a
  map_inf : ∀ a b, act (a ⊓ b) = act a ⊓ act b

namespace Prenucleus

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

@[ext] theorem ext {P Q : Prenucleus L} (h : P.act = Q.act) : P = Q := by
  cases P
  cases Q
  cases h
  simp

/-- Every nucleus induces a prenucleus by forgetting idempotence. -/
def ofNucleus (n : _root_.Nucleus L) : Prenucleus L where
  act := n
  extensive := fun a => _root_.Nucleus.le_apply (n := n) (x := a)
  map_inf := fun a b => _root_.Nucleus.map_inf (n := n) (x := a) (y := b)

/-- A prenucleus is monotone (same argument as for nuclei). -/
theorem monotone (P : Prenucleus L) : Monotone P.act := by
  intro a b hab
  have hInf : a ⊓ b = a := inf_eq_left.mpr hab
  calc
    P.act a = P.act (a ⊓ b) := by simp [hInf]
    _ = P.act a ⊓ P.act b := P.map_inf a b
    _ ≤ P.act b := inf_le_right

/-- Optional promotion into the core nucleus record once idempotence is supplied. -/
def toCoreNucleus (P : Prenucleus L)
    (hidem : ∀ a, P.act (P.act a) = P.act a) : HeytingLean.Core.Nucleus L where
  R := P.act
  extensive := P.extensive
  idempotent := hidem
  meet_preserving := P.map_inf

end Prenucleus

end Extensions
end Nucleus
end Bridges
end HeytingLean
