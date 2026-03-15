import Mathlib.Order.Heyting.Basic

/-!
# The R-Nucleus Operator (bundle core)

This file provides a lightweight “bundle-friendly” nucleus interface,
independent of Mathlib’s `Order.Nucleus` development.

An R-nucleus `R : L → L` on a meet-semilattice with bottom satisfies:

* (N1) Extensive: `a ≤ R a`
* (N2) Idempotent: `R (R a) = R a`
* (N3) Meet-preserving: `R (a ⊓ b) = R a ⊓ R b`

The fixed-point locus `Ω_R = {x | R x = x}` is closed under meets.
-/

namespace HeytingLean
namespace Core

/-- A nucleus on a meet-semilattice with bottom.

This is a minimal structure used by the standalone bundle.
For a richer API, see Mathlib’s `Order.Nucleus`.
-/
structure Nucleus (L : Type*) [SemilatticeInf L] [OrderBot L] where
  /-- The nucleus operator. -/
  R : L → L
  /-- (N1) Extensive: `a ≤ R a`. -/
  extensive : ∀ a, a ≤ R a
  /-- (N2) Idempotent: `R (R a) = R a`. -/
  idempotent : ∀ a, R (R a) = R a
  /-- (N3) Meet-preserving: `R (a ⊓ b) = R a ⊓ R b`. -/
  meet_preserving : ∀ a b, R (a ⊓ b) = R a ⊓ R b

namespace Nucleus

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

/-- Fixed points of the nucleus. -/
def fixedPoints (N : Nucleus L) : Set L :=
  { x | N.R x = x }

theorem mem_fixedPoints (N : Nucleus L) (x : L) :
    x ∈ N.fixedPoints ↔ N.R x = x :=
  Iff.rfl

/-- `R a` is always a fixed point. -/
theorem R_mem_fixedPoints (N : Nucleus L) (a : L) :
    N.R a ∈ N.fixedPoints :=
  N.idempotent a

/-- The nucleus operator is monotone. -/
theorem monotone (N : Nucleus L) : Monotone N.R := by
  intro a b hab
  have hInf : a ⊓ b = a := inf_eq_left.mpr hab
  calc
    N.R a = N.R (a ⊓ b) := by simp [hInf]
    _ = N.R a ⊓ N.R b := N.meet_preserving a b
    _ ≤ N.R b := inf_le_right

/-- Fixed points are closed under meets (membership form). -/
theorem fixedPoints_closed_inf (N : Nucleus L)
    {a b : L} (ha : a ∈ N.fixedPoints) (hb : b ∈ N.fixedPoints) :
    a ⊓ b ∈ N.fixedPoints := by
  simp [Nucleus.fixedPoints] at ha hb ⊢
  simp [N.meet_preserving, ha, hb]

/-- Fixed points are closed under meets (equality form). -/
theorem fixed_eq_closed_inf (N : Nucleus L)
    {a b : L} (ha : N.R a = a) (hb : N.R b = b) :
    N.R (a ⊓ b) = a ⊓ b := by
  simp [N.meet_preserving, ha, hb]

end Nucleus

end Core
end HeytingLean
