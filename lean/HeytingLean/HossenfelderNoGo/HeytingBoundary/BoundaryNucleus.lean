import Mathlib.Data.Set.Lattice
import HeytingLean.Core.Nucleus
import HeytingLean.HossenfelderNoGo.Networks.NoGoTheorem

namespace HeytingLean.HossenfelderNoGo.HeytingBoundary

open HeytingLean.HossenfelderNoGo.Networks

/-- The boundary nucleus is exactly the repo's existing core nucleus interface. -/
abbrev BoundaryNucleus (L : Type*) [SemilatticeInf L] [OrderBot L] :=
  HeytingLean.Core.Nucleus L

/-- Booleanity at the boundary means the nucleus acts as the identity on every element. -/
def isBoolean {L : Type*} [SemilatticeInf L] [OrderBot L] (N : BoundaryNucleus L) : Prop :=
  ∀ x, N.R x = x

/-- The boundary gap at `a` is the singleton image `{R a}` with the fixed-point case removed. This
keeps the existing set-difference shape used by Heyting gap measures elsewhere in the repo. -/
def boundaryGap {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) (a : L) : Set L :=
  ({N.R a} : Set L) \ ({a} : Set L)

theorem mem_boundaryGap_iff {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) (a x : L) :
    x ∈ boundaryGap N a ↔ x = N.R a ∧ x ≠ a := by
  simp [boundaryGap]

/-- A local bridge hypothesis for a specific boundary nucleus: if that nucleus were Boolean,
it would realize a faithful Poincare-invariant locally finite network. This is a hypothesis
schema, not a global axiom over all nuclei. -/
def BooleanBoundaryBridge
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : BoundaryNucleus L) : Prop :=
  isBoolean N →
    ∃ (Net : SpacetimeNetwork), LocallyFinite Net ∧ PoincareInvariant Net

end HeytingLean.HossenfelderNoGo.HeytingBoundary
