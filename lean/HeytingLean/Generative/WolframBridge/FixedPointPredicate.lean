import HeytingLean.Core.Nucleus
import HeytingLean.HossenfelderNoGo.HeytingBoundary.BoundaryNucleus

namespace HeytingLean.Generative.WolframBridge

open HeytingLean.Core
open HeytingLean.HossenfelderNoGo.HeytingBoundary

variable {L : Type*} [SemilatticeInf L] [OrderBot L]

/-- Abstract fixed-point predicate for a nucleus. -/
def NucleusInvariant (N : Core.Nucleus L) : Prop :=
  ∀ x, N.R x = x

theorem nucleusInvariant_iff_all_fixed (N : Core.Nucleus L) :
    NucleusInvariant N ↔ ∀ x, x ∈ N.fixedPoints := by
  simp [NucleusInvariant, Core.Nucleus.mem_fixedPoints]

/-- On the Hossenfelder side, Booleanity is definitionally the same fixed-point predicate. -/
theorem hossenfelder_isBoolean_iff_nucleusInvariant
    (N : BoundaryNucleus L) :
    isBoolean N ↔ NucleusInvariant N :=
  Iff.rfl

theorem not_nucleusInvariant_iff_exists_moved
    (N : Core.Nucleus L) :
    ¬ NucleusInvariant N ↔ ∃ x, N.R x ≠ x := by
  simp [NucleusInvariant]

theorem boundaryGap_eq_empty_of_fixed
    (N : BoundaryNucleus L) (a : L) (hfix : N.R a = a) :
    boundaryGap N a = ∅ := by
  ext x
  simp [boundaryGap, hfix]

theorem boundaryGap_nonempty_of_moved
    (N : BoundaryNucleus L) (a : L) (hmoved : N.R a ≠ a) :
    boundaryGap N a ≠ ∅ := by
  intro hempty
  have hmem : N.R a ∈ boundaryGap N a := by
    rw [mem_boundaryGap_iff]
    exact ⟨rfl, hmoved⟩
  simp [hempty] at hmem

end HeytingLean.Generative.WolframBridge
