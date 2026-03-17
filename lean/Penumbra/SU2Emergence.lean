import Penumbra.MobiusSO4Embedding
import HeytingLean.Generative.SpinorBridge.SU2Core

/-!
# Penumbra.SU2Emergence

This completes the lean side of the Exp 6 extension. The topology-to-algebra chain is:

1. Re-entry is Möbius (`ReentryNonOrientable`)
2. The Möbius half-twist embeds as the concrete anti-self-dual generator `J₁⁻`
3. The commuting self-dual triple is present, and the existing spinor bridge already proves that
   the corresponding `SU(2)` generator family has cardinality three
-/

namespace Penumbra

open HeytingLean.Generative.SpinorBridge

/-- The concrete anti-self-dual commutant carries the self-dual triple. -/
theorem anti_self_dual_commutant_is_su2 :
    commutator mobiusGenerator j1Plus = 0 ∧
    commutator mobiusGenerator j2Plus = 0 ∧
    commutator mobiusGenerator j3Plus = 0 := by
  exact anti_self_dual_commutant_contains_su2plus

/-- The imported spinor bridge provides exactly three `SU(2)` generators. -/
theorem commutant_gives_su2 : Fintype.card SU2Generator = 3 := by
  simpa using su2_generator_count

/-- The canonical re-entry traversal forces the anti-self-dual generator in the concrete
`SO(4)` embedding. -/
theorem reentry_topology_forces_anti_self_dual_generator :
    IsMobiusTraversal reentryCycle → traversalGenerator reentryCycle = j1Minus := by
  intro hMobius
  exact mobius_traversal_lands_in_anti_self_dual_factor reentryCycle hMobius

/-- Once the re-entry traversal is Möbius, the self-dual commutant follows in the concrete
embedding. -/
theorem reentry_topology_forces_su2_commutant :
    IsMobiusTraversal reentryCycle →
    commutator (traversalGenerator reentryCycle) j1Plus = 0 ∧
    commutator (traversalGenerator reentryCycle) j2Plus = 0 ∧
    commutator (traversalGenerator reentryCycle) j3Plus = 0 := by
  intro hMobius
  exact mobius_traversal_commutant_contains_su2plus reentryCycle hMobius

/-- Re-entry Möbius topology plus the explicit `SO(4)` embedding yields the `SU(2)` commutant
surface used by the Rust extension. -/
theorem su2_emerges_from_reentry :
    IsMobiusTraversal reentryCycle →
    traversalGenerator reentryCycle = j1Minus ∧
    commutator (traversalGenerator reentryCycle) j1Plus = 0 ∧
    commutator (traversalGenerator reentryCycle) j2Plus = 0 ∧
    commutator (traversalGenerator reentryCycle) j3Plus = 0 ∧
    Fintype.card SU2Generator = 3 := by
  intro hMobius
  refine ⟨reentry_topology_forces_anti_self_dual_generator hMobius, ?_, ?_, ?_, commutant_gives_su2⟩
  · exact (reentry_topology_forces_su2_commutant hMobius).1
  · exact (reentry_topology_forces_su2_commutant hMobius).2.1
  · exact (reentry_topology_forces_su2_commutant hMobius).2.2

end Penumbra
