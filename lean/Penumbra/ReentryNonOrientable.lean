import Mathlib.Data.Real.GoldenRatio
import HeytingLean.Generative.ReEntryPlane

/-!
# Penumbra.ReentryNonOrientable

This module isolates the topological part of the Exp 6 extension. Re-entry is modeled as a
two-sheeted traversal whose single-cycle action swaps sheets. The point is not heavy topology; it
is to separate the orientation-reversal fact from the later `SO(4)` decomposition.
-/

namespace Penumbra

/-- The two local sheets of the re-entry cover. -/
inductive Sheet
  | left
  | right
  deriving DecidableEq, Repr

/-- A re-entry geometry carries only the aspect ratio needed to instantiate the traversal. -/
structure ReentryGeometry where
  aspectRatio : ℝ
  aspect_pos : 0 < aspectRatio

/-- One re-entry cycle swaps the two sheets of the cover. -/
def reentryCycle : Sheet → Sheet
  | .left => .right
  | .right => .left

/-- A Möbius traversal is exactly a one-cycle orientation reversal on the two-sheeted cover. -/
def IsMobiusTraversal (cycle : Sheet → Sheet) : Prop :=
  cycle Sheet.left = Sheet.right ∧ cycle Sheet.right = Sheet.left

/-- The canonical re-entry geometry inherits the golden-ratio aspect from the existing generative
surface. -/
noncomputable def canonicalReentryGeometry : ReentryGeometry where
  aspectRatio := Real.goldenRatio
  aspect_pos := Real.goldenRatio_pos

/-- Re-entry is a Möbius traversal: one circuit swaps sheets, two circuits return to the start. -/
theorem reentry_is_mobius : IsMobiusTraversal reentryCycle := by
  constructor <;> rfl

/-- Two re-entry cycles restore the original orientation. -/
theorem reentry_cycle_sq_id (s : Sheet) : reentryCycle (reentryCycle s) = s := by
  cases s <;> rfl

/-- A single re-entry cycle is orientation reversing on each sheet. -/
theorem reentry_cycle_ne_self (s : Sheet) : reentryCycle s ≠ s := by
  cases s <;> decide

end Penumbra
