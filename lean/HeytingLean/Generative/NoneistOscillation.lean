import HeytingLean.Noneism.Foundation

/-!
# Generative.NoneistOscillation — Step 0→1: Dimensional Emergence

From the Noneist ground (static nothing is self-contradictory), the minimum
differentiation is two oscillating points: the primordial axis.

## The Argument

**Step 0**: Nothing. 0D. No extension, no distinction.

But static nothing is self-contradictory (the Noneist argument):
singularity is a constraint, and nothing-that-is-singular is already
something. So nothing must differentiate. The minimum differentiation
from a point is...

**Step 1**: Two points. 1D.

The minimal plurality. But these are not static points — they are
*oscillating*, because the contradiction that produced the differentiation
doesn't resolve, it persists as oscillation. Two oscillating points are
equivalent to two points counter-rotating. This is the proto-UDP.

## Formal Content

We package `PrimordialTension` as a geometric `OscillationAxis`:
two distinct states with involutive counter-rotation and a 1-bit phase
observable. This is the carrier of the 1D structure.
-/

namespace HeytingLean.Generative

open HeytingLean.Noneism

/-- An oscillation axis: the minimal structure emerging from 0D.
Two distinct states with involutive counter-rotation and a 1-bit phase
observable. The `states_step` field ties the two states as one step apart,
making the axis endpoints the counter-rotating pair. -/
structure OscillationAxis where
  /-- The carrier type -/
  Carrier : Type
  /-- First state (one phase of the oscillation) -/
  state₁ : Carrier
  /-- Second state (counter-phase) -/
  state₂ : Carrier
  /-- The two states are distinct (non-degeneracy) -/
  distinct : state₁ ≠ state₂
  /-- The dynamics: counter-rotation (involutive map) -/
  step : Carrier → Carrier
  /-- Involutivity: step ∘ step = id (exact 2-cycle) -/
  involutive : ∀ x, step (step x) = x
  /-- Phase observable: a 1-bit distinction -/
  obs : Carrier → Bool
  /-- The observable flips at each step (phase coupling at the pivot) -/
  flips : ∀ x, obs (step x) = Bool.not (obs x)
  /-- state₂ is the step of state₁ (counter-rotating pair) -/
  states_step : state₂ = step state₁

/-- The Noneist ground produces an oscillation axis.

This is the 0D → 1D emergence: static nothing is self-contradictory
(Noneist argument), therefore oscillation is necessary, therefore a
binary oscillator with these exact properties exists. -/
def noneistAxis : OscillationAxis where
  Carrier := Nothing
  state₁ := Foundation.seed
  state₂ := Foundation.step Foundation.seed
  distinct := Foundation.seed_ne_step_seed
  step := Foundation.step
  involutive := PrimordialTension.step_step
  obs := Foundation.obs
  flips := PrimordialTension.obs_step
  states_step := rfl

/-- The oscillation axis witnesses the minimum plurality from the
Noneist ground: at least two distinct states exist. -/
theorem oscillation_produces_plurality :
    ∃ (ax : OscillationAxis), ax.state₁ ≠ ax.state₂ :=
  ⟨noneistAxis, Foundation.seed_ne_step_seed⟩

/-- On any oscillation axis, the two states have opposite phase.
The counter-rotation ensures they are always out of phase: if one
is at +θ, the other is at −θ. -/
theorem oscillation_axis_opposite_phase (ax : OscillationAxis) :
    ax.obs ax.state₂ = Bool.not (ax.obs ax.state₁) := by
  rw [ax.states_step, ax.flips]

/-- On any oscillation axis, the step maps state₁ to state₂ and back.
The dynamics is a clean 2-cycle between the two axis endpoints. -/
theorem oscillation_axis_step_cycle (ax : OscillationAxis) :
    ax.step ax.state₁ = ax.state₂ ∧ ax.step ax.state₂ = ax.state₁ := by
  exact ⟨ax.states_step.symm, by rw [ax.states_step, ax.involutive]⟩

/-- The observable partitions the carrier into two non-empty classes
(Mark and Unmark). This is the 1-bit distinction — the minimal
information content of the oscillation. -/
theorem oscillation_axis_partition (ax : OscillationAxis) :
    (∃ x, ax.obs x = true) ∧ (∃ x, ax.obs x = false) := by
  by_cases h : ax.obs ax.state₁ = true
  · exact ⟨⟨ax.state₁, h⟩,
           ⟨ax.state₂, by rw [oscillation_axis_opposite_phase ax, h]; rfl⟩⟩
  · have h' : ax.obs ax.state₁ = false := by
      cases hc : ax.obs ax.state₁ <;> simp_all
    exact ⟨⟨ax.state₂, by rw [oscillation_axis_opposite_phase ax, h']; rfl⟩,
           ⟨ax.state₁, h'⟩⟩

end HeytingLean.Generative
