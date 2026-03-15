import Mathlib.Data.Fin.Basic
import HeytingLean.Generative.SpinorBridge.SU2Core
import HeytingLean.Generative.NoneistOscillation

namespace HeytingLean.Generative.SpinorBridge

open HeytingLean.Generative

noncomputable section

/-- The two distinguished oscillation states, isolated as the spinorial support. -/
abbrev OscillationSupport (ax : OscillationAxis) : Type :=
  { x : ax.Carrier // x = ax.state₁ ∨ x = ax.state₂ }

/-- The step map preserves the two-state oscillation support. -/
def stepOnSupport (ax : OscillationAxis) (x : OscillationSupport ax) :
    OscillationSupport ax := by
  classical
    by_cases h₁ : x.1 = ax.state₁
  · refine ⟨ax.step x.1, Or.inr ?_⟩
    calc
      ax.step x.1 = ax.step ax.state₁ := by simp [h₁]
      _ = ax.state₂ := ax.states_step.symm
  · refine ⟨ax.step x.1, Or.inl ?_⟩
    have h₂ : x.1 = ax.state₂ := by
      rcases x.property with hx | hx
      · exact False.elim (h₁ hx)
      · exact hx
    calc
      ax.step x.1 = ax.step ax.state₂ := by simp [h₂]
      _ = ax.state₁ := by simpa [ax.states_step] using ax.involutive ax.state₁

theorem step_state₁ (ax : OscillationAxis) :
    ax.step ax.state₁ = ax.state₂ :=
  ax.states_step.symm

theorem step_state₂ (ax : OscillationAxis) :
    ax.step ax.state₂ = ax.state₁ := by
  simpa only [ax.states_step] using ax.involutive ax.state₁

/-- Encode the oscillation support as the two basis labels. -/
def oscillationToFin (ax : OscillationAxis) (x : OscillationSupport ax) : Fin 2 := by
  classical
  exact if x.1 = ax.state₁ then 0 else 1

/-- Decode the two basis labels back to the distinguished oscillation states. -/
def finToOscillation (ax : OscillationAxis) : Fin 2 → OscillationSupport ax
  | 0 => ⟨ax.state₁, Or.inl rfl⟩
  | 1 => ⟨ax.state₂, Or.inr rfl⟩

/-- Encode the two oscillation endpoints as the two basis spin states. -/
def oscillationStates (ax : OscillationAxis) : OscillationSupport ax ≃ Fin 2 where
  toFun := oscillationToFin ax
  invFun := finToOscillation ax
  left_inv := by
    classical
    intro x
    rcases x.property with hx | hx
    · apply Subtype.ext
      simp [oscillationToFin, finToOscillation, hx]
    · apply Subtype.ext
      have h21 : ax.state₂ ≠ ax.state₁ := fun h => ax.distinct h.symm
      simp [oscillationToFin, finToOscillation, hx, h21]
  right_inv := by
    intro i
    fin_cases i
    · simp [oscillationToFin, finToOscillation]
    · have h21 : ax.state₂ ≠ ax.state₁ := fun h => ax.distinct h.symm
      simp [oscillationToFin, finToOscillation, h21]

@[simp] theorem oscillationStates_state₁ (ax : OscillationAxis) :
    oscillationStates ax ⟨ax.state₁, Or.inl rfl⟩ = 0 := by
  classical
  simp [oscillationStates, oscillationToFin]

@[simp] theorem oscillationStates_state₂ (ax : OscillationAxis) :
    oscillationStates ax ⟨ax.state₂, Or.inr rfl⟩ = 1 := by
  classical
  have hne : ax.state₂ ≠ ax.state₁ := fun h => ax.distinct h.symm
  simp [oscillationStates, oscillationToFin, hne]

theorem step_is_spin_flip (ax : OscillationAxis) (x : OscillationSupport ax) :
    oscillationStates ax (stepOnSupport ax x) =
      Fin.rev (oscillationStates ax x) := by
  classical
  have h21 : ax.state₂ ≠ ax.state₁ := fun h => ax.distinct h.symm
  have hstep1 : ax.step ax.state₁ ≠ ax.state₁ := by
    simpa [step_state₁ ax] using h21
  have hstep_state₁ :
      stepOnSupport ax ⟨ax.state₁, Or.inl rfl⟩ = ⟨ax.state₂, Or.inr rfl⟩ := by
    apply Subtype.ext
    simp [stepOnSupport, step_state₁ ax]
  have hstep_state₂ :
      stepOnSupport ax ⟨ax.state₂, Or.inr rfl⟩ = ⟨ax.state₁, Or.inl rfl⟩ := by
    apply Subtype.ext
    simp [stepOnSupport, step_state₂ ax, h21]
  rcases x.property with hx | hx
  · have hx' : x = ⟨ax.state₁, Or.inl rfl⟩ := by
      apply Subtype.ext
      simp [hx]
    subst hx'
    rw [hstep_state₁]
    simp [oscillationStates_state₁, oscillationStates_state₂]
  · have hx' : x = ⟨ax.state₂, Or.inr rfl⟩ := by
      apply Subtype.ext
      simp [hx]
    subst hx'
    rw [hstep_state₂]
    simp [oscillationStates_state₁, oscillationStates_state₂]

/-- On the encoded two-state support, two spin flips return the original state. -/
theorem involutivity_is_double_cover (ax : OscillationAxis) (x : OscillationSupport ax) :
    stepOnSupport ax (stepOnSupport ax x) = x := by
  classical
  have h21 : ax.state₂ ≠ ax.state₁ := fun h => ax.distinct h.symm
  have hstep1 : ax.step ax.state₁ ≠ ax.state₁ := by
    simpa [step_state₁ ax] using h21
  have hstep_state₁ :
      stepOnSupport ax ⟨ax.state₁, Or.inl rfl⟩ = ⟨ax.state₂, Or.inr rfl⟩ := by
    apply Subtype.ext
    simp [stepOnSupport, step_state₁ ax]
  have hstep_state₂ :
      stepOnSupport ax ⟨ax.state₂, Or.inr rfl⟩ = ⟨ax.state₁, Or.inl rfl⟩ := by
    apply Subtype.ext
    simp [stepOnSupport, step_state₂ ax, h21]
  rcases x.property with hx | hx
  · have hx' : x = ⟨ax.state₁, Or.inl rfl⟩ := by
      apply Subtype.ext
      simp [hx]
    subst hx'
    rw [hstep_state₁, hstep_state₂]
  · have hx' : x = ⟨ax.state₂, Or.inr rfl⟩ := by
      apply Subtype.ext
      simp [hx]
    subst hx'
    rw [hstep_state₂, hstep_state₁]

theorem obs_is_spin_measurement (ax : OscillationAxis) :
    ax.obs ax.state₁ ≠ ax.obs ax.state₂ := by
  intro hEq
  have hOpp := oscillation_axis_opposite_phase ax
  rw [hEq] at hOpp
  cases h : ax.obs ax.state₁ <;> simp at hOpp

theorem oscillation_is_minimal_spinor (ax : OscillationAxis) :
    Nonempty (OscillationSupport ax ≃ Fin 2) ∧
    (∀ x : OscillationSupport ax, stepOnSupport ax (stepOnSupport ax x) = x) ∧
    (ax.obs ax.state₁ ≠ ax.obs ax.state₂) := by
  exact ⟨⟨oscillationStates ax⟩, involutivity_is_double_cover ax, obs_is_spin_measurement ax⟩

end

end HeytingLean.Generative.SpinorBridge
