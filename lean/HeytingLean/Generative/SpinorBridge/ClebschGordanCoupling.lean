import HeytingLean.Generative.SpinorBridge.SU2Core
import HeytingLean.Generative.SpinorBridge.OscillatorSpinorEquiv
import HeytingLean.Generative.ReEntryPlane

namespace HeytingLean.Generative.SpinorBridge

open HeytingLean.Generative

theorem clebsch_gordan_dimension :
    1 + 3 = Fintype.card (Fin 2) * Fintype.card (Fin 2) := by
  decide

/-- A coupling channel for two spin-1/2 states. -/
structure CouplingChannel where
  j : ℕ
  multiplicity : ℕ
  mult_eq : multiplicity = 2 * j + 1

def singlet : CouplingChannel where
  j := 0
  multiplicity := 1
  mult_eq := rfl

def triplet : CouplingChannel where
  j := 1
  multiplicity := 3
  mult_eq := rfl

/-- Channels with positive total spin support a preferred spatial direction. -/
def supportsPreferredDirection (c : CouplingChannel) : Prop :=
  0 < c.j

theorem singlet_has_no_preferred_direction :
    ¬ supportsPreferredDirection singlet := by
  simp [supportsPreferredDirection, singlet]

theorem triplet_has_preferred_direction :
    supportsPreferredDirection triplet := by
  simp [supportsPreferredDirection, triplet]

/-- A re-entry triangle contributes the positive aspect-ratio witness, while the
canonical re-entry spin channel is the triplet. This is an interpretive
assignment of the channel, not a derivation from Clebsch-Gordan coefficients. -/
theorem reentry_triangle_has_positive_aspect_and_canonical_triplet
    (t : ReEntryTriangle) :
    0 < t.aspect_ratio ∧ supportsPreferredDirection triplet ∧
      ¬ supportsPreferredDirection singlet := by
  exact ⟨t.aspect_pos, triplet_has_preferred_direction, singlet_has_no_preferred_direction⟩

/-- A trivalent spin-network vertex, recorded in doubled half-integer units. -/
structure TrivalentVertex where
  j₁ : ℕ
  j₂ : ℕ
  jOut : ℕ
  lower₁ : j₁ - j₂ ≤ jOut
  lower₂ : j₂ - j₁ ≤ jOut
  upper : jOut ≤ j₁ + j₂

def fundamentalVertex : TrivalentVertex where
  j₁ := 1
  j₂ := 1
  jOut := 2
  lower₁ := by omega
  lower₂ := by omega
  upper := by omega

theorem fundamental_vertex_admissible :
    fundamentalVertex.j₁ = 1 ∧
    fundamentalVertex.j₂ = 1 ∧
    fundamentalVertex.jOut = 2 ∧
    fundamentalVertex.jOut = fundamentalVertex.j₁ + fundamentalVertex.j₂ := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Canonical spin-1 output channel assigned to re-entry couplings. -/
def reentryChannel : CouplingChannel :=
  triplet

end HeytingLean.Generative.SpinorBridge
