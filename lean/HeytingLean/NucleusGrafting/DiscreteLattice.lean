import Mathlib.Tactic
import HeytingLean.NucleusGrafting.Types
import HeytingLean.Eigen.NucleusReLU
import HeytingLean.Eigen.NucleusThreshold

namespace HeytingLean
namespace NucleusGrafting

def qRelu (z q : Int) : Int := max q z

theorem qRelu_idempotent (z q : Int) :
    qRelu z (qRelu z q) = qRelu z q := by
  dsimp [qRelu]
  exact max_eq_left (le_max_right q z)

theorem qRelu_extensive (z q : Int) :
    q ≤ qRelu z q := by
  dsimp [qRelu]
  exact le_max_left q z

theorem qRelu_meet_preserving (z a b : Int) :
    qRelu z (min a b) = min (qRelu z a) (qRelu z b) := by
  simpa [qRelu] using (max_min_distrib_right a b z)

theorem qRelu_fixed_iff (z q : Int) :
    qRelu z q = q ↔ z ≤ q := by
  dsimp [qRelu]
  constructor
  · intro h
    have hz : z ≤ max q z := le_max_right q z
    simpa [h] using hz
  · intro hz
    exact max_eq_left hz

structure ProductWitness where
  a : ActivationVector 2
  b : ActivationVector 2
  hNotALeB : ¬ a ≤ b
  hNotBLeA : ¬ b ≤ a

def canonicalProductWitness : ProductWitness where
  a
    | ⟨0, _⟩ => 0
    | ⟨1, _⟩ => 1
  b
    | ⟨0, _⟩ => 1
    | ⟨1, _⟩ => 0
  hNotALeB := by
    intro h
    have h1 := h ⟨1, by decide⟩
    norm_num at h1
  hNotBLeA := by
    intro h
    have h0 := h ⟨0, by decide⟩
    norm_num at h0

theorem productWitness_exists : ∃ _ : ProductWitness, True := by
  exact ⟨canonicalProductWitness, trivial⟩

end NucleusGrafting
end HeytingLean
