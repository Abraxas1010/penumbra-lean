import Mathlib.Data.Set.Lattice

namespace HeytingLean
namespace OTM
namespace DynamicsComputation

universe u

/-- A discrete-time dynamical system with semigroup-style flow laws. -/
structure DynamicalSystem (X : Type u) where
  flow : Nat → X → X
  flow_zero : ∀ x : X, flow 0 x = x
  flow_add : ∀ m n x, flow (m + n) x = flow m (flow n x)

namespace DynamicalSystem

variable {X : Type u} (D : DynamicalSystem X)

/-- Reachability in the underlying discrete-time flow. -/
def reaches (x y : X) : Prop :=
  ∃ n : Nat, D.flow n x = y

/-- Reachability closure of a proposition on states. -/
def reachabilityClosure (U : Set X) : Set X :=
  { x | ∃ n : Nat, D.flow n x ∈ U }

/-- Equilibrium states: fixed by all time steps. -/
def equilibriumSet : Set X :=
  { x | ∀ n : Nat, D.flow n x = x }

theorem mem_reachabilityClosure_iff (U : Set X) (x : X) :
    x ∈ D.reachabilityClosure U ↔ ∃ n : Nat, D.flow n x ∈ U := Iff.rfl

theorem reachabilityClosure_mono {U V : Set X} (hUV : U ⊆ V) :
    D.reachabilityClosure U ⊆ D.reachabilityClosure V := by
  intro x hx
  rcases hx with ⟨n, hn⟩
  exact ⟨n, hUV hn⟩

theorem subset_reachabilityClosure (U : Set X) :
    U ⊆ D.reachabilityClosure U := by
  intro x hx
  refine ⟨0, ?_⟩
  simpa [D.flow_zero x] using hx

theorem reachabilityClosure_idempotent (U : Set X) :
    D.reachabilityClosure (D.reachabilityClosure U) = D.reachabilityClosure U := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with ⟨n, hn⟩
    rcases hn with ⟨m, hm⟩
    refine ⟨m + n, ?_⟩
    simpa [D.flow_add m n x] using hm
  · exact D.subset_reachabilityClosure (D.reachabilityClosure U)

theorem reachabilityClosure_inter_subset (U V : Set X) :
    D.reachabilityClosure (U ∩ V) ⊆ D.reachabilityClosure U ∩ D.reachabilityClosure V := by
  intro x hx
  rcases hx with ⟨n, hn⟩
  exact ⟨⟨n, hn.1⟩, ⟨n, hn.2⟩⟩

theorem reaches_refl (x : X) : D.reaches x x := by
  refine ⟨0, ?_⟩
  simpa using D.flow_zero x

theorem reaches_trans {x y z : X} (hxy : D.reaches x y) (hyz : D.reaches y z) :
    D.reaches x z := by
  rcases hxy with ⟨m, hm⟩
  rcases hyz with ⟨n, hn⟩
  refine ⟨n + m, ?_⟩
  calc
    D.flow (n + m) x = D.flow n (D.flow m x) := D.flow_add n m x
    _ = D.flow n y := by simp [hm]
    _ = z := hn

theorem equilibrium_mem_reachabilityClosure_of_mem (U : Set X) {x : X}
    (hxU : x ∈ U) :
    x ∈ D.reachabilityClosure U := by
  refine ⟨0, ?_⟩
  simpa [D.flow_zero x] using hxU

theorem flow_preserves_equilibrium {x : X} (hx : x ∈ D.equilibriumSet) (n : Nat) :
    D.flow n x = x :=
  hx n

end DynamicalSystem

end DynamicsComputation
end OTM
end HeytingLean
