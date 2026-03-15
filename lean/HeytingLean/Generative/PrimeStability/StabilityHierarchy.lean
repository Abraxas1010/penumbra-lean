import Mathlib.Dynamics.PeriodicPts.Lemmas
import HeytingLean.Generative.PrimeStability.MagmaticPrimeFixed
import HeytingLean.Generative.NoneistOscillation
import HeytingLean.Generative.UDTPostulates

/-!
# Generative.PrimeStability.StabilityHierarchy

Phase 4 interprets the prime-period results physically.

The only genuinely derived concrete particle here is the electron: the existing
`noneistAxis` is an involutive non-fixed oscillation, so its minimal period is
exactly `2`. The photon surface is represented by the identity closure on the
pre-differentiated ground.
-/

namespace HeytingLean.Generative.PrimeStability

open HeytingLean.Generative

structure UDPState (α : Type*) where
  closure : RotationalClosure α

structure PhotonState (α : Type*) extends UDPState α where
  period_one : closure.period = 1

structure ElectronState (α : Type*) extends UDPState α where
  period_two : closure.period = 2

def photonClosure : RotationalClosure PUnit where
  F := id
  x₀ := PUnit.unit
  periodic_mem := by
    refine ⟨1, by decide, ?_⟩
    rfl

def noneistClosure : RotationalClosure noneistAxis.Carrier where
  F := noneistAxis.step
  x₀ := noneistAxis.state₁
  periodic_mem := by
    refine ⟨2, by decide, ?_⟩
    simpa using noneistAxis.involutive noneistAxis.state₁

theorem photon_closure_period_one :
    photonClosure.period = 1 := by
  simp [photonClosure, RotationalClosure.period]

theorem noneist_axis_period_two :
    Function.minimalPeriod noneistAxis.step noneistAxis.state₁ = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hper : Function.IsPeriodicPt noneistAxis.step 2 noneistAxis.state₁ := by
    simpa using noneistAxis.involutive noneistAxis.state₁
  have hfix : ¬ Function.IsFixedPt noneistAxis.step noneistAxis.state₁ := by
    intro hfix
    have h21 : noneistAxis.state₂ = noneistAxis.state₁ := by
      rw [noneistAxis.states_step, hfix]
    exact noneistAxis.distinct h21.symm
  exact Function.minimalPeriod_eq_prime hper hfix

def canonicalPhoton : PhotonState PUnit where
  toUDPState := ⟨photonClosure⟩
  period_one := photon_closure_period_one

def canonicalElectron : ElectronState noneistAxis.Carrier where
  toUDPState := ⟨noneistClosure⟩
  period_two := by
    simp [noneistClosure, RotationalClosure.period, noneist_axis_period_two]

theorem photon_massless {α : Type*} (p : PhotonState α) :
    ¬ hasTrappedAsymmetry p.closure := by
  simp [hasTrappedAsymmetry, p.period_one]

theorem electron_massive {α : Type*} (e : ElectronState α) :
    hasTrappedAsymmetry e.closure := by
  simp [hasTrappedAsymmetry, e.period_two]

theorem electron_stable {α : Type*} (e : ElectronState α) :
    IrreducibleClosure e.closure := by
  simpa [IrreducibleClosure, e.period_two] using (by decide : Nat.Prime 2)

theorem electron_is_terminal {α : Type*} (rc : RotationalClosure α)
    (hStable : IrreducibleClosure rc) :
    2 ≤ rc.period :=
  two_is_terminal_prime rc.period hStable

theorem stability_hierarchy {α : Type*} (rc : RotationalClosure α)
    (hMassive : hasTrappedAsymmetry rc) (hStable : ¬ Decomposable rc) :
    Nat.Prime rc.period ∧ 2 ≤ rc.period := by
  refine ⟨stable_massive_has_prime_period rc hMassive hStable, ?_⟩
  exact two_is_terminal_prime rc.period
    (stable_massive_has_prime_period rc hMassive hStable)

end HeytingLean.Generative.PrimeStability
