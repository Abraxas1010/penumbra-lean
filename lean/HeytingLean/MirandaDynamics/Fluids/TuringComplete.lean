import Mathlib.Order.Nucleus
import HeytingLean.MirandaDynamics.Fluids.HarmonicNS
import HeytingLean.MirandaDynamics.FixedPoint.PeriodicNucleus
import HeytingLean.MirandaDynamics.External.Interfaces
import HeytingLean.MirandaDynamics.Undecidability.Transfers

/-!
# Navier-Stokes Turing completeness and undecidability

The geometry remains external, but the transfer from a halting reduction to
fluid-trajectory and fluid-periodicity undecidability is proved in Lean.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids

open Nat.Partrec
open HeytingLean.MirandaDynamics

universe u

/-- The full fluids-lane construction: a cosymplectic Euler realization, the
viscosity-invariance step, and a halting reduction into a trajectory predicate. -/
structure FluidTuringConstruction (M : Type u) [Primcodable M] where
  /-- The geometric chain up to a harmonic Euler solution. -/
  euler : CosymplecticEulerConstruction M
  /-- The viscosity-invariance package extending Euler to NS. -/
  viscosityInvariant : HarmonicViscosityInvariance M
  /-- External certificate that the construction encodes a universal TM. -/
  encodesUniversalTM : Prop
  /-- The trajectory predicate used for the halting reduction. -/
  trajectoryPredicate : M → Prop
  /-- For each input length, halting reduces to the trajectory predicate. -/
  haltingReduces : ∀ n : ℕ, External.HaltingReduction (β := M) n trajectoryPredicate

/-- Trajectory prediction is undecidable whenever the halting problem reduces to
the fluid predicate supplied by the construction. -/
theorem fluid_trajectory_undecidable {M : Type u} [Primcodable M]
    (C : FluidTuringConstruction M) (n : ℕ) :
    ¬ComputablePred C.trajectoryPredicate :=
  Undecidability.Halting.not_computable_of_halting_reduces (n := n) (C.haltingReduces n).red

/-- A periodicity detector for the fluid system, together with the equivalence
between periodicity and the trajectory predicate used in the reduction. -/
structure PeriodicityDetection (M : Type u) [Primcodable M] where
  periodic : M → Prop
  construction : FluidTuringConstruction M
  periodicIffTrajectory : ∀ x, periodic x ↔ construction.trajectoryPredicate x

/-- The trajectory predicate many-one reduces to periodicity via the identity
map whenever the two predicates are equivalent pointwise. -/
def trajectoryReducesToPeriodicity {M : Type u} [Primcodable M]
    (P : PeriodicityDetection M) :
    Undecidability.ManyOne
      (p := P.construction.trajectoryPredicate)
      (q := P.periodic) where
  f := id
  computable_f := Computable.id
  correct := fun x => (P.periodicIffTrajectory x).symm

/-- Periodicity detection for the fluid flow is undecidable because trajectory
prediction already is. -/
theorem fluid_periodicity_undecidable {M : Type u} [Primcodable M]
    (P : PeriodicityDetection M) (n : ℕ) :
    ¬ComputablePred P.periodic :=
  Undecidability.ManyOne.not_computable_of_reduces
    (p := P.construction.trajectoryPredicate)
    (q := P.periodic)
    (trajectoryReducesToPeriodicity P)
    (fluid_trajectory_undecidable P.construction n)

/-- The periodicity predicate yields the familiar union nucleus on sets of
fluid states. -/
def fluidPeriodicNucleus {M : Type u} (periodic : M → Prop) :
    Nucleus (Set M) :=
  FixedPoint.unionNucleus (α := M) {x | periodic x}

/-- Fixed points of the fluid periodicity nucleus are exactly the supersets of
the periodic region. -/
theorem fluidPeriodicNucleus_fixed_iff {M : Type u} (periodic : M → Prop) (S : Set M) :
    fluidPeriodicNucleus periodic S = S ↔ {x | periodic x} ⊆ S := by
  simpa [fluidPeriodicNucleus] using
    (FixedPoint.isFixedPoint_unionNucleus_iff (α := M) {x | periodic x} S)

end Fluids
end MirandaDynamics
end HeytingLean
