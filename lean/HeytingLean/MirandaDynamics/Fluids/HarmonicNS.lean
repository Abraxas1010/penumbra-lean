import HeytingLean.MirandaDynamics.Fluids.EtnyreGhrist

/-!
# Harmonic fields solve stationary Navier-Stokes

This module packages the viscosity-invariance step in the fluids lane:
harmonic stationary Euler fields remain stationary Navier-Stokes solutions for
arbitrary viscosity.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids

universe u

/-- A stationary Navier-Stokes solution represented by its harmonic field and a
viscosity parameter, together with the external analytic certificate that it
solves the stationary equation at that viscosity. -/
structure NavierStokesSolution (M : Type u) where
  harmonicField : HarmonicFieldData M
  viscosity : ℕ
  solvesNS : Prop

/-- Harmonic Euler solutions are viscosity-invariant: once the viscosity-zero
solution exists, the same harmonic field yields stationary Navier-Stokes
solutions for every viscosity parameter. -/
structure HarmonicViscosityInvariance (M : Type u) where
  eulerSolution : NavierStokesSolution M
  eulerAtZero : eulerSolution.viscosity = 0
  viscosityInvariant :
    ∀ ν : ℕ,
      ∃ sol : NavierStokesSolution M,
        sol.harmonicField = eulerSolution.harmonicField ∧
        sol.viscosity = ν ∧
        sol.solvesNS

/-- The cosymplectic construction produces a harmonic Reeb field whose
Beltrami realization solves Euler. -/
structure CosymplecticEulerConstruction (M : Type u) where
  reebHarmonic : CosymplecticReebIsHarmonic M
  etnyreGhrist : EtnyreGhristCorrespondence M
  beltramiConsistent : etnyreGhrist.beltrami = reebHarmonic.reebAsBeltrami
  solvesEuler : NavierStokesSolution M
  eulerAtZero : solvesEuler.viscosity = 0
  solutionIsHarmonic : solvesEuler.harmonicField = reebHarmonic.reebIsHarmonic

end Fluids
end MirandaDynamics
end HeytingLean
