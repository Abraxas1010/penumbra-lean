import HeytingLean.MirandaDynamics.Fluids.ContactGeometry

/-!
# Cosymplectic geometry interfaces for viscosity-invariant fluid flows

This module packages the cosymplectic and harmonic-field data used to move from
contact/Reeb dynamics to viscosity-invariant stationary Navier-Stokes solutions.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids

universe u

/-- A cosymplectic structure packaged by its underlying contact data together
with the standard external closure/volume certificates. -/
structure CosymplecticData (M : Type u) where
  /-- The underlying contact-form data producing the Reeb flow. -/
  contact : ContactFormData M
  /-- External certificate that `α` is closed. -/
  alphaClosed : Prop
  /-- External certificate that `ω` is closed and `α ∧ ω` is a volume form. -/
  omegaClosedVolume : Prop

/-- A harmonic field is a Beltrami field together with the external certificate
that its Hodge Laplacian vanishes. -/
structure HarmonicFieldData (M : Type u) where
  /-- The underlying Beltrami field. -/
  beltrami : BeltramiFieldData M
  /-- External certificate that `ΔX = 0`. -/
  isHarmonic : Prop

/-- The cosymplectic Reeb field can be realized as a harmonic Beltrami field. -/
structure CosymplecticReebIsHarmonic (M : Type u) where
  /-- The ambient cosymplectic structure. -/
  cosymplectic : CosymplecticData M
  /-- The Reeb flow viewed as a Beltrami field. -/
  reebAsBeltrami : BeltramiFieldData M
  /-- The induced Beltrami flow agrees with the contact Reeb flow. -/
  flowConsistent : reebAsBeltrami.flow = cosymplectic.contact.reebFlow
  /-- External certificate that the Reeb field is harmonic. -/
  reebIsHarmonic : HarmonicFieldData M
  /-- The harmonic field is exactly the Beltrami realization above. -/
  harmonicIsBeltrami : reebIsHarmonic.beltrami = reebAsBeltrami

end Fluids
end MirandaDynamics
end HeytingLean
