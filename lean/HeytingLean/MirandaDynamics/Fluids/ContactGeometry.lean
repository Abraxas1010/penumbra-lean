import HeytingLean.OTM.DynamicsComputation.DynamicalSystem

/-!
# Contact geometry interfaces for the Miranda fluids lane

This module packages the contact-form and Beltrami-field data needed for the
Navier-Stokes/cosymplectic undecidability chain.

The geometry itself remains external. Lean tracks only the algebraic flow laws
and the certificates exposed by the cited literature.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids

universe u

open HeytingLean.OTM.DynamicsComputation

/-- A contact form on a 3-manifold, represented by the discrete-time Reeb flow
it induces together with an external contact certificate. -/
structure ContactFormData (M : Type u) where
  /-- The Reeb vector field integrated to a discrete flow. -/
  reebFlow : ℕ → M → M
  reebFlow_zero : ∀ x, reebFlow 0 x = x
  reebFlow_add : ∀ m n x, reebFlow (m + n) x = reebFlow m (reebFlow n x)
  /-- External certificate for the contact condition `α ∧ dα ≠ 0`. -/
  isContact : Prop

/-- The Reeb flow can be viewed as a discrete-time dynamical system. -/
def ContactFormData.toDynamics {M : Type u} (C : ContactFormData M) :
    DynamicalSystem M where
  flow := C.reebFlow
  flow_zero := C.reebFlow_zero
  flow_add := C.reebFlow_add

/-- A Beltrami field is packaged by its induced flow and the standard external
hydrodynamic certificates used in the Etnyre-Ghrist correspondence. -/
structure BeltramiFieldData (M : Type u) where
  /-- The flow induced by the Beltrami field. -/
  flow : ℕ → M → M
  flow_zero : ∀ x, flow 0 x = x
  flow_add : ∀ m n x, flow (m + n) x = flow m (flow n x)
  /-- External certificate that `curl X = f • X` for some nonvanishing `f`. -/
  isBeltrami : Prop
  /-- External certificate that the field is incompressible. -/
  isDivergenceFree : Prop
  /-- External certificate that the Beltrami factor never vanishes. -/
  isRotational : Prop

/-- Any Beltrami field also determines a discrete-time dynamical system. -/
def BeltramiFieldData.toDynamics {M : Type u} (B : BeltramiFieldData M) :
    DynamicalSystem M where
  flow := B.flow
  flow_zero := B.flow_zero
  flow_add := B.flow_add

end Fluids
end MirandaDynamics
end HeytingLean
