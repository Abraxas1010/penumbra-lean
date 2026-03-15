import HeytingLean.MirandaDynamics.Fluids.CosymplecticGeometry

/-!
# Etnyre-Ghrist correspondence

This module packages the hydrodynamic/contact-topological bridge:
rotational Beltrami fields and Reeb flows share the same orbit structure up to
reparametrization.
-/

namespace HeytingLean
namespace MirandaDynamics
namespace Fluids

universe u

/-- The Etnyre-Ghrist correspondence packages a contact form, a rotational
Beltrami field, and the monotone reparametrization relating their flows. -/
structure EtnyreGhristCorrespondence (M : Type u) where
  /-- A contact form producing the Reeb flow. -/
  contact : ContactFormData M
  /-- The corresponding rotational Beltrami field. -/
  beltrami : BeltramiFieldData M
  /-- A monotone time reparametrization relating the two flows. -/
  reparametrization : ℕ → ℕ
  reparam_mono : ∀ m n, m ≤ n → reparametrization m ≤ reparametrization n
  reparam_consistent : ∀ n x, beltrami.flow n x = contact.reebFlow (reparametrization n) x

/-- Beltrami periodicity transfers directly to Reeb periodicity via the
reparametrization identity. -/
theorem periodic_reeb_of_beltrami_periodic {M : Type u}
    (eg : EtnyreGhristCorrespondence M) {x : M} {n : ℕ}
    (hperiodic : eg.beltrami.flow n x = x) :
    eg.contact.reebFlow (eg.reparametrization n) x = x := by
  calc
    eg.contact.reebFlow (eg.reparametrization n) x = eg.beltrami.flow n x := by
      symm
      exact eg.reparam_consistent n x
    _ = x := hperiodic

/-- Reverse orbit sharing is packaged explicitly because the corresponding
return time generally depends on the external geometry. -/
structure SharedOrbitWitness (M : Type u) where
  eg : EtnyreGhristCorrespondence M
  /-- Any Reeb-periodic point returns under the Beltrami flow at some positive
  iterate. -/
  reebPeriodicImpliesBeltramiReturns :
    ∀ x n, 0 < n → eg.contact.reebFlow n x = x →
      ∃ m, 0 < m ∧ eg.beltrami.flow m x = x

end Fluids
end MirandaDynamics
end HeytingLean
