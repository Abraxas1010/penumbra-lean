import HeytingLean.Core.Nucleus

namespace HeytingLean.Integration.MagmaAsymptotic

/-- A property `φ` on a lattice `L` is preserved by a nucleus `N` when `φ x`
holds only if it also holds after applying the nucleus action. -/
def NucleusPreserved {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) (φ : L → Prop) : Prop :=
  ∀ x, φ x → φ (N.R x)

theorem nucleusPreserved_iff_carrier_closed {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) (φ : L → Prop) :
    NucleusPreserved N φ ↔ ∀ x, φ x → φ (N.R x) := by
  rfl

theorem fixed_preserves_all {L : Type*} [SemilatticeInf L] [OrderBot L]
    (N : HeytingLean.Core.Nucleus L) {x : L} (hx : N.R x = x) (φ : L → Prop) (hφ : φ x) :
    φ (N.R x) := by
  simpa [hx] using hφ

end HeytingLean.Integration.MagmaAsymptotic
