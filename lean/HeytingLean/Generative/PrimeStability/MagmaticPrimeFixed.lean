import HeytingLean.Generative.PrimeStability.PrimePeriodicity
import HeytingLean.Magma.Bridge.NucleusProjection
import HeytingLean.Magma.Bridge.HeytingGapMeasure
import HeytingLean.Magma.Bridge.ComputationalIrreducibility
import HeytingLean.Magma.Separation.MagmaticClass
import HeytingLean.Magma.Separation.MSS

/-!
# Generative.PrimeStability.MagmaticPrimeFixed

Phase 3 connects prime-period closures to the existing Tzouvaras magmatic
infrastructure.

The existing `Magma/Bridge/*` files already give the fixed-point surface
`omega_R`, the Heyting gap, and the nonzero-gap witness for non-fixed magma
elements. What they do not provide by themselves is a canonical coercion from
periodic orbit data to the magmatic nucleus. This file makes that bridge
explicit.

The key design choice is honesty: when a statement needs a link between orbit
irreducibility and the magmatic fixed-point layer, that link is carried as a
named bridge hypothesis in `MagmaticRotationalClosure` instead of being
smuggled in through a vacuous proof.
-/

namespace HeytingLean.Generative.PrimeStability

open HeytingLean
open HeytingLean.Magma
open HeytingLean.Magma.Bridge
open HeytingLean.Magma.Separation

variable {A : Type*} [MagmaticAtoms A] [u : MagmaticUniverse A]

/-- Lower families in a magma are magmatic classes. -/
theorem familyOf_magmatic (x : Magma A) :
    MagmaticClass (familyOf x) := by
  intro y hy z hz
  unfold familyOf at hy ⊢
  exact u.le_trans hz hy

variable [PairEncoding A] [ProductEncoding A]

/-- A rotational closure equipped with the explicit bridge data needed to talk
honestly to the magmatic nucleus. -/
structure MagmaticRotationalClosure (N : MagmaticNucleus A) where
  closure : RotationalClosure (Magma A)
  evolution_is_nucleus :
    ∀ x, familyOf (closure.F x) = N.nucleus.R (familyOf x)
  prime_to_fixed :
    IrreducibleClosure closure → closure.x₀ ∈ omega_R N
  composite_to_gap :
    CompositeClosure closure → closure.x₀ ∈ irreducible_complement N
  inseparable_family :
    ∀ (φ : Magma A → Prop), MagmaticClass { x | φ x } →
      (∀ y ∈ familyOf closure.x₀, φ y) ∨
      (∀ y ∈ familyOf closure.x₀, ¬ φ y)

/-- The magmatic separation scheme carves out any downward-closed subfamily of
the base magma. -/
theorem separated_subfamily_exists [SeparationPresentation A]
    {N : MagmaticNucleus A} (mrc : MagmaticRotationalClosure N)
    (φ : Magma A → Prop) (hMag : MagmaticClass { x | φ x })
    (hNonempty : ∃ x, x ∈ mrc.closure.x₀ ∧ φ x) :
    ∃ m : Magma A, ∀ x : Magma A, x ∈ m ↔ x ∈ mrc.closure.x₀ ∧ φ x := by
  simpa using magmatic_separation_scheme φ hMag mrc.closure.x₀ hNonempty

/-- Bridge hypothesis unpacking: the chosen prime-period closure is assumed to land in `Ω_R`. -/
theorem bridge_prime_to_fixed {N : MagmaticNucleus A}
    (mrc : MagmaticRotationalClosure N)
    (hIrr : IrreducibleClosure mrc.closure) :
    mrc.closure.x₀ ∈ omega_R N :=
  mrc.prime_to_fixed hIrr

/-- Bridge hypothesis unpacking: the chosen composite closure is assumed to lie outside `Ω_R`. -/
theorem bridge_composite_to_gap {N : MagmaticNucleus A}
    (mrc : MagmaticRotationalClosure N)
    (hComp : CompositeClosure mrc.closure) :
    mrc.closure.x₀ ∉ omega_R N :=
  mrc.composite_to_gap hComp

/-- Under the bridge hypothesis, fixed magmatic closures have vanishing Heyting gap. -/
theorem bridge_irreducible_gap_zero {N : MagmaticNucleus A}
    (mrc : MagmaticRotationalClosure N)
    (hIrr : IrreducibleClosure mrc.closure) :
    heyting_gap N mrc.closure.x₀ = ∅ :=
  (gap_zero_iff_fixed N mrc.closure.x₀).2 (bridge_prime_to_fixed mrc hIrr)

/-- Under the bridge hypothesis, composite closures carry a nonzero Heyting gap. -/
theorem bridge_composite_gap_nonzero {N : MagmaticNucleus A}
    (mrc : MagmaticRotationalClosure N)
    (hComp : CompositeClosure mrc.closure) :
    heyting_gap N mrc.closure.x₀ ≠ ∅ :=
  irreducible_has_nonzero_gap N (mrc.composite_to_gap hComp)

/-- Bridge hypothesis unpacking: inseparable families stay all-or-nothing on the chosen core. -/
theorem bridge_inseparable_family {N : MagmaticNucleus A}
    (mrc : MagmaticRotationalClosure N)
    (hIrr : IrreducibleClosure mrc.closure)
    (φ : Magma A → Prop) (hMag : MagmaticClass { x | φ x }) :
    (∀ y ∈ familyOf mrc.closure.x₀, φ y) ∨
    (∀ y ∈ familyOf mrc.closure.x₀, ¬ φ y) := by
  have _hω : mrc.closure.x₀ ∈ omega_R N := bridge_prime_to_fixed mrc hIrr
  have _hcore : MagmaticClass (N.nucleus.R (familyOf mrc.closure.x₀)) :=
    fixed_core_magmatic N mrc.closure.x₀
  exact mrc.inseparable_family φ hMag

end HeytingLean.Generative.PrimeStability
