import HeytingLean.Numbers.SurrealCore
import HeytingLean.LoF.IntReentry
import Mathlib.Data.Set.BooleanAlgebra

/-!
# Surreal nucleus support

This module lifts the `SurrealCore` canonicalisation
machinery into a closure operator `J` that behaves like a nucleus on
sets of pre-games.  It is the primary bridge between the rank-indexed
games developed in `GameN`/`Operations` and the more abstract re-entry
interface used by the generative API.
-/

namespace HeytingLean
namespace Numbers
namespace Surreal

open Set

universe u

variable {α : Type u}

namespace Core

open HeytingLean.Numbers.SurrealCore

/-- Canonical legal image of a set of pre-games. -/
def canonImage (S : Set PreGame) : Set PreGame :=
  { g | SurrealCore.legal g ∧ ∃ h ∈ S, SurrealCore.canonicalize h = g }

/-- Surreal nucleus (closure on sets of pre-games): keep original games and add
    canonical legal images. -/
def J (S : Set PreGame) : Set PreGame :=
  S ∪ canonImage S

@[simp] lemma subset_J (S : Set PreGame) : S ⊆ J S := by
  intro x hx; exact Or.inl hx

lemma mono_J {S T : Set PreGame} (hST : S ⊆ T) : J S ⊆ J T := by
  intro g hg
  rcases hg with hg | hg
  · exact Or.inl (hST hg)
  · -- g ∈ canonImage S
    rcases hg with ⟨hleg, h, hS, hcanon⟩
    exact Or.inr ⟨hleg, h, hST hS, hcanon⟩

lemma idem_J (S : Set PreGame) : J (J S) = J S := by
  ext g; constructor
  · intro hg
    rcases hg with hg | hg
    · exact hg
    · rcases hg with ⟨hleg, h, hJS, hcanon⟩
      rcases hJS with hS | hCanonS
      · exact Or.inr ⟨hleg, h, hS, hcanon⟩
      · rcases hCanonS with ⟨hleg', t, htS, htc⟩
        have hcanon' : SurrealCore.canonicalize (SurrealCore.canonicalize t) = g := by
          simpa [htc] using hcanon
        have hcanon_t : SurrealCore.canonicalize t = g := by
          simpa [SurrealCore.canonicalize_idem] using hcanon'
        exact Or.inr ⟨hleg, t, htS, hcanon_t⟩
  · intro hg
    exact Or.inl hg

end Core

/-! Note: a closure-style nucleus `J_nucleus : Nucleus (Set PreGame)` can be
packaged from `Core.J` following the pattern of `R_union` in
`Surreal.NucleusCore`. For the current Direction 6 plan we keep this as a
blueprint-level comment and reuse `R_union`-style nuclei where needed. -/

-- Interior-style nucleus candidate: restrict to legal canonical elements.
namespace Int

open HeytingLean.Numbers.SurrealCore

/-- Canonical legal core. -/
def C : Set PreGame := { g | SurrealCore.legal g ∧ SurrealCore.canonicalize g = g }

/-- Interior operator: intersect with the canonical legal core. -/
def I (S : Set PreGame) : Set PreGame := S ∩ C

@[simp] lemma I_subset {S : Set PreGame} : I S ⊆ S := by
  intro g hg; exact hg.1

lemma mono_I {S T : Set PreGame} (hST : S ⊆ T) : I S ⊆ I T := by
  intro g hg
  exact And.intro (hST hg.1) hg.2

@[simp] lemma idem_I (S : Set PreGame) : I (I S) = I S := by
  ext g; constructor
  · intro hg
    rcases hg with ⟨hgIS, hgC⟩
    rcases hgIS with ⟨hS, _⟩
    exact And.intro hS hgC
  · intro hg
    rcases hg with ⟨hS, hC⟩
    exact And.intro ⟨hS, hC⟩ hC

@[simp] lemma I_inf (S T : Set PreGame) : I (S ∩ T) = I S ∩ I T := by
  ext g; constructor
  · intro hg; rcases hg with ⟨⟨hS, hT⟩, hC⟩; exact And.intro ⟨hS, hC⟩ ⟨hT, hC⟩
  · intro hg; rcases hg with ⟨⟨hS, hC1⟩, ⟨hT, hC2⟩⟩; exact ⟨⟨hS, hT⟩, hC1⟩

/-- Polarity-reversed dual closure generated from surreal interior `I`. -/
def dualClosure (S : Set PreGame) : Set PreGame :=
  (I Sᶜ)ᶜ

@[simp] lemma dualClosure_eq_compl_interior_compl (S : Set PreGame) :
    dualClosure S = (I Sᶜ)ᶜ := rfl

@[simp] lemma interior_eq_compl_dualClosure_compl (S : Set PreGame) :
    I S = (dualClosure Sᶜ)ᶜ := by
  ext g
  simp [dualClosure]

/--
Queue anchor theorem for `ontology_closure_interior_duality_20260219` in the
Surreal setting.
--/
theorem ontology_closure_interior_duality_20260219 (S : Set PreGame) :
    I S = (dualClosure Sᶜ)ᶜ :=
  interior_eq_compl_dualClosure_compl (S := S)

end Int

/-- `Set PreGame` carries a natural frame; lift it to `PrimaryAlgebra`. -/
instance : HeytingLean.LoF.PrimaryAlgebra (Set SurrealCore.PreGame) :=
  { toFrame := inferInstance }

/-- Build an interior re-entry for sets of pre-games using `Int.I`. -/
def intReentry : HeytingLean.LoF.IntReentry (Set SurrealCore.PreGame) where
  nucleus :=
    { act := Int.I
      monotone := by
        intro S T hST; intro g hg; exact And.intro (hST hg.1) hg.2
      idempotent := by
        intro S; exact Int.idem_I (S := S)
      apply_le := by intro S g hg; exact hg.1
      map_inf := by
        intro S T; exact Int.I_inf (S := S) (T := T) }

end Surreal
end Numbers
end HeytingLean
