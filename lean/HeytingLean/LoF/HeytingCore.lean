import Mathlib.Order.Heyting.Basic
import HeytingLean.LoF.Nucleus

/-!
# Heyting core of a re-entry nucleus

Basic API for the fixed-point sublocale `Ω_R`.

Direct path (LoF → Heyting):
- The re-entry nucleus `R` on a primary algebra `α` selects its stable
  elements; the fixed points `Ω_R` form a Heyting algebra. This provides a
  logic directly from LoF without requiring a numeric substrate.

Generative path (LoF → Surreal → Heyting):
- Alternatively, treat the Surreal layer as a generative substrate and apply
  an interior/closure operator `R` to extract a Heyting core on that domain.
  Both views are compatible; this module focuses on the direct path.
-/

namespace HeytingLean
namespace LoF
namespace Reentry

variable {α : Type u} [PrimaryAlgebra α]

section CoeLemmas

variable (R : Reentry α)

/-- Taking the infimum in `Ω_R` matches infimum of the underlying elements. -/
@[simp, norm_cast] lemma coe_inf (a b : R.Omega) :
    ((a ⊓ b : R.Omega) : α) = (a : α) ⊓ (b : α) := rfl

/-- Taking Heyting implication in `Ω_R` matches implication in the ambient algebra. -/
@[simp, norm_cast] lemma coe_himp (a b : R.Omega) :
    ((a ⇨ b : R.Omega) : α) = (a : α) ⇨ (b : α) := rfl

/-- Coercing a fixed point back to `α` and reentering leaves it unchanged. -/
@[simp] lemma apply_coe (a : R.Omega) : R (a : α) = a :=
  Reentry.Omega.apply_coe (R := R) a

end CoeLemmas

section HeytingFacts

variable (R : Reentry α)

instance instHeytingOmega : HeytingAlgebra (R.Omega) := inferInstance

/-- The standard Heyting adjunction transferred to the fixed-point algebra. -/
lemma heyting_adjunction (a b c : R.Omega) :
    a ⊓ b ≤ c ↔ a ≤ b ⇨ c :=
  (le_himp_iff (a := a) (b := b) (c := c)).symm

/-- Residuation restated in terms of the fixed-point Heyting structure. -/
lemma residuation (a b c : R.Omega) :
    c ≤ a ⇨ b ↔ c ⊓ a ≤ b :=
  (heyting_adjunction (R := R) c a b).symm

/-! #### Residuation simp helpers -/

/-- In `Ω_R`, bounding an implication is equivalent to bounding the corresponding meet. -/
@[simp] lemma le_himp_iff_inf_le (a b c : R.Omega) :
    a ≤ b ⇨ c ↔ a ⊓ b ≤ c :=
  (heyting_adjunction (R := R) a b c).symm

/-- Symmetric version of the Heyting adjunction on the fixed points. -/
@[simp] lemma inf_le_iff_le_himp (a b c : R.Omega) :
    a ⊓ b ≤ c ↔ a ≤ b ⇨ c :=
  (heyting_adjunction (R := R) a b c)

/-! #### Basic Heyting simp facts on `Ω_R` -/

/-- Every element implies itself to top inside `Ω_R`. -/
@[simp] lemma himp_self (a : R.Omega) : a ⇨ a = (⊤ : R.Omega) := by
  apply le_antisymm
  · exact le_top
  · -- `⊤ ≤ a ⇨ a` via `le_himp_iff_inf_le` on `⊤ ⊓ a ≤ a`.
    have : (⊤ : R.Omega) ⊓ a ≤ a := by simp
    exact (le_himp_iff_inf_le (R := R) (a := (⊤ : R.Omega)) (b := a) (c := a)).2 this

/-- Implicating from top simply returns the target element. -/
@[simp] lemma top_himp (a : R.Omega) : (⊤ : R.Omega) ⇨ a = a := by
  apply le_antisymm
  · -- `(⊤ ⇨ a) ≤ a` via the adjunction with `t := ⊤ ⇨ a`.
    have h : ((⊤ : R.Omega) ⇨ a) ⊓ (⊤ : R.Omega) ≤ a := by
      -- From `t ≤ ⊤ ⇨ a` with `t := ⊤ ⇨ a`.
      have ht : ((⊤ : R.Omega) ⇨ a) ≤ (⊤ : R.Omega) ⇨ a := le_rfl
      exact (inf_le_iff_le_himp (R := R)
        (a := ((⊤ : R.Omega) ⇨ a)) (b := (⊤ : R.Omega)) (c := a)).mpr ht
    have h' : (⊤ : R.Omega) ⇨ a ≤ a := by
      convert h using 1
      simp
    exact h'
  · -- `a ≤ ⊤ ⇨ a` from `a ⊓ ⊤ ≤ a`.
    have : a ⊓ (⊤ : R.Omega) ≤ a := by simp
    exact (heyting_adjunction (R := R) (a := a) (b := (⊤ : R.Omega)) (c := a)).mp this

/-- Implicating from bottom always yields top in the Heyting core. -/
@[simp] lemma bot_himp (a : R.Omega) : (⊥ : R.Omega) ⇨ a = (⊤ : R.Omega) := by
  apply le_antisymm
  · exact le_top
  · -- `⊤ ≤ ⊥ ⇨ a` via `⊤ ⊓ ⊥ ≤ a`.
    have : (⊤ : R.Omega) ⊓ (⊥ : R.Omega) ≤ a := by simp
    exact
      (le_himp_iff_inf_le (R := R) (a := (⊤ : R.Omega)) (b := (⊥ : R.Omega)) (c := a)).2 this

/-- Double negation is inflationary in the fixed-point algebra. -/
lemma double_neg (a : R.Omega) :
    a ≤ ((a ⇨ (⊥ : R.Omega)) ⇨ (⊥ : R.Omega)) := by
  have h₁ : (a ⇨ (⊥ : R.Omega)) ≤ a ⇨ (⊥ : R.Omega) := le_rfl
  have h₂ :
      (a ⇨ (⊥ : R.Omega)) ⊓ a ≤ (⊥ : R.Omega) :=
    (heyting_adjunction (R := R)
        (a := a ⇨ (⊥ : R.Omega)) (b := a) (c := ⊥)).mpr h₁
  have h₃ : a ⊓ (a ⇨ (⊥ : R.Omega)) ≤ (⊥ : R.Omega) := by
    convert h₂ using 1
    simp [inf_comm]
  exact
    (heyting_adjunction (R := R)
        (a := a) (b := a ⇨ (⊥ : R.Omega)) (c := ⊥)).mp h₃

/-! #### Additional residuation-style helper -/

/-- Modus ponens style inequality inside the Heyting core. -/
lemma inf_himp_le (a b : R.Omega) : a ⊓ (a ⇨ b) ≤ b := by
  -- Using `inf_le_iff_le_himp` with `t := a ⇨ b`, `u := a`, `v := b`.
  have : (a ⇨ b) ≤ a ⇨ b := le_rfl
  -- Convert to `(a ⇨ b) ⊓ a ≤ b` then swap by commutativity of inf.
  have h := (inf_le_iff_le_himp (R := R)
    (a := (a ⇨ b)) (b := a) (c := b)).mpr this
  have h' : a ⊓ (a ⇨ b) ≤ b := by
    convert h using 1
    simp [inf_comm]
  exact h'

section BooleanLimit

open scoped Classical

variable (R : Reentry α)

/-- If the nucleus fixes every element, `Ω_R` is equivalent to the ambient algebra. -/
def booleanEquiv (h : ∀ a : α, R a = a) : R.Omega ≃ α where
  toFun := Subtype.val
  invFun := fun a => Omega.mk (R := R) a (h a)
  left_inv := by
    intro a
    ext
    rfl
  right_inv := by
    intro a
    have hx : R a = a := h a
    simp [Omega.mk]

/-- The equivalence sends a fixed point to its underlying element. -/
@[simp] lemma booleanEquiv_apply (h : ∀ a : α, R a = a) (a : R.Omega) :
    booleanEquiv (R := R) h a = (a : α) := rfl

/-- The inverse equivalence equips an ambient element with the proof that `R` fixes it. -/
@[simp] lemma booleanEquiv_symm_apply (h : ∀ a : α, R a = a) (a : α) :
    (booleanEquiv (R := R) h).symm a = Omega.mk (R := R) a (h a) := rfl

/-- When `R` is the identity nucleus, reentering the Boolean equivalence returns the input. -/
lemma boolean_limit (h : ∀ a : α, R a = a) (a : α) :
    R ((booleanEquiv (R := R) h).symm a : R.Omega) = a := by
  have hx : R a = a := h a
  dsimp [booleanEquiv]
  change R ((Omega.mk (R := R) a hx : R.Omega) : α) = a
  simp [Omega.mk, hx]

end BooleanLimit

end HeytingFacts

end Reentry
end LoF
end HeytingLean
