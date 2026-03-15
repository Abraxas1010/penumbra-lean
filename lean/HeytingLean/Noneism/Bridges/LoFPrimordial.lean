import HeytingLean.Noneism.Foundation
import HeytingLean.LoF.HeytingCore
import HeytingLean.LoF.Instances
import Mathlib.Order.Heyting.Hom

/-!
# Noneism ↔ LoF bridge: Primordial distinction as a 2-point re-entry core

This module ties the `Noneism.Foundation` assumption to the existing Laws-of-Form (LoF) machinery.

Key idea:
- The `PrimordialTension` engine supplies a 1-bit observable `obs : Nothing → Bool`.
- That induces a canonical "two-point" view of the world (`Bool`) and a pullback map on predicates:
    `S ⊆ Bool` ↦ `{ x : Nothing | obs x ∈ S }`.
- On `Set Bool` we can build a tiny LoF `Reentry` structure (with the identity nucleus),
  whose primordial/counter elements are the singletons `{true}` and `{false}`.

This is intentionally the *smallest* bridge that:
1) makes the Mark/unmark polarity explicit,
2) hooks into `LoF.Reentry` and its Heyting core `Ω_R`,
3) documents what is axiomatic vs derived.

Future extension:
- Replace the trivial identity nucleus by a nontrivial nucleus derived from additional structure,
  while keeping the same API and bridge theorems.
-/

namespace HeytingLean
namespace Noneism
namespace Bridge
namespace LoFPrimordial

open HeytingLean.LoF

noncomputable section

/-! ## A canonical 2-point LoF core -/

abbrev TwoPoint : Type := Bool
abbrev TwoPred : Type := Set TwoPoint

-- `Set Bool` is a complete Boolean algebra, hence a frame; we package it as a LoF primary algebra.
instance : LoF.PrimaryAlgebra TwoPred := by
  -- `PrimaryAlgebra` just extends `Order.Frame`.
  -- Mathlib provides `Order.Frame` for `Set α`.
  classical
  infer_instance

/-- The identity nucleus on `Set Bool`. In Mathlib, `⊥ : Nucleus X` is the identity nucleus. -/
def idNucleus : Nucleus TwoPred := (⊥ : Nucleus TwoPred)

/-- The singleton `{b}` as a subset of `Bool`. -/
def sing (b : Bool) : TwoPred := {b}

theorem sing_true_nonbot : (⊥ : TwoPred) < sing true := by
  -- `⊥` is `∅`, so strictness is `∅ ⊆ {true}` and not equal.
  constructor
  · intro x hx
    cases hx
  · intro hle
    have : (true : Bool) ∈ (sing true : TwoPred) := by simp [sing]
    have : (true : Bool) ∈ (⊥ : TwoPred) := hle this
    cases this

theorem sing_false_nonbot : (⊥ : TwoPred) < sing false := by
  constructor
  · intro x hx
    cases hx
  · intro hle
    have : (false : Bool) ∈ (sing false : TwoPred) := by simp [sing]
    have : (false : Bool) ∈ (⊥ : TwoPred) := hle this
    cases this

theorem sing_orthogonal : sing true ⊓ sing false = (⊥ : TwoPred) := by
  ext b
  simp [sing]

/-- A tiny `Reentry` on the two-point predicate algebra.

We use the **identity** nucleus and choose `support := primordial`, so the `primordial_minimal`
field is provable (there is no nontrivial element strictly below `{true}` in `Set Bool`).
-/
def twoPointReentry : LoF.Reentry TwoPred where
  nucleus := idNucleus
  primordial := sing true
  counter := sing false
  support := sing true
  primordial_mem := by
    -- identity nucleus fixes everything
    rfl
  counter_mem := by
    rfl
  primordial_nonbot := by
    simpa using sing_true_nonbot
  counter_nonbot := by
    simpa using sing_false_nonbot
  orthogonal := by
    simpa using sing_orthogonal
  primordial_in_support := by
    -- `primordial = support`
    rfl
  map_bot := by
    rfl
  primordial_minimal := by
    intro x hx_fix hx_pos hx_support
    -- Since the nucleus is identity, `hx_fix` is trivial; the key is `x ≤ {true}` and `x ≠ ∅`.
    -- We show `{true} ⊆ x`.
    have hx_ne : x ≠ (⊥ : TwoPred) := by
      intro hEq
      have hx_pos' := hx_pos
      simp [hEq] at hx_pos'
    -- From `x ⊆ {true}` and `x ≠ ∅`, we get `true ∈ x`.
    have htrue_in : (true : Bool) ∈ x := by
      by_contra hnot
      -- If `true ∉ x` and `x ⊆ {true}`, then `x = ∅`.
      have : x = (⊥ : TwoPred) := by
        ext b
        by_cases hb : b = true
        · subst hb
          simp [hnot]
        · have hb_not_in : b ∉ sing true := by simp [sing, hb]
          have hx_sub : b ∉ x := by
            intro hb_in
            have hb_in_sing : b ∈ sing true := hx_support hb_in
            exact hb_not_in hb_in_sing
          simp [hx_sub]
      exact hx_ne this
    -- Now `{true} ⊆ x`.
    intro b hb
    -- membership in singleton forces `b = true`
    have : b = true := by simpa [sing] using hb
    subst this
    exact htrue_in

/-! ## Heyting/nucleus layer (beyond the pullback) -/

@[simp] theorem idNucleus_apply (S : TwoPred) : idNucleus S = S := by
  -- `idNucleus` is `⊥` in the lattice of nuclei, i.e. the identity nucleus.
  simp [idNucleus]

@[simp] theorem twoPointReentry_apply (S : TwoPred) : twoPointReentry S = S := by
  simp [twoPointReentry, idNucleus]

-- The fixed points `Ω_R` of a re-entry nucleus form a Heyting algebra (see `LoF.HeytingCore`).
instance : HeytingAlgebra (twoPointReentry.Omega) := by
  infer_instance

/--
For the identity nucleus, the Heyting core `Ω_R` is equivalent to the ambient predicate algebra.

This makes the “LoF → nucleus → Heyting algebra” correspondence explicit in the simplest model.
-/
noncomputable def omegaEquivTwoPred : twoPointReentry.Omega ≃ TwoPred :=
  HeytingLean.LoF.Reentry.booleanEquiv (R := twoPointReentry) (h := by
    intro S
    simp)

@[simp] lemma omegaEquivTwoPred_apply (w : twoPointReentry.Omega) :
    omegaEquivTwoPred w = (w : TwoPred) := rfl

@[simp] lemma omegaEquivTwoPred_symm_apply (S : TwoPred) :
    (omegaEquivTwoPred).symm S =
      HeytingLean.LoF.Reentry.Omega.mk (R := twoPointReentry) S (by simp) := by
  rfl

@[simp] lemma omegaEquivTwoPred_process :
    omegaEquivTwoPred (twoPointReentry.process) = sing true := by
  -- `booleanEquiv` is just coercion on the forward map.
  simp [omegaEquivTwoPred, twoPointReentry]

@[simp] lemma omegaEquivTwoPred_counterProcess :
    omegaEquivTwoPred (twoPointReentry.counterProcess) = sing false := by
  simp [omegaEquivTwoPred, twoPointReentry]

theorem sing_true_ne_false : sing true ≠ sing false := by
  intro hEq
  have htrue : (true : Bool) ∈ sing true := by simp [sing]
  have : (true : Bool) ∈ sing false := by simpa [hEq] using htrue
  simp [sing] at this

theorem twoPoint_process_ne_counter :
    twoPointReentry.process ≠ twoPointReentry.counterProcess := by
  intro hEq
  have hSetEq : sing true = sing false := by
    simpa [omegaEquivTwoPred_process, omegaEquivTwoPred_counterProcess] using
      congrArg omegaEquivTwoPred hEq
  exact sing_true_ne_false hSetEq

@[simp] theorem twoPoint_eulerBoundary_eq_process :
    twoPointReentry.eulerBoundary = twoPointReentry.process := by
  exact HeytingLean.LoF.Reentry.eulerBoundary_eq_process (R := twoPointReentry)

@[simp] theorem omegaEquivTwoPred_eulerBoundary :
    omegaEquivTwoPred twoPointReentry.eulerBoundary = sing true := by
  calc
    omegaEquivTwoPred twoPointReentry.eulerBoundary
        = omegaEquivTwoPred twoPointReentry.process := by
          simp
    _ = sing true := omegaEquivTwoPred_process

theorem twoPoint_eulerBoundary_minimal_nontrivial :
    ⊥ < ((twoPointReentry.eulerBoundary : twoPointReentry.Omega) : TwoPred) ∧
      twoPointReentry (((twoPointReentry.eulerBoundary : twoPointReentry.Omega) : TwoPred)) =
        ((twoPointReentry.eulerBoundary : twoPointReentry.Omega) : TwoPred) ∧
      ∀ {y : twoPointReentry.Omega},
        ⊥ < (y : TwoPred) → (y : TwoPred) ≤ twoPointReentry.support →
          ((twoPointReentry.eulerBoundary : twoPointReentry.Omega) : TwoPred) ≤ (y : TwoPred) := by
  simpa using
    (HeytingLean.LoF.Reentry.eulerBoundary_minimal_nontrivial (R := twoPointReentry))

/-! ## Polarized core (`process`/`counterProcess`) as a Bool equivalence -/

/-- The two distinguished polarized fixed points in the two-point re-entry core. -/
def Polarized : Type :=
  {w : twoPointReentry.Omega |
    w = twoPointReentry.process ∨ w = twoPointReentry.counterProcess}

/-- Boolean encoding into the polarized core. -/
def boolToPolarized : Bool → Polarized
  | true => ⟨twoPointReentry.process, Or.inl rfl⟩
  | false => ⟨twoPointReentry.counterProcess, Or.inr rfl⟩

/-- Decode a polarized core point back to a Bool. -/
noncomputable def polarizedToBool (w : Polarized) : Bool := by
  classical
  exact if (w.1 : twoPointReentry.Omega) = twoPointReentry.process then true else false

@[simp] theorem polarizedToBool_process :
    polarizedToBool ⟨twoPointReentry.process, Or.inl rfl⟩ = true := by
  classical
  simp [polarizedToBool]

@[simp] theorem polarizedToBool_counter :
    polarizedToBool ⟨twoPointReentry.counterProcess, Or.inr rfl⟩ = false := by
  classical
  simp [polarizedToBool, twoPoint_process_ne_counter.symm]

@[simp] theorem polarizedToBool_boolToPolarized (b : Bool) :
    polarizedToBool (boolToPolarized b) = b := by
  cases b <;> simp [boolToPolarized]

@[simp] theorem boolToPolarized_polarizedToBool (w : Polarized) :
    boolToPolarized (polarizedToBool w) = w := by
  classical
  rcases w with ⟨w, hw⟩
  rcases hw with hw | hw
  · subst hw
    apply Subtype.ext
    simp [boolToPolarized]
  · subst hw
    apply Subtype.ext
    simp [boolToPolarized]

/-- The polarized two-point core is equivalent to Bool. -/
def polarizedEquivBool : Polarized ≃ Bool where
  toFun := polarizedToBool
  invFun := boolToPolarized
  left_inv := boolToPolarized_polarizedToBool
  right_inv := polarizedToBool_boolToPolarized

/-! ## Pullback along `obs : Nothing → Bool` -/

open Noneism.Foundation

/-- Pull back a subset of Bool along `obs`. -/
def pull (S : TwoPred) : Set Noneism.Nothing := fun x => obs x ∈ S

/-- `pull` is a Heyting-homomorphism from the two-point predicate algebra into `Set Nothing`. -/
def pullHeytingHom : HeytingHom TwoPred (Set Noneism.Nothing) where
  toFun := pull
  map_sup' := by
    intro A B
    ext x
    show obs x ∈ A ∪ B ↔ (obs x ∈ A ∨ obs x ∈ B)
    simp
  map_inf' := by
    intro A B
    ext x
    show obs x ∈ A ∩ B ↔ (obs x ∈ A ∧ obs x ∈ B)
    simp
  map_bot' := by
    ext x
    show obs x ∈ (∅ : TwoPred) ↔ False
    simp
  map_himp' := by
    intro A B
    rw [himp_eq, himp_eq]
    ext x
    constructor
    · intro hx
      change obs x ∈ B ∪ Aᶜ at hx
      change (obs x ∈ B) ∨ ¬ (obs x ∈ A)
      exact hx
    · intro hx
      change (obs x ∈ B) ∨ ¬ (obs x ∈ A) at hx
      change obs x ∈ B ∪ Aᶜ
      exact hx

/-- Predicate-level view of an `Ω_R` fixed point via the `obs` pullback. -/
def omegaPull (w : twoPointReentry.Omega) : Set Noneism.Nothing :=
  pull (omegaEquivTwoPred w)

theorem pull_sing_true_eq_mark : pull (sing true) = {x | Mark x} := by
  ext x
  -- `x ∈ pull (sing true)` is `obs x ∈ {true}` i.e. `obs x = true`, which is `Mark x`.
  change pull (sing true) x ↔ Mark x
  simp [pull, sing, Foundation.Mark, PrimordialTension.Mark, Foundation.obs, PrimordialTension.obs, PrimordialTension.E]

theorem pull_sing_false_eq_unmark : pull (sing false) = {x | Unmark x} := by
  ext x
  change pull (sing false) x ↔ Unmark x
  simp [pull, sing, Foundation.Unmark, PrimordialTension.Unmark, Foundation.obs, PrimordialTension.obs, PrimordialTension.E]

@[simp] theorem omegaPull_process_eq_mark :
    omegaPull twoPointReentry.process = {x | Mark x} := by
  simpa [omegaPull, omegaEquivTwoPred_process] using
    pull_sing_true_eq_mark

@[simp] theorem omegaPull_counterProcess_eq_unmark :
    omegaPull twoPointReentry.counterProcess = {x | Unmark x} := by
  simpa [omegaPull, omegaEquivTwoPred_counterProcess] using
    pull_sing_false_eq_unmark

@[simp] theorem omegaPull_eulerBoundary_eq_mark :
    omegaPull twoPointReentry.eulerBoundary = {x | Mark x} := by
  simp [omegaPull_process_eq_mark]

end

end LoFPrimordial
end Bridge
end Noneism
end HeytingLean
