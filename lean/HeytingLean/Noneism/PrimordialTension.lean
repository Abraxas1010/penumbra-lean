import Mathlib.Data.Bool.Basic

/-!
# Noneism.PrimordialTension

This module packages the **minimal productive kernel** we use as the ontological seed:

*We start with an otherwise unconstrained carrier `Nothing : Type` and add a single assumption
that supplies both:*

1. a **generative witness** (`seed : Nothing`), and
2. an **intrinsic oscillation** (`step : Nothing → Nothing`) that flips a 1-bit distinction
   (`obs : Nothing → Bool`) at every step.

Formally, this is captured by `PrimordialEngine` and the typeclass `PrimordialTension`.

Notes for future agents:
- This is intentionally **assumption-minimal** and **interface-first**. It does *not* claim that
  physics has been derived. It provides a disciplined place to connect:
  noneist intentionality / witness talk ↔ LoF Mark/unmark ↔ Heyting/nucleus machinery.
- Most downstream theorems are *conditional* on `[PrimordialTension Nothing]`.
- We provide a concrete model instance for `Bool` to witness consistency.
-/

namespace HeytingLean
namespace Noneism

universe u

/-- The primordial engine: a seed, a step dynamics, and a 1-bit observable that must flip each step.

`step_involutive` makes the dynamics a 2-cycle (`step ∘ step = id`).
`obs_flips` prevents fixed points and forces oscillation at the level of the observable.
-/
structure PrimordialEngine (Nothing : Type u) where
  seed : Nothing
  step : Nothing → Nothing
  obs : Nothing → Bool
  step_involutive : ∀ x : Nothing, step (step x) = x
  obs_flips : ∀ x : Nothing, obs (step x) = Bool.not (obs x)

/-- The "primordial tension" assumption: an engine exists.

This is intentionally a `Type`-valued class (not `Prop`-valued), because it carries data
(`PrimordialEngine Nothing`) rather than just a proof.
-/
class PrimordialTension (Nothing : Type u) where
  engine : PrimordialEngine Nothing

namespace PrimordialTension

variable {Nothing : Type u} [PrimordialTension Nothing]

/-- The canonical engine extracted from the typeclass. -/
def E : PrimordialEngine Nothing := (inferInstance : PrimordialTension Nothing).engine

/-- The oscillation step. -/
def step : Nothing → Nothing := (E (Nothing := Nothing)).step

/-- The 1-bit observation ("Mark" bit). -/
def obs : Nothing → Bool := (E (Nothing := Nothing)).obs

/-- The generative seed witness. -/
def seed : Nothing := (E (Nothing := Nothing)).seed

@[simp] theorem step_step (x : Nothing) : step (step x) = x :=
  (E (Nothing := Nothing)).step_involutive x

@[simp] theorem obs_step (x : Nothing) : obs (step x) = Bool.not (obs x) :=
  (E (Nothing := Nothing)).obs_flips x

/-!
## The "necessary witness" produced by the oscillation

From the assumption we can *derive* plurality: `seed ≠ step seed`.
This is the minimal constructive witness of distinction.
-/

theorem seed_ne_step_seed : seed (Nothing := Nothing) ≠ step (Nothing := Nothing) (seed (Nothing := Nothing)) := by
  intro hEq
  -- Apply `obs` to the equality and contradict `obs_flips`.
  have hObs : obs (Nothing := Nothing) (seed (Nothing := Nothing)) =
      obs (Nothing := Nothing) (step (Nothing := Nothing) (seed (Nothing := Nothing))) :=
    congrArg (obs (Nothing := Nothing)) hEq
  have : obs (Nothing := Nothing) (seed (Nothing := Nothing)) =
      Bool.not (obs (Nothing := Nothing) (seed (Nothing := Nothing))) := by
    calc
      obs (Nothing := Nothing) (seed (Nothing := Nothing))
          = obs (Nothing := Nothing) (step (Nothing := Nothing) (seed (Nothing := Nothing))) := hObs
      _ = Bool.not (obs (Nothing := Nothing) (seed (Nothing := Nothing))) := by
        simp [obs_step (Nothing := Nothing) (x := seed (Nothing := Nothing))]
  -- No Bool equals its negation.
  cases h : obs (Nothing := Nothing) (seed (Nothing := Nothing)) <;> simp [h] at this

theorem exists_two_distinct : ∃ x y : Nothing, x ≠ y := by
  refine ⟨seed (Nothing := Nothing), step (Nothing := Nothing) (seed (Nothing := Nothing)), ?_⟩
  exact seed_ne_step_seed (Nothing := Nothing)

/-!
## Mark / Unmark as predicates

We treat the observable bit as the minimal distinction operator.
This embeds the LoF Mark/unmark pattern into `Nothing → Prop` without requiring any extra structure.
-/

def Mark (x : Nothing) : Prop := obs (Nothing := Nothing) x = true
def Unmark (x : Nothing) : Prop := obs (Nothing := Nothing) x = false

theorem mark_or_unmark (x : Nothing) : Mark (Nothing := Nothing) x ∨ Unmark (Nothing := Nothing) x := by
  -- `obs x` is Bool, so it is either true or false.
  cases h : obs (Nothing := Nothing) x <;> simp [Mark, Unmark, h]

theorem mark_iff_not_unmark (x : Nothing) :
    Mark (Nothing := Nothing) x ↔ ¬ Unmark (Nothing := Nothing) x := by
  cases h : obs (Nothing := Nothing) x <;> simp [Mark, Unmark, h]

theorem unmark_iff_not_mark (x : Nothing) :
    Unmark (Nothing := Nothing) x ↔ ¬ Mark (Nothing := Nothing) x := by
  cases h : obs (Nothing := Nothing) x <;> simp [Mark, Unmark, h]

theorem mark_step_iff_unmark (x : Nothing) :
    Mark (Nothing := Nothing) (step (Nothing := Nothing) x) ↔ Unmark (Nothing := Nothing) x := by
  -- `obs (step x) = not (obs x)` flips the equality-to-true/false.
  cases h : obs (Nothing := Nothing) x <;>
    simp [Mark, Unmark, obs_step (Nothing := Nothing) (x := x), h]

theorem unmark_step_iff_mark (x : Nothing) :
    Unmark (Nothing := Nothing) (step (Nothing := Nothing) x) ↔ Mark (Nothing := Nothing) x := by
  cases h : obs (Nothing := Nothing) x <;>
    simp [Mark, Unmark, obs_step (Nothing := Nothing) (x := x), h]

theorem mark_and_unmark_false (x : Nothing) :
    ¬ (Mark (Nothing := Nothing) x ∧ Unmark (Nothing := Nothing) x) := by
  cases h : obs (Nothing := Nothing) x <;> simp [Mark, Unmark, h]

/--
Canonical noneist oscillatory interpretation bundle:
observable flips every step, seed distinguishes from its step image, and plurality exists.
-/
theorem oscillatory_interpretation_bundle :
    (∀ x : Nothing,
      obs (Nothing := Nothing) (step (Nothing := Nothing) x) =
        Bool.not (obs (Nothing := Nothing) x)) ∧
      (seed (Nothing := Nothing) ≠ step (Nothing := Nothing) (seed (Nothing := Nothing))) ∧
      (∃ x y : Nothing, x ≠ y) := by
  refine ⟨?_, seed_ne_step_seed (Nothing := Nothing), exists_two_distinct (Nothing := Nothing)⟩
  intro x
  exact obs_step (Nothing := Nothing) x

/-!
## Concrete consistency model: `Bool`

This instance witnesses that `PrimordialTension` is consistent (at least in the meta-theory),
by interpreting:
- `seed := false`
- `step := Bool.not`
- `obs := id`
-/

instance instPrimordialTensionBool : PrimordialTension Bool where
  engine :=
    { seed := false
      step := Bool.not
      obs := fun b => b
      step_involutive := by intro b; cases b <;> rfl
      obs_flips := by intro b; cases b <;> rfl }

end PrimordialTension

end Noneism
end HeytingLean
