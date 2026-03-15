import HeytingLean.Noneism.PrimordialTension

/-!
# Noneism.Foundation (Ontological Foundation)

This file pins the "ontological foundation" used by HeytingLean as a **single explicit instance**:

We introduce a named carrier `Nothing` and provide `PrimordialTension Nothing`.

Everything that follows is then derived constructively from that assumption:
- a necessary witness of plurality (`seed ≠ step seed`),
- a minimal distinction operator (`Mark/Unmark`),
- and the flip/oscillation laws.

Design notes:
- We keep this in `Noneism` because it is the repo's "intentionality / existence-discipline" layer.
- We do *not* hide assumptions: future agents should be able to trace exactly what is assumed.
- This module is the intended import point for downstream ontology → LoF/Heyting bridges.
-/

namespace HeytingLean
namespace Noneism

/-- The unconstrained carrier used by foundational Noneism modules. -/
abbrev Nothing : Type := Bool

/-- Foundational instance: the canonical primordial engine on `Bool`. -/
instance instPrimordialTensionNothing : PrimordialTension (Nothing := Nothing) := by
  dsimp [Nothing]
  infer_instance

attribute [instance] instPrimordialTensionNothing

namespace Foundation

open PrimordialTension

noncomputable section

-- Re-export the canonical names specialized to `Noneism.Nothing`.
abbrev seed : Nothing := PrimordialTension.seed (Nothing := Nothing)
abbrev step : Nothing → Nothing := PrimordialTension.step (Nothing := Nothing)
abbrev obs : Nothing → Bool := PrimordialTension.obs (Nothing := Nothing)

abbrev Mark : Nothing → Prop := PrimordialTension.Mark (Nothing := Nothing)
abbrev Unmark : Nothing → Prop := PrimordialTension.Unmark (Nothing := Nothing)

theorem seed_ne_step_seed : seed ≠ step seed :=
  PrimordialTension.seed_ne_step_seed (Nothing := Nothing)

theorem mark_step_iff_unmark (x : Nothing) : Mark (step x) ↔ Unmark x :=
  PrimordialTension.mark_step_iff_unmark (Nothing := Nothing) (x := x)

theorem unmark_step_iff_mark (x : Nothing) : Unmark (step x) ↔ Mark x :=
  PrimordialTension.unmark_step_iff_mark (Nothing := Nothing) (x := x)

theorem mark_or_unmark (x : Nothing) : Mark x ∨ Unmark x :=
  PrimordialTension.mark_or_unmark (Nothing := Nothing) (x := x)

end

end Foundation

end Noneism
end HeytingLean
