import HeytingLean.LoF.Nucleus
import HeytingLean.Epistemic.Occam
import HeytingLean.Logic.Dialectic

/-!
# Generative NucleusKit — Aliases and Lemmas

Unified surface for `birth`, `occam`, and `synth` over a nucleus `R : Reentry α`.
This module re-exports existing constructions with cohesive names to serve as a
common entry point for generative domains (surreals, ordinals, circuits).

R as logic‑extraction:
- We treat `R : Reentry α` as the stabilization operator that extracts
  self‑consistent elements of the ambient carrier. Its fixed points `Ω_R`
  carry a Heyting algebra — the emergent logic of the domain. The aliases
  here expose the “generative toolkit”: stage index (`birth`), parsimony
  (`occam`), and synthesis via closure (`synth`).

Irreversibility (scope note):
- Heyting structure constrains but does not generate the raw constructors
  of a domain (e.g., Surreal {L|R} generation and transfinite hierarchies).
  Treat generators as substrate and `R` as the logic‑extraction layer.
-/

namespace HeytingLean
namespace Generative
namespace NucleusKit

open HeytingLean.LoF

universe u

variable {α : Type u} [PrimaryAlgebra α]

abbrev birth (R : Reentry α) := Epistemic.birth (R := R)
abbrev occam (R : Reentry α) := Epistemic.occam (R := R)

/-- Synthesis via closure: least invariant above two propositions. -/
def synth (R : Reentry α) (T A : α) : α :=
  HeytingLean.Logic.Dialectic.synth (R := R) T A

@[simp] lemma occam_idem (R : Reentry α) (a : α) :
    R (occam (R := R) a) = occam (R := R) a :=
  Epistemic.occam_idempotent (R := R) (a := a)

lemma synth_least {R : Reentry α} {T A W : α}
    (hT : T ≤ W) (hA : A ≤ W) (hW : R W = W) :
    synth (R := R) T A ≤ W :=
  HeytingLean.Logic.Dialectic.synthesis_least (R := R)
    (T := T) (A := A) (W := W) hT hA hW

end NucleusKit
end Generative
end HeytingLean
