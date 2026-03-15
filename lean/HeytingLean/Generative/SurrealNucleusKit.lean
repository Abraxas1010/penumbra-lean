import HeytingLean.LoF.Instances
import HeytingLean.Generative.IntNucleusKit
import HeytingLean.Numbers.Surreal.ReentryAdapter

/-!
# Surreal Interior Nucleus Kit

This module specialises the generic `IntNucleusKit` utilities to the
surreal pre-game interior nucleus `Surreal.surrealIntReentry`.  It
provides named aliases for the breathing/birth/Occam operations so
downstream generative components can depend on a stable façade without
manipulating the underlying re-entry directly.
-/

namespace HeytingLean
namespace Generative
namespace SurrealNucleusKit

open HeytingLean.Numbers
open HeytingLean.Numbers.Surreal
open HeytingLean.Generative

open scoped Classical

/-! ### Carrier shorthand -/

/-- The ambient primary algebra for surreal interior nuclei. -/
abbrev Carrier := Set SurrealCore.PreGame

/-! ### Alias operations -/

/-- Iterate the surreal interior nucleus until stabilisation. -/
def breathe : ℕ → Carrier → Carrier :=
  IntNucleusKit.ibreathe (R := surrealIntReentry)

@[simp] lemma breathe_zero (S : Carrier) :
    breathe 0 S = S := by
  simpa [breathe] using IntNucleusKit.ibreathe_zero
    (R := surrealIntReentry) (a := S)

@[simp] lemma breathe_succ (n : ℕ) (S : Carrier) :
    breathe (n + 1) S = surrealIntReentry (breathe n S) := by
  simpa [breathe] using IntNucleusKit.ibreathe_succ
    (R := surrealIntReentry) (n := n) (a := S)

/-- Minimal number of breaths required for the surreal interior nucleus to stabilise. -/
noncomputable def birth (S : Carrier) : ℕ :=
  IntNucleusKit.ibirth (R := surrealIntReentry) S

/-- Result of applying the surreal interior Occam operation. -/
def occam (S : Carrier) : Carrier :=
  IntNucleusKit.ioccam (R := surrealIntReentry) S

@[simp] lemma occam_idem (S : Carrier) :
    surrealIntReentry (occam S) = occam S := by
  simpa [occam] using IntNucleusKit.ioccam_idem
    (R := surrealIntReentry) (a := S)

/-- Fixed-point certificate for sets already stable under the interior nucleus. -/
@[simp] lemma birth_eq_zero_iff (S : Carrier) :
    birth S = 0 ↔ surrealIntReentry S = S := by
  simpa [birth] using IntNucleusKit.ibirth_eq_zero_iff
    (R := surrealIntReentry) (a := S)

end SurrealNucleusKit
end Generative
end HeytingLean
