import HeytingLean.LoF.IntReentry
import HeytingLean.Numbers.Surreal.Nucleus

namespace HeytingLean
namespace Numbers
namespace Surreal

/-!
Adapter: re-export the interior-style re-entry for Surreals.

R as logic-extraction (Surreal lens):
- The interior nucleus on `Set PreGame` acts as the stabilizer that
  selects self-consistent (stable) constructions under Conway rules.
- Its fixed points form the Heyting core for the Surreal lens, aligning
  with the general pattern “raw objects → R_domain → Ω_R → logic”.

This module exposes a stable top-level name `Surreal.intReentry` of type
`HeytingLean.LoF.IntReentry (Set SurrealCore.PreGame)` so downstream modules can
depend on the interior nucleus without importing internals.

Notes (expository): `{∅|∅} = 0` is the canonical null cut; the symmetric
cut `{−1|1}` serves as an Euler-style boundary exemplar when relating
process/counter-process narratives to short Surreal games. These are
documentation anchors only; no non-Conway constructs are introduced.
--/

abbrev IntReentryS :=
  HeytingLean.LoF.IntReentry (Set SurrealCore.PreGame)

/-- The interior re-entry for surreal pre-games (re-export). -/
def surrealIntReentry : IntReentryS := intReentry

end Surreal
end Numbers
end HeytingLean
