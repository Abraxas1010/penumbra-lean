import HeytingLean.HossenfelderNoGo.HeytingBoundary.GapNonZero
import HeytingLean.Bridges.Nucleus.Extensions.Prenucleus

namespace HeytingLean.HossenfelderNoGo.Bridge

open HeytingLean.Bridges.Nucleus.Extensions
open HeytingLean.HossenfelderNoGo.HeytingBoundary

/-- Completing a boundary prenucleus uses the existing promotion API, not a new axiom. -/
def completeBoundaryPrenucleus
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (pn : Prenucleus L)
    (hidem : ∀ a, pn.act (pn.act a) = pn.act a) :
    BoundaryNucleus L :=
  Prenucleus.toCoreNucleus pn hidem

theorem completed_prenucleus_non_boolean
    {L : Type*} [SemilatticeInf L] [OrderBot L]
    (pn : Prenucleus L)
    (hidem : ∀ a, pn.act (pn.act a) = pn.act a)
    (hBridge : BooleanBoundaryBridge (completeBoundaryPrenucleus pn hidem)) :
    ¬ isBoolean (completeBoundaryPrenucleus pn hidem) :=
  boundary_necessarily_non_boolean (completeBoundaryPrenucleus pn hidem) hBridge

end HeytingLean.HossenfelderNoGo.Bridge
