/-!
# Penumbra: The Universal Information Shadow of Non-Boolean Projection

This barrel file imports the complete 10-layer synthesis chain.
Building this file (`lake build Penumbra`) verifies all declarations
across all layers are sorry-free and type-correct.

## The Central Result

Every non-Boolean nucleus R on a Heyting algebra L produces an irreducible
information gap: the boundary ∂Ω_R = {x ∈ L : R(x) ≠ x ∧ R(x) ≠ ⊤} is
non-empty. This gap appears identically across:

- Neural network quantization (qReLU as nucleus)
- Spacetime structure (Hossenfelder no-go)
- Fluid dynamics (Turing-complete undecidability)
- Matter stability (prime rotational periods)
- Dimensional emergence (SU(2) from re-entry)
- Causal invariance (Wolfram confluence independence)
- Spinor structure (Penrose bridge)
- Controlled system saturation (PM-bounded τ-control)
- Asymptotic safety (RG fixed points = Ω_R)
- Two-clock physics (Al-Mayahi UDT projection)
-/

-- ════════════════════════════════════════════════════════════════
-- Foundation
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Core.Nucleus

-- ════════════════════════════════════════════════════════════════
-- Layer 0: Noneist Ground → Generative Emergence
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Generative.NoneistOscillation
import HeytingLean.Generative.ReEntryPlane
import HeytingLean.Generative.SpatialClosure
import HeytingLean.Generative.FourDBarrier
import HeytingLean.Generative.UDPGeometry
import HeytingLean.Generative.PropagationSpeed
import HeytingLean.Generative.UDTPostulates

-- ════════════════════════════════════════════════════════════════
-- Layer 1: Spinor Bridge (SU(2) from Re-Entry Geometry)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Generative.SpinorBridge

-- ════════════════════════════════════════════════════════════════
-- Layer 2: Heyting Gap (Hossenfelder No-Go + Nucleus Grafting)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.HossenfelderNoGo.Basic
import HeytingLean.NucleusGrafting.Certificate
import HeytingLean.NucleusGrafting.BoundaryConnection

-- ════════════════════════════════════════════════════════════════
-- Layer 3: Wolfram Causal Confluence (Independence Result)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Generative.WolframBridge
import HeytingLean.WPP.Wolfram.ConfluenceCausalInvariance
import HeytingLean.Bridge.Wolfram.CausalInvariance

-- ════════════════════════════════════════════════════════════════
-- Layer 5: Two-Clock Physics (Al-Mayahi UDT Projection)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Bridge.AlMayahi.TauEpoch
import HeytingLean.Bridge.AlMayahi.UDTSynthesis
import HeytingLean.Bridge.AlMayahi.UDTRecovery
import HeytingLean.Bridge.AlMayahi.TauCoordination.Bridge

-- ════════════════════════════════════════════════════════════════
-- Layer 6: Fluid Undecidability (Miranda Dynamics)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.MirandaDynamics.Fluids.TuringComplete
import HeytingLean.MirandaDynamics.Fluids.EtnyreGhrist

-- ════════════════════════════════════════════════════════════════
-- Layer 7: PM-Bounded τ-Control (Tokamak Saturation)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Analysis.PMBoundedControl.CompletionOperator
import HeytingLean.Analysis.PMBoundedControl.TauProgression

-- ════════════════════════════════════════════════════════════════
-- Layer 8: Prime Stability (Matter from Prime Periodicity)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.Generative.PrimeStability

-- ════════════════════════════════════════════════════════════════
-- Cross-Cutting F: Asymptotic Safety (RG Fixed Points = Ω_R)
-- ════════════════════════════════════════════════════════════════
import HeytingLean.AsymptoticSafety.NucleusInstance
