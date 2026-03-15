import HeytingLean.Bridge.AlMayahi.UDTSynthesis.ClockRateField
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.MassGenerationGap
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.LagrangianReduction
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.FalsifiabilityPredicates
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.GapDecompositionBridge
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.SparseProjectionField
import HeytingLean.Bridge.AlMayahi.UDTSynthesis.HZComputationalBridge

/-!
# Bridge.AlMayahi.UDTSynthesis

Barrel file importing all seven UDT synthesis bridge modules.

These modules connect four previously independent formalizations into a
single verified chain:

- **PM-Bounded τ-Control** → saturation operators, risk functionals
- **Nucleus Grafting** → ReLU nucleus on Fin n → ℝ
- **Hossenfelder No-Go** → boundary nucleus, gap non-zero
- **τ-Epoch** → projection operator, two-clock model

Plus the computational bridge:

- **SparseProjectionField** → discretized χ-deviation, trapped energy
- **HZComputationalBridge** → arithmetic selector, HZ density regime

The synthesis formalizes the algebraic framework from Al-Mayahi's UDT paper,
NOT the physical ontology.
-/
