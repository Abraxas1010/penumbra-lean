<img src="assets/Apoth3osis.webp" alt="Apoth3osis — Formal Mathematics and Verified Software" width="140"/>

<sub><strong>Our tech stack is ontological:</strong><br>
<strong>Hardware — Physics</strong><br>
<strong>Software — Mathematics</strong><br><br>
<strong>Our engineering workflow is simple:</strong> discover, build, grow, learn & teach</sub>

---

<sub>
<strong>Acknowledgment</strong><br>
We humbly thank the collective intelligence of humanity for providing the technology and culture we cherish. We do our best to properly reference the authors of the works utilized herein, though we may occasionally fall short. Our formalization acts as a reciprocal validation—confirming the structural integrity of their original insights while securing the foundation upon which we build. In truth, all creative work is derivative; we stand on the shoulders of those who came before, and our contributions are simply the next link in an unbroken chain of human ingenuity.
</sub>

---

[![License: Apoth3osis License Stack v1](https://img.shields.io/badge/License-Apoth3osis%20License%20Stack%20v1-blue.svg)](LICENSE.md)
[![Lean Build](https://github.com/Abraxas1010/penumbra-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/Abraxas1010/penumbra-lean/actions/workflows/lean.yml)

# Penumbra: The Universal Information Shadow of Non-Boolean Projection

Machine-checked proof that every non-Boolean nucleus on a Heyting algebra produces an irreducible information gap — a *penumbra* — and that this gap appears with identical algebraic structure across neural network quantization, spacetime geometry, fluid dynamics, matter stability, dimensional emergence, causal invariance, spinor structure, controlled system saturation, renormalization group flow, and two-clock relativistic projection. 162 Lean 4 files, 1,486 declarations, 733 theorems/lemmas, zero `sorry`. Independently verifiable via `lake build`.

## What Is This?

This repository contains a formally verified argument, written in Lean 4 with Mathlib, that a single algebraic mechanism — the *nucleus operator* R on a Heyting algebra L — generates an irreducible information gap whenever L is non-Boolean. The gap is not an artifact of any particular physical domain; it is a structural consequence of non-Boolean projection itself. We instantiate this result across 8 distinct substrates and prove that the instantiations share structural identity.

## The Central Thesis

Let L be a Heyting algebra and R : L → L a nucleus (monotone, inflationary, idempotent, meet-preserving). The *fixed-point set* Ω_R = {x ∈ L : R(x) = x} is a sub-Heyting algebra. The *boundary* ∂Ω_R = {x ∈ L : R(x) ≠ x} contains elements that are projected but not absorbed — information that survives the projection without being captured by the fixed-point structure.

**The key result:** When L is non-Boolean, ∂Ω_R is non-empty for every non-trivial nucleus. This non-emptiness is the *penumbra* — an irreducible information shadow cast by every non-Boolean projection. It cannot be eliminated by changing the nucleus, the algebra, or the domain. It is structural.

## The 10-Layer Argument

### Layer 0: Noneist Ground → Generative Emergence

**Claim:** From the bare oscillation of Nothing (Meinongian noneism), spatial closure forces exactly 3 dimensions, a 4th-dimensional barrier, and a propagation speed proportional to π·φ (golden ratio).

**Key theorems:**
- `golden_ratio_reentry_equation`, `reentry_ratio_unique` — the re-entry equation φ² = φ + 1
- `residualFreedom` — spatial closure yields exactly 3 degrees of freedom
- `space_time_asymmetry` — 4th-dimensional barrier from asymmetry
- `udp_is_derived` — UDP geometry as derived, not postulated
- `phasePropagationFactor_pos`, `no_three_fifths_factor` — propagation speed structure

**Files:** `HeytingLean/Generative/{NoneistOscillation, ReEntryPlane, SpatialClosure, FourDBarrier, UDPGeometry, PropagationSpeed, UDTPostulates}.lean` (~990 lines)

### Layer 1: Spinor Bridge (SU(2) from Re-Entry Geometry)

**Claim:** The re-entry geometry of Layer 0 carries an SU(2) structure. Oscillator states correspond to spinor components; Clebsch-Gordan coupling emerges from composition; dimensionality follows from representation theory.

**Key theorems:**
- `oscillator_spinor_equiv` — oscillator ↔ spinor equivalence
- `clebsch_gordan_coupling` — composition gives CG coefficients
- `dimensionality_from_su2` — 3+1 dimensions from SU(2) representation theory

**Files:** `HeytingLean/Generative/SpinorBridge/{SU2Core, OscillatorSpinorEquiv, ClebschGordanCoupling, DimensionalityFromSU2, ComplexificationBarrier, NucleusPenroseBridge}.lean` (~561 lines)

### Layer 2: The Heyting Gap (Hossenfelder No-Go)

**Claim:** On any non-Boolean Heyting algebra, the nucleus boundary is non-empty. Neural network quantization (qReLU) is a concrete instance: the gap between pre- and post-activation values is exactly the Heyting gap.

**Key theorems:**
- `gapNonZero` — boundary of non-Boolean nucleus is non-empty
- `qRelu_extensive`, `qRelu_idempotent`, `qRelu_meet_preserving` — qReLU is a nucleus
- `certificate_gap_nonzero` — certificate of positive gap
- `graftBoundaryNucleus_not_boolean` — grafted boundary nucleus is non-Boolean

**Files:** `HeytingLean/HossenfelderNoGo/` (12 files, ~492 lines)

### Layer 3: Wolfram Causal Confluence (Independence)

**Claim:** Confluence (Church-Rosser) and causal invariance are logically independent properties of rewrite systems. The Heyting gap appears as a fixed-point obstruction shared between the Hossenfelder no-go and Wolfram's causal framework.

**Key theorems:**
- `confluence_causal_invariance_independent` — neither implies the other
- `hossenfelder_and_graft_share_fixed_point_predicate` — shared obstruction
- `wolfram_hossenfelder_grafting_share_fixed_point_obstruction` — three-way bridge

**Files:** `HeytingLean/WPP/Wolfram/` (8 files, ~1,826 lines), `HeytingLean/Generative/WolframBridge/` (4 files)

### Layer 4: Neural Networks / Nucleus Grafting (qReLU)

**Claim:** Quantized ReLU (qReLU) satisfies all nucleus axioms on discrete integer lattices. The gap between pre- and post-activation values is the Heyting gap instantiated in neural network form.

**Key theorems:**
- `qRelu_extensive` — qReLU is inflationary (x ≤ qReLU(x))
- `qRelu_idempotent` — qReLU is idempotent
- `qRelu_meet_preserving` — qReLU preserves meets
- `certificate_gap_nonzero` — certificate of positive gap
- `graftBoundaryNucleus_not_boolean` — grafted boundary nucleus is non-Boolean

**Files:** `HeytingLean/NucleusGrafting/` (4 files, ~298 lines)

### Layer 5: Two-Clock Physics (Al-Mayahi UDT)

**Claim:** Al-Mayahi's Union Dipole Theory (UDT) projects a single τ-clock onto observer-local (t, x) coordinates. The projection operator is a nucleus; the gap between τ-evolution and (t, x)-evolution is the Heyting gap instantiated in relativistic kinematics.

**Key theorems:**
- `tau_projection_is_nucleus` — the τ → t projection is a nucleus
- `tau_epoch_necessity` — necessity of the τ-epoch structure
- `mass_generation_gap` — mass generation as a gap phenomenon
- `clock_rate_field_properties` — clock-rate field derivation

**Files:** `HeytingLean/Bridge/AlMayahi/` (~4,113 lines across TauEpoch, TauCoordination, UDTSynthesis, UDTRecovery)

### Layer 6: Fluid Undecidability (Miranda Dynamics)

**Claim:** Navier-Stokes trajectory prediction and periodicity detection are Turing-undecidable. The periodic nucleus on fluid orbits inherits the Heyting gap — the undecidable boundary between periodic and aperiodic flow.

**Key theorems:**
- `fluid_trajectory_undecidable` — trajectory prediction is undecidable
- `fluid_periodicity_undecidable` — periodicity detection is undecidable
- `fluidPeriodicNucleus` — periodic orbit operator is a nucleus
- `etnyre_ghrist_contact` — Etnyre-Ghrist contact topology of fluid flow

**Files:** `HeytingLean/MirandaDynamics/` (~678 lines)

### Layer 7: PM-Bounded τ-Control (Tokamak Saturation)

**Claim:** In PM-bounded control systems (tokamak plasma confinement), the completion operator that enforces saturation bounds is a nucleus. The gap between actual and saturated control signals is the Heyting gap in control-theoretic form.

**Key theorems:**
- `completion_is_nucleus` — completion operator satisfies nucleus axioms
- `tau_progression_bounded` — τ-progression respects PM bounds

**Files:** `HeytingLean/Analysis/PMBoundedControl/` (~449 lines)

### Layer 8: Prime Stability (Matter from Prime Periodicity)

**Claim:** Stable matter requires prime-period rotational closures. Composite periods decompose; identity periods carry no asymmetry. Only prime periods are simultaneously massive (period > 1) and indecomposable — the electron (period 2) is the terminal stable particle.

**Key theorems:**
- `stable_massive_has_prime_period` — stability + mass → prime period
- `electron_is_terminal` — period 2 is the minimal stable configuration
- `stability_hierarchy` — the complete hierarchy theorem
- `born_weight_eq_surviving_fraction` — Born rule from surviving fraction
- `relu_gap_matches_born_structure` — ReLU gap matches Born structure

**Files:** `HeytingLean/Generative/PrimeStability/` (6 files, ~620 lines)

### Cross-Cutting F: Asymptotic Safety (RG Fixed Points = Ω_R)

**Claim:** Renormalization group fixed points are the fixed-point set Ω_R of a nucleus on coupling-constant space. The running of couplings under RG flow is exactly nuclear projection; the Heyting gap appears as the distance between bare and renormalized couplings.

**Key theorems:**
- `nucleus_instance` — RG flow operator satisfies nucleus axioms
- `fixed_point_is_rg_fixed` — Ω_R elements are RG fixed points
- `beta_function_vanishes_at_fixed_point` — β = 0 at Ω_R

**Files:** `HeytingLean/AsymptoticSafety/` (~815 lines)

## Cross-Cutting Connections

| Connection | Bridges | Key Result |
|:-----------|:--------|:-----------|
| A: Neural ↔ Spacetime | Layers 2, 3, 4 | qReLU gap = Hossenfelder gap = Wolfram fixed-point obstruction |
| B: Oscillation ↔ Spinor | Layers 0, 1 | Re-entry involution carries SU(2) |
| C: τ-Clock ↔ RG Flow | Layers 5, F | τ-projection and RG flow are both nuclear projections |
| D: Fluid ↔ Control | Layers 6, 7 | Undecidability boundary = saturation boundary |
| E: Born Rule ↔ Stability | Layer 8 | Surviving fraction under nucleus = Born probability |
| F: Prime Period ↔ Mass | Layer 8 | Mass = trapped asymmetry at prime period > 1 |

## Build & Verify

**Prerequisites:** [elan](https://github.com/leanprover/elan) (Lean version manager)

```bash
# Clone
git clone https://github.com/Abraxas1010/penumbra-lean.git
cd penumbra-lean/lean

# Build everything (first run downloads Mathlib — may take 30-60 minutes)
lake build

# Or build just the barrel import (verifies full synthesis chain)
lake build Penumbra

# Verify zero sorry/admit
grep -r "sorry\|admit" HeytingLean/ --include="*.lean" | grep -v "^.*:.*--"
# Expected: no output
```

**What `lake build` does:** Lean's kernel independently type-checks every declaration. If the build succeeds with exit code 0, every theorem in the repository has been machine-verified. No trust in the authors is required — only trust in the Lean 4 kernel.

## Theorem Inventory

See [INVENTORY.md](INVENTORY.md) for a complete listing of all 1,486 declarations organized by layer and file.

## Contributors & Heritage

This synthesis builds on and formalizes work from:

| Contributor | Domain | Contribution |
|:------------|:-------|:-------------|
| **Al-Mayahi** | Relativistic kinematics | UDT two-clock framework (Layer 5) |
| **Veselov** | Number theory | Hybrid Zeckendorf arithmetic (computational tools) |
| **Miranda** | Fluid dynamics | Turing-completeness of Navier-Stokes (Layer 6) |
| **Tzouvaras** | Set theory | Noneist/Meinongian foundations (Layer 0) |
| **Eichhorn, Piskunov** | Quantum gravity | Asymptotic safety program (Cross-cutting F) |
| **Hossenfelder** | Foundations of physics | Superdeterminism no-go structure (Layer 2) |
| **Penrose** | Mathematical physics | Spinor-flag structure (Layer 1 bridge) |
| **Wolfram** | Computational physics | Multiway causal invariance (Layer 3) |
| **Goodman / Apoth3osis** | Synthesis | Nucleus-as-universal-gap unification |

## Development Provenance

This repository was extracted from the [HeytingLean](https://github.com/Abraxas1010/HeytingLean) monorepo using automated transitive import tracing. Development history spanning December 2025 through March 2026 is preserved in the internal repository. The single-commit structure of this extracted repo reflects the extraction process, not the development workflow. The authoritative test is `lake build`, which does not depend on git history.

## License

[Apoth3osis License Stack v1](LICENSE.md)
