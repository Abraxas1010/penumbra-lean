# Penumbra — Declaration Inventory

Complete listing of all declarations in the 10-layer synthesis chain.
Generated from Lean source files. 162 files, 1,486 declarations, zero sorry.

## `HeytingLean/Analysis/PMBoundedControl/CompletionOperator.lean`

- Line 18: `def SatRational (Q_PM : ℝ) (x : ℝ) : ℝ :=`
- Line 22: `def SatTanh (Q_PM : ℝ) (x : ℝ) : ℝ :=`
- Line 26: `structure PMCompletion where`
- Line 32: `theorem sat_rational_denominator_pos {Q_PM x : ℝ} (hQ : 0 < Q_PM) :`
- Line 36: `theorem sat_rational_nonneg {Q_PM x : ℝ} (hQ : 0 < Q_PM) (hx : 0 ≤ x) :`
- Line 41: `theorem sat_rational_nonpos {Q_PM x : ℝ} (hQ : 0 < Q_PM) (hx : x ≤ 0) :`
- Line 46: `theorem sat_rational_odd {Q_PM x : ℝ} :`
- Line 51: `theorem sat_rational_continuous {Q_PM : ℝ} (hQ : 0 < Q_PM) :`
- Line 57: `theorem sat_rational_bounded {Q_PM x : ℝ} (hQ : 0 < Q_PM) :`
- Line 70: `theorem sat_rational_fix_on_interval {Q_PM x : ℝ}`
- Line 80: `theorem sat_rational_monotone {Q_PM : ℝ} (hQ : 0 < Q_PM) :`
- Line 113: `theorem sat_rational_sub_self {Q_PM x : ℝ} (hQ : 0 < Q_PM) :`
- Line 120: `theorem sat_rational_identity_regime_bound {Q_PM x : ℝ} (hQ : 0 < Q_PM) :`
- Line 136: `theorem sat_rational_identity_regime {Q_PM ε x : ℝ} (hQ : 0 < Q_PM) (_hε : 0 < ε)`
- Line 149: `theorem sat_tanh_continuous {Q_PM : ℝ} :`
- Line 158: `theorem sat_tanh_odd {Q_PM x : ℝ} :`
- Line 163: `theorem sat_tanh_bounded {Q_PM x : ℝ} (hQ : 0 ≤ Q_PM) :`
- Line 190: `def pmBoundaryClamp (Q_PM x : ℝ) : ℝ :=`
- Line 194: `def pmSafeSet (Q_PM : ℝ) : Set ℝ :=`
- Line 200: `def pmBoundaryNucleus (Q_PM : ℝ) : Nucleus (Set ℝ) where`
- Line 223: `theorem sat_rational_mem_safeSet {Q_PM x : ℝ} (hQ : 0 < Q_PM) (hx : 0 ≤ x) :`
- Line 232: `theorem sat_rational_le_boundary_clamp {Q_PM x : ℝ}`
- Line 247: `theorem pmBoundaryNucleus_fix_safeSet {Q_PM : ℝ} :`
- Line 253: `def rationalCompletion (Q_PM : ℝ) (hQ : 0 < Q_PM) : PMCompletion where`

## `HeytingLean/Analysis/PMBoundedControl/RiskFunctional.lean`

- Line 19: `class RiskFunctional (α : Type*) where`
- Line 23: `structure PMBoundary where`
- Line 28: `def PMBoundedInvariant {α : Type*} (Q : α → ℝ) (B : PMBoundary) (u : ι → α) : Prop :=`
- Line 32: `def safetyPenalty (q : ℝ) : ℝ :=`
- Line 36: `def TokamakRisk (β_local q T : ℝ) : ℝ :=`
- Line 39: `theorem safety_penalty_nonneg {q : ℝ} (hq : 0 ≤ q) :`
- Line 44: `theorem tokamak_risk_nonneg {β_local q T : ℝ}`
- Line 51: `theorem tokamak_risk_monotone_beta {β₁ β₂ q T : ℝ}`
- Line 62: `theorem pm_invariant_of_completion {α ι : Type*} (Q : α → ℝ) (B : PMBoundary)`
- Line 74: `def classicalBlowupProfile (u₀ t : ℝ) : ℝ :=`
- Line 78: `def classicalBlowupTime (u₀ : ℝ) : ℝ :=`
- Line 82: `def completedScalarProfile (Q_PM u₀ t : ℝ) : ℝ :=`
- Line 85: `theorem classical_blowup_denominator_zero (u₀ : ℝ) (hu₀ : u₀ ≠ 0) :`
- Line 91: `theorem scalar_bounded_completed {Q_PM u₀ t : ℝ} (hQ : 0 < Q_PM) :`
- Line 98: `theorem risk_classical_regime {Q_PM ε s : ℝ} (hQ : 0 < Q_PM) (hε : 0 < ε)`

## `HeytingLean/Analysis/PMBoundedControl/TauProgression.lean`

- Line 15: `def progressionDensity (Q Q_PM ε : ℝ) : ℝ :=`
- Line 19: `def effectiveStep (Δσ ρ : ℝ) : ℝ :=`
- Line 23: `def completedUpdate (u : ℝ) (L N_PM : ℝ → ℝ) (Δσ_eff : ℝ) : ℝ :=`
- Line 26: `theorem progression_density_ge_one {Q Q_PM ε : ℝ}`
- Line 34: `theorem effective_step_le_external {Δσ ρ : ℝ}`
- Line 41: `theorem effective_step_vanishes_of_large_density {Δσ ρ ε : ℝ}`
- Line 50: `theorem completed_update_error_bound (u Δσ_eff : ℝ) (L N N_PM : ℝ → ℝ) :`
- Line 62: `theorem completed_update_preserves_classical {Q_PM ε Δσ_eff u : ℝ}`

## `HeytingLean/AsymptoticSafety/BetaFunctions.lean`

- Line 7: `structure CriticalExponentProfile where`
- Line 20: `def eichhornCriticalProfile : CriticalExponentProfile where`
- Line 33: `structure BetaSystem where`
- Line 38: `def eichhornBetaSystem : BetaSystem where`
- Line 43: `def linearizedBeta (sys : BetaSystem) (g : CouplingPoint) : CouplingPoint :=`
- Line 61: `theorem linearizedBeta_at_fixedPoint (sys : BetaSystem) :`
- Line 68: `def PortalScreeningHypothesis (sys : BetaSystem) : Prop :=`
- Line 71: `theorem portal_beta_nonpos_of_screening`

## `HeytingLean/AsymptoticSafety/CouplingSpace.lean`

- Line 18: `structure ExperimentalBand where`
- Line 22: `def ExperimentalBand.Contains (band : ExperimentalBand) (value : ℝ) : Prop :=`
- Line 26: `structure ExperimentalTargets where`
- Line 34: `structure TruncationScheme where`
- Line 45: `def eichhornBenchmark : TruncationScheme where`
- Line 56: `def eichhornTargets : ExperimentalTargets where`
- Line 64: `structure CouplingPoint where`
- Line 100: `instance : Zero CouplingPoint where`
- Line 123: `instance : Add CouplingPoint where`
- Line 136: `instance : Neg CouplingPoint where`
- Line 149: `instance : Sub CouplingPoint where`
- Line 152: `instance : SMul ℝ CouplingPoint where`
- Line 166: `def gravitationalFixedPoint (ts : TruncationScheme) : CouplingPoint where`
- Line 178: `def squaredDistanceTo (g ref : CouplingPoint) : ℝ :=`
- Line 190: `def EuclideanTruncation (ts : TruncationScheme) : Prop :=`
- Line 194: `def portalOff (g : CouplingPoint) : Prop :=`
- Line 197: `theorem gravitationalFixedPoint_portalOff (ts : TruncationScheme) :`

## `HeytingLean/AsymptoticSafety/FixedPoint.lean`

- Line 7: `structure FixedPointWitness where`
- Line 14: `def gravitationalWitness (sys : BetaSystem) : FixedPointWitness where`
- Line 21: `theorem witness_zero_self_distance (w : FixedPointWitness) :`
- Line 26: `structure PhysicalAssumptions (sys : BetaSystem) where`
- Line 30: `theorem gravitationalWitness_respects_assumptions`

## `HeytingLean/AsymptoticSafety/GravityMatter.lean`

- Line 8: `structure GravityMatterModel where`
- Line 18: `def gravitationalTopDrift (model : GravityMatterModel) : ℝ :=`
- Line 21: `def gravitationalBottomDrift (model : GravityMatterModel) : ℝ :=`
- Line 24: `def gravitationalQuarticDrift (model : GravityMatterModel) : ℝ :=`
- Line 27: `def effectiveTopYukawaShift (model : GravityMatterModel) : ℝ :=`
- Line 30: `def effectiveBottomYukawaShift (model : GravityMatterModel) : ℝ :=`
- Line 33: `def effectiveHiggsQuarticShift (model : GravityMatterModel) : ℝ :=`
- Line 36: `def topMassShift (model : GravityMatterModel) : ℝ :=`
- Line 39: `def higgsMassShift (model : GravityMatterModel) : ℝ :=`
- Line 42: `def topBottomRatioShift (model : GravityMatterModel) : ℝ :=`
- Line 46: `def predictTopMass (model : GravityMatterModel) : ℝ :=`
- Line 49: `def predictHiggsMass (model : GravityMatterModel) : ℝ :=`
- Line 52: `def predictTopBottomRatio (model : GravityMatterModel) : ℝ :=`
- Line 55: `theorem topMass_prediction_offset (model : GravityMatterModel) :`
- Line 59: `theorem higgsMass_prediction_offset (model : GravityMatterModel) :`
- Line 63: `theorem topBottomRatio_prediction_offset (model : GravityMatterModel) :`
- Line 68: `theorem topMass_abs_error_eq_rg_drift (model : GravityMatterModel) :`
- Line 73: `theorem higgsMass_abs_error_eq_rg_drift (model : GravityMatterModel) :`
- Line 78: `theorem topBottomRatio_abs_error_eq_rg_drift (model : GravityMatterModel) :`
- Line 84: `def neutrinoDamping (model : GravityMatterModel) : ℝ :=`
- Line 87: `def neutrinoNumerator (model : GravityMatterModel) : ℝ :=`
- Line 90: `noncomputable def predictNeutrinoUpper (model : GravityMatterModel) : ℝ :=`
- Line 93: `theorem neutrinoDamping_pos (model : GravityMatterModel) :`
- Line 100: `theorem matter_preserves_fixed_point (model : GravityMatterModel) :`
- Line 104: `theorem matter_changes_top_shift (model : GravityMatterModel)`

## `HeytingLean/AsymptoticSafety/MatterSector.lean`

- Line 7: `structure MatterFieldContent where`
- Line 13: `structure MatterSector where`
- Line 20: `def gaussianMatterCompatible (g : CouplingPoint) : Prop :=`
- Line 29: `def matterBackreaction (sector : MatterSector) : ℝ :=`
- Line 34: `theorem gravitationalFixedPoint_gaussianMatterCompatible (ts : TruncationScheme) :`
- Line 38: `theorem matter_matters (sector : MatterSector)`

## `HeytingLean/AsymptoticSafety/NucleusInstance.lean`

- Line 12: `abbrev CouplingRegion := OrderDual (Set CouplingPoint)`
- Line 14: `def carrier (U : CouplingRegion) : Set CouplingPoint := U`
- Line 17: `def uvSafeSet (sys : BetaSystem) : Set CouplingPoint :=`
- Line 21: `def rgRestrict (sys : BetaSystem) : CouplingRegion → CouplingRegion :=`
- Line 24: `def orderNucleus (sys : BetaSystem) : _root_.Nucleus CouplingRegion where`
- Line 48: `def coreNucleus (sys : BetaSystem) : HeytingLean.Core.Nucleus CouplingRegion where`
- Line 76: `theorem fixed_region_iff_subset_uvSafe (sys : BetaSystem) (U : CouplingRegion) :`
- Line 92: `def heytingNegation (sys : BetaSystem) (U : CouplingRegion) : CouplingRegion :=`
- Line 95: `theorem heytingNegation_carrier (sys : BetaSystem) (U : CouplingRegion) :`

## `HeytingLean/AsymptoticSafety/Predictions/DarkMatter.lean`

- Line 6: `def portalPositiveSet : Set CouplingPoint := { g | 0 < g.portalCoupling }`
- Line 8: `def portalPositiveRegion : CouplingRegion := portalPositiveSet`
- Line 10: `def portalExclusionRegion (sys : BetaSystem) : CouplingRegion :=`
- Line 13: `theorem no_simplest_WIMP (sys : BetaSystem)`

## `HeytingLean/AsymptoticSafety/RGFlow.lean`

- Line 7: `structure RGStepConfig where`
- Line 11: `def eulerStep (cfg : RGStepConfig) (sys : BetaSystem) (g : CouplingPoint) : CouplingPoint :=`
- Line 15: `noncomputable def projectToUVSafe (sys : BetaSystem) (g : CouplingPoint) : CouplingPoint :=`
- Line 33: `def isUVSafe (sys : BetaSystem) (g : CouplingPoint) : Prop :=`
- Line 36: `theorem projectToUVSafe_idempotent (sys : BetaSystem) (g : CouplingPoint) :`
- Line 53: `theorem gravitationalFixedPoint_isUVSafe (sys : BetaSystem) :`
- Line 57: `theorem topYukawa_zero_of_uvSafe_and_screening`
- Line 68: `theorem portal_zero_of_uvSafe_and_screening`

## `HeytingLean/AsymptoticSafety/ScaleSymmetry.lean`

- Line 7: `def scaleThreshold (s : Renormalization.RatchetScale) : ℝ :=`
- Line 10: `def scaleSafeSet (sys : BetaSystem) (s : Renormalization.RatchetScale) : Set CouplingPoint :=`
- Line 27: `def rgRestrictAtScale (sys : BetaSystem) (s : Renormalization.RatchetScale) :`
- Line 31: `theorem gravitationalFixedPoint_mem_scaleSafeSet`
- Line 36: `theorem scaleSafeSet_mono (sys : BetaSystem)`
- Line 66: `noncomputable def rgDimensionalRatchet (sys : BetaSystem) :`
- Line 100: `def uvScale : Renormalization.RatchetScale := ⟨0, 0⟩`
- Line 102: `theorem constructive_at_uv : Renormalization.logicAtScale uvScale = .constructive := by`
- Line 105: `noncomputable def freeEnergyProxy (sys : BetaSystem) (g : CouplingPoint) : ℝ :=`
- Line 108: `theorem freeEnergy_at_fixedPoint_zero (sys : BetaSystem) :`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/AgentModel.lean`

- Line 25: `structure Agent (n : Nat) where`
- Line 34: `structure AgentNetwork where`
- Line 42: `def throughputVec (net : AgentNetwork) : Fin net.n → ℝ :=`
- Line 46: `def qualityVec (net : AgentNetwork) : Fin net.n → ℝ :=`
- Line 50: `def totalThroughput (net : AgentNetwork) : ℝ :=`
- Line 53: `theorem totalThroughput_pos (net : AgentNetwork) : 0 < totalThroughput net := by`
- Line 64: `def meanThroughput (net : AgentNetwork) : ℝ :=`
- Line 67: `theorem meanThroughput_pos (net : AgentNetwork) : 0 < meanThroughput net := by`
- Line 72: `def meanQuality (net : AgentNetwork) : ℝ :=`
- Line 76: `def qualityThroughputCov (net : AgentNetwork) : ℝ :=`
- Line 81: `def rho (net : AgentNetwork) : ℝ :=`
- Line 84: `theorem rho_nonneg (net : AgentNetwork) : 0 ≤ rho net := by`
- Line 88: `def A1 (net : AgentNetwork) : Prop :=`
- Line 92: `def A2 (net : AgentNetwork) : Prop :=`
- Line 96: `def A2Strict (net : AgentNetwork) : Prop :=`
- Line 100: `def A3 (_net : AgentNetwork) : Prop := True`
- Line 102: `theorem not_A1_iff_all_throughputs_equal (net : AgentNetwork) :`
- Line 113: `def floatTotalThroughput (xs : List Float) : Float :=`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/Bridge.lean`


## `HeytingLean/Bridge/AlMayahi/TauCoordination/ConsensusQuality.lean`

- Line 22: `def uniformWeight (net : AgentNetwork) : ℝ :=`
- Line 26: `def clockWeight (net : AgentNetwork) (i : Fin net.n) : ℝ :=`
- Line 30: `def tauWeight (net : AgentNetwork) (_i : Fin net.n) : ℝ :=`
- Line 34: `def protocolWeight (net : AgentNetwork) (protocol : Protocol) : Fin net.n → ℝ :=`
- Line 39: `theorem clockWeight_nonneg (net : AgentNetwork) (i : Fin net.n) :`
- Line 44: `theorem tauWeight_nonneg (net : AgentNetwork) (i : Fin net.n) :`
- Line 49: `theorem clockWeight_sum (net : AgentNetwork) :`
- Line 62: `theorem tauWeight_sum (net : AgentNetwork) :`
- Line 73: `def consensusNumerator (net : AgentNetwork) (protocol : Protocol) : ℝ :=`
- Line 77: `def consensusDenominator (net : AgentNetwork) (protocol : Protocol) : ℝ :=`
- Line 81: `def consensusQuality (net : AgentNetwork) (protocol : Protocol) : ℝ :=`
- Line 85: `def consensusBias (net : AgentNetwork) (protocol : Protocol) : ℝ :=`
- Line 88: `theorem consensusDenominator_pos (net : AgentNetwork) (protocol : Protocol) :`
- Line 92: `theorem consensusQuality_unit_interval (net : AgentNetwork) (protocol : Protocol) :`
- Line 128: `theorem consensusBias_nonneg (net : AgentNetwork) (protocol : Protocol) :`
- Line 133: `theorem consensusBias_zero_iff_uniform (net : AgentNetwork) (protocol : Protocol) :`
- Line 157: `lemma throughput_eq_of_clock_uniform (net : AgentNetwork)`
- Line 174: `theorem clockBias_pos_of_heterogeneous (net : AgentNetwork) (hA1 : A1 net) :`
- Line 188: `def floatConsensusBias (weights : List Float) : Float :=`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/Corollaries.lean`

- Line 16: `abbrev mift_steady_state`
- Line 25: `abbrev reputation_converges_to_quality`
- Line 33: `abbrev tau_minimizes_bias (net : AgentNetwork) (hA1 : A1 net) :`
- Line 38: `def criticalNetworkSize (rho muL eps : ℝ) : Nat :=`
- Line 41: `theorem criticalNetworkSize_nonneg (rho muL eps : ℝ) :`
- Line 46: `theorem phase_transition`
- Line 62: `theorem clock_precision_ceiling (rho muL : ℝ) :`
- Line 67: `theorem universal_scaling_law (eps : ℝ) (hEps : 0 < eps) :`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/PoVReputation.lean`

- Line 17: `structure ReputationParams where`
- Line 26: `def reputationUpdate`
- Line 35: `theorem reputationUpdate_monotone_verified`
- Line 48: `def stationaryReputation (params : ReputationParams) (p_v p_f : ℝ) : ℝ :=`
- Line 52: `theorem reputation_equilibrium`
- Line 62: `def acceptedWeight {n : Nat} (agents : List (Agent n × Bool)) : ℝ :=`
- Line 66: `def claimAccepted {n : Nat} (agents : List (Agent n × Bool)) (threshold : ℝ) : Prop :=`
- Line 69: `theorem claimAccepted_of_lower_threshold`
- Line 80: `def floatReputationUpdate`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/Propositions.lean`

- Line 16: `theorem progress_fairness (net : AgentNetwork) :`
- Line 22: `def unsupportedClaimGain (reward : ℝ) (pUnsupportedAccepted : ℕ → ℝ) (k : ℕ) : ℝ :=`
- Line 26: `def ConvergesToZero (f : ℕ → ℝ) : Prop :=`
- Line 31: `theorem spam_resistance`
- Line 59: `def verificationRatioNat (verified proposed : ℕ) : ℝ :=`
- Line 79: `def alphaCrit (m : ℝ) : ℝ :=`
- Line 82: `def alphaCritM3 : ℝ := alphaCrit 3`
- Line 84: `theorem alphaCritM3_eq : alphaCritM3 = (2 : ℝ) / 5 := by`
- Line 88: `theorem adversarial_resilience (α : ℝ) (hα : α < alphaCritM3) : α < (2 : ℝ) / 5 := by`
- Line 92: `theorem monotonic_knowledge_growth (verified refuted : Nat) :`
- Line 97: `theorem progress_fairness_heterogeneous (net : AgentNetwork) :`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/StabilityInvariant.lean`

- Line 16: `structure StabilityState where`
- Line 23: `def verificationRatio (s : StabilityState) : ℝ :=`
- Line 27: `def isStable (s : StabilityState) : Prop :=`
- Line 31: `inductive CorrectionAction`
- Line 38: `def miftMonitor (s : StabilityState) : List CorrectionAction := by`
- Line 45: `def floatVerificationRatio (verified proposed : Nat) : Float :=`
- Line 49: `inductive RuntimeCorrectionAction`
- Line 56: `def miftMonitorRuntime (verified proposed : Nat) (threshold : Float) :`
- Line 63: `theorem verification_improves_stability`
- Line 79: `theorem stability_recovery (s : StabilityState) :`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/TauConsensusLimit.lean`

- Line 20: `def ConvergesAS (f : ℕ → ℝ) (limit : ℝ) : Prop :=`
- Line 24: `structure IIDDraws (nets : ℕ → AgentNetwork) : Prop where`
- Line 31: `structure AsymptoticMoments (nets : ℕ → AgentNetwork) where`
- Line 41: `structure ZeroAsymptoticBias`
- Line 49: `structure MinimumVariance (protocol : Protocol) (_nets : ℕ → AgentNetwork) where`
- Line 56: `structure TauConsensusLimitAssumptions (nets : ℕ → AgentNetwork) where`
- Line 68: `theorem convergesAS_unique`
- Line 101: `theorem tau_convergence`
- Line 109: `theorem persistent_clock_bias`
- Line 118: `def precisionFloor (rho muL : ℝ) : ℝ := rho / muL`
- Line 120: `theorem precision_floor_pos (rho muL : ℝ) (hRho : 0 < rho) (hMu : 0 < muL) :`
- Line 130: `theorem tau_asymptotic_optimality`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/TauCoordinationThm.lean`

- Line 19: `def expectedConsensusQuality (net : AgentNetwork) (protocol : Protocol) : ℝ :=`
- Line 23: `def QualityIndependentOfThroughput (net : AgentNetwork) : Prop :=`
- Line 26: `lemma tau_quality_eq_mean (net : AgentNetwork) :`
- Line 40: `lemma clock_quality_eq_weighted (net : AgentNetwork) :`
- Line 62: `lemma clock_quality_decomposition (net : AgentNetwork) :`
- Line 87: `theorem tau_quality_geq`
- Line 97: `theorem tau_bias_leq (net : AgentNetwork) (_hA1 : A1 net) :`
- Line 108: `theorem tau_bias_eq_iff_homogeneous (net : AgentNetwork) :`
- Line 153: `theorem tau_strict_quality_gain`
- Line 179: `theorem tau_quality_gain_pos`

## `HeytingLean/Bridge/AlMayahi/TauCoordination/Types.lean`

- Line 17: `structure Tau where`
- Line 22: `structure ClockTime where`
- Line 27: `noncomputable def clockRateField (dt : ClockTime) (dτ : Tau) : ℝ :=`
- Line 30: `theorem clockRateField_nonneg`
- Line 37: `inductive VerificationState`
- Line 46: `structure KnowledgeClaim where`
- Line 54: `inductive Protocol`
- Line 60: `def floatClockRateField (dt dτ : Float) : Float :=`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/AlphaBridge.lean`

- Line 14: `noncomputable def fineStructureConstant : ℝ :=`
- Line 18: `noncomputable def alphaBridgeRatio : ℝ :=`
- Line 21: `theorem fineStructureConstant_pos : 0 < fineStructureConstant := by`
- Line 25: `theorem alphaBridgeRatio_pos : 0 < alphaBridgeRatio := by`
- Line 32: `def alphaBridgeRatioFloat : Float :=`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/BetaSpectrum.lean`

- Line 14: `noncomputable def log10 (x : ℝ) : ℝ :=`
- Line 18: `noncomputable def betaFromTau (kappa τMethod τPlanck : ℝ) : ℝ :=`
- Line 22: `structure BetaDatum where`
- Line 32: `structure BetaCouplingSpectrum where`
- Line 36: `def tauEpochBetaSpectrum : BetaCouplingSpectrum :=`
- Line 104: `def betaReportedRows : List BetaDatum :=`
- Line 108: `theorem tauEpochBetaSpectrum_card :`
- Line 113: `theorem beta_missing_count_eq_one :`
- Line 117: `theorem betaFromTau_zero_kappa (τMethod τPlanck : ℝ) :`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/DomainData.lean`

- Line 15: `structure H0Measurement where`
- Line 24: `structure LhcKappaMeasurement where`
- Line 35: `structure NmrMeasurement where`
- Line 47: `structure NeutronMeasurement where`
- Line 56: `structure ProtonMeasurement where`
- Line 65: `structure MuonMeasurement where`
- Line 75: `def h0Ensemble : Array H0Measurement := #[`
- Line 86: `def lhcKappaTable : Array LhcKappaMeasurement := #[`
- Line 97: `def nmrTable : Array NmrMeasurement := #[`
- Line 109: `def neutronTable : Array NeutronMeasurement := #[`
- Line 122: `def protonTable : Array ProtonMeasurement := #[`
- Line 132: `def muonTable : Array MuonMeasurement := #[`
- Line 139: `def h0Values : List Float := h0Ensemble.toList.map (fun r => r.h0Value)`
- Line 140: `def h0Sigmas : List Float := h0Ensemble.toList.map (fun r => r.sigma)`
- Line 141: `def h0LogTau : List Float := h0Ensemble.toList.map (fun r => r.log10TauMethod)`
- Line 143: `def lhcDeltaKappa : List Float := lhcKappaTable.toList.map (fun r => r.deltaKappa)`
- Line 145: `def nmrH2OFieldInv : List Float :=`
- Line 148: `def nmrH2OShift : List Float :=`
- Line 151: `def neutronBottleLifetimes : List Float :=`
- Line 154: `def neutronBeamLifetimes : List Float :=`
- Line 157: `def neutronBottleSigmas : List Float :=`
- Line 160: `def neutronBeamSigmas : List Float :=`
- Line 163: `def protonElectronic : List Float :=`
- Line 166: `def protonMuonic : List Float :=`
- Line 169: `def protonTauProxyAll : List Float := protonTable.toList.map (fun r => r.log10TauMethod)`
- Line 170: `def protonRadiusAll : List Float := protonTable.toList.map (fun r => r.radiusFm)`
- Line 172: `def muonTheoryValues : List Float := muonTable.toList.map (fun r => r.aMuTimes1e11)`
- Line 173: `def muonTauProxy : List Float := muonTable.toList.map (fun r => r.log10TauMethod)`
- Line 176: `theorem default_proxy_table_valid :`

## `HeytingLean/Bridge/AlMayahi/TauEpoch.lean`


## `HeytingLean/Bridge/AlMayahi/TauEpoch/NecessityTheorem.lean`

- Line 17: `structure OneClockModel where`
- Line 26: `structure InvariantSignature where`
- Line 38: `def generates (M : OneClockModel) (S : InvariantSignature) : Prop :=`
- Line 43: `structure TwoClockAssumptions where`
- Line 60: `lemma domain_locality_constraint`
- Line 68: `lemma directional_recurrence_constant : ((1 : ℚ) / 2) ^ 6 = (1 : ℚ) / 64 := by`
- Line 72: `lemma directional_recurrence_constraint`
- Line 80: `lemma locked_tau_monotonicity_constraint`
- Line 87: `lemma no_calibration_channel_constraint`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/Predictions.lean`

- Line 14: `inductive PredictionStatus`
- Line 22: `structure Prediction where`
- Line 34: `def h1ComputedRho : Float :=`
- Line 37: `def h1ComputedStatus : PredictionStatus :=`
- Line 40: `def l2ComputedStatus : PredictionStatus :=`
- Line 45: `def n1NmrComputedStatus : PredictionStatus :=`
- Line 49: `def n1NeutronComputedStatus : PredictionStatus :=`
- Line 54: `def p1ComputedStatus : PredictionStatus :=`
- Line 61: `def m1ComputedStatus : PredictionStatus :=`
- Line 68: `def p1PearsonR : Float := floatPearson protonTauProxyAll protonRadiusAll`
- Line 69: `def p1PearsonP : Float := floatPearsonOneSidedPValue protonTauProxyAll protonRadiusAll true`
- Line 71: `def m1PearsonR : Float := floatPearson muonTauProxy muonTheoryValues`
- Line 72: `def m1PearsonP : Float := floatPearsonOneSidedPValue muonTauProxy muonTheoryValues false`
- Line 74: `def predictionH1 : Prediction :=`
- Line 85: `def predictionL2 : Prediction :=`
- Line 96: `def predictionN1Nmr : Prediction :=`
- Line 107: `def predictionN1Neutron : Prediction :=`
- Line 118: `def predictionP1 : Prediction :=`
- Line 129: `def predictionM1 : Prediction :=`
- Line 140: `def allPredictions : List Prediction :=`
- Line 143: `def predictionStatusCounts : Nat × Nat × Nat × Nat :=`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/ProjectionLaw.lean`

- Line 16: `structure TwoClockModel where`
- Line 23: `noncomputable def TwoClockModel.predict (m : TwoClockModel) (tauRatio : ℝ) : ℝ :=`
- Line 31: `noncomputable def TwoClockModel.offset (m : TwoClockModel) (tauRatio : ℝ) : ℝ :=`
- Line 35: `theorem TwoClockModel.offset_mono_of_nonneg`
- Line 52: `theorem TwoClockModel.sign_prediction`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/ProjectionOperator.lean`

- Line 14: `structure ProjectionOperator where`
- Line 20: `noncomputable def ProjectionOperator.eval (P : ProjectionOperator) (x : ℝ) : ℝ :=`
- Line 28: `theorem ProjectionOperator.mono_of_nonneg_beta`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/Stats.lean`

- Line 30: `noncomputable def wtWeight (σ : Fin n → ℝ) (i : Fin n) : ℝ :=`
- Line 34: `noncomputable def wtMean (x σ : Fin n → ℝ) : ℝ :=`
- Line 38: `noncomputable def chi2Wt (x σ : Fin n → ℝ) : ℝ :=`
- Line 42: `noncomputable def birge (chi2 : ℝ) (dof : ℕ) : ℝ :=`
- Line 46: `noncomputable def lambdaStat (chi2 : ℝ) (n : ℕ) : ℝ :=`
- Line 50: `def noTension (chi2 : ℝ) (dof : ℕ) : Prop :=`
- Line 53: `theorem birge_nonneg (chi2 : ℝ) (dof : ℕ) : 0 ≤ birge chi2 dof := by`
- Line 56: `theorem lambda_eq_zero_iff (chi2 : ℝ) (n : ℕ) (hnn : (n : ℝ) ≠ 0) :`
- Line 69: `theorem birge_sq_eq (chi2 : ℝ) (dof : ℕ) (hchi : 0 ≤ chi2 / (dof : ℝ)) :`
- Line 74: `theorem birge_eq_one_iff_no_tension`
- Line 97: `theorem birge_mono_lambda (chi2 : ℝ) (n : ℕ) (hchi : 0 ≤ chi2 / (n : ℝ)) :`
- Line 105: `noncomputable def mean (x : Fin n → ℝ) : ℝ :=`
- Line 109: `noncomputable def centered (x : Fin n → ℝ) (i : Fin n) : ℝ :=`
- Line 113: `noncomputable def covariance (x y : Fin n → ℝ) : ℝ :=`
- Line 117: `noncomputable def variance (x : Fin n → ℝ) : ℝ :=`
- Line 121: `noncomputable def pearsonRhoRaw (x y : Fin n → ℝ) : ℝ :=`
- Line 128: `noncomputable def pearsonRho (x y : Fin n → ℝ) : ℝ :=`
- Line 132: `noncomputable def rank (x : Fin n → ℝ) (i : Fin n) : ℝ :=`
- Line 136: `noncomputable def spearmanRho (x y : Fin n → ℝ) : ℝ :=`
- Line 139: `theorem pearsonRho_bound (x y : Fin n → ℝ) :`
- Line 149: `theorem spearmanRho_bound (x y : Fin n → ℝ) :`
- Line 156: `noncomputable def binomialUpperTailRaw (positiveCount total : ℕ) : ℝ :=`
- Line 161: `noncomputable def binomialSignPValue (positiveCount total : ℕ) : ℝ :=`
- Line 164: `theorem binomialSignPValue_unit_interval (positiveCount total : ℕ) :`
- Line 176: `noncomputable def regressionDenom (x : Fin n → ℝ) : ℝ :=`
- Line 180: `noncomputable def regressionSlope (x y : Fin n → ℝ) : ℝ :=`
- Line 187: `noncomputable def regressionIntercept (x y : Fin n → ℝ) : ℝ :=`
- Line 191: `noncomputable def regressionPredict (x y : Fin n → ℝ) (i : Fin n) : ℝ :=`
- Line 195: `noncomputable def residualSS (x y : Fin n → ℝ) : ℝ :=`
- Line 199: `noncomputable def totalSS (y : Fin n → ℝ) : ℝ :=`
- Line 203: `noncomputable def rSquaredRaw (x y : Fin n → ℝ) : ℝ :=`
- Line 210: `noncomputable def linearRegression (x y : Fin n → ℝ) : ℝ × ℝ × ℝ :=`
- Line 213: `theorem linearRegression_r2_unit_interval (x y : Fin n → ℝ) :`
- Line 223: `theorem linearRegression_perfect (x y : Fin n → ℝ) (h : rSquaredRaw x y = 1) :`
- Line 232: `def floatSum (xs : List Float) : Float :=`
- Line 236: `def floatMean (xs : List Float) : Float :=`
- Line 242: `def floatWeightedMean (xs σs : List Float) : Float :=`
- Line 256: `def floatChi2Wt (xs σs : List Float) : Float :=`
- Line 265: `def floatRanks (xs : List Float) : List Float :=`
- Line 272: `def floatCovariance (xs ys : List Float) : Float :=`
- Line 286: `def floatVariance (xs : List Float) : Float :=`
- Line 290: `def floatClampUnit (x : Float) : Float :=`
- Line 294: `def floatPearson (xs ys : List Float) : Float :=`
- Line 303: `def floatSpearman (xs ys : List Float) : Float :=`
- Line 311: `def floatPearsonOneSidedPValue (xs ys : List Float) (positive : Bool) : Float :=`
- Line 326: `def floatBinomialUpperTail (positiveCount total : Nat) : Float :=`
- Line 332: `def floatBinomialSignPValue (positiveCount total : Nat) : Float :=`
- Line 336: `def floatAllPositive (xs : List Float) : Bool :=`
- Line 340: `def floatRegressionSlope (xs ys : List Float) : Float :=`
- Line 356: `def floatRegressionIntercept (xs ys : List Float) : Float :=`
- Line 360: `def floatRegressionPredict (xs ys : List Float) (x : Float) : Float :=`
- Line 364: `def floatLinearRegression (xs ys : List Float) : Float × Float × Float :=`

## `HeytingLean/Bridge/AlMayahi/TauEpoch/TauProxy.lean`

- Line 13: `inductive DomainKind`
- Line 23: `structure TauProxyAssignment where`
- Line 34: `def ValidTauProxy (a : TauProxyAssignment) : Prop :=`
- Line 38: `def defaultTauProxy : DomainKind → TauProxyAssignment`
- Line 76: `theorem defaultTauProxy_valid (d : DomainKind) :`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery/ElectromagneticAnalogue.lean`

- Line 23: `abbrev Vec3 := Fin 3 → ℝ`
- Line 26: `structure TauElectromagneticState where`
- Line 41: `def TauGaussLike (s : TauElectromagneticState) : Prop :=`
- Line 45: `def TauMagneticGaussLike (s : TauElectromagneticState) : Prop :=`
- Line 49: `def TauFaradayLike (s : TauElectromagneticState) : Prop :=`
- Line 53: `def TauAmpereLike (s : TauElectromagneticState) : Prop :=`
- Line 57: `def tauChargeContinuityResidual (s : TauElectromagneticState) : ℝ :=`
- Line 60: `theorem tau_continuity_equation_of_ampere_balance (s : TauElectromagneticState)`
- Line 66: `theorem tau_faraday_zero_of_static_magnetic (s : TauElectromagneticState)`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery/GravityRecovery.lean`

- Line 25: `structure GravityModel where`
- Line 33: `noncomputable def causalVelocity (M : GravityModel) (τ : ℝ) : ℝ :=`
- Line 36: `theorem causalVelocity_eq_clockRate (M : GravityModel) {τ : ℝ} (hτ : τ ≠ 0) :`
- Line 44: `theorem clockProjection_le_tau_of_unit_clock_bound (M : GravityModel) {τ : ℝ}`
- Line 55: `theorem causalVelocity_le_c_of_clock_bound (M : GravityModel) {τ : ℝ}`
- Line 62: `noncomputable def redshiftRatio (M : GravityModel) (τ_emit τ_obs : ℝ) : ℝ :=`
- Line 66: `theorem redshiftRatio_pos (M : GravityModel) (τ_emit τ_obs : ℝ) :`
- Line 72: `noncomputable def weakFieldPotential (M : GravityModel) (r : ℝ) : ℝ :=`
- Line 76: `noncomputable def inverseSquareAcceleration (M : GravityModel) (r : ℝ) : ℝ :=`
- Line 79: `theorem inverseSquareAcceleration_nonneg (M : GravityModel) {r : ℝ} (hr : r ≠ 0) :`
- Line 86: `theorem weak_field_potential_halves_at_double_radius (M : GravityModel) {r : ℝ}`
- Line 92: `theorem newtonian_limit_of_inverse_square (M : GravityModel) {r : ℝ}`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery.lean`


## `HeytingLean/Bridge/AlMayahi/UDTRecovery/MassEnergyRecovery.lean`

- Line 26: `noncomputable def tauEnergy (K : RecoveryConstants) (τ : ℝ) : ℝ :=`
- Line 30: `noncomputable def restMassOfGap (K : RecoveryConstants) (g : AsymmetryGap) : ℝ :=`
- Line 34: `noncomputable def restEnergyOfGap (K : RecoveryConstants) (g : AsymmetryGap) : ℝ :=`
- Line 37: `theorem planck_einstein_of_tau_frequency (K : RecoveryConstants) {τ : ℝ} (hτ : 0 < τ) :`
- Line 42: `theorem rest_energy_of_asymmetry_gap (K : RecoveryConstants) (g : AsymmetryGap)`
- Line 48: `theorem massive_of_trapped_component {n : ℕ} {v : Fin n → ℝ}`
- Line 53: `theorem gap_energy_positive (K : RecoveryConstants) (g : AsymmetryGap)`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery/QuantumRecovery.lean`

- Line 33: `structure TauWavefunction (n : ℕ) where`
- Line 38: `def waveNormSq {n : ℕ} (ψ : TauWavefunction n) : ℝ :=`
- Line 41: `theorem waveNormSq_nonneg {n : ℕ} (ψ : TauWavefunction n) :`
- Line 47: `noncomputable def bornWeight {n : ℕ} (ψ : TauWavefunction n) (i : Fin n) : ℝ :=`
- Line 50: `theorem bornWeight_nonneg {n : ℕ} (ψ : TauWavefunction n) (hnorm : 0 < waveNormSq ψ)`
- Line 56: `theorem born_normalization_surface {n : ℕ} (ψ : TauWavefunction n)`
- Line 75: `structure QuantumEvolution (n : ℕ) where`
- Line 87: `def SatisfiesRealLinearEvolution {n : ℕ} (e : QuantumEvolution n) : Prop :=`
- Line 91: `inductive BellClosureStatus`
- Line 97: `def bellClosureStatus : BellClosureStatus := .open`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery/StandardRecoveries.lean`

- Line 25: `inductive RecoveryStatus`
- Line 33: `structure StandardRecoveryLedger where`
- Line 52: `def standardRecoveries : StandardRecoveryLedger where`
- Line 70: `theorem newton_status :`
- Line 73: `theorem emc2_status :`
- Line 76: `theorem planck_einstein_status :`
- Line 79: `theorem poisson_status :`
- Line 82: `theorem maxwell_status :`
- Line 85: `theorem schrodinger_status :`
- Line 88: `theorem lorentz_status :`
- Line 91: `theorem dalembert_status :`
- Line 94: `theorem born_rule_status :`
- Line 97: `theorem bell_status :`
- Line 100: `theorem euler_lagrange_status :`
- Line 103: `theorem noether_status :`
- Line 106: `theorem weak_field_gr_status :`
- Line 109: `theorem prime_stability_status :`
- Line 112: `theorem born_heyting_gap_status :`
- Line 115: `theorem koide_formula_status :`
- Line 119: `def standardRecoveryRows : List (String × RecoveryStatus) :=`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery/TauFieldCore.lean`

- Line 34: `structure RecoveryConstants where`
- Line 43: `structure ContinuousPhaseState where`
- Line 50: `def phaseDifference (s : ContinuousPhaseState) : ℝ :=`
- Line 54: `def synchronized (s : ContinuousPhaseState) : Prop :=`
- Line 58: `def evolvePhase (s : ContinuousPhaseState) (δτ : ℝ) : ContinuousPhaseState where`
- Line 64: `theorem phaseDifference_evolve (s : ContinuousPhaseState) (δτ : ℝ) :`
- Line 72: `noncomputable def tauRate (τ : ℝ) : ℝ :=`
- Line 81: `theorem tauRate_pos {τ : ℝ} (hτ : 0 < τ) : 0 < tauRate τ := by`
- Line 85: `theorem nuTau_pos {τ : ℝ} (hτ : 0 < τ) : 0 < nuTau τ :=`
- Line 88: `theorem tauPotential_pos {τ : ℝ} (hτ : 0 < τ) : 0 < tauPotential τ :=`
- Line 91: `theorem tauRate_antitone_on_pos {τ₁ τ₂ : ℝ}`
- Line 97: `theorem tauPotential_antitone_on_pos {τ₁ τ₂ : ℝ}`
- Line 103: `noncomputable def clockPhase (t τ : ℝ) : ℝ :=`
- Line 106: `theorem clockPhase_zero_left {τ : ℝ} : clockPhase 0 τ = 0 := by`
- Line 109: `theorem clockPhase_nonneg {t τ : ℝ} (ht : 0 ≤ t) (hτ : 0 < τ) :`
- Line 115: `structure TauDensity where`
- Line 120: `structure TauFlux where`
- Line 124: `structure TauCurrent where`
- Line 129: `def staticTauFlux : TauFlux := ⟨0⟩`
- Line 134: `def inducedTauFlux (ρ v : ℝ) : TauFlux := ⟨ρ * v⟩`
- Line 136: `theorem inducedTauFlux_zero_of_static_velocity (ρ : ℝ) :`
- Line 141: `def continuityResidual (densityRate divergenceFlux : ℝ) : ℝ :=`
- Line 144: `theorem continuityResidual_zero_of_balance {densityRate divergenceFlux : ℝ}`
- Line 151: `theorem clockRateField_reconstructs_time`
- Line 158: `theorem flat_clock_projection_eq_tau (τ : ℝ) :`

## `HeytingLean/Bridge/AlMayahi/UDTRecovery/VariationalDynamics.lean`

- Line 35: `structure TauFieldState where`
- Line 43: `structure TauVariationalModel where`
- Line 49: `noncomputable def recoveryLagrangianDensity (M : TauVariationalModel) (s : TauFieldState) : ℝ :=`
- Line 52: `theorem recoveryLagrangianDensity_static (M : TauVariationalModel) (s : TauFieldState)`
- Line 59: `def eulerLagrangeResidual (M : TauVariationalModel) (s : TauFieldState) : ℝ :=`
- Line 63: `def SatisfiesEulerLagrange (M : TauVariationalModel) (s : TauFieldState) : Prop :=`
- Line 66: `theorem euler_lagrange_of_balance (M : TauVariationalModel) (s : TauFieldState)`
- Line 73: `def SatisfiesStaticPoisson (M : TauVariationalModel) (s : TauFieldState) : Prop :=`
- Line 76: `theorem static_poisson_source_form (M : TauVariationalModel) (s : TauFieldState)`
- Line 87: `def SatisfiesDalembert (s : TauFieldState) : Prop :=`
- Line 90: `theorem perturbative_dalembert_surface (M : TauVariationalModel) (s : TauFieldState)`
- Line 101: `structure TauCurrentBalance where`
- Line 106: `def ConservedTauCurrent (b : TauCurrentBalance) : Prop :=`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/ClockRateField.lean`

- Line 24: `structure ClockRateField where`
- Line 30: `def clockProjection (crf : ClockRateField) (τ : ℝ) : ℝ :=`
- Line 34: `theorem clockProjection_zero (crf : ClockRateField) :`
- Line 41: `theorem clockProjection_monotone_nonneg (crf : ClockRateField)`
- Line 53: `def flatClockRateField : ClockRateField where`
- Line 59: `theorem clockProjection_flat (τ : ℝ) :`
- Line 67: `noncomputable def projectedClockRate (crf : ClockRateField)`
- Line 72: `theorem projectedClockRate_flat_eq_one (P : ProjectionOperator) :`
- Line 77: `def clockRateDeviation (crf : ClockRateField) (τ : ℝ) : ℝ :=`
- Line 81: `theorem clockRateDeviation_zero (crf : ClockRateField) :`
- Line 86: `theorem clockRateDeviation_gt_neg_one (crf : ClockRateField) (τ : ℝ) :`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/FalsifiabilityPredicates.lean`

- Line 24: `inductive MechanismLevel`
- Line 32: `structure FormalPrediction where`
- Line 50: `def mechanismIndependent (P Q : FormalPrediction) : Prop :=`
- Line 54: `theorem mechanismIndependent_symm {P Q : FormalPrediction}`
- Line 60: `theorem not_mechanismIndependent_self (P : FormalPrediction) :`
- Line 65: `theorem mechanism_levels_distinct :`
- Line 76: `structure Discriminator where`
- Line 84: `def discriminatorD1 : Discriminator :=`
- Line 90: `def discriminatorD2 : Discriminator :=`
- Line 96: `def discriminatorD3 : Discriminator :=`
- Line 102: `def discriminatorD4 : Discriminator :=`
- Line 108: `def discriminatorD5 : Discriminator :=`
- Line 115: `def allDiscriminators : List Discriminator :=`
- Line 119: `theorem discriminators_span_mechanism_levels :`
- Line 129: `theorem structural_exclusion_is_mechanism_specific`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/GapDecompositionBridge.lean`

- Line 36: `structure GapDecomposition where`
- Line 45: `def totalGap (g : GapDecomposition) : ℝ :=`
- Line 49: `theorem totalGap_nonneg (g : GapDecomposition) :`
- Line 56: `theorem gap_decomposition_additive (g : GapDecomposition) :`
- Line 61: `theorem Δ_quant_le_total (g : GapDecomposition) :`
- Line 66: `theorem Δ_gate_le_total (g : GapDecomposition) :`
- Line 71: `theorem Δ_recon_le_total (g : GapDecomposition) :`
- Line 77: `theorem totalGap_zero_iff (g : GapDecomposition) :`
- Line 92: `def gapFromNucleus {n : ℕ} (v : Fin n → ℝ)`
- Line 104: `theorem gapFromNucleus_gate_eq {n : ℕ} (v : Fin n → ℝ)`
- Line 113: `theorem hossenfelder_gap_from_nucleus {n : ℕ} (v : Fin n → ℝ)`
- Line 125: `theorem pm_bounded_gate_gap {n : ℕ} (v : Fin n → ℝ) :`
- Line 131: `def flatGapDecomposition (Δ_gate Δ_recon : ℝ)`
- Line 141: `theorem flatGap_total (Δ_gate Δ_recon : ℝ)`
- Line 148: `def composeGaps (g₁ g₂ : GapDecomposition) : GapDecomposition where`
- Line 157: `theorem composeGaps_total (g₁ g₂ : GapDecomposition) :`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/HZComputationalBridge.lean`

- Line 40: `inductive ArithmeticMode`
- Line 46: `theorem hz_ne_standard : ArithmeticMode.hz ≠ ArithmeticMode.standard := by decide`
- Line 51: `structure SparsityRegime where`
- Line 57: `noncomputable def selectArithmetic (regime : SparsityRegime) (ρ : ℝ) : ArithmeticMode :=`
- Line 61: `theorem selectArithmetic_hz (regime : SparsityRegime) (ρ : ℝ)`
- Line 68: `theorem selectArithmetic_standard (regime : SparsityRegime) (ρ : ℝ)`
- Line 76: `theorem selectArithmetic_monotone (regime : SparsityRegime) {ρ₁ ρ₂ : ℝ}`
- Line 84: `theorem flat_selects_hz (regime : SparsityRegime) (n : ℕ) (hn : n ≠ 0)`
- Line 92: `theorem sparseField_selects_hz {n : ℕ} (regime : SparsityRegime)`
- Line 101: `theorem hz_density_bound (X : HybridNumber) (hX : IsCanonical X)`
- Line 109: `structure HZGapAnalysis (n : ℕ) where`
- Line 119: `def HZGapAnalysis.gapDecomp {n : ℕ} (a : HZGapAnalysis n) : GapDecomposition :=`
- Line 123: `theorem HZGapAnalysis.selects_hz {n : ℕ} (a : HZGapAnalysis n) :`
- Line 130: `theorem HZGapAnalysis.positive_gap {n : ℕ} (a : HZGapAnalysis n)`
- Line 139: `theorem HZGapAnalysis.gate_eq_trapped {n : ℕ} (a : HZGapAnalysis n) :`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/LagrangianReduction.lean`

- Line 26: `structure TauFieldPotential where`
- Line 33: `noncomputable def lagrangianDensity (L : TauFieldPotential) (dtau : ℝ) (τ : ℝ) : ℝ :=`
- Line 37: `theorem kineticTerm_nonneg (dtau : ℝ) :`
- Line 45: `theorem lagrangianDensity_static (L : TauFieldPotential) (τ : ℝ) :`
- Line 51: `theorem static_lagrangian_min (L : TauFieldPotential) (τ : ℝ) :`
- Line 59: `theorem saturation_bounded_by_potential_basin`
- Line 66: `theorem saturation_confines_to_basin`
- Line 72: `def quadraticPotential (k : ℝ) (hk : 0 ≤ k) : TauFieldPotential where`
- Line 81: `theorem quadratic_static (k : ℝ) (hk : 0 ≤ k) (τ : ℝ) :`
- Line 87: `theorem saturation_at_minimum {Q_PM : ℝ} (_hQ : 0 < Q_PM) :`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis.lean`


## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/MassGenerationGap.lean`

- Line 30: `structure AsymmetryGap where`
- Line 35: `def massless (g : AsymmetryGap) : Prop := g.Δτ = 0`
- Line 38: `def massive (g : AsymmetryGap) : Prop := 0 < g.Δτ`
- Line 41: `theorem massless_or_massive (g : AsymmetryGap) :`
- Line 48: `theorem not_massless_iff_massive (g : AsymmetryGap) :`
- Line 59: `def trappedRegime (n : ℕ) (v : Fin n → ℝ) : Set (Fin n) :=`
- Line 63: `def freeRegime (n : ℕ) (v : Fin n → ℝ) : Set (Fin n) :=`
- Line 67: `theorem trapped_free_partition (n : ℕ) (v : Fin n → ℝ) :`
- Line 75: `theorem trapped_free_disjoint (n : ℕ) (v : Fin n → ℝ) :`
- Line 84: `def nucleusGap (n : ℕ) (v : Fin n → ℝ) : ℝ :=`
- Line 88: `theorem nucleusGap_nonneg (n : ℕ) (v : Fin n → ℝ) :`
- Line 95: `theorem nucleusGap_eq_sum (n : ℕ) (v : Fin n → ℝ) :`
- Line 102: `theorem nucleusGap_zero_of_nonneg {n : ℕ} (v : Fin n → ℝ) (h : ∀ i, 0 ≤ v i) :`
- Line 111: `theorem nonneg_of_nucleusGap_zero {n : ℕ} (v : Fin n → ℝ)`
- Line 135: `theorem nucleusGap_zero_iff_nonneg {n : ℕ} (v : Fin n → ℝ) :`
- Line 140: `theorem nucleusGap_pos_iff_trapped {n : ℕ} (v : Fin n → ℝ) :`
- Line 149: `theorem nucleusGap_le_sqSum (n : ℕ) (v : Fin n → ℝ) :`

## `HeytingLean/Bridge/AlMayahi/UDTSynthesis/SparseProjectionField.lean`

- Line 38: `structure GridSample (n : ℕ) where`
- Line 44: `def deviationVector {n : ℕ} (gs : GridSample n) : Fin n → ℝ :=`
- Line 48: `theorem deviationVector_gt_neg_one {n : ℕ} (gs : GridSample n) (i : Fin n) :`
- Line 54: `theorem deviationVector_at_origin {n : ℕ} (gs : GridSample n)`
- Line 60: `theorem flat_deviation_zero {n : ℕ} (pts : Fin n → ℝ) (i : Fin n) :`
- Line 65: `theorem deviation_neg_iff_slow {n : ℕ} (gs : GridSample n) (i : Fin n) :`
- Line 70: `theorem deviation_pos_iff_fast {n : ℕ} (gs : GridSample n) (i : Fin n) :`
- Line 75: `def deviationEnergy {n : ℕ} (gs : GridSample n) : ℝ :=`
- Line 79: `theorem deviationEnergy_nonneg {n : ℕ} (gs : GridSample n) :`
- Line 85: `theorem flat_deviationEnergy_zero {n : ℕ} (pts : Fin n → ℝ) :`
- Line 92: `def deviationTrappedEnergy {n : ℕ} (gs : GridSample n) : ℝ :=`
- Line 96: `theorem deviationTrappedEnergy_le {n : ℕ} (gs : GridSample n) :`
- Line 101: `theorem deviationTrappedEnergy_nonneg {n : ℕ} (gs : GridSample n) :`
- Line 107: `theorem deviationTrappedEnergy_zero_of_χ_ge_one {n : ℕ} (gs : GridSample n)`
- Line 116: `theorem deviationTrappedEnergy_pos_of_slow {n : ℕ} (gs : GridSample n)`
- Line 126: `def gapFromGridSample {n : ℕ} (gs : GridSample n)`
- Line 132: `theorem gapFromGridSample_gate_eq {n : ℕ} (gs : GridSample n)`
- Line 140: `theorem gridSample_positive_gap {n : ℕ} (gs : GridSample n)`
- Line 152: `structure SparseProjectionField (n : ℕ) extends GridSample n where`
- Line 161: `noncomputable def sparseFieldDensity {n : ℕ} (sp : SparseProjectionField n) : ℝ :=`
- Line 165: `theorem sparseFieldDensity_nonneg {n : ℕ} (sp : SparseProjectionField n) :`
- Line 173: `theorem sparseFieldDensity_le_one {n : ℕ} (sp : SparseProjectionField n) :`
- Line 182: `def flatSparseField (n : ℕ) (pts : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :`
- Line 200: `theorem flatSparseField_density_zero (n : ℕ) (hn : n ≠ 0)`
- Line 209: `theorem deviationEnergy_le_n_mul_maxSq {n : ℕ} (gs : GridSample n)`

## `HeytingLean/Bridges/Flow.lean`

- Line 17: `abbrev FlowPoint := Array Float`
- Line 18: `abbrev FlowTraj  := Array FlowPoint`
- Line 23: `def smoothOnce (t : FlowTraj) : FlowTraj := Id.run do`
- Line 40: `def flowNucleusId : Nucleus (Set FlowTraj) where`
- Line 50: `def flowNucleusUnion (U : Set FlowTraj) : Nucleus (Set FlowTraj) where`
- Line 87: `def pointNorm (p : FlowPoint) : Float := Id.run do`
- Line 91: `def maxCurvature (t : FlowTraj) : Float := Id.run do`
- Line 101: `def avgVelMag (t : FlowTraj) : Float := Id.run do`
- Line 109: `def isAdmissible (kTol vTol : Float) (t : FlowTraj) : Bool :=`
- Line 114: `def admissibleSet (kTol vTol : Float) : Set FlowTraj :=`
- Line 117: `def flowNucleusBounded (kTol vTol : Float) : Nucleus (Set FlowTraj) :=`
- Line 121: `def dot (a b : FlowPoint) : Float := Id.run do`
- Line 128: `def cosSim (a b : FlowPoint) : Float :=`
- Line 136: `def isLoop (posTol dirCosTol : Float) (t : FlowTraj) : Bool := Id.run do`
- Line 159: `def loopSet (posTol dirCosTol : Float) : Set FlowTraj :=`
- Line 162: `def flowNucleusOsc (posTol dirCosTol : Float) : Nucleus (Set FlowTraj) :=`
- Line 167: `def isLoopStrict (posTol dirCosTol minPerim minArea : Float) (t : FlowTraj) : Bool := Id.run do`
- Line 173: `def loopSetStrict (posTol dirCosTol minPerim minArea : Float) : Set FlowTraj :=`
- Line 176: `def flowNucleusOscStrict (posTol dirCosTol minPerim minArea : Float) : Nucleus (Set FlowTraj) :=`

## `HeytingLean/Bridges/MirandaWolframHeyting.lean`

- Line 29: `def toReachingRel (R : WppRel State) : MirandaDynamics.TKFT.ReachingRel State State :=`
- Line 37: `theorem reachabilityNucleus_fixed_iff (R : WppRel State) (s₀ : State) (U : Set State) :`
- Line 66: `def toReachingRel : MirandaDynamics.TKFT.ReachingRel (HGraph V) (HGraph V) :=`

## `HeytingLean/Bridges/Nucleus/Extensions/Prenucleus.lean`

- Line 10: `structure Prenucleus (L : Type*) [SemilatticeInf L] [OrderBot L] where`
- Line 26: `def ofNucleus (n : _root_.Nucleus L) : Prenucleus L where`
- Line 32: `theorem monotone (P : Prenucleus L) : Monotone P.act := by`
- Line 41: `def toCoreNucleus (P : Prenucleus L)`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/Addition.lean`

- Line 13: `noncomputable def addLazy (A B : LazyHybridNumber) : LazyHybridNumber :=`
- Line 16: `theorem addLazy_eval (A B : LazyHybridNumber) :`
- Line 41: `noncomputable def add (A B : HybridNumber) : HybridNumber :=`
- Line 44: `theorem add_correct (A B : HybridNumber) :`
- Line 48: `theorem add_comm_eval (A B : HybridNumber) :`
- Line 53: `theorem add_fromNat (m n : Nat) :`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/DensityBounds.lean`

- Line 47: `theorem supportCard_single_level_bound (z : ZeckPayload)`
- Line 69: `theorem active_levels_bound (X : HybridNumber) (hX : IsCanonical X) (hpos : 0 < eval X) :`
- Line 136: `theorem density_upper_bound (X : HybridNumber) (hX : IsCanonical X)`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/FibIdentities.lean`

- Line 15: `theorem fib_double_identity (k : Nat) :`
- Line 27: `abbrev LazyZeckendorf := List Nat`
- Line 30: `def lazyEvalFib (z : LazyZeckendorf) : Nat :=`
- Line 40: `theorem lazyEvalFib_append (z₁ z₂ : LazyZeckendorf) :`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/HybridNumber.lean`

- Line 16: `abbrev ZeckPayload := List Nat`
- Line 19: `abbrev LazyPayload := List Nat`
- Line 21: `instance : AddZeroClass ZeckPayload where`
- Line 30: `instance : AddZeroClass LazyPayload where`
- Line 40: `abbrev HybridNumber := Nat →₀ ZeckPayload`
- Line 43: `abbrev LazyHybridNumber := Nat →₀ LazyPayload`
- Line 46: `def levelEval (z : ZeckPayload) : Nat :=`
- Line 50: `def eval (X : HybridNumber) : Nat :=`
- Line 54: `def lazyEval (X : LazyHybridNumber) : Nat :=`
- Line 57: `theorem eval_add (A B : HybridNumber) :`
- Line 83: `noncomputable def fromNat (n : Nat) : HybridNumber :=`
- Line 87: `def toLazy (X : HybridNumber) : LazyHybridNumber :=`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/Multiplication.lean`

- Line 14: `noncomputable def doubleHybrid (X : HybridNumber) : HybridNumber :=`
- Line 18: `theorem weight_even_of_pos : ∀ {i : Nat}, 0 < i → 2 ∣ weight i`
- Line 27: `noncomputable def halfTailNat (X : HybridNumber) : Nat :=`
- Line 30: `theorem eval_erase_zero_even (X : HybridNumber) : 2 ∣ eval (X.erase 0) := by`
- Line 41: `theorem eval_erase_zero_eq_two_mul_halfTailNat (X : HybridNumber) :`
- Line 71: `theorem eval_eq_level_zero_add_eval_erase_zero (X : HybridNumber) :`
- Line 82: `noncomputable def halveHybrid (X : HybridNumber) : HybridNumber :=`
- Line 88: `def isOddHybrid (X : HybridNumber) : Bool :=`
- Line 91: `theorem doubleHybrid_correct (X : HybridNumber) :`
- Line 99: `theorem halveHybrid_correct (X : HybridNumber) :`
- Line 124: `noncomputable def repeatAdd (A : HybridNumber) : Nat → HybridNumber`
- Line 128: `theorem repeatAdd_correct (A : HybridNumber) :`
- Line 143: `noncomputable def multiplyUpTo (A B : HybridNumber) : Nat → HybridNumber`
- Line 147: `theorem multiplyUpTo_correct (A B : HybridNumber) :`
- Line 169: `theorem sum_range_supportDepth_eq_eval (B : HybridNumber) :`
- Line 193: `noncomputable def multiplyBinary (A B : HybridNumber) : HybridNumber :=`
- Line 196: `theorem multiplyBinary_correct (A B : HybridNumber) :`
- Line 206: `def supportCard (X : HybridNumber) : Nat :=`
- Line 210: `noncomputable def density (X : HybridNumber) : Real :=`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/Normalization.lean`

- Line 20: `def intraStep : LazyZeckendorf → LazyZeckendorf`
- Line 33: `theorem intraStep_preserves_eval (z : LazyZeckendorf) :`
- Line 87: `def intraIter : Nat → LazyZeckendorf → LazyZeckendorf`
- Line 91: `theorem intraIter_preserves_eval (n : Nat) (z : LazyZeckendorf) :`
- Line 100: `def intraCore (z : LazyZeckendorf) : LazyZeckendorf :=`
- Line 105: `def intraNormalize (z : LazyZeckendorf) : ZeckPayload :=`
- Line 108: `theorem intraNormalize_sound (z : LazyZeckendorf) :`
- Line 116: `theorem intraNormalize_canonical (z : LazyZeckendorf) :`
- Line 122: `noncomputable def carryAt (i : Nat) (X : HybridNumber) : HybridNumber :=`
- Line 137: `def IsCanonical (X : HybridNumber) : Prop :=`
- Line 140: `theorem carryAt_preserves_eval (i : Nat) (X : HybridNumber) :`
- Line 227: `theorem carryAt_preserves_canonical (i : Nat) (X : HybridNumber) :`
- Line 250: `noncomputable def interCarryLoop : Nat → HybridNumber → HybridNumber`
- Line 254: `theorem interCarryLoop_preserves_eval (n : Nat) (X : HybridNumber) :`
- Line 267: `theorem interCarryLoop_preserves_canonical (n : Nat) (X : HybridNumber) :`
- Line 279: `theorem interCarryLoop_small (n : Nat) (X : HybridNumber) :`
- Line 299: `theorem carryAt_eq_self_of_small (i : Nat) (X : HybridNumber)`
- Line 342: `noncomputable def interCarry (X : HybridNumber) : HybridNumber :=`
- Line 345: `theorem interCarry_preserves_eval (X : HybridNumber) :`
- Line 349: `theorem interCarry_preserves_canonical (X : HybridNumber) :`
- Line 354: `theorem interCarry_idempotent_of_canonical (X : HybridNumber) (hX : IsCanonical X) :`
- Line 386: `noncomputable def normalizeIntra (X : LazyHybridNumber) : HybridNumber :=`
- Line 389: `theorem normalizeIntra_sound (X : LazyHybridNumber) :`
- Line 408: `theorem normalizeIntra_canonical (X : LazyHybridNumber) :`
- Line 414: `noncomputable def normalize (X : LazyHybridNumber) : HybridNumber :=`
- Line 417: `theorem normalize_sound (X : LazyHybridNumber) :`
- Line 422: `theorem normalize_canonical (X : LazyHybridNumber) :`
- Line 428: `theorem intraNormalize_terminates (z : LazyZeckendorf) :`
- Line 433: `theorem normalize_terminates (X : LazyHybridNumber) :`

## `HeytingLean/Bridge/Veselov/HybridZeckendorf/WeightSystem.lean`

- Line 13: `def weight : Nat → Nat`
- Line 25: `theorem weight_closed : ∀ i : Nat, weight (i + 1) = 1000 ^ (2 ^ i)`
- Line 37: `theorem weight_pos (i : Nat) : 0 < weight i := by`
- Line 45: `theorem weight_ge_two_of_pos : ∀ i : Nat, 0 < i → 2 ≤ weight i`
- Line 57: `theorem weight_lt_succ : ∀ i : Nat, weight i < weight (i + 1)`
- Line 72: `theorem weight_strict_mono : StrictMono weight :=`
- Line 75: `theorem weight_strict_mono' {i j : Nat} (h : i < j) : weight i < weight j :=`

## `HeytingLean/Bridge/Wolfram/CausalInvariance.lean`

- Line 14: `theorem ce1_confluentNF :`
- Line 20: `theorem ce1_not_causalInvariant :`
- Line 26: `theorem ce2_causalInvariant :`
- Line 32: `theorem ce2_not_confluentNF :`
- Line 38: `theorem confluence_causal_invariance_independent :`

## `HeytingLean/Core/Nucleus.lean`

- Line 26: `structure Nucleus (L : Type*) [SemilatticeInf L] [OrderBot L] where`
- Line 41: `def fixedPoints (N : Nucleus L) : Set L :=`
- Line 44: `theorem mem_fixedPoints (N : Nucleus L) (x : L) :`
- Line 49: `theorem R_mem_fixedPoints (N : Nucleus L) (a : L) :`
- Line 54: `theorem monotone (N : Nucleus L) : Monotone N.R := by`
- Line 63: `theorem fixedPoints_closed_inf (N : Nucleus L)`
- Line 70: `theorem fixed_eq_closed_inf (N : Nucleus L)`

## `HeytingLean/Eigen/NucleusReLU.lean`

- Line 24: `def relu (x : ℝ) : ℝ := max x 0`
- Line 26: `def reluNucleus (n : Nat) : Nucleus (Fin n → ℝ) where`
- Line 43: `theorem reluNucleus_idempotent (n : Nat) (v : Fin n → ℝ) : reluNucleus n (reluNucleus n v) = reluNucleus n v := by`
- Line 46: `theorem reluNucleus_le_apply (n : Nat) (v : Fin n → ℝ) : v ≤ reluNucleus n v := by`
- Line 49: `theorem reluNucleus_map_inf (n : Nat) (v w : Fin n → ℝ) :`

## `HeytingLean/Eigen/NucleusThreshold.lean`

- Line 21: `def threshold (x a : ℝ) : ℝ := max x a`
- Line 23: `def thresholdNucleus (n : Nat) (a : Fin n → ℝ) : Nucleus (Fin n → ℝ) where`
- Line 38: `theorem thresholdNucleus_idempotent (n : Nat) (a v : Fin n → ℝ) :`
- Line 42: `theorem thresholdNucleus_le_apply (n : Nat) (a v : Fin n → ℝ) : v ≤ thresholdNucleus n a v := by`
- Line 45: `theorem thresholdNucleus_map_inf (n : Nat) (a v w : Fin n → ℝ) :`
- Line 49: `theorem thresholdNucleus_fixed_iff (n : Nat) (a v : Fin n → ℝ) :`

## `HeytingLean/Eigen/SafEDMD.lean`

- Line 30: `def sqSum (v : Fin n → ℝ) : ℝ :=`
- Line 34: `def projectedGramDiag (samples : Fin m → Fin n → ℝ) (j : Fin n) : ℝ :=`
- Line 38: `theorem relu_idempotent (v : Fin n → ℝ) :`
- Line 43: `theorem relu_nonneg (v : Fin n → ℝ) (i : Fin n) :`
- Line 49: `theorem relu_component_le_abs (v : Fin n → ℝ) (i : Fin n) :`
- Line 55: `theorem relu_sq_le_sq (v : Fin n → ℝ) (i : Fin n) :`
- Line 64: `theorem relu_sqSum_le_sqSum (v : Fin n → ℝ) :`
- Line 70: `theorem relu_sqSum_nonneg (v : Fin n → ℝ) :`
- Line 76: `theorem relu_eq_of_nonneg (v : Fin n → ℝ) (h : ∀ i, 0 ≤ v i) :`
- Line 83: `theorem relu_map_inf (v w : Fin n → ℝ) :`
- Line 88: `theorem projectedGramDiag_nonneg (samples : Fin m → Fin n → ℝ) (j : Fin n) :`
- Line 94: `theorem projectedGramDiag_le (samples : Fin m → Fin n → ℝ) (j : Fin n) :`

## `HeytingLean/Epistemic/Occam.lean`

- Line 13: `def breathe (R : Reentry α) : ℕ → α → α`
- Line 34: `noncomputable def birth (R : Reentry α) (a : α) : ℕ :=`
- Line 38: `lemma birth_spec (R : Reentry α) (a : α) :`
- Line 44: `lemma birth_min (R : Reentry α) (a : α) {m : ℕ}`
- Line 50: `lemma birth_le_one (R : Reentry α) (a : α) : birth R a ≤ 1 := by`
- Line 60: `lemma birth_eq_zero_iff (R : Reentry α) (a : α) :`
- Line 88: `lemma fixed_of_birth_zero (R : Reentry α) {a : α}`
- Line 98: `def occamCandidates (R : Reentry α) (a : α) : Set α :=`
- Line 102: `lemma occamCandidate_le {R : Reentry α} {a u : α}`
- Line 107: `lemma occamCandidate_fixed {R : Reentry α} {a u : α}`
- Line 118: `noncomputable def occamBirth (R : Reentry α) (a : α) : ℕ :=`
- Line 122: `lemma occamBirth_spec (R : Reentry α) (a : α) :`
- Line 127: `lemma occamBirth_min (R : Reentry α) (a : α) {m : ℕ}`
- Line 133: `lemma occamBirth_zero (R : Reentry α) (a : α) :`
- Line 143: `def occamMinimal (R : Reentry α) (a : α) : Set α :=`
- Line 147: `lemma occamMinimal_eq_candidates (R : Reentry α) (a : α) :`
- Line 160: `lemma occamMinimal_subset (R : Reentry α) (a : α) :`
- Line 166: `lemma occamMinimal_nonempty (R : Reentry α) (a : α) :`
- Line 172: `noncomputable def occamCore (R : Reentry α) (a : α) : α :=`
- Line 176: `lemma occamCore_le (R : Reentry α) (a : α) :`
- Line 183: `lemma le_occamCore_of_minimal (R : Reentry α) {a u : α}`
- Line 190: `noncomputable def occam (R : Reentry α) (a : α) : α :=`
- Line 194: `lemma occam_le_reentry (R : Reentry α) (a : α) :`
- Line 199: `lemma occam_contains_minimal (R : Reentry α) {a u : α}`
- Line 207: `lemma occam_contains_candidate (R : Reentry α) {a u : α}`
- Line 218: `lemma occam_idempotent (R : Reentry α) (a : α) :`
- Line 223: `lemma occam_monotone (R : Reentry α) :`
- Line 247: `lemma occam_birth (R : Reentry α) (a : α) :`

## `HeytingLean/Generative/FourDBarrier.lean`

- Line 13: `structure is already a fixed point of the stabilization process. Therefore,`
- Line 52: `inductive EmergenceStatus`
- Line 65: `def emergenceStatus (level : ℕ) : EmergenceStatus :=`
- Line 69: `theorem level0_forced : emergenceStatus 0 = .forced := rfl`
- Line 70: `theorem level1_forced : emergenceStatus 1 = .forced := rfl`
- Line 73: `theorem level2_barrier : emergenceStatus 2 = .barrier := rfl`
- Line 76: `theorem barrier_from_level2 (k : ℕ) (hk : 2 ≤ k) :`
- Line 87: `theorem forced_spatial_dimensions :`
- Line 92: `theorem total_spatial_dimension :`
- Line 98: `theorem four_d_barrier_specific :`
- Line 108: `theorem space_time_asymmetry :`
- Line 127: `theorem dimensionality_is_three :`

## `HeytingLean/Generative/IntNucleusKit.lean`

- Line 16: `def ibreathe (R : IntReentry α) : ℕ → α → α`
- Line 33: `noncomputable def ibirth (R : IntReentry α) (a : α) : ℕ :=`
- Line 36: `lemma ibirth_spec (R : IntReentry α) (a : α) :`
- Line 41: `lemma ibirth_min (R : IntReentry α) (a : α) {m : ℕ}`
- Line 46: `lemma ibirth_le_one (R : IntReentry α) (a : α) : ibirth (R := R) a ≤ 1 := by`
- Line 68: `def ioccam (R : IntReentry α) (a : α) : α := R a`

## `HeytingLean/Generative/NoneistOscillation.lean`

- Line 40: `structure OscillationAxis where`
- Line 65: `def noneistAxis : OscillationAxis where`
- Line 78: `theorem oscillation_produces_plurality :`
- Line 85: `theorem oscillation_axis_opposite_phase (ax : OscillationAxis) :`
- Line 91: `theorem oscillation_axis_step_cycle (ax : OscillationAxis) :`
- Line 98: `theorem oscillation_axis_partition (ax : OscillationAxis) :`

## `HeytingLean/Generative/NucleusKit.lean`

- Line 35: `abbrev birth (R : Reentry α) := Epistemic.birth (R := R)`
- Line 36: `abbrev occam (R : Reentry α) := Epistemic.occam (R := R)`
- Line 39: `def synth (R : Reentry α) (T A : α) : α :=`
- Line 46: `lemma synth_least {R : Reentry α} {T A W : α}`

## `HeytingLean/Generative/PrimeStability/BornHeytingGap.lean`

- Line 14: `inductive ProjectionType`
- Line 19: `noncomputable def projectionClassification {α : Type*} (rc : RotationalClosure α) : ProjectionType :=`
- Line 22: `theorem identity_projects_boolean {α : Type*} (rc : RotationalClosure α)`
- Line 27: `theorem massive_projects_heyting {α : Type*} (rc : RotationalClosure α)`
- Line 33: `def measurementProjection (n : ℕ) (i : Fin n) (v : Fin n → ℝ) : Fin n → ℝ :=`
- Line 36: `noncomputable def survivingFraction {n : ℕ} (v : Fin n → ℝ) (i : Fin n)`
- Line 40: `theorem measurementProjection_apply_self {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :`
- Line 44: `theorem measurementProjection_apply_ne {n : ℕ} (v : Fin n → ℝ) {i j : Fin n}`
- Line 49: `theorem measurementProjection_sqSum {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :`
- Line 55: `theorem survivingFraction_nonneg {n : ℕ} (v : Fin n → ℝ) (i : Fin n)`
- Line 61: `theorem born_weight_eq_surviving_fraction {n : ℕ} (ψ : TauWavefunction n)`
- Line 67: `def reluWavefunction {n : ℕ} (v : Fin n → ℝ) : TauWavefunction n where`
- Line 71: `theorem relu_gap_matches_born_structure {n : ℕ} (v : Fin n → ℝ)`

## `HeytingLean/Generative/PrimeStability.lean`


## `HeytingLean/Generative/PrimeStability/LeptonMassConjectures.lean`

- Line 13: `noncomputable def m_electron : ℝ := 0.51099895069`
- Line 14: `noncomputable def m_muon : ℝ := 105.6583755`
- Line 15: `noncomputable def m_tau : ℝ := 1776.93`
- Line 17: `noncomputable def koideQ (m₁ m₂ m₃ : ℝ) : ℝ :=`
- Line 20: `noncomputable def signedKoideQ (r₁ r₂ r₃ : ℝ) : ℝ :=`
- Line 23: `noncomputable def brannenRoot (μ δ : ℝ) (n : Fin 3) : ℝ :=`
- Line 26: `noncomputable def brannenMass (μ δ : ℝ) (n : Fin 3) : ℝ :=`
- Line 29: `theorem koideQ_bounds {m₁ m₂ m₃ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) (h₃ : 0 < m₃) :`
- Line 64: `theorem cos_two_pi_div_three :`
- Line 69: `theorem sin_two_pi_div_three :`
- Line 74: `theorem cos_four_pi_div_three :`
- Line 79: `theorem sin_four_pi_div_three :`
- Line 85: `theorem cos_cycle_sum (δ : ℝ) :`
- Line 91: `theorem cos_cycle_sq_sum (δ : ℝ) :`
- Line 102: `theorem brannen_root_sum (μ δ : ℝ) :`
- Line 122: `theorem brannen_root_sq_sum (μ δ : ℝ) :`
- Line 161: `theorem brannen_gives_signed_koide_exact (μ δ : ℝ) (hμ : 0 < μ) :`
- Line 172: `theorem brannen_gives_koide_exact (μ δ : ℝ) (hμ : 0 < μ)`

## `HeytingLean/Generative/PrimeStability/MagmaticPrimeFixed.lean`

- Line 36: `theorem familyOf_magmatic (x : Magma A) :`
- Line 46: `structure MagmaticRotationalClosure (N : MagmaticNucleus A) where`
- Line 61: `theorem separated_subfamily_exists [SeparationPresentation A]`
- Line 69: `theorem bridge_prime_to_fixed {N : MagmaticNucleus A}`
- Line 76: `theorem bridge_composite_to_gap {N : MagmaticNucleus A}`
- Line 83: `theorem bridge_irreducible_gap_zero {N : MagmaticNucleus A}`
- Line 90: `theorem bridge_composite_gap_nonzero {N : MagmaticNucleus A}`
- Line 97: `theorem bridge_inseparable_family {N : MagmaticNucleus A}`

## `HeytingLean/Generative/PrimeStability/PrimePeriodicity.lean`

- Line 12: `theorem decomposable_has_proper_divisor {α : Type*} (rc : RotationalClosure α)`
- Line 19: `theorem composite_iff_decomposable {α : Type*} (rc : RotationalClosure α) :`
- Line 33: `theorem irreducible_iff_not_decomposable {α : Type*} (rc : RotationalClosure α)`
- Line 47: `theorem stable_iff_prime_period {α : Type*} (rc : RotationalClosure α)`
- Line 53: `theorem stable_massive_has_prime_period {α : Type*} (rc : RotationalClosure α)`
- Line 59: `theorem two_is_terminal_prime :`

## `HeytingLean/Generative/PrimeStability/RotationalClosure.lean`

- Line 21: `structure RotationalClosure (α : Type*) where`
- Line 32: `noncomputable def period {α : Type*} (rc : RotationalClosure α) : ℕ :=`
- Line 36: `theorem periodic {α : Type*} (rc : RotationalClosure α) :`
- Line 41: `theorem period_pos {α : Type*} (rc : RotationalClosure α) :`
- Line 46: `theorem one_le_period {α : Type*} (rc : RotationalClosure α) :`
- Line 53: `def IrreducibleClosure {α : Type*} (rc : RotationalClosure α) : Prop :=`
- Line 57: `def CompositeClosure {α : Type*} (rc : RotationalClosure α) : Prop :=`
- Line 61: `def IdentityClosure {α : Type*} (rc : RotationalClosure α) : Prop :=`
- Line 65: `def hasTrappedAsymmetry {α : Type*} (rc : RotationalClosure α) : Prop :=`
- Line 69: `structure SubClosure {α : Type*} (rc : RotationalClosure α) where`
- Line 80: `def Decomposable {α : Type*} (rc : RotationalClosure α) : Prop :=`
- Line 83: `theorem identityClosure_iff_period_one {α : Type*} (rc : RotationalClosure α) :`
- Line 87: `theorem trappedAsymmetry_iff_period_gt_one {α : Type*} (rc : RotationalClosure α) :`

## `HeytingLean/Generative/PrimeStability/StabilityHierarchy.lean`

- Line 21: `structure UDPState (α : Type*) where`
- Line 24: `structure PhotonState (α : Type*) extends UDPState α where`
- Line 27: `structure ElectronState (α : Type*) extends UDPState α where`
- Line 30: `def photonClosure : RotationalClosure PUnit where`
- Line 37: `def noneistClosure : RotationalClosure noneistAxis.Carrier where`
- Line 44: `theorem photon_closure_period_one :`
- Line 48: `theorem noneist_axis_period_two :`
- Line 60: `def canonicalPhoton : PhotonState PUnit where`
- Line 64: `def canonicalElectron : ElectronState noneistAxis.Carrier where`
- Line 69: `theorem photon_massless {α : Type*} (p : PhotonState α) :`
- Line 73: `theorem electron_massive {α : Type*} (e : ElectronState α) :`
- Line 77: `theorem electron_stable {α : Type*} (e : ElectronState α) :`
- Line 81: `theorem electron_is_terminal {α : Type*} (rc : RotationalClosure α)`
- Line 86: `theorem stability_hierarchy {α : Type*} (rc : RotationalClosure α)`

## `HeytingLean/Generative/PropagationSpeed.lean`

- Line 43: `noncomputable def phasePropagationFactor : ℝ := Real.pi * goldenRatio`
- Line 46: `theorem phasePropagationFactor_pos : 0 < phasePropagationFactor :=`
- Line 50: `theorem phasePropagationFactor_eq : phasePropagationFactor = Real.pi * goldenRatio := rfl`
- Line 53: `theorem phasePropagationFactor_gt_pi : Real.pi < phasePropagationFactor := by`
- Line 60: `theorem phasePropagationFactor_lt_two_pi : phasePropagationFactor < 2 * Real.pi := by`
- Line 67: `theorem golden_ratio_irrational : Irrational goldenRatio :=`
- Line 90: `structure PlanckScale where`
- Line 105: `noncomputable def speedOfCausality (ps : PlanckScale) : ℝ :=`
- Line 109: `theorem speedOfCausality_pos (ps : PlanckScale) : 0 < speedOfCausality ps := by`
- Line 119: `theorem no_three_fifths_factor :`

## `HeytingLean/Generative/ReEntryPlane.lean`

- Line 59: `theorem golden_ratio_reentry_equation :`
- Line 70: `theorem reentry_equation_iff_quadratic (r : ℝ) (hr : r ≠ 0) :`
- Line 91: `theorem reentry_ratio_unique (r : ℝ) (hr : 0 < r) (h : r = 1 + 1 / r) :`
- Line 111: `theorem reentry_ratio_unique_iff (r : ℝ) (hr : 0 < r) :`
- Line 123: `theorem reentry_quadratic_discriminant :`
- Line 134: `theorem golden_ratio_selfsimilar_partition :`
- Line 155: `structure ReEntryTriangle where`
- Line 166: `noncomputable def noneistReEntryTriangle : ReEntryTriangle where`
- Line 175: `theorem reentry_triangle_selfsimilar (t : ReEntryTriangle) :`
- Line 183: `theorem reentry_triangle_uniquely_determined (r : ℝ) (hr : 0 < r)`
- Line 191: `theorem reentry_dimension_count :`

## `HeytingLean/Generative/SpatialClosure.lean`

- Line 44: `structure EmergenceLevel where`
- Line 53: `def level0 : EmergenceLevel where`
- Line 59: `def level1 : EmergenceLevel where`
- Line 65: `def level2 : EmergenceLevel where`
- Line 73: `theorem frame_directions_eq_dim (l : EmergenceLevel) :`
- Line 81: `theorem axis_determined_at_each_level (l : EmergenceLevel) :`
- Line 91: `def residualFreedom (l : EmergenceLevel) : ℕ :=`
- Line 97: `theorem residual_freedom_zero (l : EmergenceLevel) :`
- Line 108: `def stabilizationProductive (l : EmergenceLevel) : Prop :=`
- Line 113: `theorem stabilization_always_productive (l : EmergenceLevel) :`
- Line 119: `def nextLevel (l : EmergenceLevel) : EmergenceLevel where`
- Line 125: `theorem level0_to_level1 : nextLevel level0 = level1 := by`
- Line 129: `theorem level1_to_level2 : nextLevel level1 = level2 := by`
- Line 135: `theorem full_frame_at_each_level (l : EmergenceLevel) :`
- Line 147: `theorem three_dimensions_from_two_stabilizations :`
- Line 152: `structure SpatialFrame where`
- Line 161: `theorem spatial_frame_golden (sf : SpatialFrame) :`
- Line 167: `theorem spatial_frame_level : level2.dim = 3 := rfl`

## `HeytingLean/Generative/SpinorBridge/ClebschGordanCoupling.lean`

- Line 9: `theorem clebsch_gordan_dimension :`
- Line 14: `structure CouplingChannel where`
- Line 19: `def singlet : CouplingChannel where`
- Line 24: `def triplet : CouplingChannel where`
- Line 30: `def supportsPreferredDirection (c : CouplingChannel) : Prop :=`
- Line 33: `theorem singlet_has_no_preferred_direction :`
- Line 37: `theorem triplet_has_preferred_direction :`
- Line 44: `theorem reentry_triangle_has_positive_aspect_and_canonical_triplet`
- Line 51: `structure TrivalentVertex where`
- Line 59: `def fundamentalVertex : TrivalentVertex where`
- Line 67: `theorem fundamental_vertex_admissible :`
- Line 75: `def reentryChannel : CouplingChannel :=`

## `HeytingLean/Generative/SpinorBridge/ComplexificationBarrier.lean`

- Line 9: `inductive GeneratorFlavor`
- Line 15: `abbrev SL2CGenerator := SU2Generator × GeneratorFlavor`
- Line 17: `theorem generatorFlavor_count :`
- Line 22: `def complexifiedGeneratorMatrix : SL2CGenerator → Mat2`
- Line 26: `theorem sl2c_generator_count :`
- Line 30: `theorem complexification_doubles_generators :`
- Line 35: `structure GroupExtension where`
- Line 42: `def su2_to_sl2c : GroupExtension where`
- Line 50: `theorem complexification_is_barrier :`
- Line 54: `theorem time_is_complexification_not_dimension :`
- Line 59: `theorem barrier_is_complexification_choice :`

## `HeytingLean/Generative/SpinorBridge/DimensionalityFromSU2.lean`

- Line 10: `def generatorIndex : SU2Generator ≃ Fin 3 where`
- Line 22: `theorem generatorIndex_bijective :`
- Line 26: `theorem generator_count_via_equiv :`
- Line 31: `theorem three_axes_from_three_generators :`
- Line 40: `theorem spatial_dimension_eq_su2_generator_count :`
- Line 45: `theorem emergence_generator_alignment :`

## `HeytingLean/Generative/SpinorBridge.lean`


## `HeytingLean/Generative/SpinorBridge/NucleusPenroseBridge.lean`

- Line 12: `structure PenroseCorrespondence where`
- Line 21: `def penroseCorrespondence : PenroseCorrespondence where`
- Line 26: `theorem non_boolean_is_aperiodic`
- Line 32: `theorem spinor_penrose_bridge_summary`

## `HeytingLean/Generative/SpinorBridge/OscillatorSpinorEquiv.lean`

- Line 12: `abbrev OscillationSupport (ax : OscillationAxis) : Type :=`
- Line 16: `def stepOnSupport (ax : OscillationAxis) (x : OscillationSupport ax) :`
- Line 33: `theorem step_state₁ (ax : OscillationAxis) :`
- Line 37: `theorem step_state₂ (ax : OscillationAxis) :`
- Line 42: `def oscillationToFin (ax : OscillationAxis) (x : OscillationSupport ax) : Fin 2 := by`
- Line 47: `def finToOscillation (ax : OscillationAxis) : Fin 2 → OscillationSupport ax`
- Line 52: `def oscillationStates (ax : OscillationAxis) : OscillationSupport ax ≃ Fin 2 where`
- Line 82: `theorem step_is_spin_flip (ax : OscillationAxis) (x : OscillationSupport ax) :`
- Line 112: `theorem involutivity_is_double_cover (ax : OscillationAxis) (x : OscillationSupport ax) :`
- Line 138: `theorem obs_is_spin_measurement (ax : OscillationAxis) :`
- Line 145: `theorem oscillation_is_minimal_spinor (ax : OscillationAxis) :`

## `HeytingLean/Generative/SpinorBridge/SU2Core.lean`

- Line 13: `abbrev Mat2 := HeytingLean.Quantum.Contextuality.Mat2`
- Line 16: `def pauliX : Mat2 :=`
- Line 20: `def pauliY : Mat2 :=`
- Line 24: `def pauliZ : Mat2 :=`
- Line 27: `theorem pauliX_trace : Matrix.trace pauliX = 0 := by`
- Line 30: `theorem pauliY_trace : Matrix.trace pauliY = 0 := by`
- Line 33: `theorem pauliZ_trace : Matrix.trace pauliZ = 0 := by`
- Line 36: `theorem pauliX_hermitian : pauliX.conjTranspose = pauliX := by`
- Line 41: `theorem pauliY_hermitian : pauliY.conjTranspose = pauliY := by`
- Line 46: `theorem pauliZ_hermitian : pauliZ.conjTranspose = pauliZ := by`
- Line 51: `theorem pauliX_sq : pauliX * pauliX = 1 := by`
- Line 54: `theorem pauliY_sq : pauliY * pauliY = 1 := by`
- Line 57: `theorem pauliZ_sq : pauliZ * pauliZ = 1 := by`
- Line 60: `theorem pauliX_mul_pauliY :`
- Line 67: `theorem pauliY_mul_pauliX :`
- Line 74: `theorem pauliY_mul_pauliZ :`
- Line 81: `theorem pauliZ_mul_pauliY :`
- Line 88: `theorem pauliZ_mul_pauliX :`
- Line 92: `theorem pauliX_mul_pauliZ :`
- Line 96: `theorem pauli_commutator_XY :`
- Line 104: `theorem pauli_commutator_YZ :`
- Line 112: `theorem pauli_commutator_ZX :`
- Line 120: `inductive SU2Generator`
- Line 127: `def generatorMatrix : SU2Generator → Mat2`
- Line 132: `theorem pauliX_ne_pauliY : pauliX ≠ pauliY := by`
- Line 138: `theorem pauliX_ne_pauliZ : pauliX ≠ pauliZ := by`
- Line 143: `theorem pauliY_ne_pauliZ : pauliY ≠ pauliZ := by`
- Line 148: `theorem generatorMatrix_injective : Function.Injective generatorMatrix := by`
- Line 164: `theorem su2_generator_count : Fintype.card SU2Generator = 3 := by`

## `HeytingLean/Generative/SurrealNucleusKit.lean`

- Line 28: `abbrev Carrier := Set SurrealCore.PreGame`
- Line 33: `def breathe : ℕ → Carrier → Carrier :=`
- Line 47: `noncomputable def birth (S : Carrier) : ℕ :=`
- Line 51: `def occam (S : Carrier) : Carrier :=`

## `HeytingLean/Generative/UDPGeometry.lean`

- Line 42: `structure UDPGeometry where`
- Line 51: `noncomputable def udpFromFrame (sf : SpatialFrame) : UDPGeometry where`
- Line 57: `theorem udp_lobe_selfsimilar (udp : UDPGeometry) :`
- Line 64: `theorem udp_aspect_unique (r : ℝ) (hr : 0 < r) (h : r = 1 + 1 / r) :`
- Line 69: `theorem udp_two_lobes (udp : UDPGeometry) :`
- Line 75: `theorem udp_counter_rotation_involutive (udp : UDPGeometry) (x : udp.frame.reentry₁.axis.Carrier) :`
- Line 81: `theorem udp_phase_coupling (udp : UDPGeometry) (x : udp.frame.reentry₁.axis.Carrier) :`
- Line 88: `theorem udp_three_dimensional : level2.dim = 3 := rfl`
- Line 97: `theorem udp_is_derived :`

## `HeytingLean/Generative/UDTPostulates.lean`

- Line 19: `structure x → 1 + 1/x — a re-entry relation.`
- Line 70: `theorem udp_existence_from_noneism :`
- Line 95: `theorem pm_characterization_from_heyting :`
- Line 121: `theorem tau_quantization_from_lattice`
- Line 141: `theorem mark_unmark_polarity_bridge :`

## `HeytingLean/Generative/WolframBridge/FixedPointPredicate.lean`

- Line 12: `def NucleusInvariant (N : Core.Nucleus L) : Prop :=`
- Line 15: `theorem nucleusInvariant_iff_all_fixed (N : Core.Nucleus L) :`
- Line 20: `theorem hossenfelder_isBoolean_iff_nucleusInvariant`
- Line 25: `theorem not_nucleusInvariant_iff_exists_moved`
- Line 30: `theorem boundaryGap_eq_empty_of_fixed`
- Line 36: `theorem boundaryGap_nonempty_of_moved`

## `HeytingLean/Generative/WolframBridge/GapTransport.lean`

- Line 10: `theorem hossenfelder_not_nucleusInvariant`
- Line 19: `theorem graft_isBoolean_iff_nucleusInvariant {n : Nat} (z : Int) :`
- Line 24: `theorem graft_not_nucleusInvariant {n : Nat} (z : Int) :`

## `HeytingLean/Generative/WolframBridge.lean`


## `HeytingLean/Generative/WolframBridge/MasterBridge.lean`

- Line 9: `structure WolframHeytingBridgeWitness where`
- Line 15: `theorem hossenfelder_and_graft_share_fixed_point_predicate`
- Line 24: `theorem wolfram_side_uses_explicit_bridge`
- Line 30: `theorem wolfram_hossenfelder_grafting_share_fixed_point_obstruction`

## `HeytingLean/Generative/WolframBridge/WolframCorrespondence.lean`

- Line 13: `structure WolframFixedPointBridge`
- Line 27: `theorem ce1_not_nucleusInvariant`
- Line 37: `theorem ce2_nucleusInvariant`
- Line 43: `theorem ce1_has_moved_point`
- Line 48: `theorem wolfram_fixed_point_separation`

## `HeytingLean/HossenfelderNoGo/Basic.lean`


## `HeytingLean/HossenfelderNoGo/Bridge/NucleusConnection.lean`

- Line 13: `def asBoundaryNucleus (sys : BetaSystem) : BoundaryNucleus CouplingRegion :=`
- Line 23: `theorem as_boundary_non_boolean (sys : BetaSystem)`
- Line 28: `theorem eichhorn_topYukawa_screened :`
- Line 42: `theorem eichhorn_nucleus_not_boolean :`
- Line 60: `theorem as_boundary_gap_nonempty (sys : BetaSystem) (hscreen : PortalScreeningHypothesis sys) :`

## `HeytingLean/HossenfelderNoGo/Bridge/PrenucleusConnection.lean`

- Line 10: `def completeBoundaryPrenucleus`
- Line 17: `theorem completed_prenucleus_non_boolean`

## `HeytingLean/HossenfelderNoGo/Bridge/RatchetCorrelation.lean`

- Line 12: `theorem uv_boundary_non_boolean (sys : BetaSystem)`

## `HeytingLean/HossenfelderNoGo/HeytingBoundary/BandConstraint.lean`

- Line 6: `structure GapBand (L : Type*) [SemilatticeInf L] [OrderBot L] [OrderTop L] where`
- Line 13: `def GapBand.fromFamily`

## `HeytingLean/HossenfelderNoGo/HeytingBoundary/BoundaryNucleus.lean`

- Line 10: `abbrev BoundaryNucleus (L : Type*) [SemilatticeInf L] [OrderBot L] :=`
- Line 14: `def isBoolean {L : Type*} [SemilatticeInf L] [OrderBot L] (N : BoundaryNucleus L) : Prop :=`
- Line 19: `def boundaryGap {L : Type*} [SemilatticeInf L] [OrderBot L]`
- Line 23: `theorem mem_boundaryGap_iff {L : Type*} [SemilatticeInf L] [OrderBot L]`
- Line 31: `def BooleanBoundaryBridge`

## `HeytingLean/HossenfelderNoGo/HeytingBoundary/DynamicGap.lean`

- Line 6: `structure NucleusFamily (L : Type*) [SemilatticeInf L] [OrderBot L] where`
- Line 10: `theorem observer_dependent_gap`

## `HeytingLean/HossenfelderNoGo/HeytingBoundary/GapNonZero.lean`

- Line 9: `theorem boundary_necessarily_non_boolean`
- Line 18: `theorem gap_nonzero_at_boundary`
- Line 36: `theorem boundary_has_nontrivial_fixed_points`

## `HeytingLean/HossenfelderNoGo/Networks/LocallyFinite.lean`

- Line 8: `structure SpacetimeNetwork where`
- Line 14: `def neighborDisplacement (N : SpacetimeNetwork) (u v : N.Node) : SpacetimeDisplacement :=`
- Line 19: `structure LocallyFinite (N : SpacetimeNetwork) : Prop where`
- Line 27: `def BoostInvariant (N : SpacetimeNetwork) : Prop :=`
- Line 33: `def TranslationInvariant (N : SpacetimeNetwork) : Prop :=`
- Line 40: `def UniformOnHyperbolae (N : SpacetimeNetwork) : Prop :=`
- Line 46: `def SupportsNonzeroHyperbola (N : SpacetimeNetwork) : Prop :=`
- Line 50: `def PoincareInvariant (N : SpacetimeNetwork) : Prop :=`

## `HeytingLean/HossenfelderNoGo/Networks/NoGoTheorem.lean`

- Line 11: `theorem no_poincare_invariant_locally_finite_network :`

## `HeytingLean/HossenfelderNoGo/Spacetime/LorentzGroup.lean`

- Line 9: `structure LorentzBoost where`
- Line 13: `noncomputable def LorentzBoost.apply (b : LorentzBoost) (d : SpacetimeDisplacement) :`
- Line 34: `theorem hyperbola_infinite_length (α : ℝ) (hα : α ≠ 0) :`

## `HeytingLean/HossenfelderNoGo/Spacetime/MinkowskiInterval.lean`

- Line 6: `structure SpacetimeDisplacement where`
- Line 11: `def minkowskiInterval (d : SpacetimeDisplacement) : ℝ :=`
- Line 15: `def hyperbolaAt (α : ℝ) : Set SpacetimeDisplacement :=`
- Line 18: `theorem minkowskiInterval_neg_time (d : SpacetimeDisplacement) :`
- Line 22: `theorem minkowskiInterval_neg_space (d : SpacetimeDisplacement) :`

## `HeytingLean/Integration/MagmaAsymptotic/IrreducibleCouplings.lean`

- Line 11: `def heytingGap_AS (sys : BetaSystem) (S : CouplingRegion) : Set CouplingPoint :=`
- Line 14: `theorem gap_zero_iff_reducible (sys : BetaSystem) (S : CouplingRegion) :`
- Line 35: `theorem portalPositive_has_nonzero_gap (sys : BetaSystem)`
- Line 45: `theorem gap_analogy_statement (sys : BetaSystem) (S : CouplingRegion) :`

## `HeytingLean/Integration/MagmaAsymptotic/NucleusPartition.lean`

- Line 12: `def UVReducible (sys : BetaSystem) (S : CouplingRegion) : Prop :=`
- Line 16: `def UVIrreducible (sys : BetaSystem) (S : CouplingRegion) : Prop :=`
- Line 19: `theorem as_nucleus_partitions (sys : BetaSystem) (S : CouplingRegion) :`
- Line 25: `theorem uvSafe_is_reducible (sys : BetaSystem)`
- Line 32: `def portalTestPoint : CouplingPoint where`
- Line 43: `theorem portalTestPoint_mem_portalPositiveRegion :`
- Line 48: `theorem portalTestPoint_not_uvSafe (sys : BetaSystem)`
- Line 55: `theorem outside_uvSafe_may_be_irreducible (sys : BetaSystem)`

## `HeytingLean/Integration/MagmaAsymptotic/NucleusPreserved.lean`

- Line 7: `def NucleusPreserved {L : Type*} [SemilatticeInf L] [OrderBot L]`
- Line 11: `theorem nucleusPreserved_iff_carrier_closed {L : Type*} [SemilatticeInf L] [OrderBot L]`
- Line 16: `theorem fixed_preserves_all {L : Type*} [SemilatticeInf L] [OrderBot L]`

## `HeytingLean/LoF/HeytingCore.lean`

- Line 48: `instance instHeytingOmega : HeytingAlgebra (R.Omega) := inferInstance`
- Line 51: `lemma heyting_adjunction (a b c : R.Omega) :`
- Line 56: `lemma residuation (a b c : R.Omega) :`
- Line 109: `lemma double_neg (a : R.Omega) :`
- Line 126: `lemma inf_himp_le (a b : R.Omega) : a ⊓ (a ⇨ b) ≤ b := by`
- Line 144: `def booleanEquiv (h : ∀ a : α, R a = a) : R.Omega ≃ α where`
- Line 165: `lemma boolean_limit (h : ∀ a : α, R a = a) (a : α) :`

## `HeytingLean/LoF/Instances.lean`


## `HeytingLean/LoF/IntReentry.lean`

- Line 13: `structure IntNucleus (α : Type u) [PrimaryAlgebra α] where`
- Line 33: `structure IntReentry (α : Type u) [PrimaryAlgebra α] where`
- Line 40: `instance : CoeFun (IntReentry α) (fun _ => α → α) where`
- Line 51: `lemma map_inf (R : IntReentry α) (a b : α) : R (a ⊓ b) = R a ⊓ R b :=`
- Line 55: `abbrev Omega (R : IntReentry α) : Type u := {a : α // R a = a}`
- Line 61: `def mk (a : α) (h : R a = a) : R.Omega := ⟨a, h⟩`

## `HeytingLean/LoF/Nucleus.lean`

- Line 12: `structure Reentry (α : Type u) [PrimaryAlgebra α] where`
- Line 41: `instance : CoeFun (Reentry α) (fun _ => α → α) where`
- Line 59: `lemma map_sup (R : Reentry α) (a b : α) :`
- Line 66: `lemma map_sup_le (R : Reentry α) (a b : α) :`
- Line 72: `lemma map_himp_le (R : Reentry α) (a b : α) :`
- Line 109: `abbrev Omega (R : Reentry α) : Type u := R.nucleus.toSublocale`
- Line 119: `lemma primordial_le_of_fixed (R : Reentry α) {x : α}`
- Line 129: `def mk (a : α) (h : R a = a) :`
- Line 148: `def process (R : Reentry α) : R.Omega :=`
- Line 152: `def counterProcess (R : Reentry α) : R.Omega :=`
- Line 162: `lemma process_inf_counter (R : Reentry α) :`
- Line 171: `lemma process_pos (R : Reentry α) : ⊥ < ((R.process : R.Omega) : α) := by`
- Line 176: `lemma process_in_support (R : Reentry α) :`
- Line 182: `lemma counter_pos (R : Reentry α) : ⊥ < ((R.counterProcess : R.Omega) : α) := by`
- Line 187: `def complementaryPair (R : Reentry α) : R.Omega × R.Omega :=`
- Line 202: `def boundaryCandidates (R : Reentry α) : Set (R.Omega) :=`
- Line 210: `lemma process_mem_boundaryCandidates (R : Reentry α) :`
- Line 221: `noncomputable def eulerBoundary (R : Reentry α) : R.Omega :=`
- Line 224: `lemma eulerBoundary_def (R : Reentry α) :`
- Line 228: `lemma eulerBoundary_le_of_candidate (R : Reentry α) {x : R.Omega}`
- Line 233: `lemma le_of_lower_bound (R : Reentry α) {a : R.Omega}`
- Line 242: `lemma eulerBoundary_le_process (R : Reentry α) :`
- Line 248: `lemma process_le_of_candidate (R : Reentry α) {x : R.Omega}`
- Line 259: `lemma process_le_eulerBoundary (R : Reentry α) :`
- Line 276: `lemma eulerBoundary_pos (R : Reentry α) :`
- Line 281: `lemma eulerBoundary_mem_candidates (R : Reentry α) :`
- Line 303: `lemma eulerBoundary_isLeast (R : Reentry α) :`
- Line 310: `lemma eulerBoundary_in_support (R : Reentry α) :`
- Line 322: `lemma eulerBoundary_minimal_nontrivial (R : Reentry α) :`
- Line 347: `lemma eulerBoundary_le_counter (R : Reentry α)`
- Line 366: `lemma eulerBoundary_complementary (R : Reentry α) :`
- Line 378: `lemma eulerBoundary_unique_minimal (R : Reentry α) (x : R.Omega)`
- Line 407: `lemma eulerBoundary_unique_minimal_support (R : Reentry α) (x : R.Omega)`

## `HeytingLean/LoF/PrimaryAlgebra.lean`

- Line 10: `class PrimaryAlgebra (α : Type u) extends Order.Frame α`

## `HeytingLean/Logic/Dialectic.lean`

- Line 13: `def synth (R : Reentry α) (T A : α) : α :=`
- Line 20: `lemma le_synth_left (R : Reentry α) (T A : α) :`
- Line 27: `lemma le_synth_right (R : Reentry α) (T A : α) :`
- Line 34: `lemma synth_le {R : Reentry α} {T A W : α}`
- Line 48: `lemma pole_left_to_synthesis (R : Reentry α) (T A : α) :`
- Line 52: `lemma pole_right_to_synthesis (R : Reentry α) (T A : α) :`
- Line 56: `lemma synthesis_least {R : Reentry α} {T A W : α}`
- Line 64: `def synthOmega (R : Reentry α) (T A : R.Omega) : R.Omega :=`
- Line 73: `lemma synthOmega_le {R : Reentry α} {T A W : R.Omega}`
- Line 99: `def oscillationOmega (R : Reentry α) : R.Omega :=`
- Line 108: `lemma le_synthOmega_left (R : Reentry α) (T A : R.Omega) :`
- Line 113: `lemma le_synthOmega_right (R : Reentry α) (T A : R.Omega) :`
- Line 118: `lemma eulerBoundary_le_oscillation (R : Reentry α) :`

## `HeytingLean/Magma/Atoms.lean`

- Line 10: `class MagmaticAtoms (A : Type*) extends PartialOrder A where`
- Line 17: `def predecessors (a : A) : Set A := { b : A | b ≤ a }`
- Line 20: `def Incomparable (a₀ a₁ : A) : Prop := ¬ a₀ ≤ a₁ ∧ ¬ a₁ ≤ a₀`
- Line 31: `noncomputable def descendingChain (a : A) : ℕ → A`
- Line 35: `theorem descendingChain_step (a : A) (n : ℕ) :`
- Line 39: `theorem descendingChain_not_back (a : A) (n : ℕ) :`
- Line 43: `theorem descendingChain_le (a : A) :`
- Line 51: `theorem descendingChain_injective (a : A) :`
- Line 68: `theorem descendingChain_mem_predecessors (a : A) (n : ℕ) :`
- Line 72: `theorem predecessors_infinite (a : A) : Set.Infinite (predecessors a) := by`
- Line 82: `theorem predecessors_eq_iff (a b : A) :`

## `HeytingLean/Magma/Bridge/ComputationalIrreducibility.lean`

- Line 12: `def ComputationallyIrreducible (N : MagmaticNucleus A) (x : Magma A) : Prop :=`
- Line 15: `theorem irreducible_nonempty (N : MagmaticNucleus A)`
- Line 19: `theorem irreducible_has_nonzero_gap (N : MagmaticNucleus A) {x : Magma A}`

## `HeytingLean/Magma/Bridge/HeytingGapMeasure.lean`

- Line 10: `def heyting_gap (N : MagmaticNucleus A) (x : Magma A) : Set (Magma A) :=`
- Line 13: `theorem gap_zero_iff_fixed (N : MagmaticNucleus A) (x : Magma A) :`
- Line 34: `def intrinsically_irreducible (x : Magma A) : Prop :=`

## `HeytingLean/Magma/Bridge/NucleusProjection.lean`

- Line 13: `def familyOf (x : Magma A) : Set (Magma A) := { y | y ≤ x }`
- Line 15: `def ResolvesCollateralAt (a₀ a₁ : A) (h : Incomparable a₀ a₁)`
- Line 19: `structure MagmaticNucleus (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]`
- Line 30: `def omega_R (N : MagmaticNucleus A) : Set (Magma A) :=`
- Line 33: `def irreducible_complement (N : MagmaticNucleus A) : Set (Magma A) :=`
- Line 36: `theorem fixed_core_magmatic (N : MagmaticNucleus A) (x : Magma A) :`

## `HeytingLean/Magma/Function.lean`

- Line 9: `structure MagmaticSemiFunction (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A)`
- Line 14: `structure MagmaticFunction (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A)`
- Line 19: `theorem disjoint_domain_implies_function (a₀ a₁ : A) (h : Incomparable a₀ a₁)`

## `HeytingLean/Magma/Hierarchy.lean`

- Line 12: `class MagmaticUniverse (A : Type*) [MagmaticAtoms A] where`
- Line 38: `abbrev Magma (A : Type*) [MagmaticAtoms A] [u : MagmaticUniverse A] := u.Magma`
- Line 48: `theorem self_mem_pr (x : Magma A) : x ∈ u.pr x := by`
- Line 51: `theorem exists_strict_smaller (x : Magma A) : ∃ y : Magma A, y < x :=`
- Line 54: `abbrev hierarchyLevel (x : Magma A) : Nat := u.level x`
- Line 56: `theorem hierarchy_cumulative {x y : Magma A} (hxy : x ≤ y) :`
- Line 60: `theorem strict_predecessor_drops_level {x y : Magma A} (hyx : y < x) :`
- Line 64: `theorem hierarchy_level_positive (x : Magma A) : 1 ≤ hierarchyLevel x :=`

## `HeytingLean/Magma/IntendedCollateral.lean`

- Line 8: `structure GeneratedMagma (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A] where`
- Line 13: `def intended (g : GeneratedMagma A) : Set (Magma A) := g.generators`
- Line 15: `def collateral (g : GeneratedMagma A) : Set (Magma A) :=`
- Line 18: `theorem intended_subset (g : GeneratedMagma A) {x : Magma A} (hx : x ∈ intended g) :`
- Line 22: `theorem collateral_subset (g : GeneratedMagma A) {x : Magma A} (hx : x ∈ collateral g) :`
- Line 26: `theorem collateral_nonempty (g : GeneratedMagma A)`

## `HeytingLean/Magma/LowerTopology.lean`

- Line 9: `structure LowerOpen (A : Type*) [MagmaticAtoms A] where`
- Line 14: `instance : SetLike (LowerOpen A) A where`
- Line 27: `instance : PartialOrder (LowerOpen A) where`
- Line 36: `instance : Max (LowerOpen A) where`
- Line 48: `theorem mem_sup {x y : LowerOpen A} {a : A} :`
- Line 53: `def principal (a : A) : LowerOpen A where`
- Line 64: `theorem principal_mono {a b : A} (h : a ≤ b) :`
- Line 69: `theorem principal_le_iff {a : A} {m : LowerOpen A} :`
- Line 77: `theorem principal_subset_iff {a b : A} :`
- Line 85: `theorem lowerOpen_infinite (m : LowerOpen A) : Set.Infinite (m : Set A) := by`
- Line 92: `theorem no_minimal_magma (m : LowerOpen A) :`

## `HeytingLean/Magma/OrderedPair.lean`

- Line 7: `class PairEncoding (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A] where`
- Line 28: `def pr2 (x : Magma A) : Magma A := pr (pr x)`
- Line 30: `def magmatic_pair (a₀ a₁ : A) (_h : Incomparable a₀ a₁) (x y : Magma A) : Magma A :=`
- Line 33: `theorem collateral_subpairs (a₀ a₁ : A) (h : Incomparable a₀ a₁)`
- Line 40: `theorem pair_injective (a₀ a₁ : A) (h : Incomparable a₀ a₁)`

## `HeytingLean/Magma/PredecessorMap.lean`

- Line 7: `abbrev pr (x : Magma A) : Magma A := u.pr x`
- Line 9: `theorem pr_eq_powerset_inter (x y : Magma A) :`
- Line 13: `theorem pr_injective : Function.Injective (pr (A := A)) := by`
- Line 23: `theorem pr_order_embedding (x y : Magma A) :`
- Line 34: `theorem pr_level_independent (x : Magma A) (_n _m : Nat) :`

## `HeytingLean/Magma/Product.lean`

- Line 7: `class ProductEncoding (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A] [PairEncoding A] where`
- Line 16: `def magmatic_product (a₀ a₁ : A) (_h : Incomparable a₀ a₁) (x y : Magma A) : Magma A :=`
- Line 19: `def weak_product (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A) : Set (Magma A) :=`
- Line 22: `theorem product_same_pairs (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A)`

## `HeytingLean/Magma/Relation.lean`

- Line 7: `structure MagmaticRelation (a₀ a₁ : A) (h : Incomparable a₀ a₁) (x y : Magma A) where`
- Line 12: `def MagmaticRelation.dom {a₀ a₁ : A} {h : Incomparable a₀ a₁} {x y : Magma A}`
- Line 16: `def MagmaticRelation.ran {a₀ a₁ : A} {h : Incomparable a₀ a₁} {x y : Magma A}`
- Line 20: `theorem MagmaticRelation.dom_subset {a₀ a₁ : A} {h : Incomparable a₀ a₁}`
- Line 26: `theorem MagmaticRelation.ran_subset {a₀ a₁ : A} {h : Incomparable a₀ a₁}`

## `HeytingLean/Magma/Separation/MagmaticClass.lean`

- Line 9: `def MagmaticClass (X : Set (Magma A)) : Prop :=`
- Line 12: `def ScaleInvariant (φ : Magma A → Prop) : Prop :=`
- Line 15: `theorem scaleInvariant_iff_magmatic (φ : Magma A → Prop) :`
- Line 19: `class SeparationPresentation (A : Type*) [MagmaticAtoms A] [MagmaticUniverse A]`

## `HeytingLean/Magma/Separation/MagmaticCompletion.lean`

- Line 9: `def magmatic_completion (φ : Magma A → Prop) : Magma A → Prop :=`
- Line 12: `theorem completion_is_magmatic (φ : Magma A → Prop) :`
- Line 18: `theorem completion_class_eq (φ : Magma A → Prop) :`

## `HeytingLean/Magma/Separation/MSS.lean`

- Line 10: `theorem magmatic_separation_scheme`

## `HeytingLean/Metrics/Curvature.lean`

- Line 15: `abbrev FlowPoint := Array Float`
- Line 19: `def l2Dist (a b : FlowPoint) : Float := Id.run do`
- Line 29: `def mengerCurvature (a b c : FlowPoint) : Float :=`
- Line 42: `def finiteDiff (traj : Array FlowPoint) : Array FlowPoint := Id.run do`
- Line 67: `def perimeter2D (poly : Array FlowPoint) : Float := Id.run do`
- Line 78: `def area2D (poly : Array FlowPoint) : Float := Id.run do`

## `HeytingLean/MirandaDynamics/External/Interfaces.lean`

- Line 34: `structure TKFTConstruction (α : Type u) (β : Type v) : Type (max u v) where`
- Line 39: `noncomputable def reachingFunction {α : Type u} {β : Type v} (h : TKFTConstruction α β) :`
- Line 43: `theorem reachingFunction_spec {α : Type u} {β : Type v} (h : TKFTConstruction α β) (a : α) (b : β) :`
- Line 48: `def reachingImage {α : Type u} {β : Type v} (h : TKFTConstruction α β) (a : α) : Type v :=`
- Line 55: `structure HaltingReduction {β : Type v} [Primcodable β] (n : ℕ) (P : β → Prop) : Type (max v 1) where`
- Line 58: `theorem not_computable_of_haltingReduction {β : Type v} [Primcodable β] {P : β → Prop} (n : ℕ)`

## `HeytingLean/MirandaDynamics/FixedPoint/PeriodicNucleus.lean`

- Line 37: `def unionNucleus (U : Set α) : Nucleus (Set α) where`
- Line 66: `theorem isFixedPoint_unionNucleus_iff (U S : Set α) :`
- Line 90: `abbrev FlowTraj := Bridges.FlowTraj`
- Line 93: `def periodicNucleus (posTol dirCosTol : Float) : Nucleus (Set FlowTraj) :=`
- Line 96: `theorem periodicNucleus_eq_flowNucleusOsc (posTol dirCosTol : Float) :`

## `HeytingLean/MirandaDynamics/Fluids/ContactGeometry.lean`

- Line 23: `structure ContactFormData (M : Type u) where`
- Line 32: `def ContactFormData.toDynamics {M : Type u} (C : ContactFormData M) :`
- Line 40: `structure BeltramiFieldData (M : Type u) where`
- Line 53: `def BeltramiFieldData.toDynamics {M : Type u} (B : BeltramiFieldData M) :`

## `HeytingLean/MirandaDynamics/Fluids/CosymplecticGeometry.lean`

- Line 18: `structure CosymplecticData (M : Type u) where`
- Line 28: `structure HarmonicFieldData (M : Type u) where`
- Line 35: `structure CosymplecticReebIsHarmonic (M : Type u) where`

## `HeytingLean/MirandaDynamics/Fluids/EtnyreGhrist.lean`

- Line 19: `structure EtnyreGhristCorrespondence (M : Type u) where`
- Line 31: `theorem periodic_reeb_of_beltrami_periodic {M : Type u}`
- Line 43: `structure SharedOrbitWitness (M : Type u) where`

## `HeytingLean/MirandaDynamics/Fluids/HarmonicNS.lean`

- Line 20: `structure NavierStokesSolution (M : Type u) where`
- Line 28: `structure HarmonicViscosityInvariance (M : Type u) where`
- Line 40: `structure CosymplecticEulerConstruction (M : Type u) where`

## `HeytingLean/MirandaDynamics/Fluids/TuringComplete.lean`

- Line 25: `structure FluidTuringConstruction (M : Type u) [Primcodable M] where`
- Line 39: `theorem fluid_trajectory_undecidable {M : Type u} [Primcodable M]`
- Line 46: `structure PeriodicityDetection (M : Type u) [Primcodable M] where`
- Line 53: `def trajectoryReducesToPeriodicity {M : Type u} [Primcodable M]`
- Line 64: `theorem fluid_periodicity_undecidable {M : Type u} [Primcodable M]`
- Line 75: `def fluidPeriodicNucleus {M : Type u} (periodic : M → Prop) :`
- Line 81: `theorem fluidPeriodicNucleus_fixed_iff {M : Type u} (periodic : M → Prop) (S : Set M) :`

## `HeytingLean/MirandaDynamics/TKFT/Reaching.lean`

- Line 26: `structure ReachingRel (α : Type u) (β : Type v) : Type (max u v) where`
- Line 44: `def id (α : Type u) : ReachingRel α α :=`
- Line 48: `def comp (R : ReachingRel α β) (S : ReachingRel β γ) : ReachingRel α γ :=`
- Line 53: `theorem id_left (R : ReachingRel α β) : comp (id α) R = R := by`
- Line 61: `theorem id_right (R : ReachingRel α β) : comp R (id β) = R := by`
- Line 69: `theorem assoc (R : ReachingRel α β) (S : ReachingRel β γ) (T : ReachingRel γ δ) :`
- Line 81: `def Functional (R : ReachingRel α β) : Prop :=`
- Line 85: `def Image (R : ReachingRel α β) (a : α) : Type v :=`
- Line 100: `noncomputable def toPart (R : ReachingRel α β) (_hFun : R.Functional) : α → Part β := by`
- Line 105: `theorem toPart_spec {R : ReachingRel α β} (hFun : R.Functional) (a : α) (b : β) :`

## `HeytingLean/MirandaDynamics/Undecidability/Transfers.lean`

- Line 29: `structure ManyOne {α : Type u} {β : Type v} [Primcodable α] [Primcodable β]`
- Line 41: `theorem computable_of_reduces (hred : ManyOne (p := p) (q := q)) (hq : ComputablePred q) :`
- Line 56: `theorem not_computable_of_reduces (hred : ManyOne (p := p) (q := q)) (hp : ¬ComputablePred p) :`
- Line 68: `def Halts (n : ℕ) : Code → Prop :=`
- Line 71: `theorem not_computable (n : ℕ) : ¬ComputablePred (Halts n) :=`
- Line 76: `theorem not_computable_of_halting_reduces`

## `HeytingLean/Noneism/Bridges/LoFPrimordial.lean`

- Line 39: `abbrev TwoPoint : Type := Bool`
- Line 40: `abbrev TwoPred : Type := Set TwoPoint`
- Line 43: `instance : LoF.PrimaryAlgebra TwoPred := by`
- Line 50: `def idNucleus : Nucleus TwoPred := (⊥ : Nucleus TwoPred)`
- Line 53: `def sing (b : Bool) : TwoPred := {b}`
- Line 55: `theorem sing_true_nonbot : (⊥ : TwoPred) < sing true := by`
- Line 65: `theorem sing_false_nonbot : (⊥ : TwoPred) < sing false := by`
- Line 74: `theorem sing_orthogonal : sing true ⊓ sing false = (⊥ : TwoPred) := by`
- Line 83: `def twoPointReentry : LoF.Reentry TwoPred where`
- Line 145: `instance : HeytingAlgebra (twoPointReentry.Omega) := by`
- Line 153: `noncomputable def omegaEquivTwoPred : twoPointReentry.Omega ≃ TwoPred :=`
- Line 175: `theorem sing_true_ne_false : sing true ≠ sing false := by`
- Line 181: `theorem twoPoint_process_ne_counter :`
- Line 201: `theorem twoPoint_eulerBoundary_minimal_nontrivial :`
- Line 214: `def Polarized : Type :=`
- Line 219: `def boolToPolarized : Bool → Polarized`
- Line 224: `noncomputable def polarizedToBool (w : Polarized) : Bool := by`
- Line 255: `def polarizedEquivBool : Polarized ≃ Bool where`
- Line 266: `def pull (S : TwoPred) : Set Noneism.Nothing := fun x => obs x ∈ S`
- Line 269: `def pullHeytingHom : HeytingHom TwoPred (Set Noneism.Nothing) where`
- Line 300: `def omegaPull (w : twoPointReentry.Omega) : Set Noneism.Nothing :=`
- Line 303: `theorem pull_sing_true_eq_mark : pull (sing true) = {x | Mark x} := by`
- Line 309: `theorem pull_sing_false_eq_unmark : pull (sing false) = {x | Unmark x} := by`

## `HeytingLean/Noneism/Foundation.lean`

- Line 25: `abbrev Nothing : Type := Bool`
- Line 28: `instance instPrimordialTensionNothing : PrimordialTension (Nothing := Nothing) := by`
- Line 41: `abbrev seed : Nothing := PrimordialTension.seed (Nothing := Nothing)`
- Line 42: `abbrev step : Nothing → Nothing := PrimordialTension.step (Nothing := Nothing)`
- Line 43: `abbrev obs : Nothing → Bool := PrimordialTension.obs (Nothing := Nothing)`
- Line 45: `abbrev Mark : Nothing → Prop := PrimordialTension.Mark (Nothing := Nothing)`
- Line 46: `abbrev Unmark : Nothing → Prop := PrimordialTension.Unmark (Nothing := Nothing)`
- Line 48: `theorem seed_ne_step_seed : seed ≠ step seed :=`
- Line 51: `theorem mark_step_iff_unmark (x : Nothing) : Mark (step x) ↔ Unmark x :=`
- Line 54: `theorem unmark_step_iff_mark (x : Nothing) : Unmark (step x) ↔ Mark x :=`
- Line 57: `theorem mark_or_unmark (x : Nothing) : Mark x ∨ Unmark x :=`

## `HeytingLean/Noneism/PrimordialTension.lean`

- Line 35: `structure PrimordialEngine (Nothing : Type u) where`
- Line 47: `class PrimordialTension (Nothing : Type u) where`
- Line 55: `def E : PrimordialEngine Nothing := (inferInstance : PrimordialTension Nothing).engine`
- Line 58: `def step : Nothing → Nothing := (E (Nothing := Nothing)).step`
- Line 61: `def obs : Nothing → Bool := (E (Nothing := Nothing)).obs`
- Line 64: `def seed : Nothing := (E (Nothing := Nothing)).seed`
- Line 79: `theorem seed_ne_step_seed : seed (Nothing := Nothing) ≠ step (Nothing := Nothing) (seed (Nothing := Nothing)) := by`
- Line 95: `theorem exists_two_distinct : ∃ x y : Nothing, x ≠ y := by`
- Line 106: `def Mark (x : Nothing) : Prop := obs (Nothing := Nothing) x = true`
- Line 107: `def Unmark (x : Nothing) : Prop := obs (Nothing := Nothing) x = false`
- Line 109: `theorem mark_or_unmark (x : Nothing) : Mark (Nothing := Nothing) x ∨ Unmark (Nothing := Nothing) x := by`
- Line 113: `theorem mark_iff_not_unmark (x : Nothing) :`
- Line 117: `theorem unmark_iff_not_mark (x : Nothing) :`
- Line 121: `theorem mark_step_iff_unmark (x : Nothing) :`
- Line 127: `theorem unmark_step_iff_mark (x : Nothing) :`
- Line 132: `theorem mark_and_unmark_false (x : Nothing) :`
- Line 140: `theorem oscillatory_interpretation_bundle :`
- Line 160: `instance instPrimordialTensionBool : PrimordialTension Bool where`

## `HeytingLean/NucleusGrafting/BoundaryConnection.lean`

- Line 12: `def graftBoundaryNucleus {n : Nat} (z : Int) :`
- Line 29: `theorem graftBoundaryNucleus_not_boolean {n : Nat} (z : Int) :`
- Line 36: `theorem boundaryGap_bot_nonempty {n : Nat} (z : Int) :`
- Line 48: `def bitwidthFamily {n : Nat} (zCoarse zFine : Int) (hLevels : zCoarse ≤ zFine) :`
- Line 72: `theorem bitwidthFamily_gap_positive {n : Nat}`
- Line 82: `def measuredGapBand {n : Nat} (zCoarse zFine : Int) (hLevels : zCoarse ≤ zFine) :`
- Line 90: `def observedBoundaryGap (g : GapDecomposition) : ℝ := g.total`
- Line 92: `theorem observedBoundaryGap_nonneg (g : GapDecomposition) :`
- Line 95: `structure DiscreteGateMeasurement where`
- Line 106: `def gateHasNontrivialBoundary (m : DiscreteGateMeasurement) : Prop :=`
- Line 109: `theorem fixedFraction_le_one (m : DiscreteGateMeasurement) :`
- Line 112: `theorem gate_boundary_nontrivial_of_positive_gap`

## `HeytingLean/NucleusGrafting/Certificate.lean`

- Line 7: `structure VerificationLayerEvidence where`
- Line 13: `structure NucleusGraftingCertificate (n : Nat) where`
- Line 22: `theorem certificate_gap_nonzero {n : Nat} (c : NucleusGraftingCertificate n) :`
- Line 25: `theorem certificate_records_nonnegative_quantization {n : Nat}`
- Line 29: `theorem certificate_has_gap_witness {n : Nat}`

## `HeytingLean/NucleusGrafting/DiscreteLattice.lean`

- Line 9: `def qRelu (z q : Int) : Int := max q z`
- Line 11: `theorem qRelu_idempotent (z q : Int) :`
- Line 16: `theorem qRelu_extensive (z q : Int) :`
- Line 21: `theorem qRelu_meet_preserving (z a b : Int) :`
- Line 25: `theorem qRelu_fixed_iff (z q : Int) :`
- Line 35: `structure ProductWitness where`
- Line 41: `def canonicalProductWitness : ProductWitness where`
- Line 57: `theorem productWitness_exists : ∃ _ : ProductWitness, True := by`

## `HeytingLean/NucleusGrafting/Types.lean`

- Line 7: `structure LayerQuantParams where`
- Line 15: `theorem latticeSpacing_pos (p : LayerQuantParams) : 0 < p.latticeSpacing := by`
- Line 19: `structure Phase1Summary where`
- Line 27: `def acceptableAccuracyDrop (s : Phase1Summary) : Prop :=`
- Line 30: `theorem acceptableAccuracyDrop_of_lt`
- Line 35: `abbrev ActivationVector (n : Nat) := Fin n → Int`
- Line 37: `def activationFixedSet {n : Nat} (z : Int) : Set (ActivationVector n) :=`
- Line 40: `theorem activationFixedSet_nonempty {n : Nat} (z : Int) :`
- Line 46: `theorem activationFixedSet_ne_empty {n : Nat} (z : Int) :`
- Line 53: `theorem activationFixedSet_mono {n : Nat} {z₁ z₂ : Int}`
- Line 59: `structure GapDecomposition where`
- Line 70: `def componentUpperBound (g : GapDecomposition) : ℝ :=`
- Line 73: `theorem componentUpperBound_eq_total (g : GapDecomposition) :`
- Line 77: `theorem componentUpperBound_nonneg (g : GapDecomposition) :`

## `HeytingLean/Numbers/SurrealCore.lean`

- Line 24: `structure PreGame where`
- Line 32: `def maxBirth (xs : List PreGame) : Nat :=`
- Line 36: `def build (L R : List PreGame) : PreGame :=`
- Line 46: `def nullCut : PreGame :=`
- Line 49: `def birthday (g : PreGame) : Nat := g.birth`
- Line 51: `def truncate (θ : Nat) (g : PreGame) : Option PreGame :=`
- Line 55: `noncomputable def leAt : Nat → PreGame → PreGame → Prop`
- Line 61: `noncomputable def le (x y : PreGame) : Prop :=`
- Line 65: `noncomputable def lt (x y : PreGame) : Prop := ¬ le y x`
- Line 68: `noncomputable def legal (g : PreGame) : Prop :=`
- Line 72: `def canonicalize (g : PreGame) : PreGame := g`
- Line 75: `def close (g : PreGame) : PreGame := canonicalize g`
- Line 77: `theorem canonicalize_idem (g : PreGame) :`
- Line 197: `noncomputable def neg : PreGame → PreGame`
- Line 208: `noncomputable def add : PreGame → PreGame → PreGame`
- Line 236: `def isNullCut : PreGame → Bool`
- Line 245: `noncomputable def mul : PreGame → PreGame → PreGame := by`
- Line 342: `def addApprox (x y : PreGame) : PreGame :=`
- Line 349: `def negApprox (x : PreGame) : PreGame :=`
- Line 376: `def mulApprox (x y : PreGame) : PreGame :=`

## `HeytingLean/Numbers/Surreal/Nucleus.lean`

- Line 30: `def canonImage (S : Set PreGame) : Set PreGame :=`
- Line 35: `def J (S : Set PreGame) : Set PreGame :=`
- Line 41: `lemma mono_J {S T : Set PreGame} (hST : S ⊆ T) : J S ⊆ J T := by`
- Line 49: `lemma idem_J (S : Set PreGame) : J (J S) = J S := by`
- Line 79: `def C : Set PreGame := { g | SurrealCore.legal g ∧ SurrealCore.canonicalize g = g }`
- Line 82: `def I (S : Set PreGame) : Set PreGame := S ∩ C`
- Line 87: `lemma mono_I {S T : Set PreGame} (hST : S ⊆ T) : I S ⊆ I T := by`
- Line 107: `def dualClosure (S : Set PreGame) : Set PreGame :=`
- Line 122: `theorem ontology_closure_interior_duality_20260219 (S : Set PreGame) :`
- Line 129: `instance : HeytingLean.LoF.PrimaryAlgebra (Set SurrealCore.PreGame) :=`
- Line 133: `def intReentry : HeytingLean.LoF.IntReentry (Set SurrealCore.PreGame) where`

## `HeytingLean/Numbers/Surreal/ReentryAdapter.lean`

- Line 27: `abbrev IntReentryS :=`
- Line 31: `def surrealIntReentry : IntReentryS := intReentry`

## `HeytingLean/OTM/DynamicsComputation/DynamicalSystem.lean`

- Line 10: `structure DynamicalSystem (X : Type u) where`
- Line 20: `def reaches (x y : X) : Prop :=`
- Line 24: `def reachabilityClosure (U : Set X) : Set X :=`
- Line 28: `def equilibriumSet : Set X :=`
- Line 31: `theorem mem_reachabilityClosure_iff (U : Set X) (x : X) :`
- Line 34: `theorem reachabilityClosure_mono {U V : Set X} (hUV : U ⊆ V) :`
- Line 40: `theorem subset_reachabilityClosure (U : Set X) :`
- Line 46: `theorem reachabilityClosure_idempotent (U : Set X) :`
- Line 56: `theorem reachabilityClosure_inter_subset (U V : Set X) :`
- Line 62: `theorem reaches_refl (x : X) : D.reaches x x := by`
- Line 66: `theorem reaches_trans {x y z : X} (hxy : D.reaches x y) (hyz : D.reaches y z) :`
- Line 76: `theorem equilibrium_mem_reachabilityClosure_of_mem (U : Set X) {x : X}`
- Line 82: `theorem flow_preserves_equilibrium {x : X} (hx : x ∈ D.equilibriumSet) (n : Nat) :`

## `HeytingLean/Quantum/Contextuality/MerminPeresRealization.lean`

- Line 32: `abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ`
- Line 33: `abbrev Mat4 := Matrix (Fin 4) (Fin 4) ℂ`
- Line 34: `abbrev Mat2x2 := Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`
- Line 38: `def σx : Mat2 :=`
- Line 44: `def σy : Mat2 :=`
- Line 50: `def σz : Mat2 :=`
- Line 56: `lemma σx_sq : σx * σx = (1 : Mat2) := by`
- Line 62: `lemma σy_sq : σy * σy = (1 : Mat2) := by`
- Line 68: `lemma σz_sq : σz * σz = (1 : Mat2) := by`
- Line 74: `lemma σz_mul_σx : σz * σx = (Complex.I : ℂ) • σy := by`
- Line 80: `lemma σx_mul_σz : σx * σz = (-Complex.I : ℂ) • σy := by`
- Line 108: `def P11 : Mat2x2 := Pauli.σz ⊗ₖ (1 : Mat2)`
- Line 109: `def P12 : Mat2x2 := (1 : Mat2) ⊗ₖ Pauli.σz`
- Line 110: `def P13 : Mat2x2 := Pauli.σz ⊗ₖ Pauli.σz`
- Line 112: `def P21 : Mat2x2 := (1 : Mat2) ⊗ₖ Pauli.σx`
- Line 113: `def P22 : Mat2x2 := Pauli.σx ⊗ₖ (1 : Mat2)`
- Line 114: `def P23 : Mat2x2 := Pauli.σx ⊗ₖ Pauli.σx`
- Line 116: `def P31 : Mat2x2 := Pauli.σz ⊗ₖ Pauli.σx`
- Line 117: `def P32 : Mat2x2 := Pauli.σx ⊗ₖ Pauli.σz`
- Line 118: `def P33 : Mat2x2 := Pauli.σy ⊗ₖ Pauli.σy`
- Line 121: `def O11 : Mat4 := toMat4 P11`
- Line 122: `def O12 : Mat4 := toMat4 P12`
- Line 123: `def O13 : Mat4 := toMat4 P13`
- Line 125: `def O21 : Mat4 := toMat4 P21`
- Line 126: `def O22 : Mat4 := toMat4 P22`
- Line 127: `def O23 : Mat4 := toMat4 P23`
- Line 129: `def O31 : Mat4 := toMat4 P31`
- Line 130: `def O32 : Mat4 := toMat4 P32`
- Line 131: `def O33 : Mat4 := toMat4 P33`
- Line 133: `theorem row1_prodP : P11 * P12 * P13 = (1 : Mat2x2) := by`
- Line 147: `theorem row2_prodP : P21 * P22 * P23 = (1 : Mat2x2) := by`
- Line 161: `theorem row3_prodP : P31 * P32 * P33 = (1 : Mat2x2) := by`
- Line 192: `theorem col1_prodP : P11 * P21 * P31 = (1 : Mat2x2) := by`
- Line 206: `theorem col2_prodP : P12 * P22 * P32 = (1 : Mat2x2) := by`
- Line 220: `theorem col3_prodP : P13 * P23 * P33 = (-1 : Mat2x2) := by`
- Line 248: `theorem row1_prod : O11 * O12 * O13 = (1 : Mat4) := by`
- Line 253: `theorem row2_prod : O21 * O22 * O23 = (1 : Mat4) := by`
- Line 258: `theorem row3_prod : O31 * O32 * O33 = (1 : Mat4) := by`
- Line 263: `theorem col1_prod : O11 * O21 * O31 = (1 : Mat4) := by`
- Line 268: `theorem col2_prod : O12 * O22 * O32 = (1 : Mat4) := by`
- Line 273: `theorem col3_prod : O13 * O23 * O33 = (-1 : Mat4) := by`

## `HeytingLean/Rel/Basic.lean`

- Line 19: `def HRel (α : Type u₁) (β : Type v₁) : Type (max u₁ v₁) :=`
- Line 25: `def restrict {α : Type u₁} {β : Type v₁} {α' : Type u₂} {β' : Type v₂}`
- Line 34: `theorem restrict_id {α : Type u₁} {β : Type v₁} (R : HRel α β) :`
- Line 38: `theorem restrict_comp {α : Type u₁} {β : Type v₁} {α' : Type u₂} {β' : Type v₂}`
- Line 45: `def unit (α : Type u₁) : HRel α α :=`
- Line 51: `def homProarrow {C : Type u₁} {D₀ : Type u₂} {D₁ : Type u₃} (f : D₀ → C) (g : D₁ → C) :`
- Line 56: `def tensor {α : Type u₁} {β : Type v₁} {γ : Type u₂} (P : HRel α β) (Q : HRel β γ) : HRel α γ :=`
- Line 60: `def top {α : Type u₁} {β : Type v₁} : HRel α β :=`
- Line 64: `def prod {α : Type u₁} {β : Type v₁} (P Q : HRel α β) : HRel α β :=`
- Line 68: `def covHom {A : Type u₁} {B : Type v₁} {C : Type u₂} (P : HRel A B) (Q : HRel C B) : HRel C A :=`
- Line 72: `def contraHom {A : Type u₁} {B : Type v₁} {C : Type u₂} (P : HRel A B) (Q : HRel A C) : HRel B C :=`
- Line 81: `theorem tensor_restrict_strict {A : Type u₁} {B : Type v₁} {C : Type u₂}`
- Line 87: `theorem covHom_restrict_strict {A : Type u₁} {B : Type v₁} {C : Type u₂}`
- Line 93: `theorem contraHom_restrict_strict {A : Type u₁} {B : Type v₁} {C : Type u₂}`
- Line 99: `theorem top_restrict_strict {A : Type u₁} {B : Type v₁} {A' : Type u₂} {B' : Type v₂}`
- Line 104: `theorem prod_restrict_strict {A : Type u₁} {B : Type v₁} {A' : Type u₂} {B' : Type v₂}`
- Line 109: `theorem unit_restrict_strict {C : Type u₁} {D₀ : Type u₂} {D₁ : Type u₃}`

## `HeytingLean/Renormalization/DimensionalRatchet.lean`

- Line 20: `structure RatchetScale where`
- Line 27: `inductive LogicType where`
- Line 34: `structure DimensionalRatchet (L : Type*) [SemilatticeInf L] [OrderBot L] where`
- Line 44: `def nucleusAt {L : Type*} [SemilatticeInf L] [OrderBot L]`
- Line 52: `def logicAtScale (s : RatchetScale) : LogicType :=`

## `HeytingLean/WPP/MultiwayRel.lean`

- Line 33: `structure WppRel (State : Type u) where`
- Line 41: `abbrev StepStar : State → State → Prop :=`
- Line 45: `def cone (s : State) : Set State := fun t => StepStar (R := R) s t`
- Line 48: `def JR (U : Set State) : Set State := fun s => ∀ t, StepStar (R := R) s t → U t`
- Line 54: `lemma mono : Monotone (JR (R := R)) := by`
- Line 58: `lemma contractive (U : Set State) : JR (R := R) U ⊆ U := by`
- Line 62: `lemma idem (U : Set State) : JR (R := R) (JR (R := R) U) = JR (R := R) U := by`
- Line 70: `lemma inf (U V : Set State) :`
- Line 92: `def unreachableFrom : Set State :=`
- Line 97: `def reachabilityNucleus : Nucleus (Set State) where`

## `HeytingLean/WPP/Wolfram/CausalGraphGC.lean`

- Line 33: `lemma fold_or_eq_true_of_mem_true :`
- Line 56: `def Created (e : sys.Event) (x : Expr V) : Prop :=`
- Line 60: `def observableB (e : sys.Event) (t : HGraph V) : Bool :=`
- Line 66: `def Observable (e : sys.Event) (t : HGraph V) : Prop :=`
- Line 72: `def observableIdxs (es : List sys.Event) (t : HGraph V) : List (Fin es.length) :=`
- Line 76: `def causalGraphGCOf (es : List sys.Event) (t : HGraph V) : CausalGraph :=`
- Line 92: `def GCausalInvariant : Prop :=`

## `HeytingLean/WPP/Wolfram/CausalGraph.lean`

- Line 23: `structure CausalGraph where`
- Line 30: `def Iso (g₁ g₂ : CausalGraph) : Prop :=`
- Line 33: `lemma Iso.n_eq {g₁ g₂ : CausalGraph} : Iso g₁ g₂ → g₁.n = g₂.n := by`
- Line 39: `lemma not_Iso_of_n_ne {g₁ g₂ : CausalGraph} (h : g₁.n ≠ g₂.n) : ¬ Iso g₁ g₂ := by`
- Line 56: `def causalGraphOf (es : List sys.Event) : CausalGraph where`

## `HeytingLean/WPP/Wolfram/ConfluenceCausalInvarianceGC.lean`

- Line 56: `theorem causalGraphGC_iso_short_long :`
- Line 204: `theorem causalInvariantGC : Properties.GCausalInvariant (sys := sys) := by`

## `HeytingLean/WPP/Wolfram/ConfluenceCausalInvariance.lean`

- Line 33: `def ConfluentNF : Prop :=`
- Line 40: `def CausalInvariant : Prop :=`
- Line 57: `def sigma2 (a b : V) : Fin 2 → V :=`
- Line 69: `lemma inj_sigma2 {a b : V} (h : a ≠ b) : Function.Injective (sigma2 (V := V) a b) := by`
- Line 95: `abbrev P : Type := Fin 2`
- Line 96: `abbrev V : Type := Fin 3`
- Line 98: `def rule : Rule P where`
- Line 102: `def init : HGraph V :=`
- Line 105: `def sys : System V P where`
- Line 111: `def e12 : sys.Event :=`
- Line 115: `def e13 : sys.Event :=`
- Line 119: `def e23 : sys.Event :=`
- Line 123: `def s0 : HGraph V := sys.init`
- Line 124: `def s1 : HGraph V := ([[1], [0, 1], [1, 2], [0, 2]] : List (Expr V))`
- Line 125: `def s2 : HGraph V := ([[2], [0, 1], [1, 2], [0, 2]] : List (Expr V))`
- Line 138: `lemma e12_app_s0 : e12.Applicable (sys := sys) s0 := by`
- Line 149: `lemma e13_app_s0 : e13.Applicable (sys := sys) s0 := by`
- Line 157: `lemma e23_app_s1 : e23.Applicable (sys := sys) s1 := by`
- Line 165: `lemma e12_apply_s0 : e12.apply (sys := sys) s0 = s1 := by`
- Line 168: `lemma e13_apply_s0 : e13.apply (sys := sys) s0 = s2 := by`
- Line 171: `lemma e23_apply_s1 : e23.apply (sys := sys) s1 = s2 := by`
- Line 190: `lemma s2_normalForm : sys.NormalForm s2 := by`
- Line 222: `lemma s0_not_normalForm : ¬ sys.NormalForm s0 := by`
- Line 226: `lemma s1_not_normalForm : ¬ sys.NormalForm s1 := by`
- Line 366: `theorem terminatingFrom_init : System.TerminatingFrom (sys := sys) s0 := by`
- Line 420: `theorem confluentNF : Properties.ConfluentNF (sys := sys) := by`
- Line 429: `theorem not_causalInvariant : ¬ Properties.CausalInvariant (sys := sys) := by`
- Line 459: `abbrev P : Type := Fin 2`
- Line 460: `abbrev V : Type := Fin 2`
- Line 462: `def rule : Rule P where`
- Line 466: `def init : HGraph V :=`
- Line 469: `def sys : System V P where`
- Line 475: `def e_id : sys.Event :=`
- Line 479: `def e_swap : sys.Event :=`
- Line 483: `def s0 : HGraph V := sys.init`
- Line 484: `def nf1 : HGraph V := ([[0], [0]] : List (Expr V))`
- Line 485: `def nf2 : HGraph V := ([[0], [1]] : List (Expr V))`
- Line 543: `lemma e_id_app : e_id.Applicable (sys := sys) s0 := by`
- Line 559: `lemma e_swap_app : e_swap.Applicable (sys := sys) s0 := by`
- Line 573: `lemma e_id_apply : e_id.apply (sys := sys) s0 = nf1 := by`
- Line 576: `lemma e_swap_apply : e_swap.apply (sys := sys) s0 = nf2 := by`
- Line 593: `lemma nf1_normalForm : sys.NormalForm nf1 := by`
- Line 602: `lemma nf2_normalForm : sys.NormalForm nf2 := by`
- Line 662: `theorem terminatingFrom_init : System.TerminatingFrom (sys := sys) s0 := by`
- Line 690: `theorem causalInvariant : Properties.CausalInvariant (sys := sys) := by`
- Line 709: `theorem not_confluentNF : ¬ Properties.ConfluentNF (sys := sys) := by`
- Line 790: `theorem confluence_causal_invariance_independent :`

## `HeytingLean/WPP/Wolfram/ConfluenceTheory.lean`

- Line 33: `def Step (s t : HGraph V) : Prop :=`
- Line 37: `abbrev StepStar : HGraph V → HGraph V → Prop :=`
- Line 41: `def NormalFormStep (s : HGraph V) : Prop :=`
- Line 44: `lemma normalForm_iff_normalFormStep (s : HGraph V) :`
- Line 56: `theorem Evolves.toStepStar {s : HGraph V} {es : List sys.Event} {t : HGraph V} :`
- Line 65: `theorem Evolves.append {s : HGraph V} {es₁ es₂ : List sys.Event} {m t : HGraph V} :`
- Line 74: `theorem StepStar.exists_evolves {s t : HGraph V} :`
- Line 95: `def Joinable (b c : HGraph V) : Prop :=`
- Line 99: `def Confluent : Prop :=`
- Line 103: `def SemiConfluent : Prop :=`
- Line 107: `theorem semiConfluent_confluent (h : SemiConfluent (sys := sys)) : Confluent (sys := sys) := by`
- Line 115: `def BoundedFrom (s : HGraph V) (n : Nat) : Prop :=`
- Line 119: `def TerminatingFrom (s : HGraph V) : Prop :=`

## `HeytingLean/WPP/Wolfram/Hypergraph.lean`

- Line 24: `abbrev Expr (V : Type u) : Type u := List V`
- Line 27: `abbrev HGraph (V : Type u) : Type u := Multiset (Expr V)`
- Line 76: `def Iso {V : Type u} (g₁ g₂ : HGraph V) : Prop :=`
- Line 111: `def vertsStep [DecidableEq V] : Finset V → Expr V → Finset V :=`
- Line 114: `instance instRightCommutative_vertsStep [DecidableEq V] :`
- Line 121: `def verts [DecidableEq V] (g : HGraph V) : Finset V :=`
- Line 150: `lemma mem_verts_of_mem {v : V} [DecidableEq V] {e : Expr V} {g : HGraph V}`

## `HeytingLean/WPP/Wolfram/MultiwayRel.lean`

- Line 27: `def toWppRel : WppRel (HGraph V) where`

## `HeytingLean/WPP/Wolfram/Rewrite.lean`

- Line 23: `structure Rule (P : Type u) where`
- Line 42: `structure System (V : Type u) (P : Type v) where`
- Line 51: `structure Event (sys : System V P) where`
- Line 68: `def Applicable (e : sys.Event) (s : HGraph V) : Prop :=`
- Line 71: `instance decidableApplicable [DecidableEq V] (e : sys.Event) (s : HGraph V) :`
- Line 79: `def apply (e : sys.Event) (s : HGraph V) : HGraph V :=`
- Line 84: `def Causes (e₁ e₂ : sys.Event) : Prop :=`
- Line 92: `inductive Evolves : HGraph V → List sys.Event → HGraph V → Prop`
- Line 101: `def Reachable (t : HGraph V) : Prop :=`
- Line 105: `def NormalForm (s : HGraph V) : Prop :=`

