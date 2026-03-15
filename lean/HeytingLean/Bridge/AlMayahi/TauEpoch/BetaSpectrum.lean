import Mathlib.Analysis.SpecialFunctions.Log.Basic
import HeytingLean.Bridge.AlMayahi.TauEpoch.ProjectionOperator
import HeytingLean.Bridge.AlMayahi.TauEpoch.TauProxy

/-!
# Bridge.AlMayahi.TauEpoch.BetaSpectrum

β-coupling spectrum encoding from Table 8 / 8A.
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Base-10 logarithm over reals. -/
noncomputable def log10 (x : ℝ) : ℝ :=
  Real.log x / Real.log 10

/-- Spectrum map from τ-scale to β-coupling. -/
noncomputable def betaFromTau (kappa τMethod τPlanck : ℝ) : ℝ :=
  kappa * log10 (τMethod / τPlanck)

/-- One row of Table 8. `betaBirge = none` denotes rows where β is not reported. -/
structure BetaDatum where
  domainLabel : String
  domainKind? : Option DomainKind
  anomaly : String
  betaBirge : Option ℝ
  tauProxyLog10 : String
  signConfirmed : Bool
  thresholdMet : Bool

/-- Aggregated β-spectrum. -/
structure BetaCouplingSpectrum where
  entries : List BetaDatum

/-- Table 8 rows as encoded data. -/
def tauEpochBetaSpectrum : BetaCouplingSpectrum :=
  { entries :=
      [ { domainLabel := "G_torsion_gravimetry"
          domainKind? := none
          anomaly := "Birge = 39.1"
          betaBirge := some 39.1
          tauProxyLog10 := "-3 to +3"
          signConfirmed := true
          thresholdMet := true }
      , { domainLabel := "h_watt_balance_xrcd"
          domainKind? := none
          anomaly := "4.34 sigma"
          betaBirge := some 7.8
          tauProxyLog10 := "~-2 to 0"
          signConfirmed := true
          thresholdMet := true }
      , { domainLabel := "alpha_atom_recoil"
          domainKind? := none
          anomaly := "5.5 sigma Parker-Morel"
          betaBirge := some 3.36
          tauProxyLog10 := "-5 to -3"
          signConfirmed := true
          thresholdMet := true }
      , { domainLabel := "III_NMR"
          domainKind? := some .chemistry
          anomaly := "1/B0 scatter"
          betaBirge := some 4.2
          tauProxyLog10 := "Table 4 (T1*omegaL values)"
          signConfirmed := true
          thresholdMet := true }
      , { domainLabel := "IV_neutron"
          domainKind? := some .nuclearPhysics
          anomaly := "5.7 sigma bottle-beam"
          betaBirge := some 1.47
          tauProxyLog10 := "~-6 vs 0"
          signConfirmed := true
          thresholdMet := true }
      , { domainLabel := "I_H0"
          domainKind? := some .cosmology
          anomaly := "~5 sigma CMB-local"
          betaBirge := some 2.54
          tauProxyLog10 := "-1 to +13"
          signConfirmed := true
          thresholdMet := false }
      , { domainLabel := "V_proton"
          domainKind? := some .atomicPhysics
          anomaly := "4.8 sigma muonic-electronic"
          betaBirge := some 2.9
          tauProxyLog10 := "-11 vs -9"
          signConfirmed := true
          thresholdMet := false }
      , { domainLabel := "II_LHC"
          domainKind? := some .particlePhysics
          anomaly := "7/7 sign offset"
          betaBirge := some 0.46
          tauProxyLog10 := "-25 to -15"
          signConfirmed := true
          thresholdMet := true }
      , { domainLabel := "VI_muon_g2"
          domainKind? := some .hadronicTheory
          anomaly := "2.1 sigma WP vs lattice"
          betaBirge := none
          tauProxyLog10 := "~-24 vs -23"
          signConfirmed := true
          thresholdMet := false }
      ] }

/-- Extract only rows with explicitly reported β values. -/
def betaReportedRows : List BetaDatum :=
  tauEpochBetaSpectrum.entries.filter (fun d => d.betaBirge.isSome)

/-- Table 8 contains nine domain rows. -/
theorem tauEpochBetaSpectrum_card :
    tauEpochBetaSpectrum.entries.length = 9 := by
  native_decide

/-- Exactly one row has no reported β value (Muon g-2 row). -/
theorem beta_missing_count_eq_one :
    (tauEpochBetaSpectrum.entries.filter (fun d => d.betaBirge.isNone)).length = 1 := by
  native_decide

theorem betaFromTau_zero_kappa (τMethod τPlanck : ℝ) :
    betaFromTau 0 τMethod τPlanck = 0 := by
  simp [betaFromTau]

end HeytingLean.Bridge.AlMayahi.TauEpoch
