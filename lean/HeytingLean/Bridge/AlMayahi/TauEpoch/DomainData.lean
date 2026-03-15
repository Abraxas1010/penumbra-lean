import HeytingLean.Bridge.AlMayahi.TauEpoch.Stats
import HeytingLean.Bridge.AlMayahi.TauEpoch.TauProxy

/-!
# Bridge.AlMayahi.TauEpoch.DomainData

Typed domain datasets for the six-domain τ-Epoch analysis.
All empirical constants are centralized in this file and transcribed
from the paper tables / Section 9 Python arrays.
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Domain I: H0 measurement row. -/
structure H0Measurement where
  experiment : String
  h0Value : Float
  sigma : Float
  methodFamily : String
  log10TauMethod : Float
  deriving Repr

/-- Domain II: LHC Higgs-coupling row. -/
structure LhcKappaMeasurement where
  channel : String
  atlasKappa : Float
  cmsKappa : Float
  atlasSigma : Float
  cmsSigma : Float
  deltaKappa : Float
  log10TauMethod : Float
  deriving Repr

/-- Domain III: NMR inter-laboratory scatter row. -/
structure NmrMeasurement where
  compound : String
  b0Tesla : Float
  omegaLMHz : Float
  shiftPpm : Float
  t1Sec : Float
  tauProxyT1wL : Float
  sigma : Float
  log10TauMethod : Float
  deriving Repr

/-- Domain IV: Neutron-lifetime row. -/
structure NeutronMeasurement where
  experiment : String
  mode : String
  lifetimeSec : Float
  sigma : Float
  log10TauMethod : Float
  deriving Repr

/-- Domain V: Proton-radius row. -/
structure ProtonMeasurement where
  measurement : String
  method : String
  radiusFm : Float
  sigma : Float
  log10TauMethod : Float
  deriving Repr

/-- Domain VI: Muon g-2 row (table-scale values in units ×10^-11). -/
structure MuonMeasurement where
  collaboration : String
  aMuTimes1e11 : Float
  sigma : Float
  expMinusTheory : Float
  tensionSigma : Float
  log10TauMethod : Float
  deriving Repr

/-- Table 2: H0 ensemble (paper Section 9 arrays). -/
def h0Ensemble : Array H0Measurement := #[
  ⟨"Planck 2018", 67.4, 0.5, "CMB / Early Universe", 13.1⟩,
  ⟨"ACT DR6", 68.3, 1.1, "CMB / Early Universe", 13.1⟩,
  ⟨"Freedman CCHP", 69.96, 1.9, "TRGB + SN Ia", 0.5⟩,
  ⟨"HoLiCOW", 73.3, 1.8, "Strong Lensing", 9.5⟩,
  ⟨"SH0ES", 73.04, 1.04, "Cepheid + SN Ia", -2.0⟩,
  ⟨"SPARC BTFR", 75.1, 2.3, "Tully-Fisher", 8.0⟩,
  ⟨"GW170817", 70.0, 10.0, "Gravitational Waves", -1.5⟩
]

/-- Table 3 / Section 9 arrays: seven Higgs channels. -/
def lhcKappaTable : Array LhcKappaMeasurement := #[
  ⟨"kappa_gammagamma", 1.04, 0.98, 0.04, 0.04, 0.06, -9.0⟩,
  ⟨"kappa_ZZ", 1.06, 0.99, 0.05, 0.05, 0.07, -10.0⟩,
  ⟨"kappa_WW", 1.05, 1.02, 0.05, 0.05, 0.03, -10.0⟩,
  ⟨"kappa_bb", 1.02, 0.90, 0.07, 0.07, 0.12, -12.0⟩,
  ⟨"kappa_tautau", 1.05, 0.91, 0.06, 0.06, 0.14, -12.0⟩,
  ⟨"kappa_tt", 1.02, 0.95, 0.07, 0.08, 0.07, -25.0⟩,
  ⟨"kappa_mumu", 1.29, 1.19, 0.33, 0.34, 0.10, -6.0⟩
]

/-- Table 4 rows (water+alanine+caffeine). Water rows are used in the N1 fit. -/
def nmrTable : Array NmrMeasurement := #[
  ⟨"1H2O_ref", 1.5, 64.0, 0.08, 3.0, 192.0, 0.005, 2.2833012287⟩,
  ⟨"1H2O_ref", 7.0, 300.0, 0.04, 3.0, 900.0, 0.004, 2.9542425094⟩,
  ⟨"1H2O_ref", 14.1, 600.0, 0.02, 3.0, 1800.0, 0.003, 3.2552725051⟩,
  ⟨"Alanine_CH3", 7.0, 300.0, 0.012, 1.2, 360.0, 0.001, 2.5563025008⟩,
  ⟨"Alanine_CH3", 11.7, 500.0, 0.008, 1.2, 600.0, 0.001, 2.7781512504⟩,
  ⟨"Alanine_CH3", 14.1, 600.0, 0.006, 1.2, 720.0, 0.001, 2.8573324964⟩,
  ⟨"Caffeine_H8", 7.0, 300.0, 0.031, 6.0, 1800.0, 0.002, 3.2552725051⟩,
  ⟨"Caffeine_H8", 14.1, 600.0, 0.018, 6.0, 3600.0, 0.002, 3.5563025008⟩
]

/-- Table 5 / Section 9 arrays: six bottle and three beam measurements. -/
def neutronTable : Array NeutronMeasurement := #[
  ⟨"BL1_2021", "bottle", 877.75, 0.28, 0.0⟩,
  ⟨"UCNtau_2018", "bottle", 877.7, 0.7, 0.0⟩,
  ⟨"Serebrov_2018", "bottle", 877.7, 0.7, 0.0⟩,
  ⟨"Arzumanov_2015", "bottle", 880.2, 1.2, 0.0⟩,
  ⟨"Pichlmaier_2010", "bottle", 880.2, 1.2, 0.0⟩,
  ⟨"Serebrov_2005", "bottle", 878.5, 0.7, 0.0⟩,
  ⟨"BPM_beam", "beam", 887.8, 2.2, -6.0⟩,
  ⟨"Nico_2005", "beam", 886.3, 3.4, -6.0⟩,
  ⟨"Byrne_1996", "beam", 889.2, 4.4, -6.0⟩
]

/-- Table 6 / Section 9 arrays: four electronic + two muonic. -/
def protonTable : Array ProtonMeasurement := #[
  ⟨"MAMI_2010_ep_scattering", "electronic", 0.879, 0.008, -9.0⟩,
  ⟨"CODATA_2014_H_spectroscopy", "electronic", 0.8751, 0.0061, -9.0⟩,
  ⟨"Grinin_2020_H_1S_3S", "electronic", 0.8482, 0.0038, -9.0⟩,
  ⟨"PRad_2019_ep_scattering", "electronic", 0.831, 0.014, -9.0⟩,
  ⟨"Antognini_2013_muonic_H", "muonic", 0.84087, 0.00039, -11.0⟩,
  ⟨"Pohl_2010_muonic_H", "muonic", 0.84184, 0.00067, -11.0⟩
]

/-- Table 7 rows used in the paper's muon ordering checks. -/
def muonTable : Array MuonMeasurement := #[
  ⟨"White_Paper_2020_dispersive", 116591810.0, 43.0, 251.0, 4.22, -23.0⟩,
  ⟨"BMW_lattice_2021", 116591954.0, 55.0, 107.0, 1.56, -25.0⟩,
  ⟨"Borsanyi_2020_lattice", 116592033.0, 63.0, 28.0, 0.32, -25.0⟩
]

/-- Convenience projections for prediction checks. -/
def h0Values : List Float := h0Ensemble.toList.map (fun r => r.h0Value)
def h0Sigmas : List Float := h0Ensemble.toList.map (fun r => r.sigma)
def h0LogTau : List Float := h0Ensemble.toList.map (fun r => r.log10TauMethod)

def lhcDeltaKappa : List Float := lhcKappaTable.toList.map (fun r => r.deltaKappa)

def nmrH2OFieldInv : List Float :=
  (nmrTable.toList.filter (fun r => r.compound == "1H2O_ref")).map (fun r => 1.0 / r.b0Tesla)

def nmrH2OShift : List Float :=
  (nmrTable.toList.filter (fun r => r.compound == "1H2O_ref")).map (fun r => r.shiftPpm)

def neutronBottleLifetimes : List Float :=
  (neutronTable.toList.filter (fun r => r.mode == "bottle")).map (fun r => r.lifetimeSec)

def neutronBeamLifetimes : List Float :=
  (neutronTable.toList.filter (fun r => r.mode == "beam")).map (fun r => r.lifetimeSec)

def neutronBottleSigmas : List Float :=
  (neutronTable.toList.filter (fun r => r.mode == "bottle")).map (fun r => r.sigma)

def neutronBeamSigmas : List Float :=
  (neutronTable.toList.filter (fun r => r.mode == "beam")).map (fun r => r.sigma)

def protonElectronic : List Float :=
  (protonTable.toList.filter (fun r => r.method == "electronic")).map (fun r => r.radiusFm)

def protonMuonic : List Float :=
  (protonTable.toList.filter (fun r => r.method == "muonic")).map (fun r => r.radiusFm)

def protonTauProxyAll : List Float := protonTable.toList.map (fun r => r.log10TauMethod)
def protonRadiusAll : List Float := protonTable.toList.map (fun r => r.radiusFm)

def muonTheoryValues : List Float := muonTable.toList.map (fun r => r.aMuTimes1e11)
def muonTauProxy : List Float := muonTable.toList.map (fun r => r.log10TauMethod)

/-- Internal anti-hack guard: all default proxy assignments are valid. -/
theorem default_proxy_table_valid :
    (∀ d : DomainKind, ValidTauProxy (defaultTauProxy d)) := by
  intro d
  exact defaultTauProxy_valid d

end HeytingLean.Bridge.AlMayahi.TauEpoch
