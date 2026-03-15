import Mathlib.Data.Real.Basic

/-!
# Bridge.AlMayahi.TauEpoch.TauProxy

Operational τ-proxy assignments and validity constraints for the
τ-Epoch Discovery II framework.
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Scientific domain categories used in the paper. -/
inductive DomainKind
  | cosmology
  | particlePhysics
  | chemistry
  | nuclearPhysics
  | atomicPhysics
  | hadronicTheory
  deriving DecidableEq, Repr

/-- τ-proxy assignment with explicit provenance. -/
structure TauProxyAssignment where
  domain : DomainKind
  methodFamily : String
  tauProxyDefinition : String
  sourceReference : String
  /-- `log10(τ / s)` from method-intrinsic timescale assignment. -/
  log10TauSeconds : ℝ
  /-- Explicit anti-hack flag: must remain `false` for valid assignments. -/
  derivedFromAnomaly : Bool := false

/-- Operational lock from Sec. 1.2: provenance is required and τ is not tuned from anomaly data. -/
def ValidTauProxy (a : TauProxyAssignment) : Prop :=
  a.sourceReference ≠ "" ∧ a.derivedFromAnomaly = false

/-- Default τ-proxy assignment table (one assignment per domain family). -/
def defaultTauProxy : DomainKind → TauProxyAssignment
  | .cosmology =>
      { domain := .cosmology
        methodFamily := "CMB / Early Universe"
        tauProxyDefinition := "Cosmic integration timescale from recombination to observation"
        sourceReference := "Planck Collaboration; ACT DR6 analyses"
        log10TauSeconds := 13.1 }
  | .particlePhysics =>
      { domain := .particlePhysics
        methodFamily := "LHC detector subsystems (tracker/ECAL/b-vertex/muon)"
        tauProxyDefinition := "Subsystem shaping / trigger timescale from detector docs"
        sourceReference := "ATLAS/CMS Run analyses"
        log10TauSeconds := -9.0 }
  | .chemistry =>
      { domain := .chemistry
        methodFamily := "1H NMR field-comparison pipelines"
        tauProxyDefinition := "T1 * omega_L proxy (Table 4 values)"
        sourceReference := "Inter-laboratory NMR method references"
        log10TauSeconds := 3.0 }
  | .nuclearPhysics =>
      { domain := .nuclearPhysics
        methodFamily := "Bottle vs beam neutron-lifetime protocols"
        tauProxyDefinition := "Protocol intrinsic cycle timescale"
        sourceReference := "Neutron lifetime bottle/beam method papers"
        log10TauSeconds := 0.0 }
  | .atomicPhysics =>
      { domain := .atomicPhysics
        methodFamily := "Hydrogen spectroscopy vs muonic hydrogen"
        tauProxyDefinition := "Method-intrinsic excitation/measurement timescale"
        sourceReference := "CODATA spectroscopy and muonic-hydrogen analyses"
        log10TauSeconds := -9.0 }
  | .hadronicTheory =>
      { domain := .hadronicTheory
        methodFamily := "Lattice-QCD and hadronic-vacuum-polarization pipelines"
        tauProxyDefinition := "Timelike hadronic scale (dispersive) / lattice Euclidean step"
        sourceReference := "BMW/RBC/UKQCD and related lattice-QCD publications"
        log10TauSeconds := -23.0 }

theorem defaultTauProxy_valid (d : DomainKind) :
    ValidTauProxy (defaultTauProxy d) := by
  cases d <;> simp [ValidTauProxy, defaultTauProxy]

end HeytingLean.Bridge.AlMayahi.TauEpoch
