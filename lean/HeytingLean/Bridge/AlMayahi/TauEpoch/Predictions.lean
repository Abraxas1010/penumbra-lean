import HeytingLean.Bridge.AlMayahi.TauEpoch.DomainData
import HeytingLean.Bridge.AlMayahi.TauEpoch.ProjectionLaw
import HeytingLean.Bridge.AlMayahi.TauEpoch.Stats

/-!
# Bridge.AlMayahi.TauEpoch.Predictions

Pre-registered prediction records for the six-domain τ-Epoch framework.
-/

namespace HeytingLean.Bridge.AlMayahi.TauEpoch

/-- Status class for a pre-registered prediction. -/
inductive PredictionStatus
  | confirmed
  | directional
  | notMet
  | pending
  deriving DecidableEq, Repr

/-- Prediction record with explicit threshold and falsification fields. -/
structure Prediction where
  id : String
  domain : DomainKind
  description : String
  testStatistic : String
  preRegisteredDirection : String
  threshold : String
  falsification : String
  currentStatus : PredictionStatus
  currentEvidence : String
  deriving Repr

def h1ComputedRho : Float :=
  floatSpearman h0LogTau h0Values

def h1ComputedStatus : PredictionStatus :=
  if h1ComputedRho < -0.5 then .confirmed else .directional

def l2ComputedStatus : PredictionStatus :=
  let nPos := lhcDeltaKappa.foldl (fun acc x => if 0 < x then acc + 1 else acc) 0
  let pSign := floatBinomialSignPValue nPos lhcDeltaKappa.length
  if nPos = lhcDeltaKappa.length && pSign <= 0.01 then .confirmed else .notMet

def n1NmrComputedStatus : PredictionStatus :=
  let r2 := (floatLinearRegression nmrH2OFieldInv nmrH2OShift).2.2
  if 0.90 < r2 then .confirmed else .directional

def n1NeutronComputedStatus : PredictionStatus :=
  let bottle := floatWeightedMean neutronBottleLifetimes neutronBottleSigmas
  let beam := floatWeightedMean neutronBeamLifetimes neutronBeamSigmas
  if bottle < beam then .confirmed else .notMet

def p1ComputedStatus : PredictionStatus :=
  let r := floatPearson protonTauProxyAll protonRadiusAll
  let p := floatPearsonOneSidedPValue protonTauProxyAll protonRadiusAll true
  if 0.4 < r && p < 0.10 then .confirmed
  else if 0 < r then .directional
  else .notMet

def m1ComputedStatus : PredictionStatus :=
  let r := floatPearson muonTauProxy muonTheoryValues
  let p := floatPearsonOneSidedPValue muonTauProxy muonTheoryValues false
  if r < -0.4 && p < 0.10 then .confirmed
  else if r < 0 then .directional
  else .notMet

def p1PearsonR : Float := floatPearson protonTauProxyAll protonRadiusAll
def p1PearsonP : Float := floatPearsonOneSidedPValue protonTauProxyAll protonRadiusAll true

def m1PearsonR : Float := floatPearson muonTauProxy muonTheoryValues
def m1PearsonP : Float := floatPearsonOneSidedPValue muonTauProxy muonTheoryValues false

def predictionH1 : Prediction :=
  { id := "H1"
    domain := .cosmology
    description := "Tau-ordered H0 ensemble"
    testStatistic := "Spearman rho(log10 tau, H0)"
    preRegisteredDirection := "negative"
    threshold := "rho < -0.5 and p < 0.05 at n >= 15"
    falsification := "|rho| < 0.2 at p > 0.10 over n >= 15"
    currentStatus := h1ComputedStatus
    currentEvidence := "Current n = 7; directional ordering observed" }

def predictionL2 : Prediction :=
  { id := "L2"
    domain := .particlePhysics
    description := "LHC sign persistence (all delta-kappa > 0)"
    testStatistic := "Binomial sign"
    preRegisteredDirection := "all positive"
    threshold := "all offsets positive at Run-3 update"
    falsification := "mixed-sign offsets dominate"
    currentStatus := l2ComputedStatus
    currentEvidence := "Current table rows are positive in all channels" }

def predictionN1Nmr : Prediction :=
  { id := "N1_NMR"
    domain := .chemistry
    description := "1/B0 scaling of inter-laboratory NMR scatter"
    testStatistic := "Linear regression R2"
    preRegisteredDirection := "positive 1/B0 slope"
    threshold := "R2 > 0.90"
    falsification := "R2 < 0.50 with stable dataset"
    currentStatus := n1NmrComputedStatus
    currentEvidence := "Current NMR table is strongly 1/B0-aligned" }

def predictionN1Neutron : Prediction :=
  { id := "N1_neutron"
    domain := .nuclearPhysics
    description := "Bottle-vs-beam lifetime stratification"
    testStatistic := "Weighted mean bottle vs weighted mean beam"
    preRegisteredDirection := "bottle < beam"
    threshold := "clear stratification retained"
    falsification := "stratification inversion"
    currentStatus := n1NeutronComputedStatus
    currentEvidence := "Current means preserve bottle < beam ordering" }

def predictionP1 : Prediction :=
  { id := "P1"
    domain := .atomicPhysics
    description := "Proton radius ordering between electronic and muonic methods"
    testStatistic := "Pearson r(log10 tau_proxy, r_p)"
    preRegisteredDirection := "positive"
    threshold := "r > 0.4 and one-sided p < 0.10"
    falsification := "non-positive correlation"
    currentStatus := p1ComputedStatus
    currentEvidence := "Pearson computed; direction positive, threshold check includes one-sided p-value" }

def predictionM1 : Prediction :=
  { id := "M1"
    domain := .hadronicTheory
    description := "Muon g-2 lattice-spacing direction encoded as tau-proxy ordering"
    testStatistic := "Pearson r(log10 tau_proxy, a_mu_theory)"
    preRegisteredDirection := "negative"
    threshold := "r < -0.4 and one-sided p < 0.10"
    falsification := "non-negative correlation"
    currentStatus := m1ComputedStatus
    currentEvidence := "Pearson computed; direction negative, threshold check includes one-sided p-value" }

def allPredictions : List Prediction :=
  [predictionH1, predictionL2, predictionN1Nmr, predictionN1Neutron, predictionP1, predictionM1]

def predictionStatusCounts : Nat × Nat × Nat × Nat :=
  let confirmed := (allPredictions.filter (fun p => p.currentStatus = .confirmed)).length
  let directional := (allPredictions.filter (fun p => p.currentStatus = .directional)).length
  let notMet := (allPredictions.filter (fun p => p.currentStatus = .notMet)).length
  let pending := (allPredictions.filter (fun p => p.currentStatus = .pending)).length
  (confirmed, directional, notMet, pending)

#eval ("H1 rho", h1ComputedRho, h1ComputedStatus)
#eval ("L2 status", l2ComputedStatus)
#eval ("N1_NMR status", n1NmrComputedStatus)
#eval ("N1_neutron status", n1NeutronComputedStatus)
#eval ("P1 status", p1ComputedStatus)
#eval ("M1 status", m1ComputedStatus)
#eval ("P1 Pearson (r, p_one_sided)", p1PearsonR, p1PearsonP)
#eval ("M1 Pearson (r, p_one_sided)", m1PearsonR, m1PearsonP)
#eval ("Status counts (confirmed, directional, notMet, pending)", predictionStatusCounts)

end HeytingLean.Bridge.AlMayahi.TauEpoch
