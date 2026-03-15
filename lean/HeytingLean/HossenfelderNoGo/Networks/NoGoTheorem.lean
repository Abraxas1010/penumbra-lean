import HeytingLean.HossenfelderNoGo.Networks.LocallyFinite
import HeytingLean.HossenfelderNoGo.Spacetime.LorentzGroup

namespace HeytingLean.HossenfelderNoGo.Networks

open HeytingLean.HossenfelderNoGo.Spacetime

/-- Hossenfelder's no-go theorem: a locally finite network cannot realize an entire nonzero
Lorentz hyperbola worth of outgoing neighbor displacements from a bounded source node. The only
external geometric input is `hyperbola_infinite_length`. -/
theorem no_poincare_invariant_locally_finite_network :
    ¬∃ (N : SpacetimeNetwork), LocallyFinite N ∧ PoincareInvariant N
:= by
  rintro ⟨N, hLF, _hBoost, _hTrans, hUniform, hNonzero⟩
  rcases hNonzero with ⟨u, v, huv, hα⟩
  let α := minkowskiInterval (neighborDisplacement N u v)
  let R : ℝ := ‖((N.position u).Δt, (N.position u).Δx)‖ + 1
  have hRpos : 0 < R := by
    dsimp [R]
    positivity
  let linkSlice : Set (N.Node × N.Node) :=
    { p | N.adjacent p.1 p.2 ∧ ‖((N.position p.1).Δt, (N.position p.1).Δx)‖ ≤ R ∧ p.1 = u }
  have hLinkSliceFinite : linkSlice.Finite := by
    refine (hLF.finite_links_crossing R hRpos).subset ?_
    intro p hp
    exact ⟨hp.1, hp.2.1⟩
  let displacementImage : Set SpacetimeDisplacement :=
    (fun p : N.Node × N.Node => neighborDisplacement N p.1 p.2) '' linkSlice
  have hDispFinite : displacementImage.Finite :=
    hLinkSliceFinite.image (fun p : N.Node × N.Node => neighborDisplacement N p.1 p.2)
  have huBound : ‖((N.position u).Δt, (N.position u).Δx)‖ ≤ R := by
    dsimp [R]
    linarith
  have hHyperbolaSubset : hyperbolaAt α ⊆ displacementImage := by
    intro d hd
    rcases hUniform u v huv d (by simpa [α] using hd) with ⟨w, huw, hdisp⟩
    refine ⟨(u, w), ?_, hdisp⟩
    exact ⟨huw, huBound, rfl⟩
  have hHyperbolaFinite : (hyperbolaAt α).Finite :=
    hDispFinite.subset hHyperbolaSubset
  have hNormFinite : Set.Finite ((fun d : SpacetimeDisplacement => ‖(d.Δt, d.Δx)‖) '' hyperbolaAt α) :=
    hHyperbolaFinite.image (fun d : SpacetimeDisplacement => ‖(d.Δt, d.Δx)‖)
  rcases hNormFinite.bddAbove with ⟨L, hL⟩
  have hBound : ∀ d ∈ hyperbolaAt α, ‖(d.Δt, d.Δx)‖ ≤ L := by
    intro d hd
    exact hL ⟨d, hd, rfl⟩
  exact hyperbola_infinite_length α hα ⟨L, hBound⟩

end HeytingLean.HossenfelderNoGo.Networks
