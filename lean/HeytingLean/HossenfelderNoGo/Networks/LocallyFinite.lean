import HeytingLean.HossenfelderNoGo.Spacetime.LorentzGroup

namespace HeytingLean.HossenfelderNoGo.Networks

open HeytingLean.HossenfelderNoGo.Spacetime

/-- A spacetime network with node positions and adjacency. -/
structure SpacetimeNetwork where
  Node : Type
  position : Node → SpacetimeDisplacement
  adjacent : Node → Node → Prop

/-- Relative displacement between two nodes. -/
def neighborDisplacement (N : SpacetimeNetwork) (u v : N.Node) : SpacetimeDisplacement :=
  ⟨(N.position v).Δt - (N.position u).Δt, (N.position v).Δx - (N.position u).Δx⟩

/-- A network is locally finite when every bounded region sees only finitely many nodes and
finitely many incident links. -/
structure LocallyFinite (N : SpacetimeNetwork) : Prop where
  finite_nodes_in_bounded_region : ∀ (R : ℝ), 0 < R →
    Set.Finite { n : N.Node | ‖((N.position n).Δt, (N.position n).Δx)‖ ≤ R }
  finite_links_crossing : ∀ (R : ℝ), 0 < R →
    Set.Finite { p : N.Node × N.Node |
      N.adjacent p.1 p.2 ∧ ‖((N.position p.1).Δt, (N.position p.1).Δx)‖ ≤ R }

/-- Lorentz boosts preserve neighbor proper lengths. -/
def BoostInvariant (N : SpacetimeNetwork) : Prop :=
  ∀ (η : ℝ) (u v : N.Node), N.adjacent u v →
    minkowskiInterval (LorentzBoost.apply ⟨η⟩ (neighborDisplacement N u v)) =
      minkowskiInterval (neighborDisplacement N u v)

/-- Translational homogeneity: every translated copy of a node position is realized by some node. -/
def TranslationInvariant (N : SpacetimeNetwork) : Prop :=
  ∀ (u : N.Node) (δ : SpacetimeDisplacement), ∃ v : N.Node,
    N.position v = ⟨(N.position u).Δt + δ.Δt, (N.position u).Δx + δ.Δx⟩

/-- Hyperbola coverage: every point on a fixed proper-length hyperbola can occur as a neighbor
displacement. This is the abstract version of the "uniform on hyperbolae" consequence used by the
no-go argument. -/
def UniformOnHyperbolae (N : SpacetimeNetwork) : Prop :=
  ∀ (u v : N.Node), N.adjacent u v →
    ∀ d ∈ hyperbolaAt (minkowskiInterval (neighborDisplacement N u v)),
      ∃ w : N.Node, N.adjacent u w ∧ neighborDisplacement N u w = d

/-- A Poincare-invariant network must realize at least one nondegenerate proper-length orbit. -/
def SupportsNonzeroHyperbola (N : SpacetimeNetwork) : Prop :=
  ∃ (u v : N.Node), N.adjacent u v ∧ minkowskiInterval (neighborDisplacement N u v) ≠ 0

/-- Poincare invariance packages the three structural requirements used by the no-go theorem. -/
def PoincareInvariant (N : SpacetimeNetwork) : Prop :=
  BoostInvariant N ∧ TranslationInvariant N ∧ UniformOnHyperbolae N ∧ SupportsNonzeroHyperbola N

end HeytingLean.HossenfelderNoGo.Networks
