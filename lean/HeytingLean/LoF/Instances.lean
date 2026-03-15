import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Data.Set.Lattice
import HeytingLean.LoF.PrimaryAlgebra

namespace HeytingLean
namespace LoF

universe u

-- Use the standard frame structure on powersets inherited from the `SetLike`
-- complete lattice; `Set α` is a complete Boolean algebra in mathlib, and
-- hence a frame.
noncomputable instance (α : Type u) : Order.Frame (Set α) :=
  inferInstance

/-- PrimaryAlgebra instance for powersets. -/
noncomputable instance (α : Type u) : PrimaryAlgebra (Set α) :=
  { toFrame := inferInstance }

end LoF
end HeytingLean
