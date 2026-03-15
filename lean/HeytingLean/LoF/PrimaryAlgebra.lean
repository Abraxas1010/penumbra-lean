import Mathlib.Order.CompleteBooleanAlgebra

namespace HeytingLean
namespace LoF

/-- `PrimaryAlgebra α` packages the LoF base assumptions as a frame.

The frame requirement ensures finite meets distribute over arbitrary joins, matching the locale
interpretation of the primary algebra that underpins the nucleus story. -/
class PrimaryAlgebra (α : Type u) extends Order.Frame α

end LoF
end HeytingLean
