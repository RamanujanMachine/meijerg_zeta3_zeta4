/-
# The prime number theorem (the single accepted `sorry` of the project)

`θ(x)/x → 1`, stated as zeta34 `blueprints/log_Delta_le.lean` `prime_number_theorem`.
By the user's decision (`LEAN_HANDOFF.md` §0) this is the only `sorry` allowed in the final
development; it is used by `LogGnewGe.lean` and `LogNormalizationLe.lean`.
-/
import Mathlib

open Filter Topology

namespace Meijer5255.PNT

/-- **The prime number theorem** `θ(x)/x → 1` (Chebyshev's `θ(x) = ∑_{p ≤ x} log p`).
* Not proved here (≈ 10000 lines; the `PrimeNumberTheoremAnd` project). -/
theorem prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) := by
  sorry

end Meijer5255.PNT
