/-
# `second_order_shell` (paper §9, boxed (SG))

For eligible `p` with `{n/p}` in a window `(1/10, 2/19) ∪ (11/12, 15/16)`:
`v_p(Q_n) ≥ 3`, `v_p(P_{3,n}) ≥ 0`, `v_p(P_{4,n}) ≥ -1`.
Pure glue: `window_root_data` gives the trace-lemma hypotheses, `trace_lemma` gives (PB),
`window_readout` turns (PB) into (SG).
-/
import Meijer5255.WindowRootData
import Meijer5255.TraceLemma
import Meijer5255.WindowReadout

namespace Meijer5255.SecondOrderShell

open Meijer5255

/-- **Second-order windows** (SG) (paper §9, boxed). -/
theorem second_order_shell (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p)) :
    ValGE p 3 (Q n) ∧ ValGE p 0 (P3 n) ∧ ValGE p (-1) (P4 n) := by
  have : Fact p.Prime := ⟨hp.1⟩
  obtain ⟨NU, DU, h⟩ := WindowRootData.window_root_data n p hn hp hw
  exact WindowReadout.window_readout n p hn hp hw
    (fun ℓ => TraceLemma.trace_lemma p _ _ _ NU DU h ℓ)

end Meijer5255.SecondOrderShell
