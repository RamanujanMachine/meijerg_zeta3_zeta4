-- Copied from ../zetas_irr/blueprints/GW_cert0.lean (zetas_irr commit d9d5223) for the analytic input of
-- `Meijer5255.QGrowth` / `Meijer5255.LinformError`. Changes: module renamed to
-- `Meijer5255.QGrowth_GW_cert0`, imports renamed accordingly, namespace `ZetasIrr` renamed to
-- `Meijer5255.QGA.ZetasIrr` (to avoid clashes with other copies), plus Mathlib-pin fixes.
/-
# Block certificates at `n = 0, …, 5` (kernel-checked)
-/
import Meijer5255.QGrowth_GW_fast

namespace Meijer5255.QGA.ZetasIrr.GW

theorem checkAll_0 : checkAll [0, 1, 2, 3, 4, 5] = true := by decide +kernel

end Meijer5255.QGA.ZetasIrr.GW
