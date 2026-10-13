-- Copied from ../zetas_irr/blueprints/GW_cert2.lean (zetas_irr commit d9d5223) for the analytic input of
-- `Meijer5255.QGrowth` / `Meijer5255.LinformError`. Changes: module renamed to
-- `Meijer5255.QGrowth_GW_cert2`, imports renamed accordingly, namespace `ZetasIrr` renamed to
-- `Meijer5255.QGA.ZetasIrr` (to avoid clashes with other copies), plus Mathlib-pin fixes.
/-
# Block certificates at `n = 12, …, 17` (kernel-checked)
-/
import Meijer5255.QGrowth_GW_fast

namespace Meijer5255.QGA.ZetasIrr.GW

theorem checkAll_2 : checkAll [12, 13, 14, 15, 16, 17] = true := by decide +kernel

end Meijer5255.QGA.ZetasIrr.GW
