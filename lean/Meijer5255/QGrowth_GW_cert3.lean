-- Copied from ../zetas_irr/blueprints/GW_cert3.lean (zetas_irr commit d9d5223) for the analytic input of
-- `Meijer5255.QGrowth` / `Meijer5255.LinformError`. Changes: module renamed to
-- `Meijer5255.QGrowth_GW_cert3`, imports renamed accordingly, namespace `ZetasIrr` renamed to
-- `Meijer5255.QGA.ZetasIrr` (to avoid clashes with other copies), plus Mathlib-pin fixes.
/-
# Block certificates at `n = 18, …, 23` (kernel-checked)
-/
import Meijer5255.QGrowth_GW_fast

namespace Meijer5255.QGA.ZetasIrr.GW

theorem checkAll_3 : checkAll [18, 19, 20, 21, 22, 23] = true := by decide +kernel

end Meijer5255.QGA.ZetasIrr.GW
