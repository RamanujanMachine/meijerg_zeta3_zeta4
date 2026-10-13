-- Copied from ../zetas_irr/blueprints/GW_cert4.lean (zetas_irr commit d9d5223) for the analytic input of
-- `Meijer5255.QGrowth` / `Meijer5255.LinformError`. Changes: module renamed to
-- `Meijer5255.QGrowth_GW_cert4`, imports renamed accordingly, namespace `ZetasIrr` renamed to
-- `Meijer5255.QGA.ZetasIrr` (to avoid clashes with other copies), plus Mathlib-pin fixes.
/-
# Block certificates at `n = 24, …, 29` (kernel-checked)
-/
import Meijer5255.QGrowth_GW_fast

namespace Meijer5255.QGA.ZetasIrr.GW

theorem checkAll_4 : checkAll [24, 25, 26, 27, 28, 29] = true := by decide +kernel

end Meijer5255.QGA.ZetasIrr.GW
