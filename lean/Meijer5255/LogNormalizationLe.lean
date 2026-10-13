/-
# Node blueprint: `log_normalization_le` (paper §11, "Consequences for reduced denominators")

Target (restated verbatim from `Blueprint_5255.lean`):
  `∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (Cn n : ℝ) ≤ (logCn + ε) * n ∧
    Real.log (dlcm (19 * n) : ℝ) ≤ (19 + ε) * n`.

Strategy (paper §11: "Since `log C_n = 30n log(3/2) + o(n)` and `log d_{19n} = 19n + o(n)`").
*`C_n`.* `log C_n = 2 log (15n)! - 3 log (10n)!`. The two-sided Stirling bounds
`m log m - m ≤ log m! ≤ m log m - m + 1 + (log m)/2` ([4]) give
`log C_n ≤ 30n (log 15n - log 10n) + 2 + log 15n = 30 log(3/2) n + 2 + log 15 + log n`; the
`n log n` and linear terms cancel exactly. With `30 log(3/2) < logCn` ([5]) and
`log n = o(n)` the first claim follows.
*`d_{19n}`.* `log d_m = ψ(m)` ([2]); the prime number theorem ([1]) gives
`θ(x) ≤ (1 + ε/38) x` for large `x`, and `ψ(x) - θ(x) ≤ (ε/38) x` for large `x` ([3]), so
`ψ(19n) ≤ (1 + ε/19) · 19n = (19 + ε) n`.

Supporting lemmas (5), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `prime_number_theorem` | ≈ 10000 (or import PrimeNumberTheoremAnd) | no (quoted) |
| 2 | `log_dlcm_eq_psi` | 5 | yes (`log lcm(1..m) = ψ(m)`, standard) |
| 3 | `psi_sub_theta_small` | 20 | yes (standard: `ψ - θ = O(√x)`) |
| 4 | `log_factorial_bounds` | 30 | yes ("Stirling") |
| 5 | `log32_lt` | 40 | yes (`30 log(3/2) = 12.16395324324…`) |

The glue (≈ 70 lines below) turns [1] into an eventual upper bound for `θ`, combines it with [3],
evaluates `log C_n` through [4] with the exact cancellation of the `n log n` terms, and absorbs
`O(log n)` into `εn` (`Real.isLittleO_log_id_atTop`).

Reuse: zeta34 `blueprints/log_Delta_le.lean` (`prime_number_theorem`, `pnt_bounds`),
`growth_estimates.lean` (`fact_bounds`); pfq54 `log_Z0_le.lean` (`log_D_eq_psi` = [2] via Mathlib
`Chebyshev.psi_eq_log_lcmUpto`; `psi_le_eventually` via Mathlib
`Chebyshev.psi_sub_theta_le_mul_sqrt`, which gives [3]; `log_factorial_bounds` = [4]); pfq54
`eps_lt_exp` and Mathlib `Real.log_two_near_10` (pattern for the atanh certificate [5]).
-/
import Meijer5255.definitions
import Meijer5255.PNT

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.LogNormalizationLe

open Meijer5255

/-! ### Supporting lemmas -/

/-- **[1] The prime number theorem** `θ(x)/x → 1` (statement as zeta34
`log_Delta_le.prime_number_theorem`; the only analytic input of this file).
* Re-exported from `PNT.lean` (the project's single accepted `sorry`; ≈ 10000 lines, or import
  `PrimeNumberTheoremAnd`).
* Directly from the PDF: no (quoted: "`log d_{19n} = 19n + o(n)`"). -/
theorem prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PNT.prime_number_theorem

/-- **[2] `log d_m = ψ(m)`** (`d_m = lcm(1, …, m)`).
* Proved (≈ 3 lines; Mathlib `Chebyshev.psi_eq_log_lcmUpto`, pfq54 `log_Z0_le.log_D_eq_psi`).
* Directly from the PDF: yes (standard). -/
theorem log_dlcm_eq_psi (m : ℕ) : Real.log (dlcm m : ℝ) = Chebyshev.psi (m : ℝ) := by
  -- pfq54 `log_Z0_le.log_D_eq_psi`
  rw [Chebyshev.psi_eq_log_lcmUpto]
  rfl

/-- **[3] `ψ - θ` is negligible**: for every `δ > 0`, `ψ(x) - θ(x) ≤ δ x` for all large `x`
(`ψ(x) - θ(x) = ∑_{k ≥ 2} θ(x^{1/k}) = O(√x)`).
* Proved (≈ 13 lines; Mathlib `Chebyshev.psi_sub_theta_le` (`ψ - θ ≤ 2 √x log x`) and
  `isLittleO_log_rpow_atTop` with exponent `1/2`).
* Directly from the PDF: yes (standard; implicit in "`log d_{19n} = 19n + o(n)`"). -/
theorem psi_sub_theta_small (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Chebyshev.psi x - Chebyshev.theta x ≤ δ * x := by
  -- `ψ - θ ≤ 2 √x log x` (Mathlib) and `log x ≤ (δ/2) √x` eventually
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).def
    (by positivity : 0 < δ / 2)
  filter_upwards [hlo, eventually_ge_atTop 1] with x hx hx1
  have hx0 : 0 ≤ x := by linarith
  have hs : x ^ (1 / 2 : ℝ) = Real.sqrt x := (Real.sqrt_eq_rpow x).symm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (Real.log_nonneg hx1)] at hx
  have h1 := Chebyshev.psi_sub_theta_le hx1
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have h2 : 2 * Real.sqrt x * Real.log x ≤ 2 * Real.sqrt x * (δ / 2 * Real.sqrt x) :=
    mul_le_mul_of_nonneg_left hx (by positivity)
  nlinarith

/-- **[4] Two-sided Stirling bounds** for `m ≥ 1`:
`m log m - m ≤ log m! ≤ m log m - m + 1 + (log m)/2` (`(m/e)^m ≤ m! ≤ e √m (m/e)^m`).
* Proved (≈ 22 lines; adapted from zeta34 `growth_estimates.log_factorial_upper` / `fact_bounds`:
  Mathlib `Stirling.le_log_factorial_stirling` and `Stirling.stirlingSeq'_antitone`).
* Directly from the PDF: yes ("Stirling"; the paper states `log C_n = 30n log(3/2) + o(n)`). -/
theorem log_factorial_bounds (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) * Real.log m - m ≤ Real.log m.factorial ∧
      Real.log m.factorial ≤ m * Real.log m - m + 1 + Real.log m / 2 := by
  -- zeta34 `growth_estimates.fact_bounds` / `log_factorial_upper`
  have hne : m ≠ 0 := by omega
  have hlm : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have h2π : 0 ≤ Real.log (2 * Real.pi) / 2 := by
    have : (1 : ℝ) ≤ 2 * Real.pi := by have := Real.pi_gt_three; linarith
    have := Real.log_nonneg this
    positivity
  refine ⟨by linarith [Stirling.le_log_factorial_stirling hne], ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have h1 : Stirling.stirlingSeq (k + 1) ≤ Stirling.stirlingSeq 1 :=
    Stirling.stirlingSeq'_antitone (Nat.zero_le k)
  have h2 := Stirling.log_stirlingSeq_formula (k + 1)
  have hpos := Stirling.stirlingSeq'_pos k
  have h3 : Real.log (Stirling.stirlingSeq (k + 1)) ≤ Real.log (Stirling.stirlingSeq 1) :=
    Real.log_le_log hpos h1
  rw [Stirling.stirlingSeq_one, Real.log_div (Real.exp_pos 1).ne' (by positivity), Real.log_exp,
    Real.log_sqrt (by norm_num)] at h3
  have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  rw [Real.log_mul (by norm_num) hk.ne', Real.log_div hk.ne' (Real.exp_pos 1).ne',
    Real.log_exp] at h2
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  push_cast at h2 h3 hlm ⊢
  linarith

/-- **[5] The constant** `30 log(3/2) < 12.1639532433 = logCn`
(`30 log(3/2) = 12.16395324324493…`).
* Proved (≈ 7 lines; `log(3/2) = -log(1 - 1/3)`, 25 terms of the Mercator series with the
  geometric remainder of Mathlib `Real.abs_log_sub_add_sum_range_le`, pattern of pfq54
  `LZ.g12_numeric`).
* Directly from the PDF: yes (the paper uses `30 log(3/2)` and its decimal value). -/
theorem log32_lt : 30 * Real.log (3 / 2) < logCn := by
  -- `-log(1 - 1/3) = log(3/2)`, series with 25 terms (pattern: pfq54 `LZ.g12_numeric`)
  have h := Real.abs_log_sub_add_sum_range_le (show |(1 / 3 : ℝ)| < 1 by norm_num) 25
  rw [show (1 : ℝ) - 1 / 3 = (3 / 2)⁻¹ by norm_num, Real.log_inv] at h
  norm_num [Finset.sum_range_succ] at h
  rw [abs_le] at h
  unfold logCn
  linarith [h.1]

/-! ### The node -/

/-- **Normalization heights** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[5]. -/
theorem log_normalization_le :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (Cn n : ℝ) ≤ (logCn + ε) * n ∧
      Real.log (dlcm (19 * n) : ℝ) ≤ (19 + ε) * n := by
  intro ε hε
  -- the prime number theorem as an eventual upper bound for `θ`
  have hθ : ∀ᶠ x : ℝ in atTop, Chebyshev.theta x ≤ (1 + ε / 38) * x := by
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp prime_number_theorem (ε / 38) (by positivity)
    filter_upwards [eventually_ge_atTop (max X 1)] with x hx
    have hx0 : 0 < x := by linarith [le_max_right X 1]
    have h := hX x (le_trans (le_max_left _ _) hx)
    rw [Real.dist_eq, abs_lt] at h
    have : Chebyshev.theta x / x < 1 + ε / 38 := by linarith [h.2]
    exact ((div_lt_iff₀ hx0).mp this).le
  -- hence `ψ(x) ≤ (1 + ε/19) x`
  have hψ : ∀ᶠ x : ℝ in atTop, Chebyshev.psi x ≤ (1 + ε / 19) * x := by
    filter_upwards [hθ, psi_sub_theta_small (ε / 38) (by positivity)] with x h1 h2
    linarith
  have hψn : ∀ᶠ n : ℕ in atTop, Chebyshev.psi (19 * (n : ℝ)) ≤ (1 + ε / 19) * (19 * n) :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 19)).eventually hψ
  -- `log n = o(n)` and the constant term
  have hlog : ∀ᶠ n : ℕ in atTop, Real.log n ≤ ε / 2 * n := by
    have h := (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).def (by positivity : 0 < ε / 2)
    filter_upwards [h] with n hn
    simp only [Function.comp_apply, id_eq, Real.norm_eq_abs, Nat.abs_cast] at hn
    exact (le_abs_self _).trans hn
  have hconst : ∀ᶠ n : ℕ in atTop, 2 + Real.log 15 ≤ ε / 2 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop
      (2 * (2 + Real.log 15) / ε)] with n hn
    rw [div_le_iff₀ hε] at hn
    linarith
  filter_upwards [hψn, hlog, hconst, eventually_ge_atTop 1] with n hψ1 hlog1 hc1 hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨?_, ?_⟩
  · -- `log C_n`
    have hC : ((Cn n : ℚ) : ℝ) =
        (((15 * n).factorial : ℕ) : ℝ) ^ 2 / (((10 * n).factorial : ℕ) : ℝ) ^ 3 := by
      simp [Cn]
    have hf15 : (0 : ℝ) < ((15 * n).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
    have hf10 : (0 : ℝ) < ((10 * n).factorial : ℕ) := by exact_mod_cast Nat.factorial_pos _
    rw [hC, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    obtain ⟨-, hu⟩ := log_factorial_bounds (15 * n) (by omega)
    obtain ⟨hl, -⟩ := log_factorial_bounds (10 * n) (by omega)
    push_cast at hu hl
    have e15 : Real.log (15 * (n : ℝ)) = Real.log 15 + Real.log n :=
      Real.log_mul (by norm_num) hn0.ne'
    have e10 : Real.log (10 * (n : ℝ)) = Real.log 10 + Real.log n :=
      Real.log_mul (by norm_num) hn0.ne'
    rw [e15] at hu
    rw [e10] at hl
    have e32 : (Real.log 15 - Real.log 10) * n = Real.log (3 / 2) * n := by
      rw [← Real.log_div (by norm_num) (by norm_num)]
      norm_num
    have h32 := mul_le_mul_of_nonneg_right (log32_lt).le hn0.le
    push_cast
    linarith
  · -- `log d_{19n}`
    rw [log_dlcm_eq_psi]
    push_cast
    linarith

end Meijer5255.LogNormalizationLe
