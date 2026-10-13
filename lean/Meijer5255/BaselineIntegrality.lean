/-
# Node blueprint: `baseline_integrality` (paper §4, "A uniform denominator bound")

Target (restated verbatim from `Blueprint_5255.lean`): for `n ≥ 1`,
  `(∀ j, C_n a_j ∈ ℤ) ∧ (∀ j, d_{16n} C_n b_j ∈ ℤ) ∧ (∀ i, Z3v n i ∈ ℤ) ∧ (∀ i, Z4v n i ∈ ℤ) ∧
   0 < (-1)^n Q_n`.

Strategy (paper §4, the binomial route). Re-pair the denominator of `F_n` as
`(t+n)_{15n+1} (t+2n)_{15n+1}` and write
`C_n F_n = P(t) L_n(t) L_{2n}(t)`, `P(t) = ∏_{u=0}^{2} C(t-un-1, 10n)` (`Pbin`),
`L_c(t) = (15n)! / ∏_{k=c}^{c+15n} (t+k)`.  `L_c` has simple poles at `-k` with integer residues
`ρ_c(k) = (-1)^{k-c} C(15n, k-c)` (`rho`); its regular part at `-j` is
`σ_c(j) = ∑_{k ≠ j} ρ_c(k)/(k-j)` (`sig`).  Expanding the product at `t = -j` gives
`C_n a_j = P(-j) ρ_n(j) ρ_{2n}(j)` and
`C_n b_j = P'(-j) ρ_n(j) ρ_{2n}(j) + P(-j) (ρ_n(j) σ_{2n}(j) + ρ_{2n}(j) σ_n(j))`
(uniformly in `j`, `ρ = 0` off `[c, c+15n]`).  Now `P(-j) = ∏_u C(j+un+10n, 10n) ∈ ℤ_{>0}`,
`d_{10n} P'(-j) ∈ ℤ` (Newton basis), `d_{16n} σ_c(j) ∈ ℤ` (`0 < |k-j| ≤ 16n`), and
`d_{10n} ∣ d_{16n} ∣ d_{19n}` (`Finset.lcm_mono`); the harmonic numbers `H^{(s)}_{j+2n}`,
`j + 2n ≤ 19n`, are cleared by `d_{19n}^s`, and the `6` absorbs the `/2`, `/3`.  Positivity:
`(-1)^n C_n a_j = P(-j) · (-1)^n ρ_n(j) ρ_{2n}(j) ≥ 0`, strictly at `j = 2n`
(`ρ_n(2n) ρ_{2n}(2n) = (-1)^n C(15n, n)`), so `(-1)^n Q_n > 0` as `C_n > 0`.
The glue (subring `(Int.castRingHom ℚ).range`, `Finset.sum_pos'`) is done below.

Supporting lemmas (7), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `Pbin_eval_neg` | 35 | yes (`P` integer-valued; explicit at `t = -j`) |
| 2 | `dPbin_int` | 80 | yes (Newton-basis identity + product rule) |
| 3 | `rho_sign` | 30 | no (positivity is not in the paper; immediate from the closed form) |
| 4 | `aCoef_formula` | 120 | yes (factorization `C_n F_n = P L_n L_{2n}`, double coefficient) |
| 5 | `bCoef_formula` | 150 | yes (same, simple coefficient, both pole types) |
| 6 | `sig_int` | 30 | yes ("denominator `j-k`, `0 < |j-k| ≤ 16n`") |
| 7 | `harm_int` | 12 | yes ("harmonic numbers of order `s` are cleared by `d_{19n}^s`") |

Reuse: pfq54 `Z_integral.lean` (`upperJet_integral`, `lowerJet_integral`, `harm_integral`,
`readout_integral`, `U_nonneg`, `U_two_n_pos`, `Z_integral`) — there the same facts are proved
for the jets `U = (-1)^n C_n a_j`, `V = (-1)^n C_n b_j` (`coeffJet`, `hyp_readout.lean`);
`Pfq54_aux.lean` (`harm_int`, `mul_choose_dvd_lcm`, `lcm_dvd_lcm`).
-/
import Meijer5255.definitions
import Meijer5255.BaselineIntegrality_Aux

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.BaselineIntegrality

open Meijer5255

/-! ### Objects -/

/-- The integer-valued polynomial `P(t) = ∏_{u=0}^{2} C(t-un-1, 10n)`, i.e. the numerator of
`F_n` divided by `(10n)!³` (its roots are `numRoots n = [1,10n] ∪ [n+1,11n] ∪ [2n+1,12n]`). -/
def Pbin (n : ℕ) : ℚ[X] := C ((((10 * n).factorial : ℚ) ^ 3)⁻¹) * rootPoly (numRoots n)

/-- The residue `ρ_c(j) = (-1)^{j-c} C(15n, j-c)` of `L_c(t) = (15n)!/∏_{k=c}^{c+15n}(t+k)` at
`t = -j`, and `0` if `j ∉ [c, c+15n]`. -/
def rho (n c j : ℕ) : ℤ :=
  if c ≤ j ∧ j ≤ c + 15 * n then (-1) ^ (j - c) * ((15 * n).choose (j - c) : ℤ) else 0

/-- The value at `t = -j` of the part of `L_c` regular at `-j`:
`σ_c(j) = ∑_{k ∈ [c, c+15n], k ≠ j} ρ_c(k)/(k-j)`. -/
def sig (n c j : ℕ) : ℚ :=
  ∑ k ∈ (Icc c (c + 15 * n)).erase j, (rho n c k : ℚ) / ((k : ℚ) - j)

/-- Glue: `rho`, `sig` agree with their copies in the helper module. -/
private theorem rho_eq (n c j : ℕ) : rho n c j = Aux.rhoA n c j := rfl

private theorem sig_eq (n c j : ℕ) : sig n c j = Aux.sigA n c j := rfl

/-- Glue: the numerator polynomial is `(10n)!³ P`. -/
private theorem rootPoly_numRoots_eq (n : ℕ) :
    rootPoly (numRoots n) = C (((10 * n).factorial : ℚ) ^ 3) * Pbin n := by
  rw [Pbin, ← mul_assoc, ← C_mul, mul_inv_cancel₀ (by positivity), C_1, one_mul]

/-- Glue: `ρ_c(j) e_c = (15n)!` on the support, with `e_c = ∏_{k ≠ j} (k - j)`. -/
private theorem rho_mul_eval (n c j : ℕ) (h : c ≤ j ∧ j ≤ c + 15 * n) :
    (rho n c j : ℚ) * (Aux.Qp (Icc c (c + 15 * n)) j).eval (-(j : ℚ)) =
      ((15 * n).factorial : ℚ) := by
  rw [rho_eq, Aux.Qp_eval]; exact Aux.rho_mul_e n c j h.1 h.2

private theorem rho_zero (n c j : ℕ) (h : ¬ (c ≤ j ∧ j ≤ c + 15 * n)) : rho n c j = 0 := by
  unfold rho; exact ite_eq_right h

/-- Glue: `pfCoeff` of `F_n` at `-j`, with the numerator `(10n)!³ P` and the denominator
re-paired as `Q_n Q_{2n}`, `Q_c = ∏_{k ∈ [c,c+15n] \ {j}} (X + k)`. -/
private theorem pfCoeff_eq (n j : ℕ) :
    pfCoeff (numRoots n) (denRoots n) (-(j : ℤ)) =
      let N := C (((10 * n).factorial : ℚ) ^ 3) * Pbin n
      let E := Aux.Qp (Icc n (n + 15 * n)) j * Aux.Qp (Icc (2 * n) (2 * n + 15 * n)) j
      if (if n ≤ j ∧ j ≤ n + 15 * n then 1 else 0) +
          (if 2 * n ≤ j ∧ j ≤ 2 * n + 15 * n then 1 else 0) = 2 then
        (N.eval (-(j : ℚ)) / E.eval (-(j : ℚ)),
          (derivative N * E - N * derivative E).eval (-(j : ℚ)) / E.eval (-(j : ℚ)) ^ 2)
      else if (if n ≤ j ∧ j ≤ n + 15 * n then 1 else 0) +
          (if 2 * n ≤ j ∧ j ≤ 2 * n + 15 * n then 1 else 0) = 1 then
        (0, N.eval (-(j : ℚ)) / E.eval (-(j : ℚ)))
      else (0, 0) := by
  unfold pfCoeff
  rw [Aux.rootPoly_den_filter, Aux.denRoots_count, rootPoly_numRoots_eq]
  push_cast
  rfl

/-! ### Supporting lemmas -/

/-- **[1] `P` at the poles.** `P(-j) = ∏_{u=0}^{2} C(j+un+10n, 10n)`: each factor is
`C(-j-un-1, 10n) = (-1)^{10n} C(j+un+10n, 10n)`, and `(-1)^{30n} = 1`.
* Proved (≈ 8 lines; `Aux.rootPoly_numRoots`, `Aux.G_eval`).
* Directly from the PDF: yes ("`P` is integer-valued on integers"). -/
theorem Pbin_eval_neg (n j : ℕ) :
    (Pbin n).eval (-(j : ℚ)) = ∏ u ∈ range 3, (((j + u * n + 10 * n).choose (10 * n) : ℕ) : ℚ) := by
  have hF : ((10 * n).factorial : ℚ) ≠ 0 := by positivity
  have hs : (-1 : ℚ) ^ (10 * n) = 1 := Even.neg_one_pow ⟨5 * n, by ring⟩
  rw [Pbin, eval_mul, eval_C, Aux.rootPoly_numRoots, eval_mul, eval_mul, Aux.G_eval, Aux.G_eval,
    Aux.G_eval, hs]
  simp only [prod_range_succ, prod_range_zero, one_mul, zero_mul, add_zero]
  field_simp

/-- **[2] The derivative of `P` is cleared by `d_{10n}`.** `d_{10n} P'(-j) ∈ ℤ`: by the
Newton-basis identity `C(x,m)' = ∑_{i=1}^{m} (-1)^{i-1} C(x, m-i)/i` each factor has
`d_{10n} C(·,10n)'` integral at integers, and the product rule.
* Proved (≈ 25 lines; `Aux.G_deriv_int`: log-derivative of `G` and `k C(n,k) ∣ d_n`).
* Directly from the PDF: yes ("apply the Newton-basis identity … and use the product rule"). -/
theorem dPbin_int (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ∃ z : ℤ, (dlcm (10 * n) : ℚ) * (derivative (Pbin n)).eval (-(j : ℚ)) = z := by
  have hs : (-1 : ℚ) ^ (10 * n) = 1 := Even.neg_one_pow ⟨5 * n, by ring⟩
  have hF : ((10 * n).factorial : ℚ) ≠ 0 := by positivity
  obtain ⟨z0, hz0⟩ := Aux.G_deriv_int 0 (10 * n) j (10 * n) le_rfl
  obtain ⟨z1, hz1⟩ := Aux.G_deriv_int n (10 * n) j (10 * n) le_rfl
  obtain ⟨z2, hz2⟩ := Aux.G_deriv_int (2 * n) (10 * n) j (10 * n) le_rfl
  have hv0 := Aux.G_eval 0 (10 * n) j
  have hv1 := Aux.G_eval n (10 * n) j
  have hv2 := Aux.G_eval (2 * n) (10 * n) j
  rw [hs, one_mul] at hv0 hv1 hv2
  refine ⟨z0 * (j + n + 10 * n).choose (10 * n) * (j + 2 * n + 10 * n).choose (10 * n) +
    (j + 0 + 10 * n).choose (10 * n) * z1 * (j + 2 * n + 10 * n).choose (10 * n) +
    (j + 0 + 10 * n).choose (10 * n) * (j + n + 10 * n).choose (10 * n) * z2, ?_⟩
  rw [Pbin, Aux.rootPoly_numRoots, derivative_C_mul, derivative_mul, derivative_mul]
  simp only [eval_mul, eval_add, eval_C]
  rw [hv0, hv1, hv2]
  push_cast
  field_simp
  linear_combination (((j + n + 10 * n).choose (10 * n) : ℚ) *
      ((j + 2 * n + 10 * n).choose (10 * n) : ℚ)) * hz0 +
    (((j + 0 + 10 * n).choose (10 * n) : ℚ) *
      ((j + 2 * n + 10 * n).choose (10 * n) : ℚ)) * hz1 +
    (((j + 0 + 10 * n).choose (10 * n) : ℚ) *
      ((j + n + 10 * n).choose (10 * n) : ℚ)) * hz2

/-- **[3] Sign of the double coefficients.** `(-1)^n ρ_n(j) ρ_{2n}(j) ≥ 0` for every `j`
(it is `0` or `(-1)^{n + (j-n) + (j-2n)} C(15n, j-n) C(15n, j-2n) = C C`), and at `j = 2n` it is
`C(15n, n) > 0`.
* Proved (≈ 20 lines).
* Directly from the PDF: no (the paper does not state positivity; it is immediate from the
  closed form of `a_j`). -/
theorem rho_sign (n : ℕ) :
    (∀ j, 0 ≤ (-1 : ℤ) ^ n * (rho n n j * rho n (2 * n) j)) ∧
      0 < (-1 : ℤ) ^ n * (rho n n (2 * n) * rho n (2 * n) (2 * n)) := by
  refine ⟨fun j => ?_, ?_⟩
  · unfold rho
    split_ifs with h1 h2 h2
    · have e : (-1 : ℤ) ^ n * ((-1) ^ (j - n) * ((15 * n).choose (j - n) : ℤ) *
          ((-1) ^ (j - 2 * n) * ((15 * n).choose (j - 2 * n) : ℤ))) =
          ((-1) ^ 2) ^ (j - n) * (((15 * n).choose (j - n) : ℤ) * (15 * n).choose (j - 2 * n)) := by
        rw [← pow_mul, show 2 * (j - n) = n + (j - n) + (j - 2 * n) by omega, pow_add, pow_add]
        ring
      rw [e]; norm_num; positivity
    all_goals simp
  · unfold rho
    rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨le_rfl, by omega⟩, show 2 * n - n = n by omega,
      Nat.sub_self, pow_zero, Nat.choose_zero_right]
    have hc : 0 < ((15 * n).choose n : ℤ) := by exact_mod_cast Nat.choose_pos (by omega)
    have h2 : (-1 : ℤ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
    calc (0 : ℤ) < (15 * n).choose n := hc
      _ = _ := by push_cast; linear_combination (-((15 * n).choose n : ℤ)) * h2

/-- **[4] The double-pole coefficients.** `C_n a_j = P(-j) ρ_n(j) ρ_{2n}(j)` for every `j`.
Proof: `C_n F_n = P L_n L_{2n}` (re-pairing `[n,17n] + [2n,16n] = [n,16n] + [2n,17n]`, and
`(15n)!²/(10n)!³ · ∏(t - x)_{numRoots} = (15n)!² P`); at a common pole `-j` the factor
`(t+j)²` is split off and `pfCoeff`'s `N/E` at `-j` is `P(-j) · (15n)!/∏_{k≠j}(k-j)` twice, the
residues `ρ_c(j)`; at a non-common pole or a non-pole both sides vanish.
* Proved (≈ 21 lines; glue `pfCoeff_eq`, `Aux.rootPoly_den_filter`, `Aux.rho_mul_e`).
* Directly from the PDF: yes ("`C_nF_n = P L_n L_{2n}`", "`L_c` has integer residues"). -/
theorem aCoef_formula (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    Cn n * aCoef n j = (Pbin n).eval (-(j : ℚ)) * ((rho n n j : ℚ) * rho n (2 * n) j) := by
  rw [aCoef, pfCoeff_eq]
  dsimp only
  have hK : ((10 * n).factorial : ℚ) ≠ 0 := by positivity
  have he1 := Aux.Qp_eval_ne_zero (Icc n (n + 15 * n)) j
  have he2 := Aux.Qp_eval_ne_zero (Icc (2 * n) (2 * n + 15 * n)) j
  by_cases h1 : n ≤ j ∧ j ≤ n + 15 * n <;> by_cases h2 : 2 * n ≤ j ∧ j ≤ 2 * n + 15 * n
  · rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left (by norm_num)]
    have r1 : (rho n n j : ℚ) = ((15 * n).factorial : ℚ) /
        (Aux.Qp (Icc n (n + 15 * n)) j).eval (-(j : ℚ)) := by
      rw [eq_div_iff he1]; exact rho_mul_eval n n j h1
    have r2 : (rho n (2 * n) j : ℚ) = ((15 * n).factorial : ℚ) /
        (Aux.Qp (Icc (2 * n) (2 * n + 15 * n)) j).eval (-(j : ℚ)) := by
      rw [eq_div_iff he2]; exact rho_mul_eval n (2 * n) j h2
    simp only [eval_mul, eval_C]
    rw [r1, r2, Cn]
    field_simp
  · simp [h1, h2, rho_zero n (2 * n) j h2]
  · simp [h1, h2, rho_zero n n j h1]
  · simp [h1, h2, rho_zero n n j h1]

/-- **[5] The simple-pole coefficients.**
`C_n b_j = P'(-j) ρ_n(j) ρ_{2n}(j) + P(-j) (ρ_n(j) σ_{2n}(j) + ρ_{2n}(j) σ_n(j))` for every `j`.
Proof: near `t = -j`, `L_c(t) = ρ_c(j)/(t+j) + R_c(t)` with `R_c(-j) = σ_c(j)` (partial fractions
of `L_c`); multiply out `P L_n L_{2n}` and read the `(t+j)⁻¹` coefficient.  At a simple pole
(`n ≤ j < 2n` or `16n < j ≤ 17n`) one `ρ` vanishes and only `P(-j) ρ σ` survives; `pfCoeff`'s
`(N/E)'(x)` resp. `(N/E₁)(x)` is identified with this expansion.
* Proved (≈ 57 lines; `Aux.sig_mul_e_in` / `Aux.sig_mul_e_out` from the Lagrange identity
  `Aux.lagrange_id`).
* Directly from the PDF: yes ("its simple coefficient is a sum of an integer multiple of `P'(-j)`
  and terms with integer numerator and denominator `j-k`"). -/
theorem bCoef_formula (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    Cn n * bCoef n j =
      (derivative (Pbin n)).eval (-(j : ℚ)) * ((rho n n j : ℚ) * rho n (2 * n) j) +
        (Pbin n).eval (-(j : ℚ)) * ((rho n n j : ℚ) * sig n (2 * n) j +
          (rho n (2 * n) j : ℚ) * sig n n j) := by
  rw [bCoef, pfCoeff_eq]
  dsimp only
  have hK : ((10 * n).factorial : ℚ) ≠ 0 := by positivity
  have he1 := Aux.Qp_eval_ne_zero (Icc n (n + 15 * n)) j
  have he2 := Aux.Qp_eval_ne_zero (Icc (2 * n) (2 * n + 15 * n)) j
  have r1 : n ≤ j ∧ j ≤ n + 15 * n → (rho n n j : ℚ) = ((15 * n).factorial : ℚ) /
      (Aux.Qp (Icc n (n + 15 * n)) j).eval (-(j : ℚ)) := fun h1 => by
    rw [eq_div_iff he1]; exact rho_mul_eval n n j h1
  have r2 : 2 * n ≤ j ∧ j ≤ 2 * n + 15 * n → (rho n (2 * n) j : ℚ) = ((15 * n).factorial : ℚ) /
      (Aux.Qp (Icc (2 * n) (2 * n + 15 * n)) j).eval (-(j : ℚ)) := fun h2 => by
    rw [eq_div_iff he2]; exact rho_mul_eval n (2 * n) j h2
  by_cases h1 : n ≤ j ∧ j ≤ n + 15 * n <;> by_cases h2 : 2 * n ≤ j ∧ j ≤ 2 * n + 15 * n
  · -- double pole: `(N/E)'(-j)`
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left (by norm_num)]
    have s1 : sig n n j = -(rho n n j : ℚ) *
        (derivative (Aux.Qp (Icc n (n + 15 * n)) j)).eval (-(j : ℚ)) /
          (Aux.Qp (Icc n (n + 15 * n)) j).eval (-(j : ℚ)) := by
      rw [eq_div_iff he1, sig_eq, rho_eq]; exact Aux.sig_mul_e_in n n j h1.1 h1.2
    have s2 : sig n (2 * n) j = -(rho n (2 * n) j : ℚ) *
        (derivative (Aux.Qp (Icc (2 * n) (2 * n + 15 * n)) j)).eval (-(j : ℚ)) /
          (Aux.Qp (Icc (2 * n) (2 * n + 15 * n)) j).eval (-(j : ℚ)) := by
      rw [eq_div_iff he2, sig_eq, rho_eq]; exact Aux.sig_mul_e_in n (2 * n) j h2.1 h2.2
    rw [derivative_C_mul, derivative_mul]
    simp only [eval_mul, eval_C, eval_sub, eval_add]
    rw [s1, s2, r1 h1, r2 h2, Cn]
    field_simp
    ring
  · -- simple pole with `j ∉ [2n, 17n]`
    rw [ite_eq_left h1, ite_eq_right h2]
    simp only [show (1 : ℕ) + 0 = 1 from rfl, show (1 : ℕ) ≠ 2 by norm_num, ite_false, ite_true]
    have s2 : sig n (2 * n) j = ((15 * n).factorial : ℚ) /
        (Aux.Qp (Icc (2 * n) (2 * n + 15 * n)) j).eval (-(j : ℚ)) := by
      rw [eq_div_iff he2, sig_eq]; exact Aux.sig_mul_e_out n (2 * n) j h2
    rw [rho_zero n (2 * n) j h2]
    simp only [eval_mul, eval_C]
    rw [s2, r1 h1, Cn]
    push_cast
    field_simp
    ring
  · -- simple pole with `j ∉ [n, 16n]`
    rw [ite_eq_right h1, ite_eq_left h2]
    simp only [show (0 : ℕ) + 1 = 1 from rfl, show (1 : ℕ) ≠ 2 by norm_num, ite_false, ite_true]
    have s1 : sig n n j = ((15 * n).factorial : ℚ) /
        (Aux.Qp (Icc n (n + 15 * n)) j).eval (-(j : ℚ)) := by
      rw [eq_div_iff he1, sig_eq]; exact Aux.sig_mul_e_out n n j h1
    rw [rho_zero n n j h1]
    simp only [eval_mul, eval_C]
    rw [s1, r2 h2, Cn]
    push_cast
    field_simp
    ring
  · simp [h1, h2, rho_zero n n j h1, rho_zero n (2 * n) j h2]

/-- **[6] The regular parts are cleared by `d_{16n}`.** For `c ∈ {n, 2n}` and `n ≤ j ≤ 17n`:
`d_{16n} σ_c(j) ∈ ℤ`, since every `k ∈ [c, c+15n] \ {j}` has `0 < |k - j| ≤ 16n`, so
`(k - j) ∣ d_{16n}`.
* Proved (≈ 23 lines).
* Directly from the PDF: yes ("All such differences satisfy `0 < |j-k| ≤ 16n`"). -/
theorem sig_int (n : ℕ) (hn : 1 ≤ n) (c j : ℕ) (hc : c = n ∨ c = 2 * n) (hj1 : n ≤ j)
    (hj2 : j ≤ 17 * n) :
    ∃ z : ℤ, (dlcm (16 * n) : ℚ) * sig n c j = z := by
  have key : ∀ k ∈ (Icc c (c + 15 * n)).erase j,
      ∃ z : ℤ, (dlcm (16 * n) : ℚ) * ((rho n c k : ℚ) / ((k : ℚ) - j)) = z := fun k hk => by
    have hkj := ne_of_mem_erase hk
    have hk' := mem_Icc.mp (mem_of_mem_erase hk)
    set δ : ℤ := (k : ℤ) - j
    have hδ : δ.natAbs ∈ Icc 1 (16 * n) := by
      simp only [mem_Icc, δ]; rcases hc with rfl | rfl <;> omega
    have hdvd : δ ∣ (dlcm (16 * n) : ℤ) :=
      Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (Finset.dvd_lcm (f := id) hδ))
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨rho n c k * q, ?_⟩
    have hq' : (dlcm (16 * n) : ℚ) = ((k : ℚ) - j) * q := by
      have := congrArg (fun z : ℤ => (z : ℚ)) hq
      push_cast [δ] at this; exact this
    have hne : (k : ℚ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hkj)
    rw [hq']; push_cast; field_simp
  choose! f hf using key
  refine ⟨∑ k ∈ (Icc c (c + 15 * n)).erase j, f k, ?_⟩
  rw [sig, mul_sum]; push_cast
  exact sum_congr rfl hf

/-- **[7] Harmonic numbers are cleared by `d_M^s`.** For `m ≤ M`: `d_M^s H^{(s)}_m ∈ ℤ`, since
`d_M^s H^{(s)}_m = ∑_{k ≤ m} (d_M / k)^s`.
* Proved (≈ 3 lines; pfq54 `harm_integral`, copied to `Aux.harm_int`).
* Directly from the PDF: yes ("the harmonic numbers of order `s` are cleared by `d_{19n}^s`"). -/
theorem harm_int (s m M : ℕ) (h : m ≤ M) : ∃ z : ℤ, (dlcm M : ℚ) ^ s * harm s m = z :=
  -- pfq54 `Z_integral.lean`, `harm_integral` (copied into the helper module)
  Aux.harm_int s m M h

/-! ### The node -/

/-- **Uniform denominator bound** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[7] and `Finset.lcm_mono`. -/
theorem baseline_integrality (n : ℕ) (hn : 1 ≤ n) :
    (∀ j, ∃ z : ℤ, Cn n * aCoef n j = z) ∧
      (∀ j, ∃ z : ℤ, (dlcm (16 * n) : ℚ) * Cn n * bCoef n j = z) ∧
      (∀ i, ∃ z : ℤ, Z3v n i = z) ∧ (∀ i, ∃ z : ℤ, Z4v n i = z) ∧ 0 < (-1) ^ n * Q n := by
  -- the subring `ℤ ⊂ ℚ`
  set R := (Int.castRingHom ℚ).range
  have mem : ∀ x : ℚ, (∃ z : ℤ, x = z) → x ∈ R := fun x ⟨z, hz⟩ => ⟨z, hz.symm⟩
  have out : ∀ x : ℚ, x ∈ R → ∃ z : ℤ, x = z := fun x ⟨z, hz⟩ => ⟨z, hz.symm⟩
  have hk : ∀ k : ℕ, (k : ℚ) ∈ R := fun k => ⟨k, map_natCast _ _⟩
  have hz : ∀ k : ℤ, (k : ℚ) ∈ R := fun k => ⟨k, rfl⟩
  -- `d_{10n} ∣ d_{16n} ∣ d_{19n}`
  obtain ⟨m1, hm1⟩ : dlcm (10 * n) ∣ dlcm (16 * n) :=
    Finset.lcm_mono (Finset.Icc_subset_Icc_right (by omega))
  obtain ⟨m2, hm2⟩ : dlcm (16 * n) ∣ dlcm (19 * n) :=
    Finset.lcm_mono (Finset.Icc_subset_Icc_right (by omega))
  have hm1q : (dlcm (16 * n) : ℚ) = dlcm (10 * n) * m1 := by rw [hm1]; push_cast; ring
  have hm2q : (dlcm (19 * n) : ℚ) = dlcm (16 * n) * m2 := by rw [hm2]; push_cast; ring
  -- `P(-j) ∈ ℤ`
  have hP : ∀ j : ℕ, (Pbin n).eval (-(j : ℚ)) ∈ R := fun j => by
    rw [Pbin_eval_neg]; exact R.prod_mem fun u _ => hk _
  -- the double-pole coefficients
  have ha : ∀ j, Cn n * aCoef n j ∈ R := fun j => by
    rw [aCoef_formula n hn j]; exact R.mul_mem (hP j) (R.mul_mem (hz _) (hz _))
  -- outside `[n, 17n]` there is no pole
  have hout : ∀ j, ¬ (n ≤ j ∧ j ≤ 17 * n) → rho n n j = 0 ∧ rho n (2 * n) j = 0 :=
    fun j hj => by
      unfold rho
      exact ⟨ite_eq_right_iff.2 fun h => absurd h (by omega),
        ite_eq_right_iff.2 fun h => absurd h (by omega)⟩
  -- the simple-pole coefficients
  have hb : ∀ j, (dlcm (16 * n) : ℚ) * Cn n * bCoef n j ∈ R := fun j => by
    rw [mul_assoc, bCoef_formula n hn j]
    by_cases hj : n ≤ j ∧ j ≤ 17 * n
    · obtain ⟨z1, hz1⟩ := dPbin_int n hn j
      obtain ⟨z2, hz2⟩ := sig_int n hn n j (Or.inl rfl) hj.1 hj.2
      obtain ⟨z3, hz3⟩ := sig_int n hn (2 * n) j (Or.inr rfl) hj.1 hj.2
      have e : (dlcm (16 * n) : ℚ) *
          ((derivative (Pbin n)).eval (-(j : ℚ)) * ((rho n n j : ℚ) * rho n (2 * n) j) +
            (Pbin n).eval (-(j : ℚ)) * ((rho n n j : ℚ) * sig n (2 * n) j +
              (rho n (2 * n) j : ℚ) * sig n n j)) =
          (m1 : ℚ) * ((dlcm (10 * n) : ℚ) * (derivative (Pbin n)).eval (-(j : ℚ))) *
              ((rho n n j : ℚ) * rho n (2 * n) j) +
            (Pbin n).eval (-(j : ℚ)) * ((rho n n j : ℚ) * ((dlcm (16 * n) : ℚ) * sig n (2 * n) j) +
              (rho n (2 * n) j : ℚ) * ((dlcm (16 * n) : ℚ) * sig n n j)) := by
        rw [hm1q]; ring
      rw [e, hz1, hz2, hz3]
      exact R.add_mem (R.mul_mem (R.mul_mem (hk _) (hz _)) (R.mul_mem (hz _) (hz _)))
        (R.mul_mem (hP j) (R.add_mem (R.mul_mem (hz _) (hz _)) (R.mul_mem (hz _) (hz _))))
    · obtain ⟨h1, h2⟩ := hout j hj
      rw [h1, h2]
      simp
  -- the harmonic numbers
  have hH : ∀ s j, j ∈ Icc n (17 * n) → (dlcm (19 * n) : ℚ) ^ s * harm s (j + 2 * n) ∈ R :=
    fun s j hj => mem _ (harm_int s (j + 2 * n) (19 * n) (by simp only [mem_Icc] at hj; omega))
  have hd : (dlcm (19 * n) : ℚ) ∈ R := hk _
  -- the three readouts, with `d^r`, `r ≥ 3`
  have hQ : ∀ r : ℕ, 6 * Cn n * (dlcm (19 * n) : ℚ) ^ r * Q n ∈ R := fun r => by
    rw [Q, Finset.mul_sum]
    refine R.sum_mem fun j _ => ?_
    rw [show 6 * Cn n * (dlcm (19 * n) : ℚ) ^ r * aCoef n j =
      6 * (dlcm (19 * n) : ℚ) ^ r * (Cn n * aCoef n j) by ring]
    exact R.mul_mem (R.mul_mem (hk 6) (R.pow_mem hd r)) (ha j)
  have hP3 : ∀ r : ℕ, 6 * Cn n * (dlcm (19 * n) : ℚ) ^ (r + 3) * P3 n ∈ R := fun r => by
    rw [P3, Finset.mul_sum]
    refine R.sum_mem fun j hj => ?_
    have e : 6 * Cn n * (dlcm (19 * n) : ℚ) ^ (r + 3) *
        (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2) =
        6 * (dlcm (19 * n) : ℚ) ^ r * (Cn n * aCoef n j) *
            ((dlcm (19 * n) : ℚ) ^ 3 * harm 3 (j + 2 * n)) +
          3 * (dlcm (19 * n) : ℚ) ^ r * (m2 : ℚ) * ((dlcm (16 * n) : ℚ) * Cn n * bCoef n j) *
            ((dlcm (19 * n) : ℚ) ^ 2 * harm 2 (j + 2 * n)) := by
      linear_combination (3 * (dlcm (19 * n) : ℚ) ^ (r + 2) * Cn n * bCoef n j *
        harm 2 (j + 2 * n)) * hm2q
    rw [e]
    exact R.add_mem (R.mul_mem (R.mul_mem (R.mul_mem (hk 6) (R.pow_mem hd r)) (ha j))
        (hH 3 j hj))
      (R.mul_mem (R.mul_mem (R.mul_mem (R.mul_mem (hk 3) (R.pow_mem hd r)) (hk m2)) (hb j))
        (hH 2 j hj))
  have hP4 : 6 * Cn n * (dlcm (19 * n) : ℚ) ^ 4 * P4 n ∈ R := by
    rw [P4, Finset.mul_sum]
    refine R.sum_mem fun j hj => ?_
    have e : 6 * Cn n * (dlcm (19 * n) : ℚ) ^ 4 *
        (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3) =
        6 * (Cn n * aCoef n j) * ((dlcm (19 * n) : ℚ) ^ 4 * harm 4 (j + 2 * n)) +
          2 * (m2 : ℚ) * ((dlcm (16 * n) : ℚ) * Cn n * bCoef n j) *
            ((dlcm (19 * n) : ℚ) ^ 3 * harm 3 (j + 2 * n)) := by
      linear_combination (2 * (dlcm (19 * n) : ℚ) ^ 3 * Cn n * bCoef n j *
        harm 3 (j + 2 * n)) * hm2q
    rw [e]
    exact R.add_mem (R.mul_mem (R.mul_mem (hk 6) (ha j)) (hH 4 j hj))
      (R.mul_mem (R.mul_mem (R.mul_mem (hk 2) (hk m2)) (hb j)) (hH 3 j hj))
  refine ⟨fun j => out _ (ha j), fun j => out _ (hb j), fun i => ?_, fun i => ?_, ?_⟩
  · fin_cases i
    · exact out _ (hQ 3)
    · exact out _ (hP3 0)
  · fin_cases i
    · exact out _ (hQ 4)
    · exact out _ (hP3 1)
    · exact out _ hP4
  -- positivity
  · have hC : 0 < Cn n := by unfold Cn; positivity
    have hsum : (-1) ^ n * Q n = ∑ j ∈ Icc n (17 * n), (Pbin n).eval (-(j : ℚ)) *
        (((-1 : ℤ) ^ n * (rho n n j * rho n (2 * n) j) : ℤ) : ℚ) / Cn n := by
      rw [Q, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [eq_div_iff hC.ne', ← mul_assoc, mul_comm _ (Cn n), ← mul_assoc, mul_comm (Cn n),
        mul_assoc, aCoef_formula n hn j]
      push_cast; ring
    rw [hsum]
    obtain ⟨hs0, hs1⟩ := rho_sign n
    refine Finset.sum_pos' (fun j _ => div_nonneg (mul_nonneg ?_ ?_) hC.le) ⟨2 * n, ?_, ?_⟩
    · rw [Pbin_eval_neg]; positivity
    · exact_mod_cast hs0 j
    · simp only [mem_Icc]; omega
    · refine div_pos (mul_pos ?_ ?_) hC
      · rw [Pbin_eval_neg]
        exact Finset.prod_pos fun u _ => by exact_mod_cast Nat.choose_pos (by omega)
      · exact_mod_cast hs1

end Meijer5255.BaselineIntegrality
