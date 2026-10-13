/-
# Blueprint: improved arithmetic for `A ζ(3) + B ζ(4)` along the MeijerG(5,2,5,5,1) trajectory

This file is a Lean blueprint of
  `results/meijerg5255_improved/meijerg_zeta3_zeta4_improved.tex`
  ("CMF conservation and the arithmetic of `Aζ(3)+Bζ(4)`; the trajectory
  `(16,17,-11,-12,-10;2,1,0,-1,-2)`"),
following the plan in `LEAN_HANDOFF.md` (repository root).

It depends on Mathlib only (pinned in `lean/lake-manifest.json`) and is checked with
  `lake build`  or  `lake env lean Meijer5255/Blueprint_5255.lean`
from the `lean/` directory.

**Main theorem** (`main_joint`, `main_pure3`). For integers `(A,B) ≠ (0,0)`,
`liminf_N δ_N(A,B) > 0.01634832`, and `liminf_N δ_N(A,0) > 0.22626234` if `A ≠ 0`.
Here `δ_N` is defined literally as in the paper, from the native CMF product `W_n` (`n = N - 1`)
along the paper's block path and the initial-condition matrix `R_{A,B}`.

Structure (following the paper):

* §1  Zeta values, the native CMF, the block path `W_n`, the approximants and `δ_N`.
* §2  The rational kernel `F_n`, its partial fractions, and the readouts `Q_n, P_{3,n}, P_{4,n}`.
* §3  The CMF readout identity (paper §3).
* §4  Integrality and the baseline carry profile (paper §§4–5, appendix table).
* §5  First-order shells (paper §§6–7).
* §6  The second-order trace lemma and its application (paper §§8–9).
* §7  The improved divisor `G_n^{new}` and its density (paper §10).
* §8  The analytic input (paper §1) and the final inequality (paper §11).

**Blueprint nodes.** There are 19 `theorem`s (no `lemma`s). Each docstring records whether the
paper proves the node (`From the manuscript: yes / partially / no`), how, and what to reuse.
* Proved here (logical glue, from the other nodes): `approxCMF_eq`, `delta_criterion`,
  `eventual_delta`, `main_joint`, `main_pure3`.
* Proved in their own node files `Meijer5255/<Node>.lean` (each from at most 10 supporting
  lemmas) and re-exported here: `cmf_readout`, `baseline_integrality`, `carry_facts`,
  `baseline_profile`, `shell_first_order`, `trace_lemma`, `window_root_data`, `window_readout`,
  `second_order_shell` (`SecondOrderShell.lean`), `Gnew_dvd`, `log_Gnew_ge`,
  `log_normalization_le`, `Q_growth`, `linform_error`.
* All definitions live in `Meijer5255/definitions.lean`.

Everything is stated about explicitly defined objects (finite products of explicit `4×4` rational
matrices, finite sums of explicit partial-fraction coefficients, factorials, `lcm`s, finite
products of primes). The analytic input (growth `a`, decay `b`) is stated as two nodes
(`Q_growth`, `linform_error`); it is proved in `../zetas_irr/blueprints` (see `LEAN_HANDOFF.md`
§5.8–5.9). The prime number theorem enters only through `log_normalization_le` and
`log_Gnew_ge`.
-/
import Meijer5255.definitions
import Meijer5255.CmfReadout
import Meijer5255.BaselineIntegrality
import Meijer5255.CarryFacts
import Meijer5255.BaselineProfile
import Meijer5255.ShellFirstOrder
import Meijer5255.SecondOrderShell
import Meijer5255.GnewDvd
import Meijer5255.LogGnewGe
import Meijer5255.LogNormalizationLe
import Meijer5255.QGrowth
import Meijer5255.LinformError

open Filter Topology Finset
open scoped Matrix

noncomputable section

namespace Meijer5255

/-! ## §3. The CMF readout identity (paper §3) -/

/-- **CMF readout** (paper §3). `Q_n = (-1)^n (W_n)₀₀`, `(W_n)₁₀ = 0`,
`P_{3,n} = (-1)^n (-(W_n)₂₀/2 + (W_n)₃₀/4)`, `P_{4,n} = (-1)^n (-(W_n)₃₀/6)`.
Proof: transport of the moment functionals `Lfun` (`∫ K₂ f/(2πi)`), `Mfun` (`∫ K₃ f/(2πi)`),
and the two rational functionals (sums of double / simple pole coefficients) along the block path,
starting from `R_{w₀} = t⁻²` with initial rows `(2ζ3, -ζ2, 1, -1/2)`, `(6ζ4, -2ζ3, 0, 1)`,
`(1,0,0,0)`, `(0,-1,0,0)`; companion relations at each vertex (zero of order `≥ 3` of
`∏(t+bⱼ) R_w` at `0`, resp. `2n` after moving the cutoff across the triple zeros `1..10n`);
endpoint `R_{w_n} = (-1)^n F_n`; read off the `Z₃, Z₂, Z₀` and `Z₄, Z₀` coefficients.
Reuse: zeta34 `CMF_basic`, `CMF_transport`, `CMF_path`; pfq54 `star_aux`.
Checked numerically for `n ≤ 3` against the definitions of this file.
* From the manuscript: yes (§3, "Proof by the CMF mechanism"). -/
theorem cmf_readout (n : ℕ) :
    Q n = (-1) ^ n * W n 0 0 ∧ W n 1 0 = 0 ∧
      P3 n = (-1) ^ n * (-(W n 2 0) / 2 + W n 3 0 / 4) ∧
      P4 n = (-1) ^ n * (-(W n 3 0) / 6) := by
  exact CmfReadout.cmf_readout n

/-- **The approximant** (paper §3, "Consequently"). `r_N(A,B) = (A P_{3,n} + B P_{4,n}) / Q_n`,
since `R_{A,B} W_n e₀ = 12 (-1)^n (A P_{3,n} + B P_{4,n}, Q_n)`.
* From the manuscript: yes. Proved here from `cmf_readout`. -/
theorem approxCMF_eq (n : ℕ) (A B : ℤ) :
    approxCMF n A B = (A * P3 n + B * P4 n) / Q n := by
  obtain ⟨h0, -, h3, h4⟩ := cmf_readout n
  have hs : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have e0 : (readoutMat A B *ᵥ (W n *ᵥ Pi.single 0 1)) 0 =
      (12 * (-1) ^ n) * (A * P3 n + B * P4 n) := by
    simp [readoutMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (-12 * (-1 : ℚ) ^ n * A) * h3 + (-12 * (-1 : ℚ) ^ n * B) * h4 -
      (-6 * A * W n 2 0 + (3 * A - 2 * B) * W n 3 0) * hs
  have e1 : (readoutMat A B *ᵥ (W n *ᵥ Pi.single 0 1)) 1 = (12 * (-1) ^ n) * Q n := by
    simp [readoutMat, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
    linear_combination (-12 * (-1 : ℚ) ^ n) * h0 - 12 * W n 0 0 * hs
  show (readoutMat A B *ᵥ (W n *ᵥ Pi.single 0 1)) 0 /
    (readoutMat A B *ᵥ (W n *ᵥ Pi.single 0 1)) 1 = _
  rw [e0, e1, mul_div_mul_left _ _ (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))]

/-! ## §4. Integrality and the baseline carry profile (paper §§4–5) -/

/-- **Uniform denominator bound** (paper §4). For `n ≥ 1`: `C_n a_j ∈ ℤ`, `d_{16n} C_n b_j ∈ ℤ`,
hence `6 C_n d_{19n}³ (Q_n, P_{3,n}) ∈ ℤ²` and `6 C_n d_{19n}⁴ (Q_n, P_{3,n}, P_{4,n}) ∈ ℤ³`.
Moreover `(-1)^n Q_n > 0` (all `(-1)^n C_n a_j ≥ 0`, and the one at `j = 2n` is positive).
Proof: `C_n F_n = P(t) L_n(t) L_{2n}(t)` with `P = ∏ C(t-un-1, 10n)` integer valued, `d_{10n} P'`
integral, `L_c` with residues `±C(15n, j-c)`; `d_{19n}^s H^{(s)}_m ∈ ℤ` for `m ≤ 19n`.
Reuse: pfq54 `Z_integral` (via `Qa = (-1)^n S0 / Cn`, …).
* From the manuscript: yes (positivity: no, but immediate from the closed form of `a_j`). -/
theorem baseline_integrality (n : ℕ) (hn : 1 ≤ n) :
    (∀ j, ∃ z : ℤ, Cn n * aCoef n j = z) ∧
      (∀ j, ∃ z : ℤ, (dlcm (16 * n) : ℚ) * Cn n * bCoef n j = z) ∧
      (∀ i, ∃ z : ℤ, Z3v n i = z) ∧ (∀ i, ∃ z : ℤ, Z4v n i = z) ∧ 0 < (-1) ^ n * Q n := by
  exact BaselineIntegrality.baseline_integrality n hn

/-- **Carry facts** (paper §§5, 7, 10). For eligible `p` and `x = n/p`:
`v_p(C_n) = c(x)` (Legendre with one term, all factorial arguments `≤ 29n < p²`);
`v_p(d_{19n}) = 1` for `p ≤ 19n` (as `p² > 19n`); on the shells and windows the baseline profile
is exactly `ψ(x) = c(x) + 1` with no upper harmonic gain (finite Farey-29 chamber check, lifts by
`c(t+f) = c(f)`); and the windows lie inside the shells (so nothing is counted twice).
* From the manuscript: yes (§5 (D), §7 last paragraph, §10). -/
theorem carry_facts (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) :
    padicValRat p (Cn n) = cfun ((n : ℚ) / p) ∧
      (p ≤ 19 * n → padicValRat p (dlcm (19 * n)) = 1) ∧
      ((inRows shellRows ((n : ℚ) / p) ∨ inRows windowRows ((n : ℚ) / p)) →
        (psi ((n : ℚ) / p) : ℤ) = cfun ((n : ℚ) / p) + 1 ∧ hgain n p = 0) ∧
      (inRows windowRows ((n : ℚ) / p) → inRows shellRows ((n : ℚ) / p)) := by
  exact CarryFacts.carry_facts n p hn hp

/-- **Baseline carry profile** (G) (paper §5 and appendix). For eligible `p`, both integer forms
have valuation `≥ g(n/p) = ψ({n/p}) + h₀(n/p)`.
Proof (handoff §5.4, avoiding the paper's `ℓ(x,y)` test): `ψ` is the maximum of
`c(x) - ∑_{d∈D} ⌊dx⌋ + ∑_{l∈L} ⌊lx⌋` over ten factorial pairings `(L, D)` (pfq54's eight plus
`([9,9,14],[15,17])` and `([8,13,13],[16,18])`), each realised by a permutation of the shifts
`(-2..2)` (pfq54 `permutation_lemma`, `pairing_bound`); `h₀` from the upper harmonic range
(pfq54 `upper_range_bound`, redone for `r = 3`). Table equality: Farey-29 chamber check.
* From the manuscript: partially (the paper proves (G) via (D), (LD), (V) and a 270-cell
  certificate; the pairing description is new). -/
theorem baseline_profile (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) :
    (∀ i, ValGE p (psi ((n : ℚ) / p) + hgain n p : ℕ) (Z3v n i)) ∧
      (∀ i, ValGE p (psi ((n : ℚ) / p) + hgain n p : ℕ) (Z4v n i)) := by
  exact BaselineProfile.baseline_profile n p hn hp

/-! ## §5. First-order shells (paper §§6–7) -/

/-- **Fourteen first-order shells with all periodic lifts** (PS). For eligible `p` with
`{n/p} ∈ 𝒮`: `v_p(Q_n) ≥ 1`, `v_p(P_{3,n}) ≥ -1`, `v_p(P_{4,n}) ≥ -2`.
Proof: root-count chamber certificate (`h ≥ -1`; on `h = -1` the shifted high-root intervals are
the table row, affine in `t`); local factorization `p F_n(k + p(V+ε)) ≡ -𝒬(k) U_t(V) (mod p)`
with `𝒬 = (X^p - X) N̄/D̄` of degree `p - 2`; the sum over residues vanishes since
`∑_{k ∈ 𝔽_p} 𝒬(k) = 0`. Reuse: generalize pfq54 `residue_block` (row 1, `t = 0`).
* From the manuscript: yes (§6 for `8n < p < 11n`, §7 in general). -/
theorem shell_first_order (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    ValGE p 1 (Q n) ∧ ValGE p (-1) (P3 n) ∧ ValGE p (-2) (P4 n) := by
  exact ShellFirstOrder.shell_first_order n p hn hp hs

/-! ## §6. The second-order trace lemma and its application (paper §§8–9) -/

/-- **Second-order trace lemma** (T2) (paper §8). Under `TraceHyp`, the trace
`p ∑_{k∈R} F(k + pV)` is `≡ 0 (mod p²)` as a local rational function; equivalently, for every
integral high pole `ℓ`, `A_ℓ ∈ p³ ℤ_(p)` and `B_ℓ ∈ p² ℤ_(p)` (PB).
Proof (Lean-friendly form, handoff §5.6): expand `(u + pv)^{±1} ≡ u^{±1}(1 ± pv/u) (mod p²)`;
the constant part vanishes by `∑ L_k = 0` (sum of residues of a function of degree `≤ -2`), the
linear part is `p U(V)(V + σ_*) D` with `D ≡ -∑_{k∈𝔽_p} Q̃'(k) = 0 (mod p)`.
* From the manuscript: yes (§8, via a deformation parameter `P`). -/
theorem trace_lemma (p : ℕ) [Fact p.Prime] (Nr Dr : Multiset ℤ) (R : Finset ℤ)
    (NU DU : Multiset ℤ) (h : TraceHyp p Nr Dr R NU DU) (ℓ : ℤ) :
    ValGE p 3 (highPoleA p Nr Dr R ℓ) ∧ ValGE p 2 (highPoleB p Nr Dr R ℓ) := by
  exact TraceLemma.trace_lemma p Nr Dr R NU DU h ℓ

/-- **Root data on the windows** (paper §9, table (S2)). For eligible `p` with
`{n/p} ∈ (1/10, 2/19) ∪ (11/12, 15/16)`, the kernel `F_n` with representatives `1, …, p`
satisfies the hypotheses of the trace lemma. The minimal-class high roots are
`(1/10,2/19)`: `N = [0,10t],[t,11t],[2t,12t]`, `D = [-17t-2,-t-1],[-16t-2,-2t-1]`;
`(11/12,15/16)`: `N = [0,10t+8],[t+1,11t+9],[2t+2,12t+10]`, `D = [-17t-16,-t-2],[-16t-15,-2t-3]`;
the `h_k = 0` quotients are `V+16t+2`, `V+2t+1`, resp. `V-(2t+1)`, `V-(10t+9)`, `V+17t+16`.
Proof: Farey-29 chamber check at `t = 0` (9 cells), then affine-in-`t` endpoint arithmetic;
separation: distinct high roots differ by `≤ 29n/p < p`.
* From the manuscript: yes (§9, with the certificate `second_order_certificate.py`). -/
theorem window_root_data (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p)) :
    ∃ NU DU : Multiset ℤ, TraceHyp p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) NU DU := by
  exact WindowRootData.window_root_data n p hn hp hw

/-- **Readout on the windows** (paper §9, "The stronger arithmetic readouts"). If (PB) holds for
`F_n` at an eligible `p` with `{n/p}` in a window, then (SG): `v_p(Q_n) ≥ 3`,
`v_p(P_{3,n}) ≥ 0`, `v_p(P_{4,n}) ≥ -1`.
Proof: move the harmonic cutoff to `η = p⌈2n/p⌉ ∈ [2n, 10n]` (`F_n', F_n''` vanish at
`2n+1..10n`); then `⌊(j+η)/p⌋ = ⌈2n/p⌉ - ℓ - 1` is independent of the residue and
`j + η ≤ 27n < p²`; individually `a_j ∈ pℤ_(p)`, `b_j ∈ ℤ_(p)`; the remaining terms are sums of
`A_ℓ/p`, `B_ℓ` with `p`-integral harmonic weights.
* From the manuscript: yes (§9). -/
theorem window_readout (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p))
    (hPB : ∀ ℓ : ℤ, ValGE p 3 (highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ) ∧
      ValGE p 2 (highPoleB p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ)) :
    ValGE p 3 (Q n) ∧ ValGE p 0 (P3 n) ∧ ValGE p (-1) (P4 n) := by
  exact WindowReadout.window_readout n p hn hp hw hPB

/-- **Second-order windows** (SG) (paper §9, boxed). For eligible `p` with `{n/p}` in
`(1/10, 2/19) ∪ (11/12, 15/16)`: `v_p(Q_n) ≥ 3`, `v_p(P_{3,n}) ≥ 0`, `v_p(P_{4,n}) ≥ -1`.
* From the manuscript: yes. Proved here from `window_root_data`, `trace_lemma`,
  `window_readout`. -/
theorem second_order_shell (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p)) :
    ValGE p 3 (Q n) ∧ ValGE p 0 (P3 n) ∧ ValGE p (-1) (P4 n) := by
  exact SecondOrderShell.second_order_shell n p hn hp hw

/-! ## §7. The improved divisor and its density (paper §10) -/

/-- **The improved divisor** (I2). `G_n^{new}` divides both integer forms:
`6 C_n d_{19n}³ (Q_n, P_{3,n}) / G_n^{new} ∈ ℤ²` and
`6 C_n d_{19n}⁴ (Q_n, P_{3,n}, P_{4,n}) / G_n^{new} ∈ ℤ³`.
Proof: prime by prime (unique factorization, pfq54 `G_dvd_Z` / `prod_prime_pow_dvd`). At an
eligible `p`: in a window, (SG) + `carry_facts` give `c + 3 = gExp`; in a shell only, (PS) gives
`c + 2 = gExp`; otherwise `baseline_profile`. Integrality from `baseline_integrality`.
* From the manuscript: yes (§10). -/
theorem Gnew_dvd (n : ℕ) (hn : 1 ≤ n) :
    (∀ i, ∃ z : ℤ, Z3v n i = Gnew n * z) ∧ (∀ i, ∃ z : ℤ, Z4v n i = Gnew n * z) := by
  exact GnewDvd.Gnew_dvd n hn

/-- **Density of the divisor** (DEN). `liminf log G_n^{new} / n ≥ γ_new > 30.45854724`.
Here `γ_new = 6 + ∑_{psiRows} ψ 𝒟(a,b) + ∑_{shellRows} 𝒟(a,b) + 𝒟(1/10,2/19) + 𝒟(11/12,15/16)`
with `𝒟(a,b) = ∑_{t ≥ 0} (1/(t+a) - 1/(t+b))` and `6 = ∫ h₀/x²`.
Proof: prime number theorem on each interval `p ∈ (n/(t+b), n/(t+a))`, `t < K`; excluded primes
cost `o(n)`; rational tail bound `∑_{t≥K} f(t) ≥ 2(b-a)/(2K+a+b) + f(K)/2` (convexity); `K = 1000`
gives `30.4585472438 > γ_new` (`LogGnewGe_Cert.lean`; `K = 200` would give only `30.4585471312`).
Reuse: pfq54 `log_G_ge`, `log_G_aux*`, `profile_aux`.
* From the manuscript: yes (§10, with the certificate `infinite_density.py`). -/
theorem log_Gnew_ge :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (gammaNew - ε) * n ≤ Real.log (Gnew n) := by
  exact LogGnewGe.log_Gnew_ge

/-- **Normalization heights.** `log C_n ≤ (30 log(3/2) + ε) n` with `30 log(3/2) < 12.1639532433`
(Stirling; atanh series for `log(3/2)`), and `log d_{19n} ≤ (19 + ε) n` (prime number theorem).
Reuse: pfq54 `log_Z0_le` (`log_D_eq_psi`, `psi_le_eventually`), zeta34 `fact_bounds`.
* From the manuscript: yes (§11, "Since log C_n = 30n log(3/2) + o(n) and log d_{19n} = 19n + o(n)"). -/
theorem log_normalization_le :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log (Cn n : ℝ) ≤ (logCn + ε) * n ∧
      Real.log (dlcm (19 * n) : ℝ) ≤ (19 + ε) * n := by
  exact LogNormalizationLe.log_normalization_le

/-! ## §8. Analytic input and the final inequality (paper §§1, 11) -/

/-- **Growth** (analytic input `σ = a`). `|Q_n| ≤ exp((a + ε) n)` with
`a < 53.28758332263`.
Proof: zeta34 `growth_estimates` (`|q N j| ≤ e^{(a+ε)N}`) transported by pfq54 `ST.sum_q_hv`
(`∑_j q n j · hv n j = (-1)^n 6 Del n Qa n`); polynomial factors absorbed.
* From the manuscript: no (accepted analytic input, paper §1). -/
theorem Q_growth :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |(Q n : ℝ)| ≤ Real.exp ((aGrowth + ε) * n) := by
  exact QGrowth.Q_growth

/-- **Decay of the linear forms** (analytic input `E = a + b`).
`|ζ(3) Q_n - P_{3,n}| + |ζ(4) Q_n - P_{4,n}| ≤ exp((-b + ε) n)` with `b > 59.51995592483`.
Proof: zeta34 `readout_error_bound` transported by pfq54 `ST.sum_q_hv`, `sum_p3_hv`,
`sum_p4_hv`.
* From the manuscript: no (accepted analytic input, paper §1, in the equivalent form
  `|ζ(s) - P_{s,n}/Q_n| ≤ exp(-En + o(n))`, `log|Q_n| = σn + o(n)`). -/
theorem linform_error :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      |ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n| ≤ Real.exp ((-bDecay + ε) * n) := by
  exact LinformError.linform_error

/-- **Delta criterion** (paper §11, abstract form). Let `M_n Q_n, M_n P_n ∈ ℤ` with `M_n ≠ 0`,
`log|M_n| ≤ (κ + ε) n`, `|Q_n| ≤ e^{(a+ε)n}`, `|α Q_n - P_n| ≤ e^{(-b+ε)n}`, `κ < b`. Then
eventually either `P_n/Q_n = α` (so `δ = ⊤`) or the reduced denominator `q_n ≥ 2` and
`δ_n ≥ (b - κ - 2ε)/(a + κ + 2ε)`; in particular `δ_n ≥ c` eventually for every
`c < (b - κ)/(a + κ)`. No lower bound on `|Q_n|` and no irrationality is needed: if `α ∉ ℤ` then
`|α - P_n/Q_n| ≤ |M_n α Q_n - M_n P_n| → 0` forces `q_n ≥ 2`; if `α ∈ ℤ` the integer
`M_n Q_n α - M_n P_n → 0` is eventually `0`.
* From the manuscript: yes (§11; the case analysis for `q_n = 1` is implicit there). -/
theorem delta_criterion (α : ℝ) (Qs Ps Ms : ℕ → ℚ) (a b κ c : ℝ)
    (hκ : 0 < a + κ) (hb : κ < b) (hc : c < (b - κ) / (a + κ))
    (hQ : ∀ᶠ n in atTop, Qs n ≠ 0)
    (hint : ∀ᶠ n in atTop, Ms n ≠ 0 ∧ (∃ z : ℤ, Ms n * Qs n = z) ∧ ∃ z : ℤ, Ms n * Ps n = z)
    (hM : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log |(Ms n : ℝ)| ≤ (κ + ε) * n)
    (hgrowth : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |(Qs n : ℝ)| ≤ Real.exp ((a + ε) * n))
    (herr : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |α * Qs n - Ps n| ≤ Real.exp ((-b + ε) * n)) :
    ∀ᶠ n in atTop, (c : EReal) ≤ deltaOf α (Ps n / Qs n) := by
  -- a small `ε` adapted to the gap `c < (b - κ)/(a + κ)`
  have hgap : 0 < (b - κ) - c * (a + κ) := by
    have := (lt_div_iff₀ hκ).1 hc; linarith
  set gap := (b - κ) - c * (a + κ) with hgap_def
  set ε := min (gap / (2 * (|c| + 2))) ((b - κ) / 4) with hε_def
  have hc2 : 0 < |c| + 2 := by positivity
  have hε0 : 0 < ε := lt_min (div_pos hgap (by positivity)) (by linarith)
  have hε1 : 2 * ε * (|c| + 2) ≤ gap := by
    have := min_le_left (gap / (2 * (|c| + 2))) ((b - κ) / 4)
    rw [← hε_def, le_div_iff₀ (by positivity)] at this; linarith
  have hε2 : ε ≤ (b - κ) / 4 := min_le_right _ _
  -- `α` keeps a positive distance from the integers different from it
  obtain ⟨η, hη0, hη⟩ : ∃ η > 0, ∀ m : ℤ, α ≠ m → η ≤ |α - m| := by
    by_cases hZ : ∃ k : ℤ, α = k
    · obtain ⟨k, rfl⟩ := hZ
      refine ⟨1, one_pos, fun m hm => ?_⟩
      have hkm : k - m ≠ 0 := sub_ne_zero.2 (fun h => hm (by rw [h]))
      have h1 : (1 : ℤ) ≤ |k - m| := Int.one_le_abs hkm
      have h2 : (1 : ℝ) ≤ |((k - m : ℤ) : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast h1
      simpa using h2
    · push Not at hZ
      have hf : Int.fract α = α - ⌊α⌋ := (Int.self_sub_floor α).symm
      have hf0 : 0 < Int.fract α := Int.fract_pos.2 (hZ ⌊α⌋)
      have hf1 : Int.fract α < 1 := Int.fract_lt_one α
      refine ⟨min (Int.fract α) (1 - Int.fract α), lt_min hf0 (by linarith), fun m _ => ?_⟩
      have hm1 := min_le_left (Int.fract α) (1 - Int.fract α)
      have hm2 := min_le_right (Int.fract α) (1 - Int.fract α)
      rcases le_or_gt m ⌊α⌋ with h | h
      · have : (m : ℝ) ≤ ⌊α⌋ := by exact_mod_cast h
        have := le_abs_self (α - m)
        linarith
      · have : (⌊α⌋ : ℝ) + 1 ≤ m := by exact_mod_cast h
        have := neg_abs_le (α - m)
        linarith
  -- the integer linear forms `u_n α - v_n` tend to zero
  have hsmall : ∀ᶠ n : ℕ in atTop, Real.exp ((κ - b + 2 * ε) * n) < min η 1 := by
    have hneg : κ - b + 2 * ε < 0 := by linarith
    have ht : Tendsto (fun n : ℕ => Real.exp ((κ - b + 2 * ε) * n)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg hneg)
    exact ht.eventually (gt_mem_nhds (lt_min hη0 one_pos))
  filter_upwards [hQ, hint, hM ε hε0, hgrowth ε hε0, herr ε hε0, hsmall, eventually_gt_atTop 0]
    with n hQn ⟨hMn, ⟨u, hu⟩, ⟨v, hv⟩⟩ hMb hgb heb hsb hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hQr : (Qs n : ℝ) ≠ 0 := by exact_mod_cast hQn
  have hMr : (Ms n : ℝ) ≠ 0 := by exact_mod_cast hMn
  have hu' : (u : ℝ) = (Ms n : ℝ) * Qs n := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hu; push_cast at this; linarith
  have hv' : (v : ℝ) = (Ms n : ℝ) * Ps n := by
    have := congrArg (fun x : ℚ => (x : ℝ)) hv; push_cast at this; linarith
  have hu0 : (u : ℝ) ≠ 0 := by rw [hu']; exact mul_ne_zero hMr hQr
  have hu0' : u ≠ 0 := by exact_mod_cast hu0
  have hMexp : |(Ms n : ℝ)| ≤ Real.exp ((κ + ε) * n) :=
    (Real.log_le_iff_le_exp (abs_pos.2 hMr)).1 hMb
  have hlin : |(u : ℝ) * α - v| < min η 1 := by
    have : (u : ℝ) * α - v = (Ms n : ℝ) * (α * Qs n - Ps n) := by rw [hu', hv']; ring
    rw [this, abs_mul]
    calc |(Ms n : ℝ)| * |α * Qs n - Ps n|
        ≤ Real.exp ((κ + ε) * n) * Real.exp ((-b + ε) * n) :=
          mul_le_mul hMexp heb (abs_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((κ - b + 2 * ε) * n) := by rw [← Real.exp_add]; ring_nf
      _ < min η 1 := hsb
  unfold deltaOf
  split_ifs with hαr
  · exact le_top
  rw [EReal.coe_le_coe_iff]
  set r : ℚ := Ps n / Qs n with hr_def
  have hrv : (r : ℝ) = (v : ℝ) / u := by
    rw [hu', hv', hr_def]; push_cast; rw [mul_div_mul_left _ _ hMr]
  have hu1 : (1 : ℝ) ≤ |(u : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hu0'
  -- `|α - r_n| ≤ |u_n α - v_n|`
  have hdist : |α - r| ≤ |(u : ℝ) * α - v| := by
    have : α - (v : ℝ) / u = ((u : ℝ) * α - v) / u := by field_simp
    rw [hrv, this, abs_div]
    exact div_le_self (abs_nonneg _) hu1
  -- the reduced denominator is at least `2`
  have hden2 : 2 ≤ r.den := by
    by_contra hlt
    have hd1 : r.den = 1 := by have := r.den_pos; omega
    have hrint : ((r.num : ℤ) : ℝ) = (r : ℝ) := by
      have := Rat.coe_int_num_of_den_eq_one hd1; exact_mod_cast this
    have h1 := hη r.num (by rw [hrint]; exact hαr)
    rw [hrint] at h1
    linarith [min_le_left η 1]
  -- `q_n ≤ |u_n|`
  have hden_le : (r.den : ℝ) ≤ |(u : ℝ)| := by
    have hrdiv : r = Rat.divInt v u := by
      rw [Rat.divInt_eq_div, hr_def, ← hu, ← hv, mul_div_mul_left _ _ hMn]
    have hd : (r.den : ℤ) ∣ u := by rw [hrdiv]; exact Rat.den_dvd v u
    have : (r.den : ℤ) ≤ |u| := Int.le_of_dvd (abs_pos.2 hu0') ((dvd_abs _ _).2 hd)
    rw [← Int.cast_abs]; exact_mod_cast this
  have hL0 : 0 < Real.log r.den := Real.log_pos (by exact_mod_cast hden2)
  have hLq : Real.log r.den ≤ Real.log |(Ms n : ℝ)| + Real.log |(Qs n : ℝ)| := by
    rw [← Real.log_mul (abs_ne_zero.2 hMr) (abs_ne_zero.2 hQr), ← abs_mul, ← hu']
    exact Real.log_le_log (by positivity) hden_le
  have hX : Real.log |(Qs n : ℝ)| ≤ (a + ε) * n :=
    (Real.log_le_iff_le_exp (abs_pos.2 hQr)).2 hgb
  have herr0 : α * Qs n - Ps n ≠ 0 := by
    intro h; apply hαr; rw [hr_def]; push_cast; field_simp; linarith
  have hY : (b - ε) * n + Real.log |(Qs n : ℝ)| ≤ -Real.log |α - r| := by
    have h1 : α - (r : ℝ) = (α * Qs n - Ps n) / Qs n := by rw [hr_def]; push_cast; field_simp
    rw [h1, abs_div, Real.log_div (abs_ne_zero.2 herr0) (abs_ne_zero.2 hQr)]
    have := (Real.log_le_iff_le_exp (abs_pos.2 herr0)).2 heb
    linarith
  -- the final inequality `(c + 1) log q_n ≤ -log|α - r_n|`
  rw [show -1 - Real.log |α - r| / Real.log r.den =
    -Real.log |α - r| / Real.log r.den - 1 by ring, le_sub_iff_add_le, le_div_iff₀ hL0]
  set L := Real.log r.den
  set X := Real.log |(Qs n : ℝ)|
  have hLb : L ≤ (κ + ε) * n + X := by linarith
  have hpos : 0 ≤ (b - κ - 2 * ε) * n := mul_nonneg (by linarith) hnpos.le
  rcases le_or_gt (c + 1) 0 with hc1 | hc1
  · have : (c + 1) * L ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc1 hL0.le
    linarith
  · have h1 : (c + 1) * L ≤ (c + 1) * ((κ + ε) * n + X) := mul_le_mul_of_nonneg_left hLb hc1.le
    have h2 : c * ((κ + ε) * n + X) ≤ (b - κ - 2 * ε) * n := by
      rcases le_or_gt c 0 with hc0 | hc0
      · have : c * ((κ + ε) * n + X) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc0 (by linarith)
        linarith
      · have h3 : c * ((κ + ε) * n + X) ≤ c * ((κ + ε) * n + (a + ε) * n) :=
          mul_le_mul_of_nonneg_left (by linarith) hc0.le
        rw [abs_of_pos hc0] at hε1
        have h4 : c * (a + κ) + 2 * ε * c ≤ b - κ - 2 * ε := by nlinarith
        have h5 : c * ((κ + ε) * n + (a + ε) * n) = (c * (a + κ) + 2 * ε * c) * n := by ring
        have h6 := mul_le_mul_of_nonneg_right h4 hnpos.le
        linarith
    have h7 : (c + 1) * ((κ + ε) * n + X) = c * ((κ + ε) * n + X) + ((κ + ε) * n + X) := by ring
    linarith

/-- **Eventual bound for the approximants** (paper §11). With `r = 4`, or `r = 3` when `B = 0`:
for every `c < (b - κ_r)/(a + κ_r)`, eventually `δ_N(A,B) ≥ c`. Here
`M_n = 6 C_n d_{19n}^r / G_n^{new}`, `log M_n ≤ (κ_r + ε) n`.
* From the manuscript: yes. Proved here from `approxCMF_eq`, `baseline_integrality`, `Gnew_dvd`,
  `log_Gnew_ge`, `log_normalization_le`, `Q_growth`, `linform_error`, `delta_criterion`. -/
theorem eventual_delta (A B : ℤ) (r : ℕ) (hr : r = 4 ∨ (r = 3 ∧ B = 0)) (c : ℝ)
    (hc : c < (bDecay - kappa r) / (aGrowth + kappa r)) :
    ∀ᶠ N in atTop, (c : EReal) ≤ deltaN N A B := by
  have hκ : 0 < aGrowth + kappa r := by
    rcases hr with rfl | ⟨rfl, -⟩ <;> norm_num [aGrowth, kappa, logCn, gammaNew]
  have hb : kappa r < bDecay := by
    rcases hr with rfl | ⟨rfl, -⟩ <;> norm_num [bDecay, kappa, logCn, gammaNew]
  -- positivity of the normalisation
  have hG : ∀ n, 0 < Gnew n := fun n =>
    Finset.prod_pos fun p hp => pow_pos (Finset.mem_filter.1 hp).2.1.pos _
  have hC : ∀ n, 0 < Cn n := fun n => by unfold Cn; positivity
  have hd : ∀ n, 0 < dlcm (19 * n) := fun n => by
    refine Nat.pos_of_ne_zero fun h => ?_
    rw [dlcm, Finset.lcm_eq_zero_iff] at h
    simp at h
  have key := delta_criterion (alpha A B) Q (fun n => A * P3 n + B * P4 n)
    (fun n => 6 * Cn n * (dlcm (19 * n) : ℚ) ^ r / Gnew n) aGrowth bDecay (kappa r) c hκ hb hc
    ?hQ ?hint ?hM Q_growth ?herr
  · filter_upwards [(tendsto_sub_atTop_nat 1).eventually key] with N hN
    simpa [deltaN, approxCMF_eq] using hN
  case hQ =>
    filter_upwards [eventually_ge_atTop 1] with n hn h
    have := (baseline_integrality n hn).2.2.2.2
    rw [h, mul_zero] at this
    exact lt_irrefl _ this
  case hint =>
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hG0 : (Gnew n : ℚ) ≠ 0 := by exact_mod_cast (hG n).ne'
    refine ⟨div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (hC n).ne')
      (pow_ne_zero _ (by exact_mod_cast (hd n).ne'))) hG0, ?_⟩
    rcases hr with rfl | ⟨rfl, rfl⟩
    · obtain ⟨z0, h0⟩ := (Gnew_dvd n hn).2 0
      obtain ⟨z3, h3⟩ := (Gnew_dvd n hn).2 1
      obtain ⟨z4, h4⟩ := (Gnew_dvd n hn).2 2
      simp only [Z4v, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons] at h0 h3 h4
      refine ⟨⟨z0, ?_⟩, ⟨A * z3 + B * z4, ?_⟩⟩
      · field_simp; linear_combination h0
      · push_cast; field_simp; linear_combination (A : ℚ) * h3 + (B : ℚ) * h4
    · obtain ⟨z0, h0⟩ := (Gnew_dvd n hn).1 0
      obtain ⟨z3, h3⟩ := (Gnew_dvd n hn).1 1
      simp only [Z3v, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h3
      refine ⟨⟨z0, ?_⟩, ⟨A * z3, ?_⟩⟩
      · field_simp; linear_combination h0
      · push_cast; field_simp; linear_combination (A : ℚ) * h3
  case hM =>
    intro ε hε
    have hr34 : (r : ℝ) ≤ 4 := by rcases hr with rfl | ⟨rfl, -⟩ <;> norm_num
    have h6 : ∀ᶠ n : ℕ in atTop, Real.log 6 ≤ ε / 8 * n :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)).eventually_ge_atTop _
    filter_upwards [h6, log_normalization_le (ε / 8) (by positivity),
      log_Gnew_ge (ε / 8) (by positivity), eventually_gt_atTop 0] with n h6n ⟨hCn, hdn⟩ hGn hn0
    have hnpos : (0 : ℝ) ≤ n := by positivity
    have hCr : (0 : ℝ) < (Cn n : ℝ) := by exact_mod_cast hC n
    have hdr : (0 : ℝ) < (dlcm (19 * n) : ℝ) := by exact_mod_cast hd n
    have hGr : (0 : ℝ) < (Gnew n : ℝ) := by exact_mod_cast hG n
    have hval : (((6 * Cn n * (dlcm (19 * n) : ℚ) ^ r / Gnew n : ℚ)) : ℝ) =
        6 * (Cn n : ℝ) * (dlcm (19 * n) : ℝ) ^ r / (Gnew n : ℝ) := by push_cast; ring
    rw [hval, abs_of_pos (by positivity), Real.log_div (by positivity) hGr.ne',
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) hCr.ne',
      Real.log_pow]
    have hlogd : (r : ℝ) * Real.log (dlcm (19 * n) : ℝ) ≤ r * ((19 + ε / 8) * n) :=
      mul_le_mul_of_nonneg_left hdn (Nat.cast_nonneg r)
    have hrε : (r : ℝ) * (ε / 8 * n) ≤ 4 * (ε / 8 * n) :=
      mul_le_mul_of_nonneg_right hr34 (by positivity)
    unfold kappa
    nlinarith
  case herr =>
    intro ε hε
    set K : ℝ := |(A : ℝ)| + |(B : ℝ)|
    have hK : ∀ᶠ n : ℕ in atTop, K ≤ ε / 2 * n :=
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)).eventually_ge_atTop _
    filter_upwards [hK, linform_error (ε / 2) (by positivity)] with n hKn hen
    have hKexp : K ≤ Real.exp (ε / 2 * n) := by
      linarith [Real.add_one_le_exp (ε / 2 * n)]
    have hsplit : alpha A B * Q n - ((A * P3 n + B * P4 n : ℚ) : ℝ) =
        A * (ζ3 * Q n - P3 n) + B * (ζ4 * Q n - P4 n) := by
      unfold alpha; push_cast; ring
    have hK0 : 0 ≤ K := by positivity
    rw [hsplit]
    calc |(A : ℝ) * (ζ3 * Q n - P3 n) + B * (ζ4 * Q n - P4 n)|
        ≤ K * (|ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n|) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          nlinarith [abs_nonneg (ζ3 * Q n - P3 n), abs_nonneg (ζ4 * Q n - P4 n),
            abs_nonneg (A : ℝ), abs_nonneg (B : ℝ)]
      _ ≤ Real.exp (ε / 2 * n) * Real.exp ((-bDecay + ε / 2) * n) :=
          mul_le_mul hKexp hen (by positivity) (Real.exp_pos _).le
      _ = Real.exp ((-bDecay + ε) * n) := by rw [← Real.exp_add]; ring_nf

set_option linter.unusedVariables false in
/-- **Main theorem, joint readout.** For every fixed `(A, B) ∈ ℤ² \ {(0,0)}`,
`liminf_{N→∞} δ_N(A,B) > 0.01634832`.
(`(b - κ₄)/(a + κ₄) = 1.81454992153/110.99298932593 = 0.0163483291… > 0.01634832`; the hypothesis
`(A,B) ≠ (0,0)` is not needed, since for `A = B = 0` every approximant is exact.)
* From the manuscript: yes (Theorem 1). Proved here from `eventual_delta` with `r = 4`. -/
theorem main_joint (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ((102177 / 6250000 : ℝ) : EReal) < Filter.liminf (fun N => deltaN N A B) atTop := by
  have hc : (3269665 / 200000000 : ℝ) < (bDecay - kappa 4) / (aGrowth + kappa 4) := by
    rw [lt_div_iff₀ (by norm_num [aGrowth, kappa, logCn, gammaNew])]
    norm_num [aGrowth, bDecay, kappa, logCn, gammaNew]
  calc ((102177 / 6250000 : ℝ) : EReal) < ((3269665 / 200000000 : ℝ) : EReal) := by
        rw [EReal.coe_lt_coe_iff]; norm_num
    _ ≤ Filter.liminf (fun N => deltaN N A B) atTop :=
        le_liminf_of_le (h := eventual_delta A B 4 (Or.inl rfl) _ hc)

set_option linter.unusedVariables false in
/-- **Main theorem, pure `ζ(3)` readout.** For `A ≠ 0`,
`liminf_{N→∞} δ_N(A,0) > 0.22626234`.
(`(b - κ₃)/(a + κ₃) = 20.81454992153/91.99298932593 = 0.2262623497… > 0.22626234`.)
* From the manuscript: yes (Theorem 1). Proved here from `eventual_delta` with `r = 3`. -/
theorem main_pure3 (A : ℤ) (hA : A ≠ 0) :
    ((11313117 / 50000000 : ℝ) : EReal) < Filter.liminf (fun N => deltaN N A 0) atTop := by
  have hc : (45252469 / 200000000 : ℝ) < (bDecay - kappa 3) / (aGrowth + kappa 3) := by
    rw [lt_div_iff₀ (by norm_num [aGrowth, kappa, logCn, gammaNew])]
    norm_num [aGrowth, bDecay, kappa, logCn, gammaNew]
  calc ((11313117 / 50000000 : ℝ) : EReal) < ((45252469 / 200000000 : ℝ) : EReal) := by
        rw [EReal.coe_lt_coe_iff]; norm_num
    _ ≤ Filter.liminf (fun N => deltaN N A 0) atTop :=
        le_liminf_of_le (h := eventual_delta A 0 3 (Or.inr ⟨rfl, rfl⟩) _ hc)

end Meijer5255
