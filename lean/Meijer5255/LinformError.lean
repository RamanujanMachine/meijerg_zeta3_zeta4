/-
# Node blueprint: `linform_error` (paper §1, accepted analytic input `E = a + b`)

Target (restated verbatim from `Blueprint_5255.lean`):
  `∀ ε > 0, ∀ᶠ n : ℕ in atTop,
     |ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n| ≤ Real.exp ((-bDecay + ε) * n)`.

Strategy (`LEAN_HANDOFF.md` §5.9; handoff §4.12). The paper does not prove the decay: it is the
accepted analytic input `|ζ(s) - P_{s,n}/Q_n| ≤ e^{-En+o(n)}` of §1 (with `E = a + b`). It is
proved in `../zetas_irr` for the zeta34 sequence (`readout_error_bound`): the rows `A_N, B_N` of
the coefficient matrix grow like `e^{bN+o(N)}`, the linear forms `S_N` decay like `e^{-aN+o(N)}`,
`det V_N ≥ e^{(2b-a)N-o(N)}`, and the cross-product readouts
`ζ3 q_N - p^{(3)}_N = -(A_N × S_N)/det V_N`, `ζ4 q_N - p^{(4)}_N = (B_N × S_N)/det V_N` give
`|ζ3 q_{Nj} - p^{(3)}_{Nj}| + |ζ4 q_{Nj} - p^{(4)}_{Nj}| ≤ 4e^{(b-a+2ε')N}/e^{(2b-a-ε')N} ≤ e^{(-b+4ε')N}`.
The zeta34 objects are those of the copied helper layer `QGrowth_*.lean`. The bridge to this repository's
readouts is pfq54's weighted readout (`star_aux.sum_q_hv`, `sum_p3_hv`, `sum_p4_hv`):
`∑_j hv_{nj} (q_{nj}, p^{(3)}_{nj}, p^{(4)}_{nj}) = (-1)^n 6 Del_n (Q_n, P_{3,n}, P_{4,n})`, the
`Z₃, Z₀` coefficients of `∑_j hv_j (q_j Z₃ - p^{(3)}_j) = 3(-1)^n Del_n 𝓛_{2n}[F_n]` and the `Z₀`
coefficient of `∑_j hv_j (q_j Z₄ - p^{(4)}_j) = (-1)^n Del_n 𝓜_{2n}[F_n]`, with the endpoint values
`𝓛_{2n}[F_n] = 2Q_n Z₃ + ⋯ - 2P_{3,n}`, `[Z₀] 𝓜_{2n}[F_n] = -6P_{4,n}`. Hence
`6 Del_n (ζ(s) Q_n - P_{s,n}) = ± ∑_j hv_j (ζ(s) q_{nj} - p^{(s)}_{nj})`, and the glue does the
bookkeeping: `Del_n ≥ 1`, `hv_j ≤ (10n+1)²`, `(10n+1)² ≤ e^{ε'n}` eventually, `ε' = ε/5`,
`b > bDecay`.

Supporting lemmas (8), all proved (the line counts are the original blueprint estimates), and whether the PDF
proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `spectral_bounds` | 2500 | no (accepted analytic input; zeta34 `growth_estimates` + `GW_*`) |
| 2 | `cross_product_readout` | 1000 | no (zeta34 `cross_product_readout.lean`) |
| 3 | `abs_cross_le` | 15 | no (elementary inequality, not in the paper) |
| 4 | `weighted_L` | 350 | no (pfq54 `star_aux` dual-kernel bridge) |
| 5 | `weighted_M` | 150 | no (pfq54 `star_aux` + zeta34 `pairing_identity`) |
| 6 | `Lfun_Fn_readout` | 150 | yes (§3, endpoint value `2Q_n Z₃ - 2P_{3,n}`) |
| 7 | `Mfun_Fn_zero` | 200 | yes (§3, endpoint value `6Q_n Z₄ - 6P_{4,n}`) |
| 8 | `poly_absorb` | 30 | yes (the `o(n)` in §1) |

Reuse (all lemmas are proved): the helper layer `Meijer5255/QGrowth_*.lean` shared with
`QGrowth.lean` (see its module docstring): verbatim copies of zeta34 `defs.lean`,
`growth_estimates`, `cross_product_readout`, `pairing_identity`, `GW_*`, `CMF_*` and their
imports (namespace renamed `Meijer5255.QGA.ZetasIrr`), the adapted pfq54 `pf_aux`/`star_aux`
(`QGrowth_PF`, `QGrowth_Star`) and the new `QGrowth_Bridge`. The glue for the zeta34 columns is
copied from `../zetas_irr/blueprints/readout_error_bound.lean`.
-/
import Meijer5255.definitions
import Meijer5255.QGrowth_Bridge

open Filter Topology Finset Polynomial
open scoped Matrix RatFunc LaurentSeries

noncomputable section

namespace Meijer5255.LinformError

open Meijer5255

/-! ### Objects

The zeta34 objects are those of the copied layer `QGrowth_defs` (zeta34 `defs.lean`, namespace
`Meijer5255.QGA.ZetasIrr`), shared with `QGrowth.lean`: `FormalZ`, `Zsym`, `Lfun` (`𝓛_K`), `Mfun`
(`𝓜_K = -𝓛_K[f']`), `coeffMat` (`𝓒_N`), `S` (here called `Sform`, the linear forms
`S_{Nj} = -∑_{t ≥ 2N+1} d/dt((-t)^j R_N(t))`), `V` (here called `Vmat`), `p3`, `p4`, `q` (rows of
`𝓡_N = U₃₄ V_N^{-T}`). pfq54's objects come from `QGrowth_PF` / `QGrowth_Star`: the kernel
`Fn n = lin (nR n) (dR n)`, which is `rootPoly (numRoots n) / rootPoly (denRoots n)`
(`QGA.Bridge.Fn_eq`), the weights `hv n = (1, 10n+1, (10n+1)²)` and `Del n = ∏_{j=8}^{12}(jn+1)`.
(zeta34's `ζ3`, `ζ4` are definitionally this repository's.) -/

open Meijer5255.QGA.ZetasIrr (FormalZ Zsym Lfun Mfun coeffMat q p3 p4)
open Meijer5255.QGA.ZetasIrr renaming V → Vmat, S → Sform
open Meijer5255.QGA.Pfq54.PF (Fn)
open Meijer5255.QGA.Pfq54.ST (hv Del)

/-! ### Supporting lemmas -/

/-- **[1] Spectral bounds** (part of zeta34 `growth_estimates`). There are `a` and
`b > 59.51995592483` such that, for every `ε > 0` and all large `N`:
`|A_{Nj}|, |B_{Nj}| ≤ e^{(b+ε)N}`, `|S_{Nj}| ≤ e^{(-a+ε)N}` and `det V_N ≥ e^{(2b-a-ε)N}`.
Proof (zeta34 Part VII §1, §6): `a = -log λ₀`, `b = ½(log c₀ + a)` (`λ₀` the real root of the
characteristic polynomial of the limit matrix, exact rational bracketing); rows by the cone
argument `GW.cone_growth`; `S_N` by the polynomial bound `GW.S_poly_bound` and the contraction
`GW.cone_decay`; `det V_N = F_N` and Stirling (`F_lower_bound`).
* Proved (≈ 8 lines): from the copied zeta34 `BP.growth_estimates` (`QGrowth_growth_estimates`,
  with `QGrowth_det_V_eq`, `QGrowth_GW_*`, `QGrowth_CMF_*`; ≈ 9000 copied lines, unchanged).
* Directly from the PDF: no (the paper accepts `E` as analytic input, §1). -/
theorem spectral_bounds :
    ∃ a b : ℝ, bDecay < b ∧
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
        (∀ j, |(coeffMat N 0 j : ℝ)| ≤ Real.exp ((b + ε) * N) ∧
          |(coeffMat N 1 j : ℝ)| ≤ Real.exp ((b + ε) * N) ∧
          |Sform N j| ≤ Real.exp ((-a + ε) * N)) ∧
        Real.exp ((2 * b - a - ε) * N) ≤ ((Vmat N).det : ℝ) := by
  obtain ⟨a, b, -, -, hb, -, hg⟩ := Meijer5255.QGA.ZetasIrr.BP.growth_estimates
  refine ⟨a, b, ?_, fun ε hε => ?_⟩
  · have : (59.51995592483 : ℝ) = 5951995592483 / 10 ^ 11 := by norm_num
    rw [bDecay, ← this]
    exact hb
  · filter_upwards [hg ε hε] with N ⟨hj, hd⟩
    exact ⟨fun j => ⟨(hj j).1, (hj j).2.1, (hj j).2.2.1⟩, hd⟩

/-- **[2] Cross-product readouts.** `ζ3 q_N - p^{(3)}_N = -(A_N × S_N)/det V_N` and
`ζ4 q_N - p^{(4)}_N = (B_N × S_N)/det V_N`.
Proof: `S_{Nj} = A_{Nj} ζ4 + B_{Nj} ζ3 + C_{Nj}` (realisation of `𝓛_{2N}`, `S_eq`), and the rows of
`𝓡_N = U₃₄ V_N^{-T}` are adjugate columns: `q = -(A × B)/det`, `p^{(3)} = -(A × C)/det`,
`p^{(4)} = (B × C)/det` (`readouts_eq_cross`); then bilinearity of `×`.
* Proved (≈ 2 lines): the copied zeta34 `cross_product_readout` (`QGrowth_cross_product_readout`).
* Directly from the PDF: no (zeta34 note; not part of this paper). -/
theorem cross_product_readout (N : ℕ) :
    (fun j => ζ3 * q N j - p3 N j) =
        -((Vmat N).det : ℝ)⁻¹ • crossProduct (fun j => (coeffMat N 0 j : ℝ)) (Sform N) ∧
    (fun j => ζ4 * q N j - p4 N j) =
        ((Vmat N).det : ℝ)⁻¹ • crossProduct (fun j => (coeffMat N 1 j : ℝ)) (Sform N) :=
  Meijer5255.QGA.ZetasIrr.cross_product_readout N

/-- **[3] Size of a cross product.** If `|u_i| ≤ M` and `|v_i| ≤ M'` then `|(u × v)_j| ≤ 2MM'`.
* Proved (≈ 2 lines): the copied zeta34 `BP.abs_cross_le` (`QGrowth_growth_estimates`).
* Directly from the PDF: no (elementary inequality, not stated in the paper). -/
theorem abs_cross_le (u v : Fin 3 → ℝ) (M M' : ℝ) (hu : ∀ i, |u i| ≤ M) (hv : ∀ i, |v i| ≤ M')
    (j : Fin 3) : |crossProduct u v j| ≤ 2 * (M * M') :=
  Meijer5255.QGA.ZetasIrr.BP.abs_cross_le u v M M' hu hv j

/-- **[4] Weighted dual readout, first functional** (pfq54 `star_aux.weighted_L` + `Lfun_W`).
`∑_j hv_{nj} (q_{nj} Z₃ - p^{(3)}_{nj}) = 3(-1)^n Del_n 𝓛_{2n}[F_n]` as formal combinations.
Proof: zeta34's dual identity `(-1)^n 3 𝓛_n[Q_{nj}(t) R*_n(t)] = q_{nj} Z₃ - p^{(3)}_{nj}`
(`dual_first_identity'`), the shift `R*_n(t+12n+1) ↔ (-t)^r F̃_n` (`Qmul_eq'`, `Lfun_laurent`),
the cutoff move `n → 2n` (`Lfun_Wj_cut`), and the reduction of `∑_j hv_j ∑_r J_{jr} (-t)^r`
modulo the companion relation of `F_n` to the scalar `Del_n` (`W_reduce`, `companion_L`).
* Proved (≈ 2 lines): `QGA.Bridge.weighted_L`, i.e. pfq54 `star_aux.weighted_L` + `Lfun_W`
  (copied in `QGrowth_Star`, with zeta34 `dual_first_identity'`).
* Directly from the PDF: no (the link between the zeta34 sequence and this paper's readouts is
  not in the paper; it is the pfq54 identification). -/
theorem weighted_L (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 3 - p3 n j • Zsym 0) =
      ((-1 : ℚ) ^ n * 3 * Del n) • Lfun (2 * n) (Fn n) :=
  Meijer5255.QGA.Bridge.weighted_L n

/-- **[5] Weighted dual readout, second functional** (pfq54 `star_aux.weighted_M` + `Mfun_W`).
`∑_j hv_{nj} (q_{nj} Z₄ - p^{(4)}_{nj}) = (-1)^n Del_n 𝓜_{2n}[F_n]` as formal combinations.
Proof: as [4], from zeta34's pairing identity `(-1)^N 𝓜_{-10N-1}[Q_{Nj} R*_N] = Z₄ q_{Nj} - p^{(4)}_{Nj}`
(`pairing_identity`, `identity_M`, `Mfun_laurent`) and `W_reduce` with `companion_M`.
* Proved (≈ 2 lines): `QGA.Bridge.weighted_M`, i.e. pfq54 `star_aux.weighted_M` + `Mfun_W`
  (copied in `QGrowth_Star`, with zeta34 `pairing_identity`).
* Directly from the PDF: no (as [4]). -/
theorem weighted_M (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 4 - p4 n j • Zsym 0) =
      ((-1 : ℚ) ^ n * Del n) • Mfun (2 * n) (Fn n) :=
  Meijer5255.QGA.Bridge.weighted_M n

/-- **[6] Endpoint values of `𝓛_{2n}[F_n]`.** `[Z₃] = 2∑_j a_j = 2Q_n` and
`[Z₀] = -∑_j (2a_j H^{(3)}_{j+2n} + b_j H^{(2)}_{j+2n}) = -2P_{3,n}`.
Proof: `F_n` is proper (`polyPart = 0`), its poles are `-j`, `n ≤ j ≤ 17n`, of order `≤ 2`, with
Laurent coefficients `a_j` (order 2) and `b_j` (order 1) (`pfCoeff_Fn_two`, `pfCoeff_Fn_one`);
the harmonic index is `⌊2n + j⌋ = j + 2n`; `aCoef, bCoef` vanish off the poles.
* Proved (≈ 2 lines): `QGA.Bridge.Lfun_Fn_three`, `Lfun_Fn_zero` (pfq54 `pf_aux`, adapted in
  `QGrowth_PF`, plus `aF n j = aCoef n j`, `bF n j = bCoef n j`; ≈ 100 new lines).
* Directly from the PDF: yes (§3, the endpoint contour integral `(-1)^n(2Q_n Z₃ + 0·Z₂ - 2P_{3,n})`). -/
theorem Lfun_Fn_readout (n : ℕ) :
    Lfun (2 * n) (Fn n) 3 = 2 * Q n ∧ Lfun (2 * n) (Fn n) 0 = -2 * P3 n :=
  ⟨Meijer5255.QGA.Bridge.Lfun_Fn_three n, Meijer5255.QGA.Bridge.Lfun_Fn_zero n⟩

/-- **[7] Endpoint value of `𝓜_{2n}[F_n]`.** `[Z₀] 𝓜_{2n}[F_n] = -∑_j (6a_j H^{(4)}_{j+2n} +
2b_j H^{(3)}_{j+2n}) = -6P_{4,n}`.
Proof: `F_n' = ∑_j (-2a_j/(t+j)³ - b_j/(t+j)²)` (Laurent coefficients of `rfDeriv`), then as [6].
* Proved (≈ 2 lines): `QGA.Bridge.Mfun_Fn_zero` (pfq54 `pf_aux.Mfun_Fn_zero`, adapted in
  `QGrowth_PF`, plus `aF_eq`, `bF_eq`).
* Directly from the PDF: yes (§3, the endpoint contour integral `(-1)^n(6Q_n Z₄ + 0·Z₃ - 6P_{4,n})`). -/
theorem Mfun_Fn_zero (n : ℕ) : Mfun (2 * n) (Fn n) 0 = -6 * P4 n :=
  Meijer5255.QGA.Bridge.Mfun_Fn_zero n

/-- **[8] Polynomial factors are subexponential.** `(10n+1)² ≤ e^{εn}` for all large `n`.
* Proved (≈ 2 lines): `QGA.Bridge.poly_absorb` (≈ 20 lines, from `x³/3! ≤ eˣ`).
* Directly from the PDF: yes (the `o(n)` of §1). -/
theorem poly_absorb (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (10 * (n : ℝ) + 1) ^ 2 ≤ Real.exp (ε * n) :=
  Meijer5255.QGA.Bridge.poly_absorb ε hε

/-! ### The node -/

/-- **Decay of the linear forms** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[8]. -/
theorem linform_error :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      |ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n| ≤ Real.exp ((-bDecay + ε) * n) := by
  obtain ⟨a, b, hb, hspec⟩ := spectral_bounds
  intro ε hε
  set ε' := ε / 5 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h4N : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ Real.exp (ε' * N) := by
    have : Tendsto (fun N : ℕ => Real.exp (ε' * N)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hε'pos)
    exact this.eventually_ge_atTop 4
  filter_upwards [hspec ε' hε'pos, h4N, poly_absorb ε' hε'pos] with n ⟨hj, hdet⟩ h4 hpoly
  have hd : (0 : ℝ) < (Vmat n).det := lt_of_lt_of_le (Real.exp_pos _) hdet
  -- the zeta34 columns: `|ζ3 q_j - p3_j| + |ζ4 q_j - p4_j| ≤ e^{(-b + 4ε')n}`
  set E := Real.exp ((-b + 4 * ε') * n) with hE
  have hcol : ∀ j, |ζ3 * q n j - p3 n j| + |ζ4 * q n j - p4 n j| ≤ E := by
    intro j
    obtain ⟨h1, h2⟩ := cross_product_readout n
    have e1 := congrFun h1 j
    have e2 := congrFun h2 j
    simp only [Pi.smul_apply, smul_eq_mul] at e1 e2
    rw [e1, e2]
    have hX1 := abs_cross_le (fun j => (coeffMat n 0 j : ℝ)) (Sform n) _ _ (fun i => (hj i).1)
      (fun i => (hj i).2.2) j
    have hX2 := abs_cross_le (fun j => (coeffMat n 1 j : ℝ)) (Sform n) _ _ (fun i => (hj i).2.1)
      (fun i => (hj i).2.2) j
    rw [abs_mul, abs_mul, abs_neg, abs_inv, abs_of_pos hd, ← mul_add, inv_mul_le_iff₀ hd]
    calc _ ≤ 2 * (Real.exp ((b + ε') * n) * Real.exp ((-a + ε') * n)) +
          2 * (Real.exp ((b + ε') * n) * Real.exp ((-a + ε') * n)) := add_le_add hX1 hX2
      _ = 4 * (Real.exp ((b + ε') * n) * Real.exp ((-a + ε') * n)) := by ring
      _ ≤ Real.exp (ε' * n) * (Real.exp ((b + ε') * n) * Real.exp ((-a + ε') * n)) := by gcongr
      _ = Real.exp ((2 * b - a - ε') * n) * E := by
          rw [hE, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ (Vmat n).det * E := mul_le_mul_of_nonneg_right hdet (Real.exp_pos _).le
  -- the bridges `∑_j hv_j (q_j, p3_j, p4_j) = (-1)^n 6 Del_n (Q_n, P3_n, P4_n)`
  obtain ⟨hL3, hL0⟩ := Lfun_Fn_readout n
  have hbq : (q n 0 : ℚ) + (10 * n + 1) * q n 1 + (10 * n + 1) ^ 2 * q n 2 =
      (-1) ^ n * 6 * Del n * Q n := by
    have h := congrArg (fun z : FormalZ => z 3) (weighted_L n)
    simp only [Fin.sum_univ_three, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Zsym, Finsupp.single_apply,
      hL3] at h
    norm_num [hv] at h
    linear_combination h
  have hb3 : (p3 n 0 : ℚ) + (10 * n + 1) * p3 n 1 + (10 * n + 1) ^ 2 * p3 n 2 =
      (-1) ^ n * 6 * Del n * P3 n := by
    have h := congrArg (fun z : FormalZ => z 0) (weighted_L n)
    simp only [Fin.sum_univ_three, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Zsym, Finsupp.single_apply,
      hL0] at h
    norm_num [hv] at h
    linear_combination -h
  have hb4 : (p4 n 0 : ℚ) + (10 * n + 1) * p4 n 1 + (10 * n + 1) ^ 2 * p4 n 2 =
      (-1) ^ n * 6 * Del n * P4 n := by
    have h := congrArg (fun z : FormalZ => z 0) (weighted_M n)
    simp only [Fin.sum_univ_three, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Zsym, Finsupp.single_apply,
      Mfun_Fn_zero] at h
    norm_num [hv] at h
    linear_combination -h
  have hbqR : ((q n 0 : ℚ) : ℝ) + (10 * n + 1) * (q n 1 : ℝ) + (10 * n + 1) ^ 2 * (q n 2 : ℝ) =
      (-1) ^ n * 6 * (Del n : ℝ) * (Q n : ℝ) := by exact_mod_cast hbq
  have hb3R : ((p3 n 0 : ℚ) : ℝ) + (10 * n + 1) * (p3 n 1 : ℝ) +
      (10 * n + 1) ^ 2 * (p3 n 2 : ℝ) = (-1) ^ n * 6 * (Del n : ℝ) * (P3 n : ℝ) := by
    exact_mod_cast hb3
  have hb4R : ((p4 n 0 : ℚ) : ℝ) + (10 * n + 1) * (p4 n 1 : ℝ) +
      (10 * n + 1) ^ 2 * (p4 n 2 : ℝ) = (-1) ^ n * 6 * (Del n : ℝ) * (P4 n : ℝ) := by
    exact_mod_cast hb4
  have hDel : (1 : ℝ) ≤ (Del n : ℝ) := by
    have : (1 : ℚ) ≤ Del n := by
      unfold Del
      refine Finset.one_le_prod₀ fun j _ => ?_
      have : (0 : ℚ) ≤ (j : ℚ) * n := by positivity
      linarith
    exact_mod_cast this
  -- the weighted error sums
  set x : ℝ := 10 * (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set e3 : Fin 3 → ℝ := fun j => ζ3 * q n j - p3 n j with he3
  set e4 : Fin 3 → ℝ := fun j => ζ4 * q n j - p4 n j with he4
  have s3 : e3 0 + x * e3 1 + x ^ 2 * e3 2 = (-1) ^ n * 6 * (Del n : ℝ) * (ζ3 * Q n - P3 n) := by
    simp only [he3]; linear_combination ζ3 * hbqR - hb3R
  have s4 : e4 0 + x * e4 1 + x ^ 2 * e4 2 = (-1) ^ n * 6 * (Del n : ℝ) * (ζ4 * Q n - P4 n) := by
    simp only [he4]; linear_combination ζ4 * hbqR - hb4R
  have habs : ∀ y : ℝ, |(-1 : ℝ) ^ n * 6 * (Del n : ℝ) * y| = 6 * (Del n : ℝ) * |y| := by
    intro y
    rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos (by linarith : (0 : ℝ) < Del n)]
    ring
  have htri : ∀ e : Fin 3 → ℝ, |e 0 + x * e 1 + x ^ 2 * e 2| ≤ |e 0| + x * |e 1| + x ^ 2 * |e 2| := by
    intro e
    refine (abs_add_three _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
  have hsum : 6 * (Del n : ℝ) * (|ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n|) ≤ 3 * x ^ 2 * E := by
    have t3 := htri e3
    have t4 := htri e4
    rw [s3, habs] at t3
    rw [s4, habs] at t4
    have c0 := hcol 0
    have c1 := hcol 1
    have c2 := hcol 2
    have hx0 : 0 ≤ x := by linarith
    have k1 : x * |e3 1| + x * |e4 1| ≤ x * E := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left c1 hx0
    have k2 : x ^ 2 * |e3 2| + x ^ 2 * |e4 2| ≤ x ^ 2 * E := by
      rw [← mul_add]; exact mul_le_mul_of_nonneg_left c2 (by positivity)
    have k3 : E + x * E + x ^ 2 * E ≤ 3 * x ^ 2 * E := by nlinarith
    have : |e3 0| + |e4 0| ≤ E := c0
    rw [mul_add]
    linarith
  have hlin : 6 * (|ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n|) ≤ 3 * x ^ 2 * E := by
    have h0 : 0 ≤ |ζ3 * Q n - P3 n| + |ζ4 * Q n - P4 n| := by positivity
    nlinarith
  -- absorb the polynomial factor
  have hfin : x ^ 2 * E ≤ Real.exp ((-bDecay + ε) * n) := by
    calc x ^ 2 * E ≤ Real.exp (ε' * n) * E := mul_le_mul_of_nonneg_right hpoly hE0
      _ = Real.exp ((-b + ε) * n) := by
          rw [hE, ← Real.exp_add]; congr 1; rw [hε']; ring
      _ ≤ Real.exp ((-bDecay + ε) * n) := by
          gcongr
  have hxE : 0 ≤ x ^ 2 * E := by positivity
  linarith

end Meijer5255.LinformError
