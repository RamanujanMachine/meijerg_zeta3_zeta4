/-
# Node blueprint: `Q_growth` (paper §1, accepted analytic input `σ = a`)

Target (restated verbatim from `Blueprint_5255.lean`):
  `∀ ε > 0, ∀ᶠ n : ℕ in atTop, |(Q n : ℝ)| ≤ Real.exp ((aGrowth + ε) * n)`.

Strategy (`LEAN_HANDOFF.md` §5.8; handoff §4.11). The paper does not prove the growth rate: it
is the accepted analytic input `log|Q_n| = σn + o(n)` of §1. It is proved in `../zetas_irr` for
the zeta34 sequence: the rows `A_N, B_N` of the coefficient matrix `𝓒_N` (the `Z₄, Z₃`
coefficients of `𝓛_{2N}[(-t)^j R_N]`) grow like `e^{bN+o(N)}`, `det V_N` like `e^{(2b-a)N+o(N)}`
(spectral analysis of the limit matrix, cone argument), and `q_N = -(A_N × B_N)/det V_N`
(cross-product readout), so `|q_{Nj}| ≤ 2e^{2(b+ε')N}/e^{(2b-a-ε')N} = 2e^{(a+3ε')N} ≤ e^{(a+4ε')N}`.
The zeta34 objects (`Lfun`, `Rker`, `coeffMat`, `V`, `T`, `𝓡 = U₃₄ T`, `q`) are those of the
copied helper layer `QGrowth_*.lean`. The bridge to this repository's `Q_n` is pfq54's weighted readout
`∑_j q_{nj} hv_{nj} = (-1)^n 6 Del_n Q_n` with `hv = (1, 10n+1, (10n+1)²)` and
`Del_n = ∏_{j=8}^{12}(jn+1) ≥ 1`: it is the `Z₃`-coefficient of the formal identity
`∑_j hv_j (q_j Z₃ - p^{(3)}_j) = 3(-1)^n Del_n 𝓛_{2n}[F_n]` (dual kernel `R*_n`, weight
reduction modulo the companion relation at the endpoint of `F_n`), together with the endpoint
value `[Z₃] 𝓛_{2n}[F_n] = 2Q_n`. The glue then does the exponential bookkeeping:
`6|Q_n| ≤ 6 Del_n |Q_n| ≤ ∑_j |q_{nj}| hv_{nj} ≤ 3(10n+1)² e^{(a+4ε')n}`, and
`(10n+1)² ≤ e^{ε'n}` eventually, with `ε' = ε/5` and `a < aGrowth`.

Supporting lemmas (6), all proved (the line counts are the original blueprint estimates), and whether the PDF
proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `spectral_bounds` | 2500 | no (accepted analytic input; zeta34 `growth_estimates` + `GW_*`) |
| 2 | `q_eq_cross` | 400 | no (zeta34 `cross_product_readout.readouts_eq_cross`) |
| 3 | `abs_cross_le` | 15 | no (elementary inequality, not in the paper) |
| 4 | `weighted_L` | 350 | no (pfq54 `star_aux` dual-kernel bridge) |
| 5 | `Lfun_Fn_three` | 150 | yes (§3, endpoint value `2Q_n Z₃`) |
| 6 | `poly_absorb` | 30 | yes (the `o(n)` in §1) |

Reuse (all lemmas are proved): the helper layer `Meijer5255/QGrowth_*.lean`, shared with
`LinformError.lean`. It holds verbatim copies (namespace `ZetasIrr` renamed
`Meijer5255.QGA.ZetasIrr`) of `../zetas_irr/defs.lean` (all zeta34 objects used below) and of
`../zetas_irr/blueprints/{cross_product_readout, ZetasAux, derivSum_eq_realize_Lfun,
Mfun_sub_Mfun_pred, CMF_basic, CMF_transport, CMF_path, CMF_pairing, CMF_kernel, CMF_det,
coeffMat_zero, CMF_main, det_V_eq, GW_fast, GW_poly, GW_cert0..5, GW_bridge, GW_limit, GW_cone,
GW_Sbound, growth_estimates, pairing_identity}.lean`; an adapted copy `QGrowth_PF` of pfq54
`pf_aux.lean` (coefficients kept abstract) and a copy `QGrowth_Star` of pfq54 `star_aux.lean`
(lines 1–227); and the new `QGrowth_Bridge` (identification with this repository's `F_n`,
`aCoef`, `bCoef`, `Q`, `P3`, `P4`; `poly_absorb`).
-/
import Meijer5255.definitions
import Meijer5255.QGrowth_Bridge

open Filter Topology Finset Polynomial
open scoped Matrix RatFunc LaurentSeries

noncomputable section

namespace Meijer5255.QGrowth

open Meijer5255

/-! ### Objects

The zeta34 objects are those of the copied layer `QGrowth_defs` (zeta34 `defs.lean`, namespace
`Meijer5255.QGA.ZetasIrr`): `FormalZ`, `Zsym`, `Lfun` (zeta34's first formal functional `𝓛_K`),
`coeffMat` (`𝓒_N`), `V` (here called `Vmat`, the block `V_N` with `𝓒_N = (-1)^N 𝓒₀ V_N`), `p3`, `q`
(rows of `𝓡_N = U₃₄ V_N^{-T}`). pfq54's objects come from `QGrowth_PF` / `QGrowth_Star`: the kernel
`Fn n = lin (nR n) (dR n)`, which is `rootPoly (numRoots n) / rootPoly (denRoots n)`
(`QGA.Bridge.Fn_eq`), the weights `hv n = (1, 10n+1, (10n+1)²)` and `Del n = ∏_{j=8}^{12}(jn+1)`. -/

open Meijer5255.QGA.ZetasIrr (FormalZ Zsym Lfun coeffMat q p3)
open Meijer5255.QGA.ZetasIrr renaming V → Vmat
open Meijer5255.QGA.Pfq54.PF (Fn)
open Meijer5255.QGA.Pfq54.ST (hv Del)

/-! ### Supporting lemmas -/

/-- **[1] Spectral bounds** (part of zeta34 `growth_estimates`). There are `a < 53.28758332263`
and `b` such that, for every `ε > 0` and all large `N`, the rows `A_N, B_N` of `𝓒_N` satisfy
`|A_{Nj}|, |B_{Nj}| ≤ e^{(b+ε)N}` and `det V_N ≥ e^{(2b-a-ε)N}`.
Proof (zeta34 Part VII §1, §6): `a = -log λ₀`, `b = ½(log c₀ + a)` with `λ₀` the real root of the
characteristic polynomial `χ` of the limit matrix (exact rational bracketing); the rows satisfy
the CMF recurrence with gauge-normalised step matrices tending to the limit matrix (cone
argument `GW.cone_growth`); `det V_N = F_N` (factorial formula) and Stirling.
* Proved (≈ 8 lines): from the copied zeta34 `BP.growth_estimates` (`QGrowth_growth_estimates`,
  with `QGrowth_det_V_eq`, `QGrowth_GW_*`, `QGrowth_CMF_*`; ≈ 9000 copied lines, unchanged).
* Directly from the PDF: no (the paper accepts `σ` as analytic input, §1). -/
theorem spectral_bounds :
    ∃ a b : ℝ, a < aGrowth ∧
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
        (∀ j, |(coeffMat N 0 j : ℝ)| ≤ Real.exp ((b + ε) * N) ∧
          |(coeffMat N 1 j : ℝ)| ≤ Real.exp ((b + ε) * N)) ∧
        Real.exp ((2 * b - a - ε) * N) ≤ ((Vmat N).det : ℝ) := by
  obtain ⟨a, b, -, ha, -, -, hg⟩ := Meijer5255.QGA.ZetasIrr.BP.growth_estimates
  refine ⟨a, b, ?_, fun ε hε => ?_⟩
  · have : (53.28758332263 : ℝ) = 5328758332263 / 10 ^ 11 := by norm_num
    rw [aGrowth, ← this]
    exact ha
  · filter_upwards [hg ε hε] with N ⟨hj, hd⟩
    exact ⟨fun j => ⟨(hj j).1, (hj j).2.1⟩, hd⟩

/-- **[2] Cross-product readout of `q`.** `q_N = -(A_N × B_N) / det V_N`.
Proof: `𝓡_N = U₃₄ V_N^{-T}`, so the row `q_N = 6 (V_N^{-1})_{2,·}` is a column of the adjugate
divided by `det V_N`; with `𝓒_N = (-1)^N 𝓒₀ V_N` the adjugate column is `-(A_N × B_N)`.
* Proved (≈ 2 lines): the copied zeta34 `BP.q_eq_cross` (`QGrowth_growth_estimates`, first
  component of `readouts_eq_cross` in `QGrowth_cross_product_readout`).
* Directly from the PDF: no (zeta34 note; not part of this paper). -/
theorem q_eq_cross (N : ℕ) :
    (fun j => (q N j : ℝ)) = -((Vmat N).det : ℝ)⁻¹ •
      crossProduct (fun j => (coeffMat N 0 j : ℝ)) (fun j => (coeffMat N 1 j : ℝ)) :=
  Meijer5255.QGA.ZetasIrr.BP.q_eq_cross N

/-- **[3] Size of a cross product.** If `|u_i| ≤ M` and `|v_i| ≤ M'` then `|(u × v)_j| ≤ 2MM'`.
* Proved (≈ 2 lines): the copied zeta34 `BP.abs_cross_le` (`QGrowth_growth_estimates`).
* Directly from the PDF: no (elementary inequality, not stated in the paper). -/
theorem abs_cross_le (u v : Fin 3 → ℝ) (M M' : ℝ) (hu : ∀ i, |u i| ≤ M) (hv : ∀ i, |v i| ≤ M')
    (j : Fin 3) : |crossProduct u v j| ≤ 2 * (M * M') :=
  Meijer5255.QGA.ZetasIrr.BP.abs_cross_le u v M M' hu hv j

/-- **[4] Weighted dual readout** (pfq54 `star_aux.weighted_L` + `Lfun_W`).
`∑_j hv_{nj} (q_{nj} Z₃ - p^{(3)}_{nj}) = 3(-1)^n Del_n 𝓛_{2n}[F_n]` as formal combinations.
Proof: zeta34's dual identity `(-1)^n 3 𝓛_n[Q_{nj}(t) R*_n(t)] = q_{nj} Z₃ - p^{(3)}_{nj}`
(`dual_first_identity'`), the shift `R*_n(t+12n+1) ↔ (-t)^r F̃_n` (`Qmul_eq'`, `Lfun_laurent`),
the cutoff move `n → 2n` (`Lfun_Wj_cut`), and the reduction of the weighted sum
`∑_j hv_j ∑_r J_{jr} (-t)^r` modulo the companion relation of `F_n` at `wpt n` to the scalar
`Del_n` (`W_reduce`, `companion_L`).
* Proved (≈ 2 lines): `QGA.Bridge.weighted_L`, i.e. pfq54 `star_aux.weighted_L` + `Lfun_W`
  (copied in `QGrowth_Star`, with zeta34 `dual_first_identity'`).
* Directly from the PDF: no (the link between the zeta34 sequence and this paper's readouts is
  not in the paper; it is the pfq54 identification). -/
theorem weighted_L (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 3 - p3 n j • Zsym 0) =
      ((-1 : ℚ) ^ n * 3 * Del n) • Lfun (2 * n) (Fn n) :=
  Meijer5255.QGA.Bridge.weighted_L n

/-- **[5] Endpoint value: the `Z₃` coefficient.** `[Z₃] 𝓛_{2n}[F_n] = 2 ∑_j a_j = 2Q_n`.
Proof: `F_n` is proper (`polyPart = 0`), its poles are `-j`, `n ≤ j ≤ 17n`, of order `≤ 2`, and
the Laurent coefficient of order `2` at `-j` is `a_j` (`pfCoeff_Fn_two`, `aCoef` vanishes off
the poles); only `r = 2` contributes to `Z₃`.
* Proved (≈ 2 lines): `QGA.Bridge.Lfun_Fn_three` (pfq54 `pf_aux.Lfun_Fn_three`, adapted in
  `QGrowth_PF`, plus the identification `aF n j = aCoef n j`, `QGA.Bridge.aF_eq`; ≈ 100 new lines).
* Directly from the PDF: yes (§3, the endpoint contour integral `(-1)^n(2Q_n Z₃ + …)`). -/
theorem Lfun_Fn_three (n : ℕ) : Lfun (2 * n) (Fn n) 3 = 2 * Q n :=
  Meijer5255.QGA.Bridge.Lfun_Fn_three n

/-- **[6] Polynomial factors are subexponential.** `(10n+1)² ≤ e^{εn}` for all large `n`.
* Proved (≈ 2 lines): `QGA.Bridge.poly_absorb` (≈ 20 lines, from `x³/3! ≤ eˣ`).
* Directly from the PDF: yes (the `o(n)` of §1). -/
theorem poly_absorb (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (10 * (n : ℝ) + 1) ^ 2 ≤ Real.exp (ε * n) :=
  Meijer5255.QGA.Bridge.poly_absorb ε hε

/-! ### The node -/

/-- **Growth** (statement verbatim from `Blueprint_5255.lean`), proved from [1]–[6]. -/
theorem Q_growth :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, |(Q n : ℝ)| ≤ Real.exp ((aGrowth + ε) * n) := by
  obtain ⟨a, b, ha, hspec⟩ := spectral_bounds
  intro ε hε
  set ε' := ε / 5 with hε'
  have hε'pos : 0 < ε' := by positivity
  have h2N : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ Real.exp (ε' * N) := by
    have : Tendsto (fun N : ℕ => Real.exp (ε' * N)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hε'pos)
    exact this.eventually_ge_atTop 2
  filter_upwards [hspec ε' hε'pos, h2N, poly_absorb ε' hε'pos] with n ⟨hAB, hdet⟩ h2 hpoly
  have hdpos : (0 : ℝ) < (Vmat n).det := lt_of_lt_of_le (Real.exp_pos _) hdet
  -- `|q_{nj}| ≤ e^{(a + 4ε')n}`
  set E := Real.exp ((a + 4 * ε') * n) with hE
  have hq : ∀ j, |(q n j : ℝ)| ≤ E := by
    intro j
    have e := congrFun (q_eq_cross n) j
    simp only [Pi.smul_apply, smul_eq_mul] at e
    have hX := abs_cross_le (fun j => (coeffMat n 0 j : ℝ)) (fun j => (coeffMat n 1 j : ℝ))
      _ _ (fun i => (hAB i).1) (fun i => (hAB i).2) j
    rw [e, abs_mul, abs_neg, abs_inv, abs_of_pos hdpos, inv_mul_le_iff₀ hdpos]
    calc |crossProduct (fun j => (coeffMat n 0 j : ℝ)) (fun j => (coeffMat n 1 j : ℝ)) j|
        ≤ 2 * (Real.exp ((b + ε') * n) * Real.exp ((b + ε') * n)) := hX
      _ ≤ Real.exp (ε' * n) * (Real.exp ((b + ε') * n) * Real.exp ((b + ε') * n)) := by gcongr
      _ = Real.exp ((2 * b - a - ε') * n) * E := by
          rw [hE, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ (Vmat n).det * E := mul_le_mul_of_nonneg_right hdet (Real.exp_pos _).le
  -- the bridge `q_{n0} + (10n+1) q_{n1} + (10n+1)² q_{n2} = 6 (-1)^n Del_n Q_n`
  have hbr : (q n 0 : ℚ) + (10 * n + 1) * q n 1 + (10 * n + 1) ^ 2 * q n 2 =
      (-1) ^ n * 6 * Del n * Q n := by
    have h := congrArg (fun z : FormalZ => z 3) (weighted_L n)
    simp only [Fin.sum_univ_three, Finsupp.coe_add, Finsupp.coe_smul, Finsupp.coe_sub,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Zsym, Finsupp.single_apply,
      Lfun_Fn_three] at h
    norm_num [hv] at h
    linear_combination h
  have hbrR : ((q n 0 : ℚ) : ℝ) + (10 * n + 1) * (q n 1 : ℝ) + (10 * n + 1) ^ 2 * (q n 2 : ℝ) =
      (-1) ^ n * 6 * (Del n : ℝ) * (Q n : ℝ) := by
    exact_mod_cast hbr
  have hDel : (1 : ℝ) ≤ (Del n : ℝ) := by
    have : (1 : ℚ) ≤ Del n := by
      unfold Del
      refine Finset.one_le_prod₀ fun j _ => ?_
      have : (0 : ℚ) ≤ (j : ℚ) * n := by positivity
      linarith
    exact_mod_cast this
  -- the size of the weighted sum
  set x : ℝ := 10 * (n : ℝ) + 1 with hx
  have hx1 : 1 ≤ x := by rw [hx]; have : (0 : ℝ) ≤ n := n.cast_nonneg; linarith
  have hxx : x ≤ x ^ 2 := by nlinarith
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hsum : |((q n 0 : ℚ) : ℝ) + x * (q n 1 : ℝ) + x ^ 2 * (q n 2 : ℝ)| ≤ 3 * x ^ 2 * E := by
    have h0 := hq 0
    have h1 := hq 1
    have h2 := hq 2
    calc |((q n 0 : ℚ) : ℝ) + x * (q n 1 : ℝ) + x ^ 2 * (q n 2 : ℝ)|
        ≤ |((q n 0 : ℚ) : ℝ)| + x * |(q n 1 : ℝ)| + x ^ 2 * |(q n 2 : ℝ)| := by
          refine (abs_add_three _ _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x),
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
      _ ≤ E + x * E + x ^ 2 * E := by gcongr
      _ ≤ 3 * x ^ 2 * E := by nlinarith
  have hQ6 : 6 * |(Q n : ℝ)| ≤ 3 * x ^ 2 * E := by
    have habs : |(-1 : ℝ) ^ n * 6 * (Del n : ℝ) * (Q n : ℝ)| = 6 * (Del n : ℝ) * |(Q n : ℝ)| := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_pos (by norm_num : (0 : ℝ) < 6), abs_of_pos (by linarith : (0 : ℝ) < Del n)]
      ring
    rw [hbrR, habs] at hsum
    have : 6 * |(Q n : ℝ)| ≤ 6 * (Del n : ℝ) * |(Q n : ℝ)| := by
      have := abs_nonneg (Q n : ℝ)
      nlinarith
    linarith
  -- absorb the polynomial factor
  have hfin : x ^ 2 * E ≤ Real.exp ((aGrowth + ε) * n) := by
    calc x ^ 2 * E ≤ Real.exp (ε' * n) * E := mul_le_mul_of_nonneg_right hpoly hE0
      _ = Real.exp ((a + ε) * n) := by
          rw [hE, ← Real.exp_add]; congr 1; rw [hε']; ring
      _ ≤ Real.exp ((aGrowth + ε) * n) := by
          gcongr
  have hxE : 0 ≤ x ^ 2 * E := by positivity
  linarith

end Meijer5255.QGrowth
