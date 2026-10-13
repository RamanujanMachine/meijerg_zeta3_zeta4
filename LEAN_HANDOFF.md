# Lean formalization handoff: improved arithmetic for `A ζ(3) + B ζ(4)` (MeijerG(5,2,5,5,1), trajectory `(16,17,-11,-12,-10;2,1,0,-1,-2)`)

This file is meant to let a formalizing agent work without re-reading the whole paper, its
predecessor, the Python certificates, and two sibling Lean projects. It is self-contained for
planning. Go to the sources only for the details pointed to.

* **Paper being formalized:**
  `results/meijerg5255_improved/meijerg_zeta3_zeta4_improved.tex` (15 pp.).
  * Its Sections 1–6 are verbatim copies of the predecessor
    `results/meijerg5255_arithmetic/meijerg_zeta3_zeta4_arithmetic.tex`.
  * The genuinely new parts are §"A second-order trace identity", §"Application to the
    Meijer–G rational kernel", §"The improved divisor and its density", and the final numbers.
* **Sibling Lean projects** (same toolchain; reuse heavily, but **by copying files into this
  repo**, see §0 and §7):
  * `../zetas_irr/`: the most important one. It contains two complete proofs of
    `LinearIndependent ℚ ![1, ζ3, ζ4]`:
    * **zeta34**: `blueprint.lean`, `defs.lean`, `blueprints/*.lean`.
    * **pfq54**: `pfq54_formalization_handoff/*.lean`.
  * `../zeta2_four_trajectory_matrices/`: an irrationality-measure proof for ζ(2). It is useful
    for its patterns only; there is nothing to import directly.

---

## 0. Decisions already made by the user (do not re-litigate)

| Question | Decision |
|---|---|
| Scope | **Everything**, including the analytic input (σ, E). The analytic input is already proved in `../zetas_irr/blueprints` (see §5.8–5.9); copy it into this repo (§7). |
| CMF link | **Include** the identity between `(Q_n, P_{3,n}, P_{4,n})` and the native CMF product `W_n` (§5.2). |
| Prime number theorem | **Same as `../zetas_irr`**: one `sorry`'d lemma `prime_number_theorem` (copied from `blueprints/log_Delta_le.lean`), used through `pnt_bounds`. Add **no other** `sorry` or `axiom`. `#print axioms` of the final theorem must show only that `sorryAx`. |
| Certificates | **Same as siblings**: `decide +kernel` (and `norm_num`), **never `native_decide`**. Split large checks into many small files (pattern: `Chamber_cert0..29`, `cas_cert0..7`). |
| Which `W_n` | **The product along the paper's block path** (§5.2), i.e. exactly what the proof walks. |
| Code location | **Only this repo.** Code reused from `../zetas_irr` (and patterns from `../zeta2…`) is **copied or rewritten into this repo**. No Lake dependency on the sibling projects. Copy list in §7. |
| Statement form | **Literal `Filter.liminf`**, as in the paper. Make it total by taking δ in `EReal`, with `⊤` for exact approximants (§4, §5.10). |

All open questions are resolved (§9).

---

## 1. What is proved (mathematically)

Fix integers `(A,B) ≠ (0,0)`. Let `n = N − 1 ≥ 0`; the paper's `N` is the depth, and Lean
should index by `n`. Define the approximant `r_n(A,B) = (A P_{3,n} + B P_{4,n}) / Q_n` (§2), its
reduced denominator `q_n`, and

    δ_n(A,B) = −1 − log|Aζ(3)+Bζ(4) − r_n| / log q_n .

**Main theorem.** `liminf δ_n(A,B) > 0.01634832` for every fixed `(A,B) ≠ 0`, and
`liminf δ_n(A,0) > 0.22626234` when `A ≠ 0`. The exact rationals are
`0.01634832 = 102177/6250000` and `0.22626234 = 11313117/50000000`.

Nonvanishing and irrationality are **not** claimed by the paper, and they are **not needed**.
The paper assigns `δ = +∞` to exact approximants. With that convention, the cases that would
make `δ_n` ill defined (`q_n = 1` with nonzero error) are excluded eventually by elementary
arguments (§5.10). So do **not** copy pfq54's irrationality proof or its analytic module
(Levinson, Mellin–Barnes, Casoratian certificates; about 80 files).

**Proof skeleton.**
1. **Readout.** `Q_n, P_{3,n}, P_{4,n}` are explicit partial-fraction sums of the rational kernel
   `F_n`. They equal entries of the native CMF product `W_n`.
2. **Integrality** (I2). `(6 C_n d_{19n}^3 / G_n) (Q_n, P_{3,n}) ∈ ℤ²` and
   `(6 C_n d_{19n}^4 / G_n) (Q_n, P_{3,n}, P_{4,n}) ∈ ℤ³`, where
   `C_n = (15n)!²/(10n)!³`, `d_m = lcm(1..m)`, and `G_n = G_n^{new}` is an explicit product of
   prime powers.
3. **Divisor density.** `liminf log G_n / n ≥ γ_new > 30.45854724` (PNT).
4. **Height.** `log|Q_n| ≤ (a+ε) n`, `log C_n ≤ (30 log(3/2) + ε) n`,
   `log d_{19n} ≤ (19+ε) n` (PNT).
5. **Error.** `|Q_n ζ(s) − P_{s,n}| ≤ e^{(−b+ε)n}` for `s = 3,4`, where
   `a ∈ (53.28758332262, 53.28758332263)` and `b > 59.51995592483`.
6. **Arithmetic.** `δ ≥ (a+b)/(30 log(3/2) + 19r − γ + a) − 1` with `r = 3` (B = 0) or `r = 4`.

---

## 2. Exact objects, with the existing Lean names to reuse

**The sequence is literally the same as pfq54's.** Do not redefine it; use the copied `Pfq54_defs` (§7).

| Paper | Meaning | Lean (existing) |
|---|---|---|
| `F_n(t) = ∏_{u=0}^{2} (t−(10+u)n)_{10n} / ((t+n)_{16n+1} (t+2n)_{14n+1})` | rational kernel | `Pfq54.PF.Fn n := lin (nR n) (dR n)` (`pf_aux.lean`; root multisets `nR`/`dR` in `residue_aux.lean`) |
| numerator roots | `[1,10n] ∪ [n+1,11n] ∪ [2n+1,12n]` | `numRoots n` (`residue_block.lean`), `nR n` |
| denominator roots | `[−17n,−n] ∪ [−16n,−2n]` | `denRoots n`, `dR n` |
| `F_n = Σ_{j=n}^{17n} (a_j/(t+j)² + b_j/(t+j))` | partial fractions; `a_j = 0` unless `2n ≤ j ≤ 16n` | `aC n j = (−1)^n U n j / Cn n`, `bC n j = (−1)^n V n j / Cn n` (`residue_block.lean`) |
| `C_n = (15n)!²/(10n)!³` | normalization | `Pfq54.Cn` |
| `C_n·(−1)^n·(a_j, b_j)` | integer jets | `Pfq54.U n j`, `Pfq54.V n j` (dual-number jets `coeffJet`) |
| `Q_n = Σ a_j` | | `Pfq54.Qa n = (−1)^n S0 n / Cn n` |
| `P_{3,n} = Σ (a_j H^{(3)}_{j+2n} + b_j H^{(2)}_{j+2n}/2)` | | `Pfq54.P3a n` (via `S3`) |
| `P_{4,n} = Σ (a_j H^{(4)}_{j+2n} + b_j H^{(3)}_{j+2n}/3)` | | `Pfq54.P4a n` (via `S4`) |
| `r_n(A,B)` | approximant | `Pfq54.approx n A B = (A S3 + B S4)/S0` (identical ratio) |
| `δ_n` | | `Pfq54.delta n A B` (uses `(approx n A B).den`) |
| `d_{19n}` | | `Pfq54.D n = (Icc 1 (19n)).lcm id` |
| `6 d^4 (S0,S3,S4)` | integer vector, r = 4 | `Pfq54.Zv n` |
| eligible primes (E): `p > 29`, `p² > 30n`, `p ∤ n` | | `Pfq54.Eligible n p` |
| `c(x) = 2⌊15x⌋ − 3⌊10x⌋` | `v_p(C_n)` at eligible `p`, `x = n/p` | `Pfq54.cfun` |
| `ζ(3), ζ(4)` | `(riemannZeta k).re` | `Pfq54.ζ3`, `Pfq54.ζ4` (and `ZetasIrr.ζ3/ζ4`) |

Closed forms of the coefficients, useful for checks (`partial_fractions.py: pf_fast`):

* For `2n ≤ j ≤ 16n`:
  `a_j = (−1)^n (j+10n)!(j+11n)!(j+12n)! / [ j!(j+n)!(j+2n)!(j−n)!(17n−j)!(j−2n)!(16n−j)! ]`
  and `b_j = a_j L_j`, where
  `L_j = Σ_u (H_{j+un} − H_{j+(10+u)n}) + H_{j−n} − H_{17n−j} + H_{j−2n} − H_{16n−j}`.
* For `n ≤ j < 2n`:
  `a_j = 0`, `b_j = (−1)^{j−n} N_j (2n−j−1)! / (D_j (16n−j)!)`.
* For `16n < j ≤ 17n`:
  `a_j = 0`, `b_j = (−1)^{j−n+1} N_j (j−16n−1)! / (D_j (j−2n)!)`.

Here `N_j = (j+10n)!(j+11n)!(j+12n)!` and `D_j = j!(j+n)!(j+2n)!(j−n)!(17n−j)!`.

**Two normalizations.** pfq54 only has the `r = 4` vector `Zv`. The B = 0 claim needs the new
`r = 3` vector `Z3v n := ![6 * D n ^ 3 * S0 n, 6 * D n ^ 3 * S3 n]`. It is integral for the same
reason (`U ∈ ℤ`, `D·V ∈ ℤ`, `D^r H^{(r)}_m ∈ ℤ` for `m ≤ 19n`; `Pfq54_aux.harm_int`).

---

## 3. Reuse map: what exists versus what is new

| Paper step | Status | Where / what to do |
|---|---|---|
| Analytic input: growth `a`, decay `b` | **exists** | `ZetasIrr.growth_estimates`, `ZetasIrr.readout_error_bound` (`blueprint.lean`, proved in `blueprints/growth_estimates.lean`, `readout_error_bound.lean`). Transfer to `Qa/P3a/P4a` via `Pfq54.ST.sum_q_hv`, `sum_p3_hv`, `sum_p4_hv` (`star_aux.lean`). See §5.8–5.9. |
| Well-definedness of δ (`q_n ≥ 2`) | **new, elementary** | No irrationality needed (§5.10). The `Rat.den_dvd` / `round` steps of `Pfq54.main_theorem`'s proof (`Blueprint_pfq54.lean:422-530`) are a good template. |
| `U ∈ ℤ`, `D V ∈ ℤ`, `Zv ∈ ℤ³` | **exists** | `Pfq54.Z_integral`. |
| `Z3v ∈ ℤ²` (d³ normalization) | **new, easy** | Copy the `Z_integral` proof. |
| Baseline carry profile `ψ` (paper eqs. (D), (LD), (V), (G); Farey-29 chambers) | **mostly exists** (new finding, §5.4) | `ψ` equals the max over factorial pairings: pfq54's 8 pairings **plus 2 more**. Reuse `Pfq54.permutation_lemma` and `Pfq54.BP.pairing_bound` with a 10-element list. This **avoids** the paper's `ℓ(x,y)` harmonic-cancellation machinery entirely. |
| Upper harmonic gains `h_0` = 3,2,1 on `x ∈ (1/19,1/18),(1/18,1/17),(1/17,1/16)` | **exists for r=4** | `Pfq54.upper_range_bound` (`hgain`). Redo for `r = 3`; the paper says `g_3 = g_4`. |
| Broad shell `8n < p < 11n` (first order, `t = 0`) | **exists** | `Pfq54.residue_block` (+ `residue_aux..5`). |
| **14 first-order shells and all periodic lifts** `{n/p} ∈ S` | **new (generalize `residue_block`)** | §5.5. |
| **Second-order trace lemma** and windows `(1/10,2/19)`, `(11/12,15/16)` with lifts | **new, hardest** | §5.6. |
| Divisibility assembly `G_new ∣ Z` | **generalize** | `Pfq54.G_dvd_Z` (`G_dvd_Z.lean`: `prod_prime_pow_dvd`, `profile_facts`, `padicValRat_Cn`, `block_valuation`). |
| Density `γ_new` | **generalize** | `Pfq54.log_G_ge` and `log_G_aux*.lean`, `profile_aux.lean` (PNT intervals, excluded primes). New: many more intervals, all periods, sharp tail bound (§5.7). |
| `log d_{19n} = 19n + o(n)`, `log C_n` | **exists** | `Pfq54.BP.log_D_eq_psi`, `psi_le_eventually`, `log_factorial_bounds` (`log_Z0_le.lean`); `ZetasIrr.BP.fact_bounds` (`growth_estimates.lean`). |
| **CMF identity** `Q_n = (−1)^n (W_n)_{00}` etc. | **new, large reuse** | zeta34 CMF library (`blueprints/CMF_basic.lean`, `CMF_transport.lean`, pattern from `CMF_path.lean`); endpoint facts in `star_aux.lean` (`wpt`, `wpt_ker`, `VC_wpt`). §5.2. |
| Final δ arithmetic | **adapt** | `Pfq54.main_theorem` second half. |

---

## 4. Recommended top-level Lean statements (blueprint nodes)

Model the blueprint file on `../zetas_irr/pfq54_formalization_handoff/Blueprint_pfq54.lean`:
* statements are verbatim copies of node-file theorems;
* each docstring says "From the manuscript: yes / partially / no";
* glue proofs live in the blueprint file.

Suggested namespace `Meijer5255` (or `Pfq54.Improved`).

```lean
-- §5.2  CMF identity (W n : Matrix (Fin 4) (Fin 4) ℚ is the native product, §5.2)
theorem cmf_readout (n : ℕ) :
    Qa n = (-1) ^ n * W n 0 0 ∧ W n 1 0 = 0 ∧
    P3a n = (-1) ^ n * (-(W n 2 0) / 2 + W n 3 0 / 4) ∧
    P4a n = (-1) ^ n * (-(W n 3 0) / 6)
-- consequently, with R_{A,B} = !![0, 0, -6A, 3A-2B; 12, 0, 0, 0]:
--   (R_{A,B} W_n e₀) = (12 (-1)^n (A P3a n + B P4a n), 12 (-1)^n Qa n),
-- so the quotient of its two entries is exactly approx n A B (checked by hand from cmf_readout).

-- §5.3  integrality, both normalizations
theorem Z3_integral (n : ℕ) (hn : 1 ≤ n) (i : Fin 2) : ∃ z : ℤ, Z3v n i = z

-- §5.4–5.6 local divisibility, one theorem per mechanism
theorem pairing_bound10 (n p) (hn : 1 ≤ n) (hp : Eligible n p) (r : Fin 2) (i) : ...p^(phi10 (n/p)) ∣ ...
theorem shell_first_order (n p) (hn : 1 ≤ n) (hp : Eligible n p)
    (hf : ∃ row ∈ shellRows, row.1 < Int.fract ((n:ℚ)/p) ∧ Int.fract ((n:ℚ)/p) < row.2) :
    1 ≤ padicValRat p (Qa n) ∧ -1 ≤ padicValRat p (P3a n) ∧ -2 ≤ padicValRat p (P4a n)
theorem trace_lemma ...            -- general (T2), §5.6
theorem shell_second_order (n p) (hn : 1 ≤ n) (hp : Eligible n p)
    (hf : (1/10 < fract (n/p) ∧ fract (n/p) < 2/19) ∨ (11/12 < fract (n/p) ∧ fract (n/p) < 15/16)) :
    3 ≤ padicValRat p (Qa n) ∧ 0 ≤ padicValRat p (P3a n) ∧ -1 ≤ padicValRat p (P4a n)
-- (padicValRat of 0 is 0 in Mathlib; prefer ZetasIrr.Aux.ValGE, which is "x = 0 ∨ k ≤ v_p x")

-- §5.7 the divisor
def Gnew (n : ℕ) : ℕ := ∏ p ∈ (range (19*n+1)).filter (Eligible n),
    p ^ ((phi10 (n/p)).toNat + hgain n p + shellInd n p + windowInd n p)
theorem Gnew_dvd (n) (hn : 1 ≤ n) : (∀ i, ∃ z : ℤ, Zv n i = Gnew n * z) ∧ (∀ i, ∃ z : ℤ, Z3v n i = Gnew n * z)
theorem log_Gnew_ge : ∀ᶠ n : ℕ in atTop, (30458547 / 10^6 : ℝ) * n ≤ Real.log (Gnew n)
    -- any rational γ with 30.4585465117 < γ < 30.4585472438 works (and must be
    -- below what the certificate of §5.7 proves, e.g. 30.4585471312 at K = 200), see §6

-- §5.8–5.9 analytic input transported to (Qa, P3a, P4a)
theorem Qa_growth : ∀ ε > 0, ∀ᶠ n in atTop, |(Qa n : ℝ)| ≤ exp ((53.28758332263 + ε) * n)
theorem linform_error : ∀ ε > 0, ∀ᶠ n in atTop,
    |ζ3 * Qa n - P3a n| + |ζ4 * Qa n - P4a n| ≤ exp ((-59.51995592483 + ε) * n)

-- §5.10 δ as a total function in EReal, following the paper's conventions:
--   paper: δ_N = −1 − log|α − r_N| / log q_N when q_N > 1 and the error is nonzero;
--   an exact approximant (error = 0) gets δ_N = +∞.
-- The remaining case (q_N = 1, error ≠ 0) is undefined in the paper. Give it any value
-- (here the junk −1); §5.10 proves it does not occur for large N.
def deltaE (n : ℕ) (A B : ℤ) : EReal :=
  if alpha A B = approx n A B then ⊤
  else ((-1 - Real.log |alpha A B - approx n A B| / Real.log (approx n A B).den : ℝ) : EReal)

-- paper's depth index N, with n = N − 1 steps
def deltaN (N : ℕ) (A B : ℤ) : EReal := deltaE (N - 1) A B

-- main theorem, literally as in the paper
theorem main_joint (A B : ℤ) (hAB : (A, B) ≠ (0, 0)) :
    ((102177 / 6250000 : ℝ) : EReal) < Filter.liminf (fun N => deltaN N A B) atTop
theorem main_pure3 (A : ℤ) (hA : A ≠ 0) :
    ((11313117 / 50000000 : ℝ) : EReal) < Filter.liminf (fun N => deltaN N A 0) atTop
```

`EReal` is a complete linear order, so `Filter.liminf` needs no boundedness side conditions.
Prove the theorems via:
* a lemma `∃ c : ℝ, c₀ < c ∧ ∀ᶠ N, (c : EReal) ≤ deltaN N A B`;
* then `Filter.le_liminf_of_le` (the cobounded side condition is automatic in a complete
  lattice: `isBoundedDefault`), with `c₀ < c ≤ liminf`.
* The index shift `N ↦ N − 1` is harmless (`Filter.tendsto_sub_atTop_nat`, or prove the eventual
  bound in `N` directly).

`alpha`, `approx` are pfq54's definitions (copied, §7). `approx` is the reduced-fraction-agnostic
rational `(A·S3 + B·S4)/S0`; `.den` gives the reduced denominator `q_N`, as the paper requires.

---

## 5. Node-by-node mathematics and Lean guidance

### 5.1 Conventions and junk values
* Work with `ZetasIrr.Aux.ValGE p k x := x = 0 ∨ k ≤ padicValRat p x` (`blueprints/ZetasAux.lean`).
  It has closure lemmas `.mul .add .sub .neg .mono`, plus `ValGE_sum` in `valuation_bound.lean`.
  Do not use raw `padicValRat` inequalities on sums.
* Integer from valuations: `exists_int_of_padicValRat_nonneg`
  (`blueprints/Delta_mul_Rmat_integral.lean`). Prime-power divisibility from local bounds:
  `prod_prime_pow_dvd` and `int_dvd_of_valGE` (pfq54 `G_dvd_Z.lean`, `pairing_bound.lean`).
* `harm` clamps negative indices. zeta34 `harm s (n:ℤ)` uses `toNat`. This caused a false
  blueprint statement before (`Mfun_sub_Mfun_pred` needed "all poles `< K`"). State "all poles
  are integers `≤ K`" and "denominator splits" explicitly (`derivSum_eq_realize_Lfun` needs
  `hsplit`).
* Excluded walls. `n/p` for eligible `p` is never a Farey fraction of order 29, because its
  reduced denominator is `p > 29` (and `p ∤ n`). So all floor-chamber checks happen at open-cell
  midpoints. Lean lemma pattern: zeta34 `Chamber_dsl.lean`, `Chamber_reduce.lean`,
  `Chamber_main.lean`; pfq54 `profile_aux.lean` (`grid`, `okF`, `chkL_sound`).

### 5.2 CMF identity (new; uses the zeta34 CMF library)

**Native matrices** (exact spec from `work/meijerg5255_arithmetic/paths/native.py`).
* Vertex `w = (a_0..a_4; b_0..b_4) ∈ ℤ^{10}`.
* `D_w(x) = ∏_i (x − (a_i − 1)) − ∏_j (x − b_j) = Σ_{k≤4} d_k x^k`, with
  `d_4 = 5 − Σa + Σb`. This is zeta34 `dc a b` (`CMF_transport.lean`).
* Companion `θ(w)`: `θ_{i,j} = [i = j+1]` for `j < 3`, and `θ_{i,3} = −d_i/d_4`.

Axis steps (`E` multiplies on the right; `W = E_1 E_2 ⋯` in path order). Here `v` is the new
vertex and `s_i = +1` for `i ∈ {0,1}`, `−1` for `i ∈ {2,3,4}`.

| step | native matrix |
|---|---|
| `a_i ↓` | `s_i (θ(w) − (a_i−1) I)` |
| `a_i ↑` | `(s_i (θ(v) − a_i I))⁻¹` |
| `b_j ↑` | `b_j I − θ(w)` |
| `b_j ↓` | `((b_j−1) I − θ(v))⁻¹` |

**Relation to zeta34.** `ZetasIrr.CMF.Amat d c = c I − θ`. Hence:

* **native step = σ · `Edge.mat e w`**, with `σ = −1` for moves of `a_0, a_1` and `σ = +1` for
  every other move. `Edge.mat` is in `CMF_transport.lean`: forward edges use
  `Amat (src).dc (cval)`, dividing edges its inverse.
* The path below makes `33n` moves of `a_0, a_1`, so `W_n^{native} = (−1)^n W_n^{zeta34-conv}`.
* This is the paper's sign `(−1)^{a_0+a_1}` in `R_w(t) = (−1)^{a_0+a_1} ∏Γ(t+b_j)/∏Γ(t+a_i)`.
* Coordinate labels: zeta34's `ker` pairs `(b₀,a₄),(b₁,a₀),…` internally, but the rational
  function `∏Γ(t+b)/∏Γ(t+a)` is symmetric. `dc` is symmetric too, and `cval` uses only the moved
  coordinate. So use your own coordinate order freely.

**Path and `W_n`.**
* Start `w_0 = (1,1,0,0,0; 0,0,0,0,0)`. End
  `w_n = (1+16n, 1+17n, −11n, −12n, −10n; 2n, n, 0, −n, −2n)`.
* Block order (`native.py` `ORDER=(2,3,4,0,1,5,6,8,9)`), i.e. the paper's path:
  1. `a_2 ↓ 11n`, `a_3 ↓ 12n`, `a_4 ↓ 10n`;
  2. `a_0 ↑ 16n`, `a_1 ↑ 17n`;
  3. `b_0 ↑ 2n`, `b_1 ↑ n`;
  4. `b_3 ↓ n`, `b_4 ↓ 2n`.
* Two products appear in the scripts:
  * `W_n^{block}`: the ordered product of native step matrices along this block path
    (`native.py` `segment`). This is the path the paper's proof uses, and `verify_readout.py`
    checks the readout identities against it for `n ≤ 5`.
  * `W_n^{traj}`: the ramanujantools trajectory walk,
    `MeijerG(5,2,5,5,1).trajectory_matrix(direction, start).walk(...)`, i.e.
    `∏_{k<n} M(w_0 + k·v)`, where `M` is one step along `v` (`reproduce.py`,
    `residuals/profile.py`). All δ measurements and `matrix_N*.json` /
    `residuals/column_N*.json` use this one.
  * `verify_readout.py` checks that column 0 of `W^{traj}` equals the `F_n` readout at
    `N = 50, 100`; hence it equals column 0 of `W^{block}` there.
* **Lean uses `W_n^{block}`** (user decision, §9). The trajectory walk is out of scope.
* `d_4 = 5 − Σa + Σb` along the path:
  * it starts at 3;
  * each `a↓` or `b↑` step adds 1, each `a↑` or `b↓` step subtracts 1;
  * so it rises to `3 + 33n`, returns to 3, rises to `3 + 3n`, and returns to 3.

  Hence `d_4 ∈ [3, 3+33n]`, never 0.
* Dividing edges are invertible: `Deval ≠ 0`, because `a_i ≠ b_j` in block 2 and
  `b_j − 1 ∉ {a_i − 1}` in block 4. Prove it symbolically.

**Kernels.**
* `ker(w_0) = 1/t²`.
* `ker(w_n) = F_n` as an unsigned rational function. pfq54 already proves this for a coordinate
  permutation of `w_n`: `Pfq54.ST.wpt n`, `wpt_ker : (wpt n).ker = Fn n` (`star_aux.lean`).

**Functionals** (zeta34 `defs.lean`):
* `Lfun K f` is the formal value of `−Σ_{t>K} f'(t)`, with `Lfun_K[(t−h)^{−r}] = r(Z_{r+1} − H^{(r+1)}_{K−h})`.
* `Mfun K f := −Lfun K f'`, which is `Σ_{t>K} f''(t)`.
* `IsMom Lfun 2` and `IsMom Mfun 3` (`CMF_basic.lean`) give linearity, the boundary identity and
  the cutoff move.
* Transport: `step_fwd`, `step_bwd`, `edge_transport`, `walk_transport` (`CMF_transport.lean`).
* The paper's contour integrals are these: `∫K_2 f/(2πi) = Lfun`, `∫K_3 f/(2πi) = −½ Mfun`.
* The paper's "two rational functionals" are just the `Z_3` and `Z_2` coefficients of `Lfun`.
  No separate functional is needed.

**Initial moments** at `w_0`, `K = 0` (`m_j = Φ[(−t)^j / t²]`):
* `Lfun`: `(2 Z₃, −Z₂, 1, −1/2)`. These use `B_0 = 1` and `B_1(1) = 1/2`.
* `Mfun`: `(6 Z₄, −2 Z₃, 0, 1)`. The paper's row `(−3ζ4, ζ3, 0, −1/2)` is `−½·` this.

**Cutoffs and boundary conditions.**
* Blocks 1–3 use `K = 0`.
* After block 3 the numerator has triple zeros at `1..10n`. Move the cutoff `0 → 2n` with the
  `IsMom` cutoff-move axiom (`Lfun_cut_many`, `star_aux.lean`).
* Block 4 uses `K = 2n`.
* The companion relation `Σ d_k m_k = 0` at each multiplicative-source vertex needs
  `g = ∏_j (t+b_j)·ker` to vanish to order `≥ ord` at `K` (zeta34 `VC ord K p`,
  `companion_of_VC`, `CMF_path.lean`).
  * Blocks 1–3: zero of order `≥ 3` at 0.
  * Block 4: zero of order `≥ 3` at `2n`. The factor `t + b_4` restores the zero lost when
    `b_4 = −2n`.
* `VC_wpt (n ord) (hord : ord ≤ 3) : VC ord (2n) (wpt n)` already covers the endpoint.

Unlike zeta34's fixed 72-step `offTable` + `decide`, these blocks have length `∝ n`. Prove the
boundary conditions for a generic vertex of each block shape, and induct over the block,
following the `AShape`/`BShape` and `VC_*` pattern of `CMF_path.lean`.

**Endpoint values** (partial fractions of `F_n`, `K − h = 2n + j`):
* `Lfun_{2n}[F_n] = 2Q_n Z₃ + (Σb_j) Z₂ − 2P_{3,n} Z₀`, with `Σ b_j = 0` because `F_n = O(t^{−2})`.
* `Mfun_{2n}[F_n] = 6Q_n Z₄ + 2(Σb_j)Z₃ − 6P_{4,n} Z₀`.

**Comparison.** `m(end) = m(start)·W^{zeta}` and `W^{zeta} = (−1)^n W_n`. Taking `Z₃, Z₂, Z₀` and
`Z₄, Z₀` coefficients of column 0 gives exactly `cmf_readout`. Check against
`verification_n*.json` / `verify_readout.py`.

Existing partial results to lean on:
* `Pfq54.ST.Lfun_W` / `Mfun_W` / `sum_q_hv` relate `Lfun_{2n}[F_n]` to zeta34's `q, p3, p4`.
* `cross_product_readout.lean` covers partial-fraction extraction (`exists_isPF`, `pfCoeff`).

### 5.3 Baseline integrality (paper §"A uniform denominator bound")
`C_n a_j ∈ ℤ` and `d_{16n} C_n b_j ∈ ℤ`. Hence `6 C_n d_{19n}^r (Q, P_3[, P_4]) ∈ ℤ`. This is
pfq54 `Z_integral`, stated via `U`, `V`. For `r = 3` (`Z3v`) only `S0`, `S3` are needed.

### 5.4 Baseline prime profile ψ (paper §"Primewise contents", appendix table)

The paper derives the exponent `g(x) = ψ({x}) + h_0(x)`, `x = n/p`, from exact valuation formulas
(D), (b±), (LD) involving the harmonic test `ℓ(x,y) = 0`, (V), and a 270-cell Farey-29 check.

**Finding (checked in this session with exact rationals; re-check in Lean).** Define

```lean
def pairings10 : List (List ℤ × List ℤ) :=
  [([8,13,13],[17,17]), ([11,11,11],[14,19]), ([9,9,14],[16,16]), ([12,12,12],[18,18]),
   ([11,11,14],[18,18]), ([9,9,12],[14,16]), ([10,10,10],[14,16]), ([9,11,14],[17,17]),
   ([9,9,14],[15,17]), ([8,13,13],[16,18])]          -- last two are NEW vs Pfq54.pairings
def phi10 (x : ℚ) : ℤ := max 0 (max over pairings10 of  cfun x − Σ_{d∈D} ⌊d x⌋ + Σ_{l∈L} ⌊l x⌋)
```

Then on **every** open Farey-29 cell, for every lift `t ≥ 0`, `ψ = phi10` and
`g = phi10 + hgain`. The midpoints of all 270 cells were checked against
`results/meijerg5255_arithmetic/profiles/exact_chambers.json` (`g3`, `g4`, `tail`); `ΣL = ΣD`
makes `phi10` 1-periodic.

* The max over all 120 permutations gives the same function.
* pfq54's 8 pairings miss `ψ` by exactly 1 on `(4/9, 5/11)` (needs `([9,9,14],[15,17])`) and on
  `(7/13, 6/11)` (needs `([8,13,13],[16,18])`). That costs density ≈ 0.0900, which would break
  the claimed constants.
* Both new pairings are realizable by permutations of the shifts `(−2..2)`, where
  `L = (10+b₀, 11+b₁, 12+b₂)` and `D = (16−b₃, 17−b₄)`:
  * `b = (−1,−2,2,1,0)` gives `([9,9,14],[15,17])`;
  * `b = (−2,2,1,0,−1)` gives `([8,13,13],[16,18])`.

So `Pfq54.BP.pairing_bound` generalizes by replacing `pairings` and `phi` with the 10-element
versions. Its proof goes per pairing via `permutation_lemma`, `pairing_realized` and
`padicValRat_lam`. **No `ℓ(x,y)` machinery is needed.** The table of `ψ` (nonzero intervals on
one period, value `v`; same as the paper's appendix):

```lean
def psiRows : List (ℚ × ℚ × ℕ) :=
  [(1/15, 1/13, 1), (1/13, 1/12, 2), (1/12, 1/10, 3), (2/15, 2/13, 1), (2/13, 3/17, 2),
   (3/17, 2/11, 1), (2/11, 1/5, 2), (1/5, 4/15, 1), (4/15, 5/17, 3), (5/17, 3/10, 2),
   (1/3, 2/5, 2), (2/5, 7/15, 1), (7/15, 9/19, 3), (9/19, 1/2, 2), (8/15, 7/13, 1),
   (7/13, 3/5, 2), (3/5, 2/3, 1), (2/3, 11/16, 3), (11/16, 9/13, 2), (9/13, 7/10, 3),
   (11/15, 14/19, 2), (14/19, 3/4, 1), (3/4, 4/5, 2), (4/5, 13/16, 1), (9/11, 16/19, 1),
   (13/15, 7/8, 2), (7/8, 15/17, 3), (15/17, 9/10, 2), (14/15, 17/18, 2), (17/18, 18/19, 1)]
```

pfq54's `profileRows` (`log_G_ge.lean`) differs exactly on the two cells above. Prove the table
with the pfq54 pattern `LG3.table_of_check` (`log_G_aux3.lean`) or zeta34's `Chamber_*`.

`h_0`: gains 3, 2, 1 for `p ∈ (18n,19n), (17n,18n), (16n,17n)` (only `t = 0`). This is
`Pfq54.hgain` and `upper_range_bound` (r = 4); redo for r = 3.

The paper also needs these exact facts:
* `ψ = c + 1` on all 47 Farey cells of the 14 shells and on the 9 cells of the two windows, where
  `c(f) = 2⌊15f⌋ − 3⌊10f⌋`. The certificates assert `C_v + 2 − tail = 1`.
* `c` is unchanged by lifts `f ↦ t + f`.

### 5.5 Fourteen first-order shells with periodic lifts (generalize `Pfq54.residue_block`)

**Claim (PS).** For eligible `p` with `f = {n/p} ∈ S` (union of the 14 open intervals):

    v_p(Q_n) ≥ 1,  v_p(P_{3,n}) ≥ −1,  v_p(P_{4,n}) ≥ −2.

Combined with `ψ = c+1` on `S`, the exponent becomes `c + 2` for both `r`.

```lean
def shellRows : List (ℚ × ℚ) :=
  [(1/11, 1/8), (3/13, 4/17), (3/11, 5/18), (4/13, 5/16), (4/11, 7/19),
   (5/13, 7/18), (5/12, 8/19), (5/11, 8/17), (6/11, 9/16), (7/12, 10/17),
   (7/11, 11/17), (7/10, 12/17), (8/11, 11/15), (10/11, 16/17)]
```

`(1/11, 1/8)` with `t = 0` is exactly pfq54's `residue_block` (`8n < p < 11n`).

**Proof outline** (paper §"Fourteen first-order shells…").
1. **Root data.** Write `n/p = t + f` and `y = k/p` for a residue `0 ≤ k < p`. High roots of class
   `k`:
   * numerator: `[⌊uf−y⌋+1, ⌊(u+10)f−y⌋]`, `u = 0,1,2`;
   * denominator: `[⌈−17f−y⌉, ⌊−f−y⌋]` and `[⌈−16f−y⌉, ⌊−2f−y⌋]` (these are the `t = 0`
     endpoints).
   * Let `h = #num − #den`. Shift by `ε₀ = ⌊2f − y⌋`.
2. **Chamber certificate** (finite, Farey-29 in `f`, all `y`-strata):
   * `h ≥ −1` everywhere;
   * where `h = −1`, the shifted endpoints equal the row of the table below, the same for all
     such `k`.
   * Endpoint changes lie on `y = mf + c` with `m ∈ {0,1,2,10,11,12,−1,−2,−16,−17}`, so all
     crossings have denominator `≤ 29`.
   * The script `all_shell_cells.py` checks 5400 strata; 47 cells pass.

   | f interval | N0 | N1 | N2 | D0 | D1 |
   |---|---|---|---|---|---|
   | (1/11,1/8) | [1,1] | [1,1] | [1,1] | [−1,0] | [−1,0] |
   | (3/13,4/17) | [0,1] | [0,2] | [1,2] | [−4,−1] | [−4,−1] |
   | (3/11,5/18) | [0,2] | [0,2] | [1,2] | [−5,−1] | [−4,−1] |
   | (4/13,5/16) | [0,2] | [1,3] | [1,3] | [−5,−1] | [−5,−1] |
   | (4/11,7/19) | [0,3] | [1,3] | [1,4] | [−6,−1] | [−6,−1] |
   | (5/13,7/18) | [1,3] | [1,4] | [1,4] | [−6,−1] | [−6,−1] |
   | (5/12,8/19) | [0,3] | [1,4] | [1,4] | [−7,−1] | [−7,−2] |
   | (5/11,8/17) | [0,3] | [0,4] | [1,4] | [−8,−2] | [−8,−2] |
   | (6/11,9/16) | [0,4] | [0,5] | [1,5] | [−10,−2] | [−9,−2] |
   | (7/12,10/17) | [−1,4] | [0,5] | [1,5] | [−11,−2] | [−10,−3] |
   | (7/11,11/17) | [−1,5] | [0,5] | [1,6] | [−12,−2] | [−11,−3] |
   | (7/10,12/17) | [−1,5] | [0,6] | [1,7] | [−13,−2] | [−12,−3] |
   | (8/11,11/15) | [−1,5] | [0,6] | [1,7] | [−13,−3] | [−13,−3] |
   | (10/11,16/17) | [−1,7] | [0,8] | [1,9] | [−17,−3] | [−16,−4] |

3. **Lifts.** `f → t + f` adds `30t` roots to each side of every class, so `h` is unchanged and
   `ε = 2t + ε₀`. The shifted intervals become:
   * `N_u`: `[(u−2)t + L_u, (u+8)t + U_u]`;
   * `D_0`: `[−19t + L_3, −3t + U_3]`;
   * `D_1`: `[−18t + L_4, −4t + U_4]`.

   All are affine in `t` and independent of `k`. Let `U_t(V)` be the corresponding monic rational
   function of degree `−1`.
4. **Local factorization.** `𝒬 = (X^p − X) N̄ / D̄ ∈ 𝔽_p[X]` has degree `p − 2` (pfq54
   `residue_aux4.Tp`, `Tp_natDegree`). Minimal classes satisfy
   `p F_n(k + p(V+ε)) ≡ −𝒬(k) U_t(V) mod p`; other classes reduce to 0.
   * High roots differ by `≤ ⌊29n/p⌋ < p`, i.e. by units (uses `p² > 30n`).
   * Harmonic indices of `U_t`'s poles are `≤ 19n/p < p`.
5. **Sum over residues.** The leading readout is `(const(t,row)) · Σ_k 𝒬(k) = 0`, since
   `deg 𝒬 < p − 1`: `FiniteField.sum_pow_lt_card_sub_one`, as in zeta2 `sum_eval_eq_zero` and
   pfq54 `residue_aux`.
   * The constant's value is irrelevant; only its `p`-integrality and independence of `k`
     matter.

pfq54's `residue_block` does steps 1–5 for row 1 with `t = 0` and an explicit kernel
`V³/((V+1)²(V+2)²)` (constants `−10`, `−28/3`). Generalize via a "row data → conclusion" lemma
parameterized by the 5 affine intervals, then instantiate 14 times.

### 5.6 Second-order trace lemma (new; highest risk)

**Lemma (T2).** Let `p` be an odd prime and `F` a monic rational function of degree `−2` with
integer roots and poles of order `≤ 2`. Take integer representatives `ℛ` of `ℤ/p` (pairwise
differences prime to `p`). Write each root as `k + pℓ` with `k ∈ ℛ`, and for each class `k` set:
* `N_k`, `D_k`: multisets of high roots `ℓ`;
* `h_k = |N_k| − |D_k|`;
* `U_k(V) = ∏_{N_k}(V−ℓ) / ∏_{D_k}(V−ℓ)`;
* `σ_k = ΣN_k − ΣD_k`.

Hypotheses:
1. `h_k ≥ −1` for all `k`;
2. all `U_k` with `h_k = −1` equal one `U`;
3. for `h_k = 0`, `U_k = (V − a_k) U` with `a_k ∈ ℤ`;
4. all used differences of distinct high roots are prime to `p`.

Conclusion: `p Σ_{k∈ℛ} F(k + pV) ≡ 0 mod p²` as a local rational function in `V`. So every
double-pole and simple-pole coefficient of this trace at an integral high pole lies in
`p²ℤ_(p)`. For `F_n` those coefficients are `A_ℓ/p` and `B_ℓ`, which gives (PB):
`A_ℓ ∈ p³ℤ_(p)`, `B_ℓ ∈ p²ℤ_(p)`.

**Proof** (paper §"A second-order trace identity"; extended version in
`results/meijerg5255_improved/arithmetic/second_order_trace.tex`).
* Deform roots `k + pℓ ↦ k + Pℓ`. At `P = 0`: `F_0 = Q̃/H`, `H = ∏_{k∈ℛ}(z−k)`,
  `Q̃ = ∏(z−k)^{h_k+1}`, `deg Q̃ = p − 2`.
* For `h_k = −1`: `F_0 = L_k/(z−k) + L_k A_k + O(z−k)`, `A_k = Σ_{s≠k} h_s/(k−s)`.
  For `h_k = 0`: `L_k = F_0(k)`. Let `B_k = Σ_{s≠k} σ_s/(k−s)`.
* Residue theorem (exact rational identities) for `F_0` and `∂_P F_P|_{P=0} = −F_0 Σ σ_s/(z−s)`
  (degree `≤ −3`) gives:
  * `Σ_{h=−1} L_k = 0`;
  * `Σ_{h=−1} L_k(B_k + σ_* A_k) + Σ_{h=0} σ_k L_k = 0`, with `σ_k = σ_* + a_k`.
* The linear coefficient of the trace is `U(V)(V+σ_*)·D`, with
  `D = Σ_{h=−1} L_k A_k + Σ_{h=0} L_k`.
* Mod `p`: `H ≡ z^p − z`, so `H' = −1`. Then `D ≡ −Σ_{k∈𝔽_p} Q̃'(k) = 0` since
  `deg Q̃' = p − 3 < p − 1`. Substitute `P = p`.

**Lean-friendly reformulation (recommended).** Skip the formal deformation parameter: expand at
`P = p` directly mod `p²`. Each factor `(u + p v)^{±1}`, with `u = k − k'` a unit, satisfies
`(u+pv)^{±1} ≡ u^{±1}(1 ± p v/u) mod p²` in `ℤ_(p)`. The products then become
"constant + p·(linear)" mod `p²`.
* The constant part vanishes by the exact identity `Σ L_k = 0`: the sum of residues of a proper
  rational function of degree `≤ −2` is 0.
* The linear part is `p·U(V)(V+σ_*)·D` with `D ≡ 0 mod p`.

Ingredients:
1. the sum of residues of a proper rational function is 0;
2. first-order expansion of products of units mod `p²` (`ValGE` calculus);
3. the finite-field derivative sum `Σ_{k∈𝔽_p} Q̃'(k) = 0`;
4. `L_k A_k ≡ −Q̃'(k)` (and `L_k ≡ −Q̃'(k)` for `h_k = 0`), from `H ≡ X^p − X`.

Partial-fraction coefficient extraction can reuse `ZetasIrr.pfCoeff` / `cross_product_readout`.
Prove the lemma generically. Its two applications differ only in data.

**Application** (paper §"Application to the Meijer–G rational kernel").
* Setting: `F = F_n`, `p > 29`, `p² > 30n`, representatives `1..p`, `n/p = t + f` with
  `f ∈ (1/10, 2/19)` or `(11/12, 15/16)` (all `t ≥ 0`).
* Minimal-class (`h_k = −1`) high-root intervals, before shifting the harmonic cutoff:

  | f | N0 | N1 | N2 | D0 | D1 |
  |---|---|---|---|---|---|
  | (1/10,2/19) | [0,10t] | [t,11t] | [2t,12t] | [−17t−2, −t−1] | [−16t−2, −2t−1] |
  | (11/12,15/16) | [0,10t+8] | [t+1,11t+9] | [2t+2,12t+10] | [−17t−16, −t−2] | [−16t−15, −2t−3] |

* `h_k = 0` quotients `U_k/U`:
  * first row: `V + 16t + 2` or `V + 2t + 1`;
  * second row: `V − (2t+1)`, `V − (10t+9)`, or `V + 17t + 16`.

  (`second_order_certificate.json` `runs.factors` stores `[slope, const]` pairs of `−a(t)`.)
* Residue 0 has `h = 1`, so representative `0 ↦ p` is harmless.
* Separation: `16n/p + 1 < p`, from `p² > 30n` and `p > 29`.
* Certificate (`second_order_certificate.py`, independent audit `independent_affine_chambers.py`):
  exactly 9 of 270 Farey-29 cells pass, and their union is the two windows.
  * Lifts are proved symbolically in `t`: the signed endpoint multiset of `U_k/U` reduces to `+1`
    at `a(t)` and `−1` at `a(t)+1`.
  * In Lean: a finite chamber check at `t = 0`, then an affine-in-`t` lemma (`omega`/`linarith`
    on endpoints).
* **Readout.**
  * Let `A_ℓ, B_ℓ` be the double- and simple-pole coefficients collected over a high pole `ℓ`.
    (T2) gives `A_ℓ ∈ p³ℤ_(p)` and `B_ℓ ∈ p²ℤ_(p)`; so `Q_n = Σ_ℓ A_ℓ ∈ p³ℤ_(p)`.
  * Use the prime-dependent harmonic cutoff `η = p⌈2n/p⌉ ∈ [2n, 10n]`. The readout is unchanged
    because `F_n', F_n''` vanish at `2n+1..10n` (triple zeros); this is the `IsMom` cutoff move,
    as in `star_aux.Lfun_cut_many` / `Lfun_mt_cut`.
  * Then `⌊(j+η)/p⌋ = ⌈2n/p⌉ − ℓ − 1` is independent of `k`, and `j + η ≤ 27n < p²`.
  * Individually `a_j ∈ pℤ_(p)` and `b_j ∈ ℤ_(p)`.
  * Result (SG): `v_p(Q_n) ≥ 3`, `v_p(P_{3,n}) ≥ 0`, `v_p(P_{4,n}) ≥ −1`. Exponent in both
    normalizations: `c + 3`, which is `ψ + 2`.
* **Rejected extension**, recorded in `REPORT.txt`: widening the window to the whole surrounding
  shell is FALSE. Counterexamples: `n = 999`, `p ∈ {1063, 1091, 1093, 1097}`; `n = 1999`,
  `p ∈ {2129, 2131}`.

### 5.7 Divisor `G_new` and density (generalize `Pfq54.log_G_ge`)

Exponent at eligible `p`, `x = n/p`, `f = {x}`:

    e(p) = phi10(x) + hgain(n,p) + 𝟙[f ∈ shells] + 𝟙[f ∈ (1/10,2/19) ∪ (11/12,15/16)]

* The windows lie inside shells 1 and 14, so total gain there is `c + 3`. Nothing is
  double-counted.
* `Pfq54.sgain` (shell 1, `t = 0`) is subsumed by the shell indicator.

Divisibility: at each eligible `p`, `v_p(6 C_n d^r P) ≥ e(p)`. Use the shell or window bound
where it applies, combined with `v_p(C_n) = c(x)` and `v_p(d_{19n}^r) = r` for `p ≤ 19n`.

**Density.** `γ_new = 6 + Σ_{psiRows} v·𝒟(a,b) + Σ_{shellRows} 𝒟(a,b) + 𝒟(1/10,2/19) + 𝒟(11/12,15/16)`,
where `𝒟(a,b) = Σ_{t≥0} (1/(t+a) − 1/(t+b))`. The 6 is `∫ h_0/x²`.

* **Paper:** `γ_new ≥ 30458547243805493774844991/10^24 > 30.45854724`.
* **Needed** (§6, with zetas_irr's analytic brackets): `γ > 30.4585465117` for r = 3 and
  `γ > 30.4585462420` for r = 4. **The margin is only about 7.3·10⁻⁷**, so crude tails fail:
  pfq54's "omit tail" and zeta2's "tail ≤ 3/K" are far too lossy.
* **Recommended certificate** (checked here): exact partial sums for `t < K`, plus the rational
  tail lower bound

      Σ_{t≥K} f(t) ≥ (b−a)/(K+b) + f(K)/2,   f(t) = 1/(t+a) − 1/(t+b).

  It follows from the trapezoid rule for convex decreasing `f` and `log(1+u) ≥ u/(1+u)`.
* Lower bounds obtained this way (vs. 30.4585465117 needed):

  | K | γ lower bound |
  |---|---|
  | 200 | 30.4585471312 |
  | 500 | 30.4585472286 |
  | 1000 | 30.4585472404 |

  Use merged intervals: 30 `psiRows` + 14 shells + 2 windows. The `f(K)/2` term is required for
  `K ≤ 1000`.
* **Kernel cost:** about 46 intervals × K terms. Follow zeta2's directed-rounding ℕ sums,
  split into chunks across files (`blueprint_gamma_sumA/B.lean`, chunks of 500).
* **PNT step:**
  * `liminf log G/n ≥ S_{K'}` for every finite `K'`, via `Pfq54.LG2.PNT`/`EXC`,
    `prime_interval`, `profile_gen`, `excluded_small` (`log_G_aux2.lean`, `log_G_ge.lean`).
  * Then `S_{K'} ≥ S_K + Σ_{intervals} [∫_K^{K'} f + (f(K) − f(K'))/2]`, and let `K' → ∞`.
    Alternatively, prove `liminf ≥ tsum` directly.
  * Eligibility exclusions cost `o(n)` (`excluded_small`).

Paper's component bounds, for cross-checks:
* `γ_old > 29.9127079828158127`;
* `𝒟(1/10,2/19) > 0.5075180069435895`;
* `𝒟(11/12,15/16) > 0.0383212540460914`;
* `𝒟` at `t = 0` over the shells: `195197/55440`.

### 5.8 Height (growth)
* `log|Q_n| ≤ (a+ε)n`. From `ZetasIrr.growth_estimates` (`|q N j| ≤ e^{(a+ε)N}`) and
  `Pfq54.ST.sum_q_hv : Σ_j q n j · hv n j = (−1)^n · 6 · Del n · Qa n`, where
  `hv = (1, 10n+1, (10n+1)²)` and `Del n = ∏_{j=8}^{12}(jn+1) ≥ 1`. Polynomial factors are
  absorbed (`pow_le_exp_eventually`-style lemma, zeta2 `readout_rates.lean`).
* `log C_n ≤ (30 log(3/2) + ε)n`. Use Stirling bounds: `ZetasIrr.BP.fact_bounds`, or pfq54
  `log_factorial_bounds`, or zeta2 `choose_le_ratio`.
  * Certify `30 log(3/2) < 12.1639532433` with rational atanh-series bounds:
    `log(3/2) = 2 atanh(1/5)`. Mathlib: `Real.log_two_near_10`; see pfq54 `eps_lt_exp`.
* `log d_{19n} ≤ (19+ε)n`: `Pfq54.BP.log_D_eq_psi`, `psi_le_eventually` (PNT).

### 5.9 Error (decay)
`ZetasIrr.readout_error_bound`:
`|ζ3 q − p3| + |ζ4 q − p4| ≤ e^{(−59.51995592483+ε)N}` for each column `j`. Combine with
`sum_q_hv`, `sum_p3_hv`, `sum_p4_hv` to get

    |ζ(3) Q_n − P_{3,n}| + |ζ(4) Q_n − P_{4,n}| ≤ poly(n) e^{(−b+ε)n}.

Then `|α − r_n| ≤ (|A|+|B|)·poly·e^{(−b+ε)n} / |Q_n|`. Do **not** route through the ratio rate of
pfq54's `error_bound` (`ε = 102/10⁵¹` gives only `E ≈ 112.8063 < 112.8075`, too weak for the
stated decimals). The linear-form route needs **no lower bound on `|Q_n|`** (§5.10).

### 5.10 Final inequality
* Let `X = log|Q_n|` and `K_r = 30 log(3/2) + 19r − γ` (`K_4 ≈ 57.71`, `K_3 ≈ 38.71`).
* Then `log q_n ≤ X + (K_r + ε)n` (reduced denominator divides `6 C_n d^r |Q_n| / G`, as in the
  `main_theorem` proof: `Rat.den_dvd`) and `−log|α − r_n| ≥ (b − ε)n + X − O(log n)`.
* The map `X ↦ (u + X)/(v + X)` is decreasing when `u > v` and `v + X ≥ log q_n > 0`. With
  `X ≤ (a + ε)n`:

      δ_n + 1 ≥ (a + b − 2ε − o(1)) / (a + K_r + 2ε + o(1)).

* **Well-definedness without irrationality.** Show that eventually `err_n = 0` (so δ = ⊤) or
  `q_n ≥ 2`.
  * Let `u_n = 6 C_n d^r Q_n / G_n` and `v_n = 6 C_n d^r (A P_{3,n} + B P_{4,n}) / G_n`. These
    are integers (§5.7), and `u_n > 0` because `S0 > 0` (`Z_integral`).
  * Then `|u_n α − v_n| ≤ e^{(K_r+ε)n} · e^{(−b+ε)n} → 0`, since `b > K_r`. Also
    `|err_n| = |u_n α − v_n| / u_n ≤ |u_n α − v_n| → 0`. No lower bound on `|Q_n|` is needed.
  * If `α ∉ ℤ`: eventually `|err_n| < dist(α, ℤ)`, so `r_n ∉ ℤ` and `q_n ≥ 2`.
  * If `α = m ∈ ℤ`: `u_n m − v_n` is an integer tending to 0, so it is eventually 0. Then
    `r_n = α` and `δ = ⊤`.
  * The `round` and `Rat.den_dvd` steps of `Pfq54.main_theorem`'s proof are a template.
* In the `err_n = 0` case, `deltaE = ⊤ ≥ c` trivially. Otherwise the inequality above applies.

---

## 6. Constants and margins (exact; recheck in Lean with rationals)

| Quantity | Value used | Source |
|---|---|---|
| `a` (growth, = σ) | `53.28758332262 < a < 53.28758332263` | `ZetasIrr.growth_estimates` |
| `b` (decay of linear forms) | `b > 59.51995592483` | `ZetasIrr.readout_error_bound` |
| `E = a + b` | `> 112.80753924745` (paper: `> 112.807539247454`) | |
| `30 log(3/2)` | `12.16395324324493…` | atanh series |
| `a + 30 log(3/2)` | `< 65.45153656587494` | **the paper's `65.451536565866` is slightly smaller; do not use it** |
| `γ_new` | `≥ 30.45854724380549` (paper) | §5.7 |
| `σ'_4 = a + 30log(3/2) + 76 − γ` | `110.99298932587493…` | |
| `σ'_3` | `91.99298932587493…` | |
| `δ` (r = 4) | `(a+b)/σ'_4 − 1 = 0.0163483291386 > 0.01634832` | margin `9.1·10⁻⁹` |
| `δ` (r = 3) | `0.2262623497084 > 0.22626234` | margin `9.7·10⁻⁹` |
| `γ` needed | r = 4: `> 30.4585462420`; r = 3: `> 30.4585465117` | |

For comparison, pfq54's own constants (65.46, 112.8, 29.004) give δ = 1/375. Replacing only γ by
30.4585 but keeping 65.46/112.8 gives δ ≈ 0.016203, which is not enough. The sharp brackets of
`growth_estimates` are required.

Final rational checks should be `norm_num`-sized:
* `δ_4`: `(a_lo + b_lo)/(a_hi + L_hi + 76 − γ) − 1 > 102177/6250000`;
* `δ_3`: the same with 57, `> 11313117/50000000`.

---

## 7. Project setup, conventions, pitfalls

* **Toolchain.** `leanprover/lean4:v4.35.0-rc4`, mathlib pinned to rev
  `850e7374944e42c0fb3cdb550d9b2ca409a51695` (as in `../zetas_irr`).
  * `../zeta2…` uses `v4.35.0-rc4` with mathlib `1f414401…`. Do not mix.
* **Layout: everything lives in this repo** (user decision). There is no Lake dependency on the
  sibling projects; reused files are copied in.
  * Suggested structure: a Lake project in `lean/`, containing `lakefile.toml`, `lean-toolchain`,
    and `lake-manifest.json` copied from `../zetas_irr` so the Mathlib pin is identical. Under it:
    * `lean/vendor/zeta34/`: copied zeta34 files;
    * `lean/vendor/pfq54/`: copied pfq54 files;
    * `lean/Meijer5255/`: new code, with the blueprint file `Blueprint_5255.lean`.
  * `../zetas_irr` registers **every file as its own `[[lean_lib]]`** with `srcDir`, so modules
    are imported by flat names (`import CMF_main`, `import Pfq54_defs`). Mirror that lakefile
    pattern for the copied files so their `import` lines and namespaces stay **unchanged**. Only
    edit a copied file where needed, and add a provenance header to each, e.g.
    `-- copied from ../zetas_irr/blueprints/CMF_basic.lean (commit d9d5223)`.
  * Make the default target (or an explicit `lean_lib` list) cover the new blueprint, so
    `lake build` really checks it. In `../zetas_irr` the default target is a stub that checks
    nothing.
  * Build: `lake exe cache get`, `lake build`, then
    `lake env lean Meijer5255/Blueprint_5255.lean` plus `#print axioms`.
* **Copy set.** This is the import closure of everything reused (computed in this session),
  with line counts. pfq54's irrationality / analytic module and zeta34's chamber, valuation and
  `Δ_N` proof are **not** needed.
  * **zeta34** (31 files, from `../zetas_irr/`):
    * `defs.lean` (276);
    * in `blueprints/`:
      * CMF transport: `CMF_basic` (416), `CMF_transport` (376), `CMF_path` (704),
        `CMF_kernel` (474), `CMF_pairing` (345), `CMF_det` (534), `CMF_main` (370);
      * growth and decay (the analytic input): `GW_fast` (369), `GW_poly` (293),
        `GW_cert0..5` (10 each), `GW_bridge` (344), `GW_limit` (160), `GW_cone` (443),
        `GW_Sbound` (242), `growth_estimates` (713), `readout_error_bound` (84);
      * functionals, partial fractions and identities: `ZetasAux` (650),
        `derivSum_eq_realize_Lfun` (196), `Mfun_sub_Mfun_pred` (453),
        `cross_product_readout` (999), `coeffMat_zero` (196), `det_V_eq` (120),
        `pairing_identity` (314);
      * `valuation_bound` (1936), needed by `upper_range_bound` for `ValGE_sum` and
        `harm_valuation`;
      * `log_Delta_le` (1543): **do not copy whole.** Copy only `prime_number_theorem` (the
        single `sorry`, line 131) and `pnt_bounds` (line 746; it depends only on
        `prime_number_theorem`) into a small `PNT.lean`. Keep namespace `ZetasIrr.BP` so callers
        still resolve, and point the `import log_Delta_le` lines of `log_G_ge` and `log_Z0_le`
        at it. Copying the whole file would also pull in `E34_le`, `Chamber_*` and 30 chamber
        certificate files.
  * **pfq54** (26 files, from `../zetas_irr/pfq54_formalization_handoff/`):
    * definitions and helpers: `Pfq54_defs` (253), `Pfq54_aux` (299), `jet_aux` (72),
      `hyp_readout` (183);
    * integrality and local divisibility: `Z_integral` (282), `permutation_lemma` (291),
      `pairing_bound` (202), `uv_aux` (131), `upper_range_bound` (177), `residue_aux` (141),
      `residue_aux2` (305), `residue_aux3` (242), `residue_aux4` (210), `residue_aux5` (339),
      `residue_block` (333), `G_dvd_Z` (168);
    * density and growth: `profile_aux` (199), `log_G_aux` (142), `log_G_aux2` (270),
      `log_G_aux3` (57), `log_G_ge` (246), `stirling_aux` (165), `log_Z0_aux` (150),
      `log_Z0_le` (243);
    * kernel link: `pf_aux` (620), `star_aux` (388).
  * The total is about 17k lines after trimming `log_Delta_le`. Many copied node files
    (`G_dvd_Z`, `log_G_ge`, `pairing_bound`, `upper_range_bound`) serve as **templates** to be
    generalized (10 pairings, shells, windows, d³). Prefer copying them unchanged and writing the
    generalized versions as new files under `Meijer5255/`, so the copies stay verifiable
    against the originals.
  * Patterns from `../zeta2_four_trajectory_matrices` are rewritten, not imported: directed-
    rounding sums `blueprint_gamma_sum*`, and `choose_le_ratio` / `pow_le_exp_eventually` in
    `Analytic/readout_rates.lean`.
* **Namespaces vary by file.** Check the `namespace` line before referencing a lemma:
  * pfq54: `Pfq54` (defs), `Pfq54.BP` (nodes, `residue_block`, `pairing_bound`, `log_Z0_le`),
    `Pfq54.ST` (`star_aux`), `Pfq54.PF` (`pf_aux`), `Pfq54.RA` (`residue_aux*`),
    `Pfq54.LG2`/`LG3` (`log_G_aux2/3`), `Pfq54.Aux` (`Pfq54_aux`);
  * zeta34: `ZetasIrr` (`blueprint.lean`, `Delta_mul_Rmat_integral`), `ZetasIrr.BP`
    (`growth_estimates`, `log_Delta_le`), `ZetasIrr.Aux` (`ZetasAux`), `ZetasIrr.CMF` (`CMF_*`).
* **Policies.** No `native_decide`. One shared PNT `sorry` only. Keep files at 1000–1400 lines.
  Machine-generated certificate files hold about 9 cases each. Use `decide +kernel` on `List ℕ`/`ℤ`/`ℚ`
  literals (never read JSON at elaboration time).
* **Blueprint discipline** (what made pfq54 succeed):
  * write the blueprint with `sorry`'d nodes first, with docstrings `Estimated proof length` and
    `From the manuscript: yes/partially/no`;
  * fill node files;
  * keep statements about explicitly defined objects;
  * label any remaining conditional assumption exactly.
* **Pitfalls.**
  * `padicValRat p 0 = 0`: use `ValGE`.
  * `harm` with negative or clamped indices.
  * Missing "poles are integers `≤ K`" and "split denominator" hypotheses.
  * `(Matrix)⁻¹ = 0` junk for singular matrices: prove invertibility of every dividing step.
  * Strict versus non-strict Farey walls: eligible `p` never lands on a wall.
  * Keep `η = p⌈2n/p⌉` per prime.
  * The two normalizations use different `d^r`.
  * Use the reduced denominator `(approx n A B).den`, not `S0`.
  * Docstring tables in the sibling projects are stale ("sorry", "open lemma ≈3000 lines");
    trust `grep sorry` / `#print axioms`.
* **Performance.** zeta34 `CMF_kernel.lean:24` has a shortcut instance to speed `field_simp`.
  One `set_option maxHeartbeats 4000000` is used in `CMF_pairing.lean`. In zeta2,
  `decide +kernel` files spend 10–40 s each.

---

## 8. Where things are in this repository

All paths are relative to this repository's root.

| Content | Path |
|---|---|
| Paper (improved) | `results/meijerg5255_improved/meijerg_zeta3_zeta4_improved.{tex,pdf}` |
| Predecessor (baseline, 14 shells; same §1–6) | `results/meijerg5255_arithmetic/meijerg_zeta3_zeta4_arithmetic.tex` |
| Trace lemma, longer write-up | `results/meijerg5255_improved/arithmetic/second_order_trace.tex` |
| Broad shell / periodic shells / readout notes | `work/meijerg5255_arithmetic/arithmetic/{broad_shell,periodic_shells,readout_and_baseline}.tex` |
| Result summary, rejected extensions | `results/meijerg5255_improved/REPORT.txt` |
| Experiment spec (trajectory, rows, spectral data) | `results/meijerg5255_improved/experiment.json` |
| Native CMF matrices (exact) | `work/meijerg5255_arithmetic/paths/native.py` |
| Partial fractions, closed forms | `work/meijerg5255_arithmetic/arithmetic/partial_fractions.py` (`pf_fast`, `kernel_readout`) |
| Readout identity checks (`n ≤ 5`) | `work/meijerg5255_arithmetic/arithmetic/verify_readout.py` |
| Baseline chambers (270 cells: `g3`, `g4`, `tail`) | `results/meijerg5255_arithmetic/profiles/exact_chambers.json` (+ `.py` in `work/…/profiles/`) |
| Shell chamber certificate (47 cells, endpoints, signatures) | `work/meijerg5255_arithmetic/arithmetic/all_shell_cells.{py,json}`, `high_kernel.py`, `shell_chamber_certificate.py` |
| Second-order certificate (9 cells, affine factors) | `work/meijerg5255_improved/arithmetic/second_order_certificate.{py,json}`; audit `work/meijerg5255_improved/audit/independent_affine_chambers.py` |
| Density and tails | `work/meijerg5255_improved/residuals/infinite_density.py`, `results/…/residuals/infinite_density.json` |
| Final δ arithmetic | `work/meijerg5255_improved/residuals/final_bound_certificate.py`, `results/…/residuals/final_bound_certificate.json` |
| Spectral constants (old rate certificate) | `work/meijerg5255_arithmetic/rates/certify_spectral_constants.py` |
| Finite regression data (`n = 1..7999`) | `results/meijerg5255_improved/verification_n*.json`, `residuals/column_N*.json`, `residuals/approximants.csv` |

Python (python-flint, sympy) is needed only to regenerate data. The Lean proof must not depend on
it.

---

## 9. Resolved questions (user answers, 2026-10-13)

1. **Which `W_n`.** The product along the paper's block path (§5.2), i.e. exactly what the
   proof uses.
   * The ramanujantools per-step trajectory walk (used for the δ measurements) is **not**
     formalized.
   * The paper only remarks that CMF conservation identifies the two. Numerically they agree in
     column 0 at N = 50, 100 (`verify_readout.py`).
2. **Location.** Only this repo. Reused sibling code is copied in (§7).
3. **Statement.** Literal `Filter.liminf` of an `EReal`-valued δ (`deltaN`, §4), with `⊤` for
   exact approximants as in the paper.
