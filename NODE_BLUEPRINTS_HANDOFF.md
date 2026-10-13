# Hand-off: per-node blueprint files for `lean/Meijer5255/Blueprint_5255.lean`

Written 2026-10-13. Continues `LEAN_HANDOFF.md` (read that first for the mathematics and the
reuse map). This file records the state of the *node blueprints* task and the designs already
worked out for the files not yet written.

## 1. The task (user request, 2026-10-13)

For every `sorry`'d theorem of `lean/Meijer5255/Blueprint_5255.lean` (13 nodes), write a
separate Lean file `lean/Meijer5255/<NodeName>.lean` that

1. restates the node **verbatim** (same statement; the file lives in a sub-namespace
   `Meijer5255.<NodeName>` so the name does not clash with the blueprint's);
2. breaks its proof into **at most 10 supporting lemmas**, each `sorry`'d, each with a docstring
   giving **estimated proof length in lines** and whether the lemma can be formalised
   **directly from the PDF** (`results/meijerg5255_improved/meijerg_zeta3_zeta4_improved.pdf`):
   `yes / partially / no`, with a reason;
3. **proves the node from those lemmas** (real glue, not `sorry`), and **compiles**.

Constraints: do **not** modify `Blueprint_5255.lean`; do **not** run computations or checks of
the paper's statements; do not edit any `sorry`-free statement.

## 2. State

| item | status |
|---|---|
| `lean/lakefile.toml` | changed: `roots = [...]` → `globs = ["Meijer5255.+"]`, so `lake build` checks every file under `lean/Meijer5255/`. Build passes (9044 jobs). |
| `lean/Meijer5255/CmfReadout.lean` | **done**, compiles (`lake env lean Meijer5255/CmfReadout.lean` clean apart from the 10 expected `sorry` warnings). 10 lemmas, node `cmf_readout` proved from lemmas [2],[3],[4],[8],[9],[10]. Use it as the **template** (header table, docstring format, namespace pattern). |
| remaining 12 node files | **done** (session 2), see §6. |

Node list with intended file names (all in `lean/Meijer5255/`):

| node | file | status |
|---|---|---|
| `cmf_readout` | `CmfReadout.lean` | done |
| `baseline_integrality` | `BaselineIntegrality.lean` | designed (§4.1) |
| `carry_facts` | `CarryFacts.lean` | designed (§4.2) |
| `baseline_profile` | `BaselineProfile.lean` | designed (§4.3) |
| `shell_first_order` | `ShellFirstOrder.lean` | sketch (§4.4) |
| `trace_lemma` | `TraceLemma.lean` | sketch (§4.5) |
| `window_root_data` | `WindowRootData.lean` | sketch (§4.6) |
| `window_readout` | `WindowReadout.lean` | sketch (§4.7) |
| `Gnew_dvd` | `GnewDvd.lean` | sketch (§4.8) |
| `log_Gnew_ge` | `LogGnewGe.lean` | sketch (§4.9) |
| `log_normalization_le` | `LogNormalizationLe.lean` | sketch (§4.10) |
| `Q_growth` | `QGrowth.lean` | sketch (§4.11) |
| `linform_error` | `LinformError.lean` | sketch (§4.12) |

## 3. Conventions (from the finished file)

```lean
import Meijer5255.Blueprint_5255
open Filter Topology Finset Polynomial
open scoped Matrix
noncomputable section
namespace Meijer5255.<NodeName>
open Meijer5255
... definitions, lemmas [1]..[≤10] (each `sorry`), then the node proved from them ...
end Meijer5255.<NodeName>
```

* **Do not use dot-notation definitions** (`def Vertex.foo`) inside the sub-namespace: they
  land in `Meijer5255.<NodeName>.Vertex.foo` and `w.foo` fails. Use plain functions
  (`kerR w`, `moveSrc m w`).
* Header docstring: strategy paragraph + a table `| # | lemma | est. lines | directly from the PDF |`
  + reuse pointers into `../zetas_irr`.
* Each lemma docstring: `**[k] Title.**`, proof idea, `* Estimated proof length: ≈ N lines`,
  `* Directly from the PDF: yes/partially/no (reason)`.
* Compile each file with `lake env lean Meijer5255/<File>.lean` from `lean/` (≈30–45 s each);
  `lake build` at the end. Python edits of these files must use UTF-8
  (`io.open(p, encoding='utf-8')`), the default codepage is cp1252 and breaks on `≥`.
* Matrix-entry arithmetic in glue proofs: `simp only [Fin.sum_univ_four] at h` then
  `norm_num [Matrix.vecHead, Matrix.vecTail] at h`, then `linear_combination`.
* `(-1)^n` bookkeeping: `have hs : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num`
  and `linear_combination c * h - X * hs`.

## 4. Designs for the remaining files

Each design lists definitions (D), lemmas (L, ≤ 10) with line estimates / PDF-directness, and the
glue proof. Line estimates are rough; PDF-directness refers to the paper's own text.

### 4.1 `baseline_integrality` (paper §4) — follow the paper's binomial route

D: `Pbin n : ℚ[X] := ∏_{u<3} C(X - un - 1, 10n)` (via `Polynomial` with
`Ring.choose`/descending Pochhammer, or `(∏_{i<10n} (X - un - 1 - i)) / (10n)!`);
`Lc n c : RatFunc ℚ := (15n)! / ∏_{j=c}^{c+15n} (X + j)`; `Fn` as in `CmfReadout` (or reuse the
`rootPoly` quotient).

L1 `factor_identity` (60, yes): `Cn n • Fn n = Pbin n * Lc n n * Lc n (2n)` as rational functions.
L2 `Pbin_int` (40, yes): `(Pbin n).eval k ∈ ℤ` for integers `k`.
L3 `dPbin_int` (80, yes): `dlcm (10n) * (derivative (Pbin n)).eval k ∈ ℤ` (Newton-basis identity
`C(x,m)' = ∑_{i=1}^m (-1)^{i-1} C(x, m-i)/i`, product rule).
L4 `Lc_residues` (40, yes): simple-pole coefficient of `Lc n c` at `-j` is `(-1)^{j-c} C(15n, j-c)`.
L5 `coeff_formulas` (120, yes): at a pole `-j`, `Cn aCoef n j = P(-j) ρ_n(j) ρ_{2n}(j)` and
`Cn bCoef n j = P'(-j) ρρ' + P(-j)(ρ ∑_{k≠j} ρ'_k/(k-j) + ρ' ∑_{k≠j} ρ_k/(k-j))` (`ρ = 0` outside
`[c, c+15n]`), from `pfCoeff` of a product.
L6 `harm_int` (30, yes): `m ≤ M → dlcm M ^ s * harm s m ∈ ℤ` (pfq54 `harm_integral`).
L7 `Z_of_coeffs` (60, yes): from `∀ j, Cn a_j ∈ ℤ` and `∀ j, d_{16n} Cn b_j ∈ ℤ` and L6 derive
`Z3v, Z4v ∈ ℤ` (the `6` absorbs `/2`, `/3`; `dlcm (16n) ∣ dlcm (19n)`).
L8 `sign_positivity` (80, **no** — not in the paper): `0 ≤ (-1)^n Cn aCoef n j` for all `j` and
`0 < (-1)^n Cn aCoef n (2n)` (from L5: `P(-j) = ∏ C(j+un+10n, 10n) > 0`,
`ρρ' = (-1)^n C(15n, j-n) C(15n, j-2n)`).
Glue: `aCoef` integrality from L5+L2+L4, `bCoef` from L5+L3+L4 (denominators `|j-k| ≤ 15n`,
`dlcm (10n), dlcm (15n) ∣ dlcm (16n)`), then L7; positivity: `(-1)^n Q = ∑ (-1)^n a_j`, sum of
nonnegatives with one positive term (`Finset.sum_pos'`-style), divided by `Cn > 0`.

### 4.2 `carry_facts` (paper §5 (E),(D); §7 last paragraph; §10)

L1 `padicValNat_factorial_small` (15, yes): `m < p² → padicValNat p m! = m / p`
(`padicValNat_factorial`, `Nat.log` bound; pfq54 `pairing_bound.lean:95`).
L2 `padicValRat_Cn` (30, yes): `= cfun (n/p)` for eligible `p` (`29n < p²`, floors of `15n/p`,
`10n/p` as `Int.floor` of rationals).
L3 `padicValNat_dlcm` (50, yes): prime `p ≤ m < p²` ⇒ `padicValNat p (dlcm m) = 1`
(`Nat.factorization_lcm` over `Finset.lcm`, or pfq54 `upper_range_bound.padicValRat_D`).
L4 `cfun_fract` (10, yes): `cfun x = cfun (Int.fract x)` (`⌊15(t+f)⌋ = 15t + ⌊15f⌋`).
L5 `psi_eq_cfun_succ_on_cells` (150, partially — asserted as certificate output): for
`f ∈ (0,1)` with `inRows shellRows f ∨ inRows windowRows f`, `psi f = cfun f + 1`. Finite case
split at the breakpoints `k/15, k/10` inside each row; each piece by `Int.floor_eq_iff` + `norm_num`
(or a `decide +kernel` chamber certificate over the Farey-29 cells, split into several files).
L6 `hgain_zero_on_cells` (30, yes): `hgain n p ≠ 0 → n/p ∈ (1/19, 1/16)`, disjoint from every
shell/window row (lowest rows `(1/11,1/8)`, `(1/10,2/19)`).
L7 `window_subset_shell` (20, yes): `(1/10,2/19) ⊂ (1/11,1/8)`, `(11/12,15/16) ⊂ (10/11,16/17)`.
Glue: L2; L3 with `19n < p²` from `30n < p²`; L4+L5+L6; L7 (unfold `inRows`, `List.any`).

### 4.3 `baseline_profile` (handoff §5.4 pairing route; paper §5 proves it differently)

D: `pairings10 : List (List ℤ × List ℤ)` (pfq54's 8 + `([9,9,14],[15,17])`,
`([8,13,13],[16,18])`); `rowVal LD x := cfun x - ∑_{d∈D}⌊dx⌋ + ∑_{l∈L}⌊lx⌋`;
`phi10 x := max 0 (max_{LD} rowVal LD x)`; `shift : Fin 5 → ℤ := ![-2,-1,0,1,2]`;
`lam σ n : ℚ` (the factorial ratio `C_n / C_b` of the permuted pairing).

L1 `phi10_cases` (15, no — new finding): `0 ≤ phi10 x ∧ (phi10 x = 0 ∨ ∃ LD ∈ pairings10, phi10 x = rowVal LD x)`.
L2 `pairing_realized` (40, no): each `LD ∈ pairings10` equals the lengths
`(10+b₀, 11+b₁, 12+b₂), (16-b₃, 17-b₄)` of some permutation `b = shift ∘ σ` (`decide`).
L3 `permutation_lemma` (300, yes — paper §4 argument applied to permuted factorials):
`lam σ n * Cn aCoef n j ∈ ℤ`, `dlcm(16n) * lam σ n * Cn bCoef n j ∈ ℤ`, hence
`lam σ n * Z3v n i, lam σ n * Z4v n i ∈ ℤ`.
L4 `padicValRat_lam` (60, yes): `padicValRat p (lam σ n) = -(rowValPerm σ (n/p) - cfun(n/p))`
style identity (Legendre, all arguments `< p²`).
L5 `valGE_of_lam_mul` (20, yes): `ValGE p (v_p l) x` from `l x ∈ ℤ`, `l ≠ 0`.
L6 `psi_eq_phi10` (250, no): for eligible `p`, `(psi (fract(n/p)) : ℤ) = phi10 (n/p)` —
Farey-29 chamber certificate (`decide +kernel`, several files; values from
`results/meijerg5255_arithmetic/profiles/exact_chambers.json`).
L7 `upper_range_bound` (180, partially): for eligible `p` with `16n < p < 19n`:
`ValGE p (phi10 (n/p) + hgain n p) (Z3v n i)` and same for `Z4v` (pfq54 `upper_range_bound`,
redone for `r = 3`); and `hgain n p = 0` otherwise is by definition.
Glue: case `hgain = 0`: L1 → either `phi10 = 0` (trivial `ValGE p 0` from integrality
`baseline_integrality`) or a row; L2 gives `σ`; L3+L4+L5 give `ValGE p (rowVal) Z`; rewrite
with L6. Case `hgain ≠ 0`: L7 + L6.

### 4.4 `shell_first_order` (paper §7; `t = 0` row 1 is pfq54 `residue_block`)

D: `rowData : List (ℚ × ℚ × (five affine intervals as (slope, const) pairs))` = the §7 table;
`resCount`, `hiRoots` (already in blueprint), `Tp p : ℤ[X] := (X^p - X) N̄ /ₘ D̄`.
L1 `root_count_cert` (200, partially): for `f` in a row, every residue has `h ≥ -1`, and `h = -1`
residues have the shifted high-root intervals of the row (finite Farey-29 × `y`-strata check at
`t = 0`, `decide +kernel`, split into files).
L2 `lift_lemma` (60, yes): `f ↦ t + f` adds `30t` roots per class, `ε = 2t + ε₀`, intervals become
the affine forms `[(u-2)t + L_u, (u+8)t + U_u]`, `[-19t + L₃, -3t + U₃]`, `[-18t + L₄, -4t + U₄]`.
L3 `Tp_natDegree` (40, yes): `deg 𝒬 = p - 2` (pfq54 `residue_aux4`).
L4 `local_factorization` (250, yes): `p F_n(k + p(V+ε)) ≡ -𝒬(k) U_t(V) (mod p)` at minimal
residues, `≡ 0` elsewhere (pfq54 `residue_block.local_identity`, `block_congruence`).
L5 `separation` (20, yes): distinct high roots differ by `≤ ⌊29n/p⌋ < p`.
L6 `harm_reduction` (60, yes): `p^r H^{(r)}_m` mod `p` for `m < p²` (pfq54 `harm_reduction`).
L7 `node_term` (120, yes): the readout of one residue is `const(t,row) · 𝒬(k)` + `p`-integral.
L8 `sum_residues` (30, yes): `∑_{k∈𝔽_p} 𝒬(k) = 0` for `deg < p-1` (`FiniteField.sum_pow_lt_card_sub_one`).
Glue: fix the row from `hs`, `t = ⌊n/p⌋`, assemble `Q, P3, P4` as sums over residues (pfq54
`readout_sums`), apply L7+L8.

### 4.5 `trace_lemma` (paper §8; handoff §5.6 "Lean-friendly" expansion mod `p²`)

L1 `residue_sum_zero` (80, yes): sum of residues of a proper rational function of degree `≤ -2`
is `0` (partial fractions + leading coefficient).
L2 `unit_expansion` (40, yes): `(u + p v)^{±1} ≡ u^{±1}(1 ∓ p v/u) (mod p²)` in `ValGE` form.
L3 `local_expansion` (150, yes): for each class `k`, `p F(k + pV) = L_k U_k(V)(1 + p(V A_k - B_k)) + O(p²)`
(minimal), `p L_k U_k + O(p²)` (`h_k = 0`), `O(p²)` otherwise.
L4 `constant_term` (40, yes): `∑_{h=-1} L_k = 0` (L1 applied to `F_0`).
L5 `linear_term` (120, yes): the `p`-coefficient equals `U(V)(V + σ_*) D` with
`D = ∑_{h=-1} L_k A_k + ∑_{h=0} L_k` (uses (RI), second identity from `∂_P F_P`).
L6 `D_mod_p` (100, yes): `L_k A_k ≡ -Q̃'(k)`, `L_k ≡ -Q̃'(k)`, hence `D ≡ -∑ Q̃'(k) = 0 (mod p)`
(`H ≡ X^p - X`, `deg Q̃' = p-3`).
L7 `coeff_extraction` (60, yes): from `p ∑_k F(k+pV) ≡ 0 (mod p²)` as local rational functions
with unit-separated poles, every double/simple-pole coefficient at an integral high pole is in
`p² ℤ_(p)`; these coefficients are `A_ℓ/p`, `B_ℓ` (gives (PB)).
Glue: L3–L6 ⇒ trace `≡ 0`; L7.

### 4.6 `window_root_data` (paper §9 table (S2))

L1 `cert_t0` (200, partially): at `t = 0` on the 9 Farey cells, all residue classes have
`h ≥ -1`, minimal classes share the table row, `h = 0` classes have the listed affine quotients
(`decide +kernel`).
L2 `lift_affine` (80, yes): endpoints affine in `t`; `U_k/U = V - a(t)` for every `t ≥ 0`.
L3 `separated` (20, yes): `16n/p + 1 < p`.
L4 `complete_reps` (15, yes): `Icc 1 p` is a complete residue system.
L5 `deg_coprime_poles` (30, yes): `Dr.card = Nr.card + 2`, `Nr ∩ Dr = ∅`, pole orders `≤ 2`.
Glue: build `TraceHyp` from L1–L5 with `NU, DU` = the row's multisets (as functions of `t`).

### 4.7 `window_readout` (paper §9 "stronger arithmetic readouts")

L1 `eta_props` (20, yes): `η = p⌈2n/p⌉ ∈ [2n, 10n]`.
L2 `cutoff_invariance` (120, yes): `P3, P4` unchanged when `H_{j+2n}` is replaced by `H_{j+η}`
(`F_n', F_n''` vanish at `2n+1..10n`; `IsMom.cut`-type argument or direct telescoping).
L3 `floor_independent` (30, yes): `-j = k + pℓ ⇒ ⌊(j+η)/p⌋ = ⌈2n/p⌉ - ℓ - 1`, `j + η < p²`.
L4 `individual_bounds` (80, yes): `a_j ∈ pℤ_(p)`, `b_j ∈ ℤ_(p)` from `h_k ≥ -1` + separation.
L5 `harm_split` (60, yes): `H^{(r)}_m = (p-free part) + p^{-r} ∑_{i ≤ ⌊m/p⌋} i^{-r}` with
`p`-integral first part (for `m < p²`).
L6 `assemble` (120, yes): `p^{r-1} P_{r,n} = ∑_ℓ (A_ℓ/p · w_ℓ + B_ℓ · w'_ℓ) + p²(…)` with
`p`-integral weights independent of `k`; apply `hPB`.
Glue: `Q = ∑_ℓ A_ℓ` (L4 + `hPB`), then L6.

### 4.8 `Gnew_dvd` (paper §10)

L1 `prod_prime_pow_dvd` (15, yes): pfq54 `G_dvd_Z.lean:31`.
L2 `int_dvd_of_valGE` (20, yes): `x ∈ ℤ`, `ValGE p k x` ⇒ `p^k ∣ x` (pfq54 `pairing_bound.lean:170`).
L3 `valGE_scaled` (40, yes): `ValGE p (cfun + r + v) (6 Cn d^r X)` from `ValGE p v X`,
`carry_facts` (`v_p Cn = cfun`, `v_p d = 1` for `p ≤ 19n`; for `p > 19n`, `gExp = 0`).
L4 `exponent_cases` (40, yes): `gExp n p = cfun+3` on windows, `cfun+2` on shells only,
`psi + hgain` otherwise (`carry_facts` clauses 3–4).
Glue: per eligible `p ≤ 19n` choose the case: `second_order_shell` / `shell_first_order` /
`baseline_profile`, then L3, L2, L1; integrality from `baseline_integrality`.

### 4.9 `log_Gnew_ge` (paper §10, handoff §5.7; margin only `7·10⁻⁷`)

L1 `log_Gnew_eq` (20, yes): `log Gnew = ∑_{p eligible ≤ 19n} gExp · log p`.
L2 `pnt_interval` (14, partially — PNT quoted): copy pfq54 `log_G_ge.lean:83` and the single
`sorry`'d `prime_number_theorem` (+ `pnt_bounds`) into a small `PNT.lean` (the only extra sorry
allowed; see `LEAN_HANDOFF.md` §0).
L3 `excluded_small` (30, yes): non-eligible primes contribute `o(n)`.
L4 `profile_gen` (120, yes): for each row `(a,b,v)` and period `t < K`, primes in
`(n/(t+b), n/(t+a))` contribute `≥ v (1/(t+a) - 1/(t+b) - ε) n`.
L5 `hgain_part` (40, yes): `h₀` contributes `≥ (6 - ε) n`.
L6 `finite_sum_cert` (kernel, many files): exact rational `S_K ≥ …` — **correction (session 2):**
`K = 200` gives only `30.4585471312 < gammaNew = 30.45854724`; use `K = 1000` with the sharper
tail `2(b-a)/(2K+a+b) + f(K)/2` (as done in `LogGnewGe.lean`). Original text:
with the tail bound `(b-a)/(K+b) + f(K)/2` per interval (directed-rounding ℕ sums, chunks).
L7 `tail_bound` (60, no — stated in paper only as an inequality): `∑_{t≥K} f(t) ≥ (b-a)/(K+b) + f(K)/2`.
L8 `assemble` (80, yes): combine with `ε/(number of intervals)`.

### 4.10 `log_normalization_le` (paper §11)

L1 `log_factorial_bounds` (40, yes): Stirling-type `|log m! - (m log m - m)| ≤ log m + 1`.
L2 `log_Cn_le` (50, yes): `log Cn ≤ 30 log(3/2) n + O(log n)`.
L3 `log32_lt` (30, yes): `30 log(3/2) < logCn` via `log(3/2) = 2 atanh(1/5)` series bounds.
L4 `log_dlcm_eq_psi` (20, yes): `log (dlcm m) = Chebyshev.psi m` (pfq54 `log_D_eq_psi`).
L5 `psi_le_eventually` (30, partially — PNT): `psi x ≤ (1+ε) x` eventually (from `pnt_bounds`
+ `ψ - θ = O(√x log x)`; pfq54 `psi_le_eventually`).
Glue: `filter_upwards`.

### 4.11 `Q_growth` and 4.12 `linform_error` (analytic input; "no" from the PDF)

Both need the zeta34 analytic module copied in (handoff §7 copy set, ≈ 7k lines:
`GW_*`, `growth_estimates`, `readout_error_bound`, `cross_product_readout`, …) plus the link
`∑_j q n j · hv n j = (-1)^n 6 Del n Q n` (pfq54 `star_aux.sum_q_hv/sum_p3_hv/sum_p4_hv`,
≈ 400 lines, after identifying this repo's `Q, P3, P4` with pfq54's `Qa, P3a, P4a`).
Lemma split: L1 `growth_estimates` (statement copied; 700+ lines, no), L2 `readout_error_bound`
(no), L3 `Q_eq_Qa`/`P3_eq_P3a`/`P4_eq_P4a` (definitional unfolding, 60), L4 `sum_q_hv` etc.
(400, partially), L5 `poly_absorb` (`Del n ≤ e^{εn}` eventually, 30, yes), L6 glue.

## 5. Next steps

1. Write the 12 remaining files following §3–§4, compiling each.
2. Run `lake build`; `grep -c sorry` per file; keep every file's lemma count `≤ 10`.
3. Report the per-file tables (lemma, lines, PDF-directness) to the user.

## 6. Progress log (updated as work proceeds)

* 2026-10-13, session 2: resumed. Plan: 4 parallel sub-agents, each owning disjoint files —
  A: `BaselineIntegrality`, `CarryFacts`, `BaselineProfile`; B: `ShellFirstOrder`, `TraceLemma`,
  `WindowRootData`, `WindowReadout`; C: `GnewDvd`, `LogGnewGe`, `LogNormalizationLe`;
  D: `QGrowth`, `LinformError`. Rules given to agents: verbatim node, ≤ 10 sorry'd lemmas,
  node glue may use only blueprint nodes that are logical prerequisites (never the node itself):
  `baseline_profile` ← `baseline_integrality`, `carry_facts`; `Gnew_dvd` ← `baseline_integrality`,
  `carry_facts`, `baseline_profile`, `shell_first_order`, `second_order_shell`;
  `log_Gnew_ge` ← `carry_facts`; `Q_growth`/`linform_error` ← `cmf_readout`; others ← none.
  PNT enters as a sorry'd lemma inside `LogGnewGe` / `LogNormalizationLe` (no extra PNT file).
  A file listed below as "done" has been compiled and reviewed by the coordinator.
* Agents A–D launched (session 2). If the session stops before they report, check which of the 12
  files exist and compile (`lake env lean Meijer5255/<File>.lean`); review each against §1 rules.
* Files done (compiled; reviewed by coordinator — statements checked by hand for truth, glue
  sorry-free): `CmfReadout.lean`; `QGrowth.lean` (6 lemmas, no blueprint deps);
  `LinformError.lean` (8 lemmas, no blueprint deps); `BaselineIntegrality.lean` (7 lemmas);
  `CarryFacts.lean` (5 lemmas); `BaselineProfile.lean` (8 lemmas; uses
  `Meijer5255.baseline_integrality`).
  Notes: QGrowth/LinformError copy the zeta34 `defs.lean` objects (renamed `harmZ`, `lpCoeff`,
  `polyPartZ`, `Vmat`, `Tmat`) into each file (duplicated, since each file imports only the
  blueprint). BaselineProfile [8] `upper_range_bound` for `r = 3` needs the sharper
  `v_p(C_n b_j) ≥ 0` at inactive `j` (pfq54's `r = 4` argument gives only `≥ -1`); noted in its
  docstring.
  `GnewDvd.lean` (3 lemmas; glue uses `baseline_integrality`, `carry_facts`, `baseline_profile`,
  `shell_first_order`, `second_order_shell`); `LogGnewGe.lean` (8 lemmas, incl. sorry'd
  `prime_number_theorem` and the certificate `gamma_cert` at `K = 1000`, see §4.9 correction);
  `LogNormalizationLe.lean` (5 lemmas, incl. sorry'd `prime_number_theorem`).
  `ShellFirstOrder.lean` (8 lemmas), `TraceLemma.lean` (6), `WindowRootData.lean` (6),
  `WindowReadout.lean` (6); no blueprint deps. Each carries a fully proved `ValGE` calculus
  section (glue helpers, not counted as lemmas). Highest-risk statements: the two chamber
  certificates `ShellFirstOrder.root_count_cert`, `WindowRootData.window_cert` (paper claims
  transcribed into floor/endpoint form), and `TraceLemma.local_expansion` (explicit mod-`p²`
  coefficient formulas, hand-checked against the paper's `U(V)(V+σ_*)D`).
  All 12 files written.
* **Task complete (2026-10-13, session 2).** `lake build`: success, 9056 jobs, 0 errors,
  99 `sorry` warnings = 13 blueprint nodes + 86 node-file lemmas; no node theorem in any node
  file warns. Lemma counts: CmfReadout 10, BaselineIntegrality 7, CarryFacts 5,
  BaselineProfile 8, ShellFirstOrder 8, TraceLemma 6, WindowRootData 6, WindowReadout 6,
  GnewDvd 3, LogGnewGe 8, LogNormalizationLe 5, QGrowth 6, LinformError 8.
  Known caveat: the blueprint's `log_Gnew_ge` docstring still says "`K = 200` already gives
  30.4585471312", which is below `gammaNew`; blueprint left untouched per the rules.

## 7. Session 3 (2026-10-13): proving the lemmas — user request

User request: (1) complete all proofs of the `sorry` lemmas; (2) move all definitions of the
blueprint into `definitions.lean` and import it where needed; (3) dependency graph of the repo
for the main theorem; (4) everything compiles + per-file compilation times.

**Done (structure):**
* `lean/Meijer5255/definitions.lean`: all defs of the old blueprint §1–constants (namespace
  `Meijer5255`). Backup of the pre-split files:
  scratchpad `Meijer5255_backup_session3/` (session-local; not in repo).
* Node files now `import Meijer5255.definitions` (+ the node files they use:
  `BaselineProfile` ← `BaselineIntegrality`; `GnewDvd` ← `BaselineIntegrality`, `CarryFacts`,
  `BaselineProfile`, `ShellFirstOrder`, `SecondOrderShell`), referencing e.g.
  `BaselineIntegrality.baseline_integrality`.
* New `SecondOrderShell.lean` (glue, sorry-free) — moved out of the blueprint to avoid an import
  cycle with `GnewDvd`.
* New `PNT.lean`: the single accepted `sorry` (`prime_number_theorem`); `LogGnewGe` and
  `LogNormalizationLe` re-export it as their lemma [1].
* `Blueprint_5255.lean` imports `definitions` + all node files; its 13 former `sorry` nodes are
  now `exact <Node>.<node> …`. It contains no `sorry`. `lake build` passes.
* Remaining `sorry`s: the node-file lemmas (84 after PNT merge) + `PNT.prime_number_theorem`.

**Plan for (1):** parallel agents, each owning whole files (never two agents on one file);
every file must compile after each edit; a false lemma statement is fixed (statement + glue) and
reported here. Helper modules allowed as `Meijer5255/<Node>_<suffix>.lean` (owner only).
Wave 1: CarryFacts+GnewDvd | BaselineIntegrality | LogNormalizationLe+LogGnewGe | TraceLemma |
WindowReadout+WindowRootData. Wave 2: ShellFirstOrder | BaselineProfile | CmfReadout |
QGrowth+LinformError (port zeta34 analytic files; note Mathlib pin differs: this repo
`f69ff855…`, zetas_irr `850e7374…`).

### 7.1 Lemma status (update per agent report)
* `CarryFacts.lean`: **all 5 proved** (verified by coordinator: compiles, no sorry). Helper
  `CarryFacts_Cells.lean` (69 breakpoints, one `decide +kernel` midpoint certificate).
* `GnewDvd.lean`: **all 3 proved** (verified).
* `LogNormalizationLe.lean`: **[2]–[5] proved** (verified; [1] = PNT re-export).
* `LogGnewGe.lean`: **[2]–[8] proved** (verified). Helpers `LogGnewGe_Aux.lean` (copied o(n) /
  prime-interval lemmas), `LogGnewGe_Cert.lean` (directed-rounding `decide +kernel` sums,
  γ_LB(1000) ≥ 30.4585472438 > gammaNew by 3.8e-9).
* `BaselineIntegrality.lean`: **all 7 proved** (verified). Helper `BaselineIntegrality_Aux.lean`
  (398 lines: lcm/binomial divisibility, Lagrange identity for `L_c` residues, denominator re-pairing).
  ⇒ node `baseline_integrality` fully sorry-free.
* `TraceLemma.lean`: **all 6 proved** (verified; no statement changes). Helpers
  `TraceLemma_Val` (ValGE / mod-p² first-order calculus), `TraceLemma_Cls` (complete residue
  systems, Wilson), `TraceLemma_Res` (Lagrange residue sums), `TraceLemma_Loc` (local Laurent
  data). ⇒ node `trace_lemma` fully sorry-free. Pitfall: `m.map fun y => x - (y : ℚ)` on
  `Multiset ℤ` coerces via monad lift; annotate `fun y : ℤ => …`.
* `QGrowth.lean` (6) and `LinformError.lean` (8): **all proved** (verified; `#print axioms` of both
  nodes = `[propext, Classical.choice, Quot.sound]`). Helper layer `QGrowth_*.lean` (31 modules,
  ≈10.1k lines): 27 zeta34 files copied verbatim (namespace `Meijer5255.QGA.ZetasIrr`, compiled
  unchanged on this Mathlib pin), `QGrowth_PF` (pfq54 pf_aux adapted), `QGrowth_Star` (pfq54
  star_aux 1–227), `QGrowth_Bridge` (new: zeta34 Laurent coeffs = `definitions.pfCoeff`, endpoint
  readouts 2Q/−2P3/−6P4). Local zeta34 def copies in the two node files removed. CmfReadout agent
  told it may import `QGrowth_*` instead of its own `CmfReadout_*` copies (`Meijer5255.CRZ`).
* `WindowReadout.lean` (6) and `WindowRootData.lean` (6): **all proved** (verified). Structural
  change: `WindowReadout` now imports `WindowRootData` ([4] `individual_bounds` uses the `h_ge`
  field of `window_root_data`). Helpers `WindowReadout_Residue` (residue sum of a proper rational
  function = 0), `WindowReadout_Bounds` (exact p-valuations), `WindowRootData_Cert` (9 Farey-29
  cells + 512-bit-vector `decide +kernel` check; matches paper table (S2)), `WindowRootData_Aux`.
  ⇒ `second_order_shell` axioms = `[propext, Classical.choice, Quot.sound]` (fully proved).
* `BaselineProfile.lean` (8): **all proved** (verified; axioms clean). ψ = φ₁₀ confirmed on all
  120 Farey-19 cells (`decide +kernel`). Helpers `BaselineProfile_Cells`, `_Jets` (new bridge
  `C_n a_j = (-1)^n U`, `C_n b_j = (-1)^n V` from `aCoef_formula`/`bCoef_formula`), `_Perm`
  (pfq54 Z_integral/permutation_lemma adapted), `_Upper` (upper range incl. the r = 3
  sharpening). NOTE: `BaselineProfile_*` imports `BaselineIntegrality_Aux` lemmas — keep names stable.
* `ShellFirstOrder.lean` (8): **all proved** (verified). Helpers `ShellFirstOrder_Cert` (47 Farey-29
  cells, monotone bit-vector `decide +kernel`, ~65 s), `_Gen` (local scaling of pfCoeff, Wilson),
  `_Core` ([2]–[7]). ⇒ `shell_first_order`, `Gnew_dvd` axioms clean; `log_Gnew_ge` and
  `log_normalization_le` carry only the PNT `sorryAx`.
* `CmfReadout.lean` (10): **all proved** (verified). Local defs changed: `Lmom`/`Mmom` = coordinates
  of zeta34 `Lfun`/`Mfun`; `IsMom` = zeta34 form on `lin Z P`; `kerR` via `gker`; removed `pfD`,
  `pfS`, `polyPart`, `Adm`, `Hw`, `pathVertex`, `cutoffAt`, `gammaRatio`. [5] `companion` uses `VC`;
  [6] `edge_transport` gained `hd4 : d₄ ≠ 0` and `hA : aUp only for i < 2`; [7] restated per block
  (`WalkOK`). Helpers `CmfReadout_Aux`, `_Path`, `_PF`; imports `QGrowth_CMF_basic` read-only.
* **definitions.lean fix:** `Move.mat (.aUp i)` was `(s•θ(v) - aᵢ•1)⁻¹`; corrected to
  `(s•(θ(v) - aᵢ•1))⁻¹` as in `native.py` line 29. Identical for `i < 2` (the only `a↑` moves of
  the block path), so `W n` is unchanged; full rebuild passes.
* **ALL 84 LEMMAS PROVED (2026-10-13 ~19:00).** `lake build`: success, 9112 jobs; the only `sorry` in
  `lean/Meijer5255/` is `PNT.prime_number_theorem`. `#print axioms main_joint / main_pure3` =
  `[propext, sorryAx, Classical.choice, Quot.sound]` (sorryAx = PNT only); `cmf_readout`,
  `Gnew_dvd`, `Q_growth`, `linform_error`, … are axiom-clean. 70 Lean files.
* **Session 3 request complete.** Per-file times in `lean/BUILD_TIMES.md` (70 files, 24,328 lines,
  1742 s sequential; ~23.5 s/file is loading Mathlib). Dependency graphs saved in `lean/DEPENDENCY_GRAPH.md` (Mermaid: condensed file
  level, theorem level, exact 132-edge import graph). Nothing committed to git yet.
* Possible cleanups: `edge_transport`'s `hA` hypothesis is now redundant after the `aUp` fix. (Blueprint `log_Gnew_ge` docstring K = 200 claim corrected to K = 1000.)
* 2026-10-13 17:05: running — BaselineIntegrality (5/7), TraceLemma (4/6), WindowReadout (4/6) then
  WindowRootData (0/6), ShellFirstOrder (3/8). Launching BaselineProfile, QGrowth+LinformError.
  CmfReadout queued.
