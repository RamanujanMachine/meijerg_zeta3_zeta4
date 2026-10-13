/-
# Node blueprint: `shell_first_order` (paper §§6–7, "Fourteen first-order shells and all their
periodic lifts")

Target (restated verbatim from `Blueprint_5255.lean`): for `n ≥ 1`, an eligible prime `p` and
`{n/p} ∈ 𝒮` (the fourteen shells),
  `ValGE p 1 (Q n) ∧ ValGE p (-1) (P3 n) ∧ ValGE p (-2) (P4 n)`.

Strategy (paper §7, generalising §6 = pfq54 `residue_block`). Write `n/p = t + f`, `y = k/p`.
The high roots of the residue class `k` are five integer intervals whose endpoints are the
`t = 0` endpoints shifted affinely in `t` ([2]); the finite Farey-29 chamber certificate at
`t = 0` ([1]) gives `h_k = #num - #den ≥ -1` at every residue and, on the minimal classes
`h_k = -1`, the same shifted intervals for every `k` (the table row), hence a single kernel
`U_t(V)` of degree `-1`. Distinct roots differ by less than `p²` ([3]), so all local
partial-fraction operations are `p`-integral. The polynomial
`𝒬 = (X^p - X) N̄/D̄ = ∏_{a ∈ 𝔽_p} (X - a)^{1 + c_a - d_a}` has degree `p - 2` ([4], lifted to
`ℤ[X]` as `Tq`). The local factorization `p F_n(k + p(V+ε)) ≡ -𝒬(k) U_t(V) (mod p)` gives
`a_j/p ≡ -𝒬(k) α_ℓ`, `b_j ≡ -𝒬(k) β_ℓ` with `p`-integral `α, β` indexed by the harmonic index
`⌊(j+2n)/p⌋ = -ℓ` ([6]); with `p^r H^{(r)}_m ≡ H^{(r)}_{⌊m/p⌋} (mod p)` for `m < p²` ([5]) every
residue class contributes `c_r · 𝒬(k)` to `p^{r-1} P_{r,n}`, with a constant `c_r` depending
only on `t` and the row ([7]). The sum over all residues vanishes because `deg 𝒬 < p - 1` ([8]).

Glue (below): `Q` from the individual bounds `a_j ∈ pℤ_(p)` (extracted from [6]); `P3`, `P4`:
split the readout sums into residue fibres (`Finset.sum_fiberwise_of_maps_to`), apply [7] in
each fibre, sum, and use [8] with the degree bound [4]; finally divide by `p²`, resp. `p³`.

Supporting lemmas (8), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `root_count_cert` | 250 | partially (certificate asserted; chamber check redone in Lean) |
| 2 | `hiRoots_lift` | 80 | yes ("Why the same table proves every lift") |
| 3 | `separation` | 20 | yes ("distinct high roots differ by at most `⌊29n/p⌋ < p`") |
| 4 | `Tq_natDegree` | 50 | yes (`deg 𝒬 = p - 2`) |
| 5 | `harm_split` | 40 | yes (harmonic index `-ℓ` after extracting multiples of `p`) |
| 6 | `local_factorization` | 250 | yes (local factorization of §7, (LK) of §6) |
| 7 | `class_congruence` | 120 | yes ("leading local readout is a constant … times `𝒬(k)`") |
| 8 | `sum_residues_dvd` | 25 | yes (`deg 𝒬 < p - 1`) |

Reuse: pfq54 `residue_block.lean` (`readout_sums`, `local_identity`, `harm_reduction`,
`node_term`, `block_congruence`, `sum_residues_dvd` — the last can be copied verbatim),
`residue_aux.lean` (`filter_class`, `card_class`, `root_count'`), `residue_aux4.lean`
(`ex`, `Tp`, `Tp_natDegree`, `Tp_congr`, `Tp_supp`), `residue_aux5.lean` (`local_identity'`,
`window_dvd`), `upper_range_bound.lean` (`harm_valGE`); zeta34 `blueprints/ZetasAux.lean`
(`ValGE.mul/add/sub/mono`), `valuation_bound.lean` (`ValGE_sum`); chamber pattern zeta34
`Chamber_dsl.lean` / `Chamber_reduce.lean`, pfq54 `profile_aux.lean`.
-/
import Meijer5255.definitions
import Meijer5255.ShellFirstOrder_Cert
import Meijer5255.ShellFirstOrder_Core

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.ShellFirstOrder

open Meijer5255

/-! ### Objects -/

/-- Number of elements of `s` congruent to `k` modulo `p` (the root counts `c(k)`, `d(k)`). -/
def resCount (s : Multiset ℤ) (p k : ℕ) : ℕ := (s.filter fun x => x % (p : ℤ) = k).card

/-- The exponent `1 + c(a) - d(a)` of `(X - a)` in `𝒬` (truncated subtraction; exact when
`h_a ≥ -1`). -/
def exT (n p a : ℕ) : ℕ := 1 + resCount (numRoots n) p a - resCount (denRoots n) p a

/-- The integer lift `∏_{a<p} (X - a)^{1 + c(a) - d(a)}` of `𝒬 = (X^p - X) N̄/D̄ ∈ 𝔽_p[X]`. -/
def Tq (n p : ℕ) : ℤ[X] := ∏ a ∈ range p, (X - C (a : ℤ)) ^ exT n p a

/-- The residue `k ∈ [0, p)` of the pole `-j`, i.e. `p ∣ j + k`. -/
def classOf (p j : ℕ) : ℕ := (p - j % p) % p

/-- Number of integers in `[L, U]` (`0` for an empty interval). -/
def icount (L U : ℤ) : ℤ := max 0 (U - L + 1)

/-- The five `t = 0` high-root intervals `N₀, N₁, N₂, D₀, D₁` of the residue `y = k/p` at
`f = {n/p}`: `[⌊uf - y⌋ + 1, ⌊(u+10)f - y⌋]` (`u = 0,1,2`), `[⌈-17f - y⌉, ⌊-f - y⌋]`,
`[⌈-16f - y⌉, ⌊-2f - y⌋]`. -/
def ends0 (f y : ℚ) : List (ℤ × ℤ) :=
  [(⌊-y⌋ + 1, ⌊10 * f - y⌋), (⌊f - y⌋ + 1, ⌊11 * f - y⌋), (⌊2 * f - y⌋ + 1, ⌊12 * f - y⌋),
   (⌈-17 * f - y⌉, ⌊-f - y⌋), (⌈-16 * f - y⌉, ⌊-2 * f - y⌋)]

/-- The `t = 0` count `h = #N₀ + #N₁ + #N₂ - #D₀ - #D₁`. -/
def hcount0 (f y : ℚ) : ℤ :=
  icount (⌊-y⌋ + 1) ⌊10 * f - y⌋ + icount (⌊f - y⌋ + 1) ⌊11 * f - y⌋ +
      icount (⌊2 * f - y⌋ + 1) ⌊12 * f - y⌋ -
    icount ⌈-17 * f - y⌉ ⌊-f - y⌋ - icount ⌈-16 * f - y⌉ ⌊-2 * f - y⌋

/-- The table of §7: each shell `(a, b)` with its five shifted minimal-class intervals
`N₀, N₁, N₂, D₀, D₁` (as `(L, U)` pairs) at `t = 0`. -/
def shellTable : List ((ℚ × ℚ) × List (ℤ × ℤ)) :=
  [((1/11, 1/8), [(1, 1), (1, 1), (1, 1), (-1, 0), (-1, 0)]),
   ((3/13, 4/17), [(0, 1), (0, 2), (1, 2), (-4, -1), (-4, -1)]),
   ((3/11, 5/18), [(0, 2), (0, 2), (1, 2), (-5, -1), (-4, -1)]),
   ((4/13, 5/16), [(0, 2), (1, 3), (1, 3), (-5, -1), (-5, -1)]),
   ((4/11, 7/19), [(0, 3), (1, 3), (1, 4), (-6, -1), (-6, -1)]),
   ((5/13, 7/18), [(1, 3), (1, 4), (1, 4), (-6, -1), (-6, -1)]),
   ((5/12, 8/19), [(0, 3), (1, 4), (1, 4), (-7, -1), (-7, -2)]),
   ((5/11, 8/17), [(0, 3), (0, 4), (1, 4), (-8, -2), (-8, -2)]),
   ((6/11, 9/16), [(0, 4), (0, 5), (1, 5), (-10, -2), (-9, -2)]),
   ((7/12, 10/17), [(-1, 4), (0, 5), (1, 5), (-11, -2), (-10, -3)]),
   ((7/11, 11/17), [(-1, 5), (0, 5), (1, 6), (-12, -2), (-11, -3)]),
   ((7/10, 12/17), [(-1, 5), (0, 6), (1, 7), (-13, -2), (-12, -3)]),
   ((8/11, 11/15), [(-1, 5), (0, 6), (1, 7), (-13, -3), (-13, -3)]),
   ((10/11, 16/17), [(-1, 7), (0, 8), (1, 9), (-17, -3), (-16, -4)])]

/-! ### Glue helpers (fully proved; the `ValGE` calculus, as in zeta34 `ZetasAux.lean`) -/

section ValGEcalc

variable {p : ℕ} [Fact p.Prime]

theorem valGE_mul {a b : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p b y) :
    ValGE p (a + b) (x * y) := by
  rcases hx with rfl | hx
  · left; simp
  rcases hy with rfl | hy
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  by_cases hy0 : y = 0
  · left; simp [hy0]
  right; rw [padicValRat.mul hx0 hy0]; omega

omit [Fact p.Prime] in
theorem valGE_neg {a : ℤ} {x : ℚ} (hx : ValGE p a x) : ValGE p a (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [padicValRat.neg]

theorem valGE_add {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem valGE_sub {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x - y) := by
  rw [sub_eq_add_neg]; exact valGE_add hx (valGE_neg hy)

omit [Fact p.Prime] in
theorem valGE_mono {a b : ℤ} (hab : b ≤ a) {x : ℚ} (hx : ValGE p a x) : ValGE p b x :=
  hx.imp id fun h => hab.trans h

theorem valGE_sum {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℚ)
    (h : ∀ i ∈ s, ValGE p a (f i)) : ValGE p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact valGE_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fact p.Prime] in
theorem valGE_int (z : ℤ) : ValGE p 0 (z : ℚ) := by
  rcases eq_or_ne z 0 with h | h
  · left; simp [h]
  · right; rw [padicValRat.of_int]; positivity

theorem valGE_p_pow (r : ℕ) : ValGE p r ((p : ℚ) ^ r) :=
  Or.inr (le_of_eq (by rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt,
    mul_one]))

/-- Dividing out `p^r`: `p^r x ∈ p^k ℤ_(p)` implies `x ∈ p^{k-r} ℤ_(p)`. -/
theorem valGE_of_pow_mul {k : ℤ} (r : ℕ) {x : ℚ} (h : ValGE p k ((p : ℚ) ^ r * x)) :
    ValGE p (k - r) x := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  by_cases hx : x = 0
  · exact Or.inl hx
  rcases h with h | h
  · exact absurd h (mul_ne_zero (pow_ne_zero _ hp0) hx)
  · right
    rw [padicValRat.mul (pow_ne_zero _ hp0) hx, padicValRat.pow,
      padicValRat.self (Fact.out : p.Prime).one_lt] at h
    linarith

end ValGEcalc

/-! ### Supporting lemmas -/

/-- **[1] The root-count chamber certificate at `t = 0`.** For `f` in a table shell, away from
the Farey walls of order `29`, and every `y ∈ [0, 1)`: `h ≥ -1`, and where `h = -1`, subtracting
`ε₀ = ⌊2f - y⌋` from the ten endpoints gives the table row.
Proof: every endpoint changes only on a line `y = mf + c` with `m ∈ {0,1,2,10,11,12,-1,-2,-16,-17}`,
so the data are constant on the strata of the Farey-29 arrangement; a finite check of the
47 cells (open `y` intervals and their boundaries) by `decide +kernel` over a certificate,
split into several files.
* Proved (≈ 2 lines here; the helper module `ShellFirstOrder_Cert.lean` has ≈ 290 lines of
  definitions and soundness proofs plus the generated 47-cell data, checked by 14
  `decide +kernel` theorems).
* Directly from the PDF: partially (the PDF asserts the table and the result of
  `all_shell_cells.py`; the Lean chamber check is new). -/
theorem root_count_cert (f y : ℚ) (row : (ℚ × ℚ) × List (ℤ × ℤ)) (hrow : row ∈ shellTable)
    (hf : row.1.1 < f ∧ f < row.1.2)
    (hF : ∀ q : ℕ, 0 < q → q ≤ 29 → ∀ m : ℤ, f * q ≠ m) (hy : 0 ≤ y ∧ y < 1) :
    -1 ≤ hcount0 f y ∧
      (hcount0 f y = -1 →
        (ends0 f y).map (fun e => (e.1 - ⌊2 * f - y⌋, e.2 - ⌊2 * f - y⌋)) = row.2) := by
  -- the certificate lives in the helper module `ShellFirstOrder_Cert` (copies of the data)
  have htbl : shellTable = Cert.tbl := rfl
  exact Cert.cert_main f y row (htbl ▸ hrow) hf hF hy

/-- **[2] High roots for every lift.** With `t = ⌊n/p⌋`, `f = {n/p}`, `y = k/p`, the high roots
of the class `k` are the five intervals whose endpoints are the `t = 0` endpoints of `ends0`
shifted by `ut, (u+10)t` (numerator), `-17t, -t` and `-16t, -2t` (denominator). (Subtracting
`ε = 2t + ε₀` gives the affine intervals `[(u-2)t + L_u, (u+8)t + U_u]`, `[-19t + L₃, -3t + U₃]`,
`[-18t + L₄, -4t + U₄]` of the paper; the counts gain `30t` on both sides, so `h` is unchanged.)
Proof: `x = k + pℓ ∈ [a, b] ⟺ ⌈(a-k)/p⌉ ≤ ℓ ≤ ⌊(b-k)/p⌋` and `⌊u(t+f) - y⌋ = ut + ⌊uf - y⌋`.
* Proved (≈ 120 lines, in the helper module `ShellFirstOrder_Core.lean`: `hi_Icc`, `hi_add`,
  `floor_lift`, `ceil_lift`, `ceil_succ`, `hiRoots_lift`).
* Directly from the PDF: yes (§7, "Why the same table proves every lift"). -/
theorem hiRoots_lift (n p k : ℕ) (hp : 0 < p) :
    hiRoots p k (numRoots n) =
        (Icc (⌊-((k : ℚ) / p)⌋ + 1)
            (10 * ⌊(n : ℚ) / p⌋ + ⌊10 * Int.fract ((n : ℚ) / p) - k / p⌋)).val +
          (Icc (⌊(n : ℚ) / p⌋ + ⌊Int.fract ((n : ℚ) / p) - k / p⌋ + 1)
            (11 * ⌊(n : ℚ) / p⌋ + ⌊11 * Int.fract ((n : ℚ) / p) - k / p⌋)).val +
          (Icc (2 * ⌊(n : ℚ) / p⌋ + ⌊2 * Int.fract ((n : ℚ) / p) - k / p⌋ + 1)
            (12 * ⌊(n : ℚ) / p⌋ + ⌊12 * Int.fract ((n : ℚ) / p) - k / p⌋)).val ∧
      hiRoots p k (denRoots n) =
        (Icc (-17 * ⌊(n : ℚ) / p⌋ + ⌈-17 * Int.fract ((n : ℚ) / p) - k / p⌉)
            (-⌊(n : ℚ) / p⌋ + ⌊-Int.fract ((n : ℚ) / p) - k / p⌋)).val +
          (Icc (-16 * ⌊(n : ℚ) / p⌋ + ⌈-16 * Int.fract ((n : ℚ) / p) - k / p⌉)
            (-2 * ⌊(n : ℚ) / p⌋ + ⌊-2 * Int.fract ((n : ℚ) / p) - k / p⌋)).val := by
  -- proof in the helper module `ShellFirstOrder_Core` (with `hi_Icc`, `floor_lift`, `ceil_lift`)
  exact Core.hiRoots_lift n p k hp

/-- **[3] Separation.** Distinct roots of `F_n` (numerator or denominator) differ by an integer
not divisible by `p²`; hence distinct high roots of one class differ by a `p`-adic unit.
Proof: all roots lie in `[-17n, 12n]`, so `0 < |x - x'| ≤ 29n < 30n < p²`.
* Proved (≈ 13 lines, in `ShellFirstOrder_Core.lean`).
* Directly from the PDF: yes ("Distinct high roots differ by at most `⌊29n/p⌋ < p`"). -/
theorem separation (n p : ℕ) (hp : Eligible n p) :
    ∀ x ∈ numRoots n + denRoots n, ∀ x' ∈ numRoots n + denRoots n, x ≠ x' →
      ¬ ((p : ℤ) ^ 2 ∣ x - x') := by
  exact Core.separation n p hp

/-- **[4] The degree of `𝒬`.** On the shells every class has `h ≥ -1` ([1], [2]), so every
exponent `1 + c(a) - d(a)` is exact and `deg Tq = p + 30n - (30n + 2) = p - 2`.
* Proved (≈ 130 lines, in `ShellFirstOrder_Core.lean`: `shell_shape` with `farey_free`,
  `count_eq` turns [1], [2] into `d_k ≤ c_k + 1`; `Tq_natDegree` ≈ 25 lines, as pfq54
  `Tp_natDegree`; `sum_rc` in `ShellFirstOrder_Gen.lean`).
* Directly from the PDF: yes ("`𝒬` is a polynomial of degree `p - 2`"). -/
theorem Tq_natDegree (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    (Tq n p).natDegree ≤ p - 2 := by
  -- proof in `ShellFirstOrder_Core` (`Tq` there is a copy, equal by `rfl`)
  exact (fun _ => Core.Tq_natDegree n p hp hs) hn

/-- **[5] Harmonic numbers modulo `p`.** For `r ≥ 1` and `m < p²`:
`p^r H^{(r)}_m ≡ H^{(r)}_{⌊m/p⌋} (mod p)`, and `H^{(r)}_{⌊m/p⌋}` is `p`-integral (only the
terms `k = pi`, `i ≤ ⌊m/p⌋ < p`, survive; the others have valuation `≥ r`).
* Proved (≈ 50 lines, in `ShellFirstOrder_Core.lean`).
* Directly from the PDF: yes ("a denominator root `l` of `U_t` has harmonic index `-l` after
  extracting the multiples of `p`"). -/
theorem harm_split (p : ℕ) [Fact p.Prime] (r m : ℕ) (hr : 1 ≤ r) (hm : m < p ^ 2) :
    ValGE p 0 (harm r (m / p)) ∧ ValGE p 1 ((p : ℚ) ^ r * harm r m - harm r (m / p)) := by
  exact Core.harm_split p r m hr hm

/-- **[6] Local factorization.** There are `p`-integral `α, β : ℕ → ℚ` (the double- and
simple-pole coefficients of the common minimal-class kernel `U_t(V)` at `V = -i`, zero off its
poles; they depend only on `t` and the table row) such that for every `j ∈ [n, 17n]`, with
`k = classOf p j`: `a_j/p ≡ -𝒬(k) α_i` and `b_j ≡ -𝒬(k) β_i (mod p)`, `i = ⌊(j+2n)/p⌋`.
Proof: `p F_n(k + p(V+ε)) ≡ -𝒬(k) U_t(V) (mod p)` at minimal residues (cancel the unit factors
`k - a`, `(X^p - X)' = -1`), `≡ 0` elsewhere (where `𝒬(k) = 0`); the pole `-j = k + p(ℓ+ε)` has
`⌊(j+2n)/p⌋ = ε - (ℓ+ε) = -ℓ`; partial fractions extracted at unit-separated poles ([3]).
* Uses: [1], [2], [3].
* Proved (≈ 300 lines in `ShellFirstOrder_Core.lean`: `core`, `shell_shape`, `pfCoeff_shift`,
  `index_eq`, `classOf_dvd`, `Tq_supp`; plus the generic module `ShellFirstOrder_Gen.lean`,
  ≈ 570 lines: root products, `pfCoeff_eq`, the local scaling `scale`, `vpf_local`, `unit_part`,
  Wilson). `α i, β i` are the partial-fraction coefficients of the common kernel at `V = -i`.
* Directly from the PDF: yes (§7 "local factorization", §6 (LK)). -/
theorem local_factorization (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    ∃ α β : ℕ → ℚ, (∀ i, ValGE p 0 (α i) ∧ ValGE p 0 (β i)) ∧
      ∀ j ∈ Icc n (17 * n),
        ValGE p 1 (aCoef n j / p +
          (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * α ((j + 2 * n) / p)) ∧
        ValGE p 1 (bCoef n j +
          (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * β ((j + 2 * n) / p)) := by
  -- proof in `ShellFirstOrder_Core` (`Core.core`: local scaling `Gen.scale`, shape of the
  -- minimal classes `Core.shell_shape`, translation invariance `Core.pfCoeff_shift`)
  exact Core.local_factorization n p hn hp hs

/-- **[7] One residue class of the readout.** There are `p`-integral constants `c₃, c₄`
(depending only on `t` and the row) such that for every residue `k < p` the contribution of the
poles `-j ≡ k` to `p² P_{3,n}` is `≡ c₃ 𝒬(k)`, and to `p³ P_{4,n}` is `≡ c₄ 𝒬(k) (mod p)`.
Proof: write `p² (a_j H³ + b_j H²/2) = (a_j/p)(p³H³_{j+2n}) + (b_j/2)(p²H²_{j+2n})`, apply [5]
(`j + 2n ≤ 19n < p²`) and [6]; on a minimal class `j ↦ -⌊(j+2n)/p⌋` runs exactly over the
poles of `U_t`, giving `c₃ = -∑_i (α_i H³_i + β_i H²_i/2)`; on other classes `𝒬(k) = 0` and
every term is `≡ 0`.
* Uses: [5], [6], [1], [2].
* Proved (≈ 90 lines in `ShellFirstOrder_Core.lean`: `class_gen`, from `core` and [5]).
* Directly from the PDF: yes ("The resulting leading local readout is therefore a constant
  depending on `t` and the table row, multiplied by `𝒬(k)`"). -/
theorem class_congruence (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    ∃ c3 c4 : ℚ, ValGE p 0 c3 ∧ ValGE p 0 c4 ∧ ∀ k ∈ range p,
      ValGE p 1 (∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ 2 * (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2) -
        c3 * (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) ∧
      ValGE p 1 (∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ 3 * (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3) -
        c4 * (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
  -- proof in `ShellFirstOrder_Core` (`Core.class_gen` with `s = 2, d = 2` and `s = 3, d = 3`)
  exact Core.class_congruence n p hn hp hs

/-- **[8] Complete residue sums vanish.** If `deg T ≤ p - 2` then `p ∣ ∑_{k=0}^{p-1} T(k)`
(`∑_{x ∈ 𝔽_p} x^i = 0` for `i < p - 1`).
* Proved (≈ 25 lines; pfq54 `residue_block.sum_residues_dvd`, verbatim).
* Directly from the PDF: yes ("The sum over `k` vanishes since `deg 𝒬 < p - 1`"). -/
theorem sum_residues_dvd (p : ℕ) [Fact p.Prime] (T : ℤ[X]) (hT : T.natDegree ≤ p - 2) :
    (p : ℤ) ∣ ∑ k ∈ range p, T.eval (k : ℤ) := by
  -- copied from pfq54 `residue_block.sum_residues_dvd`
  have hp : p.Prime := Fact.out
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
  set f := Int.castRingHom (ZMod p)
  have h1 : ∑ k ∈ range p, ((T.eval (k : ℤ) : ℤ) : ZMod p) =
      ∑ x : ZMod p, (T.map f).eval x := by
    refine Finset.sum_bij' (fun k _ => (k : ZMod p)) (fun x _ => x.val) (fun _ _ => mem_univ _)
      (fun x _ => mem_range.mpr (ZMod.val_lt x))
      (fun k hk => ZMod.val_natCast_of_lt (mem_range.mp hk)) (fun x _ => ZMod.natCast_zmod_val x)
      (fun k _ => ?_)
    rw [Polynomial.eval_map, show ((k : ℕ) : ZMod p) = f (k : ℤ) by simp [f],
      Polynomial.eval₂_hom]
    rfl
  rw [h1]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  have hi' := mem_range.mp hi
  have hdeg := Polynomial.natDegree_map_le (f := f) (p := T)
  rw [ZMod.card]
  have := hp.two_le
  omega

/-! ### The node -/

/-- **Fourteen first-order shells with all periodic lifts** (statement verbatim from
`Blueprint_5255.lean`), proved from [4], [6], [7], [8]. -/
theorem shell_first_order (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    ValGE p 1 (Q n) ∧ ValGE p (-1) (P3 n) ∧ ValGE p (-2) (P4 n) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
  obtain ⟨α, β, hαβ, hloc⟩ := local_factorization n p hn hp hs
  obtain ⟨c3, c4, hc3, hc4, hcls⟩ := class_congruence n p hn hp hs
  obtain ⟨w, hw⟩ := sum_residues_dvd p (Tq n p) (Tq_natDegree n p hn hp hs)
  -- the complete residue sum is `≡ 0 (mod p)`
  have hS : ValGE p 1 (∑ k ∈ range p, (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
    have e : ∑ k ∈ range p, (((Tq n p).eval (k : ℤ) : ℤ) : ℚ) = (p : ℚ) * w := by
      exact_mod_cast hw
    rw [e]
    have := valGE_mul (valGE_p_pow (p := p) 1) (valGE_int (p := p) w)
    simpa using this
  -- individual double-pole bounds `a_j ∈ pℤ_(p)`
  have ha : ∀ j ∈ Icc n (17 * n), ValGE p 1 (aCoef n j) := by
    intro j hj
    have h1 := (hloc j hj).1
    have hT : ValGE p 0 ((((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * α ((j + 2 * n) / p)) := by
      have := valGE_mul (valGE_int (p := p) ((Tq n p).eval (classOf p j : ℤ)))
        (hαβ ((j + 2 * n) / p)).1
      simpa using this
    have h0 : ValGE p 0 (aCoef n j / p) := by
      have := valGE_sub (valGE_mono (by norm_num) h1) hT
      rwa [add_sub_cancel_right] at this
    have e : aCoef n j = aCoef n j / p * (p : ℚ) ^ 1 := by field_simp
    rw [e]
    have := valGE_mul h0 (valGE_p_pow (p := p) 1)
    simpa using this
  -- the fibre decomposition of a readout sum
  have hmaps : ∀ j ∈ Icc n (17 * n), classOf p j ∈ range p := fun j _ =>
    mem_range.2 (Nat.mod_lt _ hp.1.pos)
  refine ⟨valGE_sum _ _ _ ha, ?_, ?_⟩
  · have hsplit : (p : ℚ) ^ 2 * P3 n = ∑ k ∈ range p,
        ∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ 2 * (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2) := by
      rw [P3, Finset.mul_sum]
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    have h1 : ValGE p 1 ((p : ℚ) ^ 2 * P3 n -
        c3 * ∑ k ∈ range p, (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
      rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact valGE_sum _ _ _ fun k hk => (hcls k hk).1
    have h2 : ValGE p 1 (c3 * ∑ k ∈ range p, (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
      have := valGE_mul hc3 hS; simpa using this
    have h3 := valGE_add h1 h2
    rw [sub_add_cancel] at h3
    have := valGE_of_pow_mul 2 h3
    norm_num at this
    exact this
  · have hsplit : (p : ℚ) ^ 3 * P4 n = ∑ k ∈ range p,
        ∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ 3 * (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3) := by
      rw [P4, Finset.mul_sum]
      exact (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    have h1 : ValGE p 1 ((p : ℚ) ^ 3 * P4 n -
        c4 * ∑ k ∈ range p, (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
      rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact valGE_sum _ _ _ fun k hk => (hcls k hk).2
    have h2 : ValGE p 1 (c4 * ∑ k ∈ range p, (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
      have := valGE_mul hc4 hS; simpa using this
    have h3 := valGE_add h1 h2
    rw [sub_add_cancel] at h3
    have := valGE_of_pow_mul 3 h3
    norm_num at this
    exact this

end Meijer5255.ShellFirstOrder
