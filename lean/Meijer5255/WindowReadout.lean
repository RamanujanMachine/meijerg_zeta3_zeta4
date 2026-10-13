/-
# Node blueprint: `window_readout` (paper §9, "The stronger arithmetic readouts")

Target (restated verbatim from `Blueprint_5255.lean`): if (PB) holds for `F_n` at an eligible
`p` with `{n/p}` in a window, then
  `ValGE p 3 (Q n) ∧ ValGE p 0 (P3 n) ∧ ValGE p (-1) (P4 n)`.

Strategy (paper §9). Index the poles `-j = k + pℓ` (`k ∈ [1, p]`) by their high root
`ℓ = ⌊(-j-1)/p⌋` (`hiIdx`); then `A_ℓ, B_ℓ` are the sums of `a_j, b_j` over the fibre of `ℓ`
([6]), so `Q_n = ∑_ℓ A_ℓ ∈ p³ℤ_(p)`. Move the harmonic cutoff from `2n` to
`η = p⌈2n/p⌉ ∈ [2n, 10n]` ([1]); the readouts do not change because `F_n', F_n''` vanish at
`2n+1, …, 10n` ([2]). Now `⌊(j+η)/p⌋ = ⌈2n/p⌉ - ℓ - 1` depends only on `ℓ`, and
`j + η < p²` ([3]). Split `H^{(r)}_m = (p-free part) + p^{-r} H^{(r)}_{⌊m/p⌋}` ([5]). With the
individual bounds `a_j ∈ pℤ_(p)`, `b_j ∈ ℤ_(p)` ([4]) the `p`-free parts of `p^{r-1} P_{r,n}`
are `≡ 0 (mod p²)`, and the remaining terms are `∑_ℓ (A_ℓ/p · w_ℓ + B_ℓ · w'_ℓ/(r-1))` with
`p`-integral weights `w_ℓ = H^{(r)}_{⌈2n/p⌉-ℓ-1}`, which are `≡ 0 (mod p²)` by (PB).

Glue (below): `Q` from [6] and (PB); `P3`, `P4`: rewrite with [2], split each term with the
exact identity `p^{r-1}(aH^{(r)}_m + bH^{(r-1)}_m/(r-1)) = [p-free part] + aH^{(r)}_i/p +
bH^{(r-1)}_i/(r-1)` (`i = ⌊m/p⌋`, rewritten by [3]), regroup by [6], and bound everything with
[4], [5], (PB) and the `ValGE` calculus; finally divide by `p²`, resp. `p³`.

Supporting lemmas (6), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `eta_bounds` | 30 | yes ("on the first unlifted interval it is `p`, on the second `2p`, for `t ≥ 1` less than `3n`") |
| 2 | `cutoff_invariance` | 120 | yes ("`F_n', F_n''` vanish at every integer `2n+1, …, 10n`") |
| 3 | `floor_class` | 30 | yes (`⌊(j+η)/p⌋ = ⌈2n/p⌉ - ℓ - 1`, `j + η ≤ 27n < p²`) |
| 4 | `individual_bounds` | 150 | yes ("`h_k ≥ -1` … gives the individual bounds") |
| 5 | `harm_split` | 40 | yes ("terms whose harmonic denominators are prime to `p`") |
| 6 | `regroup` | 40 | yes ("collect the corresponding coefficients as `A_ℓ` and `B_ℓ`") |

Formalization notes: [2] uses the residue-sum helper `WindowReadout_Residue.lean`; [4] uses the
counts `h_k ≥ -1` from the node `window_root_data` (`WindowRootData.lean`, field `h_ge`) and the
valuation helper `WindowReadout_Bounds.lean`.

Reuse: pfq54 `star_aux.lean` (`Lfun_cut_many`, `Lfun_mt_cut`: the cutoff move), pfq54
`residue_block.lean` (`harm_reduction`, `node_term`), `upper_range_bound.lean` (`harm_valGE`),
`residue_aux5.lean` (`good_double`, `good_simple`: individual bounds from root counts); zeta34
`blueprints/ZetasAux.lean` (`ValGE` calculus), `valuation_bound.lean` (`ValGE_sum`).
-/
import Meijer5255.definitions
import Meijer5255.WindowReadout_Residue
import Meijer5255.WindowReadout_Bounds
import Meijer5255.WindowRootData

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.WindowReadout

open Meijer5255

/-! ### Objects -/

/-- `⌈2n/p⌉` (for `p > 0`). -/
def ceil2 (n p : ℕ) : ℕ := (2 * n + p - 1) / p

/-- The prime-dependent harmonic cutoff `η = p⌈2n/p⌉`. -/
def eta (n p : ℕ) : ℕ := p * ceil2 n p

/-- The high root `ℓ` of the pole `-j` with respect to the representatives `1, …, p`:
`-j = k + pℓ`, `1 ≤ k ≤ p`, i.e. `ℓ = ⌊(-j-1)/p⌋`. -/
def hiIdx (p j : ℕ) : ℤ := (-(j : ℤ) - 1) / p

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

theorem valGE_add {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

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

theorem valGE_p_pow (r : ℕ) : ValGE p r ((p : ℚ) ^ r) :=
  Or.inr (le_of_eq (by rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt,
    mul_one]))

theorem valGE_p_inv : ValGE p (-1) ((p : ℚ)⁻¹) :=
  Or.inr (le_of_eq (by rw [padicValRat.inv, padicValRat.self (Fact.out : p.Prime).one_lt]))

/-- `1/q` is `p`-integral for `0 < q < p`. -/
theorem valGE_inv_small (q : ℕ) (hq0 : 0 < q) (hq : q < p) : ValGE p 0 ((q : ℚ)⁻¹) := by
  right
  rw [padicValRat.inv, padicValRat.of_nat,
    padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hq0 hq)]
  simp

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

/-- **[1] The cutoff `η` lies in `[2n, 10n]`.** `η = p⌈2n/p⌉ ≥ 2n` always; on the windows
`η = p < 10n` (`t = 0`, first window, `2n/p ∈ (1/5, 4/19)`), `η = 2p < 24n/11`
(`t = 0`, second window, `2n/p ∈ (11/6, 15/8)`), and `η < 2n + p ≤ 3n` for `t ≥ 1`.
* Proved (≈ 29 lines).
* Directly from the PDF: yes (§9, "This lies in `[2n, 10n]` …"). -/
theorem eta_bounds (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p)) :
    2 * n ≤ eta n p ∧ eta n p ≤ 10 * n := by
  have hp0 : 0 < p := hp.1.pos
  -- `{n/p} > 1/10`, hence `p < 10n`
  have hf : (1 / 10 : ℚ) < Int.fract ((n : ℚ) / p) := by
    simp only [inRows, windowRows, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with h | h
    · exact h.1
    · linarith [h.1]
  have hx : (1 / 10 : ℚ) < (n : ℚ) / p := by
    have : Int.fract ((n : ℚ) / p) ≤ (n : ℚ) / p := by
      rw [← Int.self_sub_floor]
      have h0 : (0 : ℤ) ≤ ⌊(n : ℚ) / p⌋ := Int.floor_nonneg.2 (by positivity)
      have : (0 : ℚ) ≤ ⌊(n : ℚ) / p⌋ := by exact_mod_cast h0
      linarith
    linarith
  have hp10 : p < 10 * n := by
    have hpq : (0 : ℚ) < p := by exact_mod_cast hp0
    rw [lt_div_iff₀ hpq] at hx
    exact_mod_cast (by linarith : (p : ℚ) < 10 * n)
  have hq := Nat.div_add_mod (2 * n + p - 1) p
  have hr := Nat.mod_lt (2 * n + p - 1) hp0
  unfold eta ceil2
  generalize (2 * n + p - 1) / p = q at hq ⊢
  generalize (2 * n + p - 1) % p = r at hq hr
  refine ⟨by omega, ?_⟩
  rcases Nat.lt_or_ge q 2 with h2 | h2
  · interval_cases q <;> omega
  · have : p * 2 ≤ p * q := Nat.mul_le_mul_left p h2
    omega

/-- **[2] Cutoff invariance.** For `2n ≤ K ≤ 10n` the readouts may be computed with the cutoff
`K` instead of `2n`. Proof: moving the cutoff from `K` to `K + 1` changes `P_{3,n}` by
`∑_j (a_j/(j+K+1)³ + b_j/(2(j+K+1)²)) = -F_n'(K+1)/2` and `P_{4,n}` by
`∑_j (a_j/(j+K+1)⁴ + b_j/(3(j+K+1)³)) = F_n''(K+1)/6`; both vanish for `2n < K + 1 ≤ 10n`
because every integer of `[2n+1, 10n]` is a triple zero of `F_n` (it lies in all three numerator
intervals). Induction on `K`.
* Proved (≈ 47 lines here, plus the residue-sum helper `WindowReadout_Residue.lean`,
  ≈ 330 lines).
* Directly from the PDF: yes ("The exact readout is unchanged by using this cutoff, because
  `F_n', F_n''` vanish at every integer `2n+1, …, 10n`"). -/
theorem cutoff_invariance (n K : ℕ) (hK1 : 2 * n ≤ K) (hK2 : K ≤ 10 * n) :
    P3 n = ∑ j ∈ Icc n (17 * n), (aCoef n j * harm 3 (j + K) + bCoef n j * harm 2 (j + K) / 2) ∧
      P4 n = ∑ j ∈ Icc n (17 * n),
        (aCoef n j * harm 4 (j + K) + bCoef n j * harm 3 (j + K) / 3) := by
  -- the increments `-F_n'(K+1)/2`, `F_n''(K+1)/6` vanish (residue identity, `incr_gen`)
  have hstep : ∀ K, 2 * n ≤ K → K < 10 * n →
      ∑ j ∈ Icc n (17 * n),
          (aCoef n j * harm 3 (j + (K + 1)) + bCoef n j * harm 2 (j + (K + 1)) / 2) =
        ∑ j ∈ Icc n (17 * n), (aCoef n j * harm 3 (j + K) + bCoef n j * harm 2 (j + K) / 2) ∧
      ∑ j ∈ Icc n (17 * n),
          (aCoef n j * harm 4 (j + (K + 1)) + bCoef n j * harm 3 (j + (K + 1)) / 3) =
        ∑ j ∈ Icc n (17 * n), (aCoef n j * harm 4 (j + K) + bCoef n j * harm 3 (j + K) / 3) := by
    intro K hK1 hK2
    have hs : ∀ r j : ℕ, harm r (j + (K + 1)) =
        harm r (j + K) + 1 / ((j : ℚ) + K + 1) ^ r := by
      intro r j
      unfold harm
      rw [show j + (K + 1) = (j + K) + 1 by ring, Finset.sum_Icc_succ_top (by omega)]
      push_cast
      ring
    have h2 := congrArg (fun s => (1 / 2 : ℚ) * s)
      (incr_gen n (K + 1) 1 (by norm_num) (by omega) (by omega))
    have h3 := congrArg (fun s => (-1 / 3 : ℚ) * s)
      (incr_gen n (K + 1) 2 (by norm_num) (by omega) (by omega))
    simp only [Finset.mul_sum, mul_zero] at h2 h3
    constructor
    · rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h2]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hs, hs]
      have hx : (j : ℚ) + K + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    · rw [← sub_eq_zero, ← Finset.sum_sub_distrib, ← h3]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hs, hs]
      have hx : (j : ℚ) + K + 1 ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  obtain ⟨d, rfl⟩ : ∃ d, K = 2 * n + d := ⟨K - 2 * n, by omega⟩
  induction d with
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih =>
    obtain ⟨ih3, ih4⟩ := ih (by omega) (by omega)
    obtain ⟨s3, s4⟩ := hstep (2 * n + d) (by omega) (by omega)
    rw [← add_assoc]
    exact ⟨ih3.trans s3.symm, ih4.trans s4.symm⟩

/-- **[3] The harmonic index depends only on the high root.** For `j ∈ [n, 17n]`, writing
`-j = k + pℓ` with `1 ≤ k ≤ p` (`ℓ = hiIdx p j`): `⌊(j+η)/p⌋ = ⌈2n/p⌉ - ℓ - 1`, and
`j + η < p²` (`j + η ≤ 19n + p - 1 < p²` from `30n < p²`, `p > 29`).
* Proved (≈ 30 lines).
* Directly from the PDF: yes (§9, "`⌊(j+η)/p⌋ = ⌈2n/p⌉ - ℓ - 1`, which is independent of `k`.
  Moreover `j + η ≤ 27n < p²`"). -/
theorem floor_class (n p : ℕ) (hp : Eligible n p) :
    ∀ j ∈ Icc n (17 * n), (j + eta n p) / p = ((ceil2 n p : ℤ) - hiIdx p j - 1).toNat ∧
      j + eta n p < p ^ 2 := by
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have hp0 : 0 < p := hp.1.pos
  have h29 := hp.2.1
  have h30 := hp.2.2.1
  -- `hiIdx p j = -⌊j/p⌋ - 1`
  have hhi : hiIdx p j = -((j / p : ℕ) : ℤ) - 1 := by
    unfold hiIdx
    have hjm := Nat.div_add_mod j p
    have hjr := Nat.mod_lt j hp0
    refine ((Int.ediv_emod_unique (r := (p : ℤ) - 1 - ((j % p : ℕ) : ℤ))
      (by exact_mod_cast hp0)).2 ⟨?_, ?_, ?_⟩).1
    · have : ((p * (j / p) + j % p : ℕ) : ℤ) = (j : ℤ) := by exact_mod_cast hjm
      push_cast at this ⊢
      linarith
    · omega
    · omega
  have hdiv : (j + eta n p) / p = j / p + ceil2 n p := by
    unfold eta
    rw [Nat.add_mul_div_left _ _ hp0]
  refine ⟨?_, ?_⟩
  · rw [hdiv, hhi]
    generalize j / p = a
    omega
  · -- `η ≤ 2n + p - 1`
    have hq := Nat.div_add_mod (2 * n + p - 1) p
    have hη : eta n p ≤ 2 * n + p - 1 := by
      unfold eta ceil2; omega
    have : 19 * n + p < p ^ 2 := by nlinarith
    omega

/-- **[4] Individual bounds.** On the windows, `a_j ∈ pℤ_(p)` and `b_j ∈ ℤ_(p)` for every `j`.
Proof: in the class `k` of `-j`, `p F_n(k + pV) = p^{h_k+1} U_k(V) G_k(V)` with `h_k ≥ -1`
(window root data), `G_k` a product of `p`-adic units, and the pole coefficients of `U_k` at its
unit-separated poles `p`-integral; the coefficients at `V = ℓ` are `a_j/p` and `b_j`.
* Proved (≈ 4 lines here, from `window_root_data` (field `h_ge`) and the helper
  `WindowReadout_Bounds.lean`, ≈ 250 lines).
* Directly from the PDF: yes ("The condition `h_k ≥ -1`, together with the separation of high
  poles, also gives the individual bounds `a_j ∈ pℤ_(p)` and `b_j ∈ ℤ_(p)`"). -/
theorem individual_bounds (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p)) :
    ∀ j, ValGE p 1 (aCoef n j) ∧ ValGE p 0 (bCoef n j) := by
  have : Fact p.Prime := ⟨hp.1⟩
  -- `h_k ≥ -1` for every class, from the window root data
  obtain ⟨NU, DU, hT⟩ := WindowRootData.window_root_data n p hn hp hw
  exact WindowReadoutAux.indiv_of_hge n p hp hT.h_ge

/-- **[5] Splitting harmonic numbers at `p`.** `H^{(r)}_m - p^{-r} H^{(r)}_{⌊m/p⌋}` is
`p`-integral (it is the sum over `k ≤ m`, `p ∤ k`; the multiples `k = pi` give exactly
`p^{-r} H^{(r)}_{⌊m/p⌋}`), and `H^{(r)}_m` is `p`-integral for `m < p`.
* Proved (≈ 46 lines).
* Directly from the PDF: yes ("its terms whose harmonic denominators are prime to `p`"; "a
  denominator root `l` of `U_t` has harmonic index `-l` after extracting the multiples of `p`"). -/
theorem harm_split (p : ℕ) [Fact p.Prime] (r m : ℕ) :
    ValGE p 0 (harm r m - harm r (m / p) / (p : ℚ) ^ r) ∧ (m < p → ValGE p 0 (harm r m)) := by
  have hp := (Fact.out : p.Prime)
  have hterm : ∀ k : ℕ, 0 < k → ¬ p ∣ k → ValGE p 0 (1 / (k : ℚ) ^ r) := by
    intro k hk hpk
    right
    rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hpk]
    simp
  -- the multiples `k = p i` of `p` in `[1, m]`
  have h2 : ∑ k ∈ (Icc 1 m).filter (fun k => p ∣ k), 1 / (k : ℚ) ^ r =
      harm r (m / p) / (p : ℚ) ^ r := by
    have he : (Icc 1 m).filter (fun k => p ∣ k) = (Icc 1 (m / p)).image (fun i => p * i) := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, i, rfl⟩
        refine ⟨i, ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos i with rfl | h
          · simp at h1
          · exact h
        · exact (Nat.le_div_iff_mul_le hp.pos).2 (by rw [mul_comm]; exact h2)
      · rintro ⟨i, ⟨h1, h2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
        · nlinarith [hp.pos]
        · have := (Nat.le_div_iff_mul_le hp.pos).1 h2
          rw [mul_comm]; exact this
    rw [he, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp.pos h)]
    unfold harm
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [mul_pow]
    ring
  have h1 := Finset.sum_filter_add_sum_filter_not (Icc 1 m) (fun k => p ∣ k)
    (fun k => 1 / (k : ℚ) ^ r)
  constructor
  · have hs : harm r m - harm r (m / p) / (p : ℚ) ^ r =
        ∑ k ∈ (Icc 1 m).filter (fun k => ¬ p ∣ k), 1 / (k : ℚ) ^ r := by
      rw [← h2]; unfold harm; linarith
    rw [hs]
    refine valGE_sum _ _ _ fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_filter.1 hk
    exact hterm k (Finset.mem_Icc.1 hk1).1 hk2
  · intro hm
    refine valGE_sum _ _ _ fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    exact hterm k hk1 (Nat.not_dvd_of_pos_of_lt hk1 (by omega))

/-- **[6] Regrouping the coefficients by high root.** For every weight `G` of the high root:
`∑_j a_j G(ℓ_j) = ∑_ℓ A_ℓ G(ℓ)` and `∑_j b_j G(ℓ_j) = ∑_ℓ B_ℓ G(ℓ)`, the `ℓ`-sums over the
high roots `ℓ_j = hiIdx p j` of `j ∈ [n, 17n]`.
Proof: the poles of `F_n` are the `-j`, `j ∈ [n, 17n]`; `-j - pℓ ∈ [1, p] ⟺ ℓ = hiIdx p j`; the
non-poles have `a_j = b_j = 0`; `Finset.sum_fiberwise_of_maps_to`.
* Proved (≈ 47 lines).
* Directly from the PDF: yes ("For every integral high pole `ℓ`, collect the corresponding
  coefficients as `A_ℓ` and `B_ℓ`"). -/
theorem regroup (n p : ℕ) (hp : Eligible n p) (G : ℤ → ℚ) :
    ∑ j ∈ Icc n (17 * n), aCoef n j * G (hiIdx p j) =
        ∑ ℓ ∈ (Icc n (17 * n)).image (hiIdx p),
          highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G ℓ ∧
      ∑ j ∈ Icc n (17 * n), bCoef n j * G (hiIdx p j) =
        ∑ ℓ ∈ (Icc n (17 * n)).image (hiIdx p),
          highPoleB p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G ℓ := by
  have hp0 : 0 < p := hp.1.pos
  have hp0' : (0 : ℤ) < p := by exact_mod_cast hp0
  -- the high root of `x` is `⌊(x-1)/p⌋`
  have hi_iff : ∀ x ℓ : ℤ, (x - 1) / p = ℓ ↔ x - p * ℓ ∈ Icc 1 (p : ℤ) := by
    intro x ℓ
    rw [Finset.mem_Icc]
    constructor
    · rintro rfl
      have h0 := Int.mul_ediv_add_emod (x - 1) p
      have h1 := Int.emod_nonneg (x - 1) hp0'.ne'
      have h2 := Int.emod_lt_of_pos (x - 1) hp0'
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      exact ((Int.ediv_emod_unique (r := x - 1 - p * ℓ) hp0').2
        ⟨by ring, by linarith, by linarith⟩).1
  have gen : ∀ c : ℤ → ℚ, ∑ j ∈ Icc n (17 * n), c (-(j : ℤ)) * G (hiIdx p j) =
      ∑ ℓ ∈ (Icc n (17 * n)).image (hiIdx p),
        (∑ x ∈ (denRoots n).toFinset.filter (fun x => x - p * ℓ ∈ Icc 1 (p : ℤ)), c x) * G ℓ := by
    intro c
    rw [← Finset.sum_fiberwise_of_maps_to (g := hiIdx p)
      (fun j hj => Finset.mem_image_of_mem _ hj)]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_nbij' (fun j => -(j : ℤ)) (fun x => (-x).toNat) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_Icc] at hj
      simp only [Finset.mem_filter, Multiset.mem_toFinset, denRoots, Multiset.mem_add,
        Finset.mem_val, Finset.mem_Icc]
      refine ⟨Or.inl ⟨by omega, by omega⟩, Finset.mem_Icc.1 ((hi_iff _ _).1 hj.2)⟩
    · intro x hx
      simp only [Finset.mem_filter, Multiset.mem_toFinset, denRoots, Multiset.mem_add,
        Finset.mem_val, Finset.mem_Icc] at hx
      have hx1 : x ≤ 0 := by omega
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      show (-(((-x).toNat : ℕ) : ℤ) - 1) / p = ℓ
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
      exact (hi_iff _ _).2 (Finset.mem_Icc.2 hx.2)
    · intro j _; simp
    · intro x hx
      simp only [Finset.mem_filter, Multiset.mem_toFinset, denRoots, Multiset.mem_add,
        Finset.mem_val, Finset.mem_Icc] at hx
      rw [Int.toNat_of_nonneg (by omega), neg_neg]
    · intro j hj
      rw [(Finset.mem_filter.1 hj).2]
  exact ⟨gen fun x => (pfCoeff (numRoots n) (denRoots n) x).1,
    gen fun x => (pfCoeff (numRoots n) (denRoots n) x).2⟩

/-! ### The node -/

/-- **Readout on the windows** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[6]. -/
theorem window_readout (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p))
    (hPB : ∀ ℓ : ℤ, ValGE p 3 (highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ) ∧
      ValGE p 2 (highPoleB p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ)) :
    ValGE p 3 (Q n) ∧ ValGE p 0 (P3 n) ∧ ValGE p (-1) (P4 n) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
  have hp29 := hp.2.1
  obtain ⟨hη1, hη2⟩ := eta_bounds n p hn hp hw
  obtain ⟨hcut3, hcut4⟩ := cutoff_invariance n (eta n p) hη1 hη2
  have hfl := floor_class n p hp
  have hind := individual_bounds n p hn hp hw
  -- the weights `w_ℓ = H^{(r)}_{⌈2n/p⌉ - ℓ - 1}`, `p`-integral on the occurring high roots
  set img := (Icc n (17 * n)).image (hiIdx p) with himg
  let G : ℕ → ℤ → ℚ := fun r ℓ => harm r (((ceil2 n p : ℤ) - ℓ - 1).toNat)
  have hGv : ∀ r, ∀ ℓ ∈ img, ValGE p 0 (G r ℓ) := by
    intro r ℓ hℓ
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hℓ
    obtain ⟨e, hlt⟩ := hfl j hj
    have hdiv : (j + eta n p) / p < p := Nat.div_lt_of_lt_mul (by rw [← sq]; exact hlt)
    rw [e] at hdiv
    exact (harm_split p r _).2 hdiv
  have hGj : ∀ r, ∀ j ∈ Icc n (17 * n), G r (hiIdx p j) = harm r ((j + eta n p) / p) := by
    intro r j hj
    simp only [G]
    rw [(hfl j hj).1]
  have h2inv : ValGE p 0 ((2 : ℚ)⁻¹) := by
    have := valGE_inv_small (p := p) 2 (by norm_num) (by omega); simpa using this
  have h3inv : ValGE p 0 ((3 : ℚ)⁻¹) := by
    have := valGE_inv_small (p := p) 3 (by norm_num) (by omega); simpa using this
  -- `Q_n = ∑_ℓ A_ℓ`
  have hQ : ValGE p 3 (Q n) := by
    have e : Q n = ∑ ℓ ∈ img, highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * 1 := by
      rw [← (regroup n p hp fun _ => 1).1]; simp [Q]
    rw [e]
    exact valGE_sum _ _ _ fun ℓ _ => by simpa using (hPB ℓ).1
  -- the regrouped harmonic parts
  have hAsum : ∀ r, ValGE p 2
      ((∑ ℓ ∈ img, highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G r ℓ) / p) := by
    intro r
    have h := valGE_sum img 3 _ fun ℓ hℓ => by
      simpa using valGE_mul (hPB ℓ).1 (hGv r ℓ hℓ)
    rw [div_eq_mul_inv]
    simpa using valGE_mul h (valGE_p_inv (p := p))
  have hBsum : ∀ r (q : ℚ), ValGE p 0 q⁻¹ → ValGE p 2
      ((∑ ℓ ∈ img, highPoleB p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G r ℓ) / q) := by
    intro r q hq
    have h := valGE_sum img 2 _ fun ℓ hℓ => by
      simpa using valGE_mul (hPB ℓ).2 (hGv r ℓ hℓ)
    rw [div_eq_mul_inv]
    simpa using valGE_mul h hq
  refine ⟨hQ, ?_, ?_⟩
  · -- `p² P_{3,n} ≡ 0 (mod p²)`
    have e : (p : ℚ) ^ 2 * P3 n = ∑ j ∈ Icc n (17 * n),
          ((p : ℚ) ^ 2 * aCoef n j *
              (harm 3 (j + eta n p) - harm 3 ((j + eta n p) / p) / (p : ℚ) ^ 3) +
            (p : ℚ) ^ 2 * bCoef n j *
              (harm 2 (j + eta n p) - harm 2 ((j + eta n p) / p) / (p : ℚ) ^ 2) * (2 : ℚ)⁻¹) +
        ((∑ ℓ ∈ img, highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G 3 ℓ) / p +
          (∑ ℓ ∈ img, highPoleB p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G 2 ℓ) / 2) := by
      rw [← (regroup n p hp (G 3)).1, ← (regroup n p hp (G 2)).2, hcut3, Finset.mul_sum,
        Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hGj 3 j hj, hGj 2 j hj]
      field_simp
      ring
    have hE : ValGE p 2 (∑ j ∈ Icc n (17 * n),
          ((p : ℚ) ^ 2 * aCoef n j *
              (harm 3 (j + eta n p) - harm 3 ((j + eta n p) / p) / (p : ℚ) ^ 3) +
            (p : ℚ) ^ 2 * bCoef n j *
              (harm 2 (j + eta n p) - harm 2 ((j + eta n p) / p) / (p : ℚ) ^ 2) * (2 : ℚ)⁻¹)) := by
      refine valGE_sum _ _ _ fun j _ => valGE_add ?_ ?_
      · have := valGE_mul (valGE_mul (valGE_p_pow (p := p) 2) (hind j).1)
          (harm_split p 3 (j + eta n p)).1
        exact valGE_mono (by norm_num) this
      · have := valGE_mul (valGE_mul (valGE_mul (valGE_p_pow (p := p) 2) (hind j).2)
          (harm_split p 2 (j + eta n p)).1) h2inv
        exact valGE_mono (by norm_num) this
    have h := valGE_add hE (valGE_add (hAsum 3) (hBsum 2 2 h2inv))
    rw [← e] at h
    have := valGE_of_pow_mul 2 h
    norm_num at this
    exact this
  · -- `p³ P_{4,n} ≡ 0 (mod p²)`
    have e : (p : ℚ) ^ 3 * P4 n = ∑ j ∈ Icc n (17 * n),
          ((p : ℚ) ^ 3 * aCoef n j *
              (harm 4 (j + eta n p) - harm 4 ((j + eta n p) / p) / (p : ℚ) ^ 4) +
            (p : ℚ) ^ 3 * bCoef n j *
              (harm 3 (j + eta n p) - harm 3 ((j + eta n p) / p) / (p : ℚ) ^ 3) * (3 : ℚ)⁻¹) +
        ((∑ ℓ ∈ img, highPoleA p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G 4 ℓ) / p +
          (∑ ℓ ∈ img, highPoleB p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) ℓ * G 3 ℓ) / 3) := by
      rw [← (regroup n p hp (G 4)).1, ← (regroup n p hp (G 3)).2, hcut4, Finset.mul_sum,
        Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hGj 4 j hj, hGj 3 j hj]
      field_simp
      ring
    have hE : ValGE p 2 (∑ j ∈ Icc n (17 * n),
          ((p : ℚ) ^ 3 * aCoef n j *
              (harm 4 (j + eta n p) - harm 4 ((j + eta n p) / p) / (p : ℚ) ^ 4) +
            (p : ℚ) ^ 3 * bCoef n j *
              (harm 3 (j + eta n p) - harm 3 ((j + eta n p) / p) / (p : ℚ) ^ 3) * (3 : ℚ)⁻¹)) := by
      refine valGE_sum _ _ _ fun j _ => valGE_add ?_ ?_
      · have := valGE_mul (valGE_mul (valGE_p_pow (p := p) 3) (hind j).1)
          (harm_split p 4 (j + eta n p)).1
        exact valGE_mono (by norm_num) this
      · have := valGE_mul (valGE_mul (valGE_mul (valGE_p_pow (p := p) 3) (hind j).2)
          (harm_split p 3 (j + eta n p)).1) h3inv
        exact valGE_mono (by norm_num) this
    have h := valGE_add hE (valGE_add (hAsum 4) (hBsum 3 3 h3inv))
    rw [← e] at h
    have := valGE_of_pow_mul 3 h
    norm_num at this
    exact this

end Meijer5255.WindowReadout
