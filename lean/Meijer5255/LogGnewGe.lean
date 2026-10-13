/-
# Node blueprint: `log_Gnew_ge` (paper §10, "The improved divisor and its density", (DEN))

Target (restated verbatim from `Blueprint_5255.lean`):
  `∀ ε > 0, ∀ᶠ n : ℕ in atTop, (gammaNew - ε) * n ≤ Real.log (Gnew n)`.

Strategy (paper §10, handoff §5.7). `log G_n^{new} = ∑_{p ≤ 19n eligible} gExp(n,p) log p` ([2]),
and `gExp = ψ + h₀ + 𝟙_𝒮 + 𝟙_𝒯`. Each of the three periodic parts is bounded below by a
*row weight* `∑_{rows (a,b,v)} v 𝟙[a < {x} < b]`: for `ψ` this is its definition, for the shell and
window indicators it holds because the rows of `𝒮` (resp. `𝒯`) are pairwise disjoint ([6]). The
prime number theorem ([1], turned into `θ(n/a) - θ(n/b) ≥ (1/a - 1/b - ε) n` in the glue) and the
negligibility of the excluded primes ([3]) give, for every finite number `K` of periods, the
density `∑_{rows} v ∑_{t<K} (1/(t+a) - 1/(t+b))` of each row family ([4]) and the density `6` of
the upper harmonic gain `h₀` ([5]). The convexity tail bound
`∑_{t ≥ K} f(t) ≥ 2(b-a)/(2K+a+b) + f(K)/2` ([7]) lets a large finite `M` reach the explicit
rational lower bound at `K = 1000`, and the exact rational certificate ([8]) shows that this bound
exceeds `γ_new = 30.45854724`. The glue chooses `η = ε/7`, picks `M` from [7], and adds up.

Supporting lemmas (8), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `prime_number_theorem` | ≈ 10000 (or import PrimeNumberTheoremAnd) | no (quoted) |
| 2 | `log_Gnew_eq` | 10 | yes (definition of `G_n^{new}`) |
| 3 | `excluded_small` | 30 | yes ("small excluded primes contribute `O(√n)`") |
| 4 | `rows_density` | 150 | partially (PNT; "for any fixed number of periods") |
| 5 | `hgain_density` | 40 | partially (PNT; `6 = ∫ h₀/x²`) |
| 6 | `unit_weight_le` | 30 | yes (the shells / windows are disjoint intervals) |
| 7 | `tail_bound` | 80 | partially (the convexity enclosure is stated, not proved) |
| 8 | `gamma_cert` | ≈ 600 (kernel certificate, chunked files) | partially (paper's certificate at `K = 1000`; here the logarithm is replaced by its first atanh term) |

Note on `K`: `γ_new = 30.45854724` is the paper's (DEN) value, so the certificate needs the
paper's `K = 1000`. The cheaper tail `(b-a)/(K+b)` of handoff §5.7 gives only `30.4585471312`
(`K = 200`) and `30.4585472286` (`K = 500`), *below* `γ_new` (it suffices for the
`30.4585465117` that `main_*` actually need, not for this node); at `K = 1000` it gives
`30.4585472404`, a margin of `4 · 10⁻¹⁰`. The atanh form `2(b-a)/(2K+a+b)` used here loses only
`≈ (b-a)³/(12K³)` per row against `log((K+b)/(K+a))`, so it keeps essentially the paper's margin
`30.45854724380549 - γ_new ≈ 3.8 · 10⁻⁹`.

The glue derives the interval form of the PNT from [1] (≈ 30 lines, copied from zeta34
`log_Delta_le.pnt_bounds` and pfq54 `log_G_ge.pnt_interval`), proves the pointwise inequality
`gExp ≥ rowWeight(ψ) + h₀ + rowWeight(𝒮) + rowWeight(𝒯)`, and does the `ε`-bookkeeping.

Reuse: zeta34 `blueprints/log_Delta_le.lean` (`prime_number_theorem`, `pnt_bounds`), pfq54
`log_G_ge.lean` (`log_Gdiv_eq`, `pnt_interval`, `excluded_small`), `log_G_aux2.lean` (`PNT`, `EXC`,
`elig_interval_nat`, `profile_gen`, `harmonic_gen`), `log_G_aux.lean` (`interval_sum`); zeta2
`blueprint_gamma_sumA/B.lean` (chunked directed-rounding certificate pattern for [8]).
-/
import Meijer5255.definitions
import Meijer5255.PNT
import Meijer5255.LogGnewGe_Aux
import Meijer5255.LogGnewGe_Cert

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.LogGnewGe

open Meijer5255

/-! ### Objects -/

/-- The eligible primes `p ≤ 19n` (the index set of `Gnew n`). -/
def eligSet (n : ℕ) : Finset ℕ := (range (19 * n + 1)).filter (Eligible n)

/-- The prime number theorem in interval form: `θ(n/a) - θ(n/b) ≥ (1/a - 1/b - ε) n` eventually
(pfq54 `LG2.PNT`). -/
def PNTi : Prop := ∀ (a b : ℝ), 0 < a → a < b → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
  ((n : ℝ) / a - n / b) - ε * n ≤ Chebyshev.theta ((n : ℝ) / a) - Chebyshev.theta ((n : ℝ) / b)

/-- The excluded (non-eligible) primes `p ≤ 19n` have `∑ log p = o(n)` (pfq54 `LG2.EXC`). -/
def EXC : Prop := ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
  ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p), Real.log p ≤ ε * n

/-- The periodic row weight `∑_{(a,b,v) ∈ rows} v 𝟙[a < {x} < b]` (`psi = rowWeight psiRows`). -/
def rowWeight (rows : List (ℚ × ℚ × ℕ)) (x : ℚ) : ℕ :=
  (rows.map fun r => if r.1 < Int.fract x ∧ Int.fract x < r.2.1 then r.2.2 else 0).sum

/-- The rows of an interval list, each with weight `1`. -/
def unitRows (rows : List (ℚ × ℚ)) : List (ℚ × ℚ × ℕ) := rows.map fun r => (r.1, r.2, 1)

/-- The truncated density `∑_{(a,b,v)} v ∑_{t<K} (1/(t+a) - 1/(t+b))`. -/
def rowSum (rows : List (ℚ × ℚ × ℕ)) (K : ℕ) : ℚ :=
  (rows.map fun r => (r.2.2 : ℚ) *
    ∑ t ∈ range K, (1 / ((t : ℚ) + r.1) - 1 / ((t : ℚ) + r.2.1))).sum

/-- The rational tail lower bound `∑_{(a,b,v)} v (2(b-a)/(2K+a+b) + f(K)/2)`,
`f(t) = 1/(t+a) - 1/(t+b)`. -/
def tailLB (rows : List (ℚ × ℚ × ℕ)) (K : ℕ) : ℚ :=
  (rows.map fun r => (r.2.2 : ℚ) * (2 * (r.2.1 - r.1) / (2 * (K : ℚ) + r.1 + r.2.1) +
    (1 / ((K : ℚ) + r.1) - 1 / ((K : ℚ) + r.2.1)) / 2)).sum

/-- The explicit rational lower bound for `γ_new` at `K = 1000`: the harmonic part `6` plus, for
the three row families (`ψ`, shells, windows), the partial sums over `t < 1000` and the tail
bound. -/
def gammaLB : ℚ :=
  6 + (rowSum psiRows 1000 + tailLB psiRows 1000) +
    (rowSum (unitRows shellRows) 1000 + tailLB (unitRows shellRows) 1000) +
    (rowSum (unitRows windowRows) 1000 + tailLB (unitRows windowRows) 1000)

/-! ### Supporting lemmas -/

/-- **[1] The prime number theorem** `θ(x)/x → 1` (statement as zeta34
`log_Delta_le.prime_number_theorem`; the only analytic input of this file).
* Re-exported from `PNT.lean` (the project's single accepted `sorry`; ≈ 10000 lines, or import
  `PrimeNumberTheoremAnd`).
* Directly from the PDF: no (quoted: "The prime number theorem and the bounded profiles give the
  density"). -/
theorem prime_number_theorem :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PNT.prime_number_theorem

/-- **[2] `log G_n^{new}` as a sum over eligible primes.**
* Proved (≈ 7 lines; pfq54 `log_G_ge.log_Gdiv_eq`, verbatim).
* Directly from the PDF: yes (definition of `G_n^{new}`). -/
theorem log_Gnew_eq (n : ℕ) :
    Real.log (Gnew n) = ∑ p ∈ eligSet n, (gExp n p : ℝ) * Real.log p := by
  -- pfq54 `log_G_ge.log_Gdiv_eq`
  unfold Gnew eligSet
  rw [Nat.cast_prod, Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    exact Nat.cast_ne_zero.mpr (pow_ne_zero _ (mem_filter.mp hp).2.1.ne_zero)

/-- **[3] Excluded primes are negligible**: primes `p ≤ 19n` with `p ≤ 29`, `p² ≤ 30n` or `p ∣ n`
have `∑ log p = o(n)` (`O(1) + O(√n log n) + O(log n)`).
* Proved (≈ 85 lines; pfq54 `log_G_ge.excluded_small`, verbatim; the `o(n)` bound
  `small_bound_isLittleO` is copied into the helper `LogGnewGe_Aux.lean` from zetas_irr
  `ZetasAux.lean`).
* Directly from the PDF: yes ("Small excluded primes contribute `O(√n)`; prime divisors of `n`
  contribute `O(log n)`"). -/
theorem excluded_small : EXC := by
  -- pfq54 `log_G_ge.excluded_small`, verbatim
  intro ε hε
  set A := (range 30).filter Nat.Prime
  set K := ∑ p ∈ A, Real.log p
  have hlog := (Real.isLittleO_log_id_atTop.comp_tendsto
    (tendsto_natCast_atTop_atTop (R := ℝ))).def (by positivity : 0 < ε / 3)
  have hsmall := LogGnewGeAux.small_bound_isLittleO.def (by positivity : 0 < ε / 3)
  have hK : ∀ᶠ n : ℕ in atTop, K ≤ ε / 3 * n := by
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (3 * K / ε)]
      with n hn
    rw [div_le_iff₀ hε] at hn
    linarith
  filter_upwards [hlog, hsmall, hK, eventually_ge_atTop 1] with n h1 h2 h3 hn
  set B := (range (Nat.sqrt (30 * n) + 1)).filter Nat.Prime
  set C := n.primeFactors
  have hnn : ∀ p ∈ (A ∪ B) ∪ C, 0 ≤ Real.log (p : ℝ) := fun p _ => Real.log_natCast_nonneg p
  have hsub : (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p) ⊆ (A ∪ B) ∪ C := by
    intro p hp
    obtain ⟨-, hpr, hne⟩ := mem_filter.mp hp
    simp only [Eligible, not_and_or, not_lt, not_not] at hne
    simp only [mem_union, A, B, C, mem_filter, mem_range, Nat.mem_primeFactors]
    rcases hne with h | h | h | h
    · exact absurd hpr h
    · exact Or.inl (Or.inl ⟨by omega, hpr⟩)
    · exact Or.inl (Or.inr ⟨Nat.lt_succ_of_le (Nat.le_sqrt'.mpr h), hpr⟩)
    · exact Or.inr ⟨hpr, h, by omega⟩
  have hunion : ∀ s t : Finset ℕ, (∀ p ∈ s ∪ t, 0 ≤ Real.log (p : ℝ)) →
      ∑ p ∈ s ∪ t, Real.log (p : ℝ) ≤ ∑ p ∈ s, Real.log (p : ℝ) + ∑ p ∈ t, Real.log (p : ℝ) := by
    intro s t hst
    rw [← Finset.sum_union_inter]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun p hp =>
      hst p (mem_union_left _ (mem_inter.mp hp).1))
  have hC : ∑ p ∈ C, Real.log (p : ℝ) ≤ Real.log n := by
    rw [← Real.log_prod (fun p hp => Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero),
      ← Nat.cast_prod]
    exact Real.log_le_log (by exact_mod_cast Finset.prod_pos fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).pos)
      (by exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n))
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : (0 : ℝ) ≤ Real.log 6 + 6 * Real.log (29 * n + 1) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 29 * n + 1)
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)
    linarith
  have hB : ∑ p ∈ B, Real.log (p : ℝ) ≤
      (Real.sqrt (30 * n + 10) + 1) * (Real.log 6 + 6 * Real.log (29 * n + 1)) := by
    have hcard : (B.card : ℝ) ≤ Real.sqrt (30 * n + 10) + 1 := by
      have h1 : B.card ≤ Nat.sqrt (30 * n) + 1 := (card_filter_le _ _).trans (card_range _).le
      have h2 : (Nat.sqrt (30 * n) : ℝ) ≤ Real.sqrt (30 * n + 10) :=
        (Real.nat_sqrt_le_real_sqrt).trans (Real.sqrt_le_sqrt (by push_cast; linarith))
      have : (B.card : ℝ) ≤ (Nat.sqrt (30 * n) : ℝ) + 1 := by exact_mod_cast h1
      linarith
    have hterm : ∀ p ∈ B, Real.log (p : ℝ) ≤ Real.log 6 + 6 * Real.log (29 * n + 1) := by
      intro p hp
      obtain ⟨hpr, hpp⟩ := mem_filter.mp hp
      have hp1 : p ≤ Nat.sqrt (30 * n) := Nat.lt_succ_iff.mp (mem_range.mp hpr)
      have hs := Nat.sqrt_le' (30 * n)
      have hp2 : p ≤ 29 * n + 1 := by nlinarith
      have h1 : Real.log p ≤ Real.log (29 * n + 1) :=
        Real.log_le_log (by exact_mod_cast hpp.pos) (by exact_mod_cast hp2)
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 29 * n + 1)
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 6)
      linarith
    calc ∑ p ∈ B, Real.log (p : ℝ) ≤ ∑ p ∈ B, (Real.log 6 + 6 * Real.log (29 * n + 1)) :=
          Finset.sum_le_sum hterm
      _ = B.card * (Real.log 6 + 6 * Real.log (29 * n + 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard hL
  have hlogn : Real.log n ≤ ε / 3 * n := by
    have := h1
    simp only [Function.comp_apply, id_eq] at this
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg n),
      abs_of_nonneg (Nat.cast_nonneg n)] at this
    exact this
  have hsm : (Real.sqrt (30 * n + 10) + 1) * (Real.log 6 + 6 * Real.log (29 * n + 1)) ≤
      ε / 3 * n := by
    have := h2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hL),
      abs_of_nonneg (Nat.cast_nonneg n)] at this
    exact this
  calc ∑ p ∈ (range (19 * n + 1)).filter (fun p => p.Prime ∧ ¬ Eligible n p), Real.log (p : ℝ)
      ≤ ∑ p ∈ (A ∪ B) ∪ C, Real.log (p : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp
    _ ≤ ∑ p ∈ A ∪ B, Real.log (p : ℝ) + ∑ p ∈ C, Real.log (p : ℝ) := hunion _ _ hnn
    _ ≤ (K + ∑ p ∈ B, Real.log (p : ℝ)) + ∑ p ∈ C, Real.log (p : ℝ) := by
        gcongr
        exact hunion _ _ fun p hp => hnn p (mem_union_left _ hp)
    _ ≤ ε * n := by linarith

/-- **[4] Density of a family of periodic rows.** For rows `(a, b, v)` with
`1/19 ≤ a < b ≤ 1` and every finite number `K` of periods,
`∑_{p eligible} rowWeight(n/p) log p ≥ (∑_{rows} v ∑_{t<K} (1/(t+a) - 1/(t+b)) - ε) n`
eventually. Proof: for `t < K` the primes `p ∈ (n/(t+b), n/(t+a))` have `{n/p} ∈ (a,b)` and are
`≤ 19n`; apply `PNTi` on each interval and `EXC`; distinct `t` give disjoint prime sets, overlapping
rows are counted with their weights on both sides; the other periods contribute `≥ 0`.
* Proved (≈ 120 lines; adapted from pfq54 `LG2.profile_gen` with `range 8` → `range K`; no
  disjointness is needed since `rowWeight` is linear in the rows; `elig_interval`, `cond_iff`,
  `lsum_*` from the helper `LogGnewGe_Aux.lean`).
* Directly from the PDF: partially ("For any fixed number of periods the prime number theorem
  evaluates the finite sum"). -/
theorem rows_density (hP : PNTi) (hE : EXC) (rows : List (ℚ × ℚ × ℕ))
    (hbd : ∀ r ∈ rows, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1) (K : ℕ) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ((rowSum rows K : ℝ) - ε) * n ≤
      ∑ p ∈ eligSet n, (rowWeight rows ((n : ℚ) / p) : ℝ) * Real.log p := by
  -- adapted from pfq54 `LG2.profile_gen` (`range 8` → `range K`; the table and disjointness
  -- hypotheses are replaced by the definition of `rowWeight`, which is linear in the rows)
  -- the row weight and the truncated density as list sums over the rows
  have hw : ∀ (l : List (ℚ × ℚ × ℕ)) (y : ℚ) (w : ℝ), (rowWeight l y : ℝ) * w =
      (l.map fun r => (r.2.2 : ℝ) * (if r.1 < Int.fract y ∧ Int.fract y < r.2.1 then w else 0)).sum := by
    intro l y w
    induction l with
    | nil => simp [rowWeight]
    | cons r l ih =>
      have e : rowWeight (r :: l) y =
          (if r.1 < Int.fract y ∧ Int.fract y < r.2.1 then r.2.2 else 0) + rowWeight l y := rfl
      rw [e, List.map_cons, List.sum_cons, ← ih]
      push_cast
      split_ifs <;> ring
  have hcast : ∀ l : List (ℚ × ℚ × ℕ), ((rowSum l K : ℚ) : ℝ) = (l.map fun r => (r.2.2 : ℝ) *
      ∑ k ∈ range K, (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))).sum := by
    intro l
    induction l with
    | nil => simp [rowSum]
    | cons r l ih =>
      have e : rowSum (r :: l) K = (r.2.2 : ℚ) *
          ∑ t ∈ range K, (1 / ((t : ℚ) + r.1) - 1 / ((t : ℚ) + r.2.1)) + rowSum l K := rfl
      rw [e, List.map_cons, List.sum_cons, ← ih]
      push_cast
      ring
  intro ε hε
  set Kc : ℝ := (rows.map fun r => (r.2.2 : ℝ) * K).sum
  have hK0 : 0 ≤ Kc := List.sum_nonneg fun z hz => by
    obtain ⟨r, -, rfl⟩ := List.mem_map.mp hz
    positivity
  set ε' := ε / (Kc + 1)
  have hε' : 0 < ε' := by positivity
  have hεK : ε' * Kc ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  -- the prime number theorem on each interval `(n/(t+b), n/(t+a))`, `t < K`
  have hev := LogGnewGeAux.eventually_list rows (fun r n => ∀ k ∈ range K,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1) - ε') * n ≤ ∑ p ∈ eligSet n,
        if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
        else 0)
    fun r hr => (eventually_all_finset (range K)).mpr fun k _ => by
      obtain ⟨h1, h2, -⟩ := hbd r hr
      have a1 : (1 / 19 : ℝ) ≤ r.1 := by
        have := (Rat.cast_le (K := ℝ)).mpr h1
        push_cast at this
        exact this
      have a2 : (r.1 : ℝ) < r.2.1 := by exact_mod_cast h2
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      exact LogGnewGeAux.elig_interval hP hE _ _ (one_div_pos.mpr (by linarith))
        (one_div_lt_one_div_of_lt (by linarith) (by linarith))
        (by rw [div_le_iff₀ (by linarith)]; linarith) ε' hε'
  filter_upwards [hev] with n hn
  -- pointwise: the periods `t < K` of one row are disjoint and give `{n/p} ∈ (a, b)`
  have step1 : ∀ p ∈ eligSet n, (rows.map fun r => (r.2.2 : ℝ) * ∑ k ∈ range K,
      (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
        else 0)).sum ≤ (rowWeight rows ((n : ℚ) / p) : ℝ) * Real.log p := by
    intro p hp
    have hp0 : 0 < p := (mem_filter.mp hp).2.1.pos
    rw [hw]
    refine LogGnewGeAux.lsum_le _ _ _ fun r hr => ?_
    obtain ⟨h1, h2, h3⟩ := hbd r hr
    have ha : 0 < r.1 := lt_of_lt_of_le (by norm_num) h1
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    set y := (n : ℚ) / p
    have e : ∀ k ∈ range K, (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n
        then Real.log p else 0) = (if (k : ℚ) + r.1 < y ∧ y < k + r.2.1 then Real.log p else 0) :=
      fun k _ => by
        have hci := LogGnewGeAux.cond_iff n p k hp0 r.1 r.2.1 ha (ha.trans h2)
        by_cases hc : (k : ℚ) + r.1 < y ∧ y < k + r.2.1
        · rw [ite_eq_left (hci.mpr hc), ite_eq_left hc]
        · rw [ite_eq_right fun h => hc (hci.mp h), ite_eq_right hc]
    rw [Finset.sum_congr rfl e]
    have hfl : ∀ k : ℕ, (k : ℚ) + r.1 < y ∧ y < k + r.2.1 → ⌊y⌋ = (k : ℤ) := by
      intro k hk
      rw [Int.floor_eq_iff]
      push_cast
      constructor <;> linarith [hk.1, hk.2]
    by_cases h : ∃ k ∈ range K, (k : ℚ) + r.1 < y ∧ y < k + r.2.1
    · obtain ⟨k0, hk0, hk⟩ := h
      have hfr : Int.fract y = y - k0 := by
        rw [Int.fract, hfl k0 hk]
        push_cast
        ring
      have huniq : ∀ k ∈ range K, (k : ℚ) + r.1 < y ∧ y < k + r.2.1 → k = k0 := by
        intro k _ hk'
        have := (hfl k hk').symm.trans (hfl k0 hk)
        exact_mod_cast this
      rw [Finset.sum_eq_single k0 (fun k hk hne => ite_eq_right fun h' => hne (huniq k hk h'))
        (fun h' => absurd hk0 h'), ite_eq_left hk,
        ite_eq_left (by rw [hfr]; constructor <;> linarith [hk.1, hk.2])]
    · rw [Finset.sum_eq_zero fun k hk => ite_eq_right fun h' => h ⟨k, hk, h'⟩]
      split_ifs
      · exact Real.log_natCast_nonneg p
      · exact le_rfl
  have step2 := Finset.sum_le_sum step1
  have hs := LogGnewGeAux.lsum_swap rows (eligSet n) fun r p => (r.2.2 : ℝ) * ∑ k ∈ range K,
    (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p else 0)
  beta_reduce at hs
  rw [hs] at step2
  have step3 := LogGnewGeAux.lsum_le rows
    (fun r => (r.2.2 : ℝ) * ∑ k ∈ range K,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1) - ε') * n)
    (fun r => ∑ p ∈ eligSet n, (r.2.2 : ℝ) * ∑ k ∈ range K,
      (if 1 / ((k : ℝ) + r.2.1) * n < p ∧ (p : ℝ) < 1 / ((k : ℝ) + r.1) * n then Real.log p
        else 0))
    fun r hr => by
      rw [← Finset.mul_sum, Finset.sum_comm]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => hn r hr k hk)
        (Nat.cast_nonneg _)
  have e4 : ∀ r : ℚ × ℚ × ℕ, (r.2.2 : ℝ) * ∑ k ∈ range K,
      (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1) - ε') * n =
      ((r.2.2 : ℝ) * ∑ k ∈ range K, (1 / ((k : ℝ) + r.1) - 1 / ((k : ℝ) + r.2.1))) * n -
        (ε' * n) * ((r.2.2 : ℝ) * K) := fun r => by
    rw [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
    ring
  rw [List.map_congr_left fun r _ => e4 r, LogGnewGeAux.lsum_lin] at step3
  rw [hcast]
  have := mul_le_mul_of_nonneg_right hεK (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith

/-- **[5] The upper harmonic gain.** `∑_{p eligible} h₀(n/p) log p ≥ (6 - ε) n` eventually
(`(3 + 2 + 1) n + o(n)` from `(18n,19n)`, `(17n,18n)`, `(16n,17n)`).
* Proved (≈ 20 lines; pfq54 `LG2.harmonic_gen`, verbatim).
* Directly from the PDF: partially (`6 = ∫ h₀/x²`; PNT). -/
theorem hgain_density (hP : PNTi) (hE : EXC) : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
    (6 - ε) * n ≤ ∑ p ∈ eligSet n, (hgain n p : ℝ) * Real.log p := by
  -- pfq54 `LG2.harmonic_gen`, verbatim
  intro ε hε
  filter_upwards [LogGnewGeAux.elig_interval_nat hP hE 18 19 (by norm_num) (by norm_num) le_rfl
      (ε / 6) (by positivity),
    LogGnewGeAux.elig_interval_nat hP hE 17 18 (by norm_num) (by norm_num) (by norm_num)
      (ε / 6) (by positivity),
    LogGnewGeAux.elig_interval_nat hP hE 16 17 (by norm_num) (by norm_num) (by norm_num)
      (ε / 6) (by positivity)]
    with n h1 h2 h3
  have e : ∀ p ∈ eligSet n, (hgain n p : ℝ) * Real.log p =
      3 * (if 18 * n < p ∧ p < 19 * n then Real.log p else 0) +
        2 * (if 17 * n < p ∧ p < 18 * n then Real.log p else 0) +
          (if 16 * n < p ∧ p < 17 * n then Real.log p else 0) := fun p _ => by
    unfold hgain
    split_ifs <;> first | omega | (push_cast; ring)
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  push_cast at h1 h2 h3
  unfold eligSet
  linarith

/-- **[6] The shell and window indicators dominate their row weights.** The fourteen shells are
pairwise disjoint subintervals of `(0,1)`, and so are the two windows; hence at most one row of
each family contains `{x}`.
* Proved (≈ 28 lines; `List.Pairwise` of the sorted rows by `decide +kernel`, then an induction
  over the list).
* Directly from the PDF: yes (the shells are listed as disjoint intervals in §7, the windows in
  §9). -/
theorem unit_weight_le (x : ℚ) :
    rowWeight (unitRows shellRows) x ≤ (if inRows shellRows x then 1 else 0) ∧
      rowWeight (unitRows windowRows) x ≤ (if inRows windowRows x then 1 else 0) := by
  set y := Int.fract x
  have hcons : ∀ (r : ℚ × ℚ) (l : List (ℚ × ℚ)), rowWeight (unitRows (r :: l)) x =
      (if r.1 < y ∧ y < r.2 then 1 else 0) + rowWeight (unitRows l) x := fun r l => rfl
  have hzero : ∀ l : List (ℚ × ℚ), (∀ s ∈ l, ¬ (s.1 < y ∧ y < s.2)) →
      rowWeight (unitRows l) x = 0 := by
    intro l hl
    induction l with
    | nil => rfl
    | cons r l ih =>
      rw [hcons, ite_eq_right (hl r List.mem_cons_self),
        ih fun s hs => hl s (List.mem_cons_of_mem r hs)]
  have key : ∀ l : List (ℚ × ℚ), l.Pairwise (fun r s => r.2 ≤ s.1) →
      rowWeight (unitRows l) x ≤ (if inRows l x then 1 else 0) := by
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons r l ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hl
      have hin : inRows (r :: l) x = (decide (r.1 < y ∧ y < r.2) || inRows l x) := rfl
      rw [hcons, hin]
      by_cases h : r.1 < y ∧ y < r.2
      · rw [ite_eq_left h, hzero l fun s hs hs' => by linarith [hhead s hs, hs'.1, h.2]]
        simp [h]
      · rw [ite_eq_right h, decide_eq_false h, Bool.false_or, Nat.zero_add]
        exact ih htail
  exact ⟨key _ (by decide +kernel), key _ (by decide +kernel)⟩

/-- **[7] Tail bound.** For rows with `0 < a < b`, the full series `∑_{t ≥ 0}` exceeds the
partial sum to `K` plus `∑ v (2(b-a)/(2K+a+b) + f(K)/2)`, so the partial sums to `M` eventually come
within any `η > 0` of this bound. Proof: `f(t) = (b-a)/((t+a)(t+b))` is positive, decreasing and
convex on `t ≥ 0`, so the trapezoid rule gives `∑_{t ≥ K} f(t) ≥ ∫_K^∞ f + f(K)/2`, and
`∫_K^∞ f = log y ≥ 2(y-1)/(y+1) = 2(b-a)/(2K+a+b)` with `y = (K+b)/(K+a) ≥ 1` (first term of
the atanh series of `log y`); the series converges (`f(t) ≤ (b-a)/t²`).
* Proved (≈ 120 lines, without integrals or `tsum`: with `g(x) = 2(b-a)/(2x+a+b) + f(x)/2` the
  discrete trapezoid step `g(t) - g(t+1) ≤ f(t)` holds for `t ≥ 0` (with `R = 2t+a+b`,
  `S = R + 2`: `4/(RS) ≤ 2/R² + 2/S² ≤ 1/(2(t+a)(t+b)) + 1/(2(t+1+a)(t+1+b))`), so
  `∑_{t<M} f ≥ ∑_{t<K} f + g(K) - g(M)` for `M ≥ K`, and `g(M) ≤ 2(b-a)/M`).
* Directly from the PDF: partially (the enclosure `log((K+b)/(K+a)) + f(K)/2 ≤ ∑_{t≥K} f(t)` is
  stated "by convexity"; the paper then encloses the logarithm by its atanh series, of which only
  the first term is kept here). -/
theorem tail_bound (rows : List (ℚ × ℚ × ℕ)) (hbd : ∀ r ∈ rows, 0 < r.1 ∧ r.1 < r.2.1)
    (K : ℕ) : ∀ η > (0 : ℝ), ∀ᶠ M : ℕ in atTop,
      ((rowSum rows K + tailLB rows K : ℚ) : ℝ) - η ≤ (rowSum rows M : ℝ) := by
  -- `f(x) = 1/(x+a) - 1/(x+b)` and the telescoping majorant `g(x) = 2(b-a)/(2x+a+b) + f(x)/2`
  let f : ℚ → ℚ → ℚ → ℚ := fun a b x => 1 / (x + a) - 1 / (x + b)
  let g : ℚ → ℚ → ℚ → ℚ := fun a b x => 2 * (b - a) / (2 * x + a + b) + f a b x / 2
  -- the discrete trapezoid step `g(t) - g(t+1) ≤ f(t)` (convexity, by AM-GM)
  have hstep : ∀ a b : ℚ, 0 < a → a < b → ∀ x : ℚ, 0 ≤ x →
      g a b x - g a b (x + 1) ≤ f a b x := by
    intro a b ha hab x hx
    have hb : 0 < b := ha.trans hab
    have hP : 0 < (x + a) * (x + b) := by positivity
    have hQ : 0 < (x + 1 + a) * (x + 1 + b) := by positivity
    have hR : 0 < 2 * x + a + b := by positivity
    have hS : 0 < 2 * (x + 1) + a + b := by positivity
    have ef : ∀ y : ℚ, 0 ≤ y → f a b y = (b - a) / ((y + a) * (y + b)) := fun y hy => by
      have : 0 < y + a := by positivity
      have : 0 < y + b := by positivity
      simp only [f]
      field_simp
      ring
    have eL : 2 * (b - a) / (2 * x + a + b) - 2 * (b - a) / (2 * (x + 1) + a + b) =
        (b - a) * (4 / ((2 * x + a + b) * (2 * (x + 1) + a + b))) := by
      field_simp
      ring
    have h1 : 2 / (2 * x + a + b) ^ 2 ≤ 1 / (2 * ((x + a) * (x + b))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (b - a)]
    have h2 : 2 / (2 * (x + 1) + a + b) ^ 2 ≤ 1 / (2 * ((x + 1 + a) * (x + 1 + b))) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (b - a)]
    have h3 : 4 / ((2 * x + a + b) * (2 * (x + 1) + a + b)) ≤
        2 / (2 * x + a + b) ^ 2 + 2 / (2 * (x + 1) + a + b) ^ 2 := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_pos hR hS
      nlinarith [sq_nonneg (2 * x + a + b - (2 * (x + 1) + a + b)), mul_pos this this]
    have h4 : 4 / ((2 * x + a + b) * (2 * (x + 1) + a + b)) ≤
        1 / (2 * ((x + a) * (x + b))) + 1 / (2 * ((x + 1 + a) * (x + 1 + b))) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (by linarith : (0 : ℚ) ≤ b - a)
    have e1 : f a b (x + 1) = (b - a) / ((x + 1 + a) * (x + 1 + b)) := ef _ (by positivity)
    have e0 := ef x hx
    simp only [g]
    rw [e0, e1]
    rw [e0] at *
    have : (b - a) * (1 / (2 * ((x + a) * (x + b))) + 1 / (2 * ((x + 1 + a) * (x + 1 + b)))) =
        (b - a) / ((x + a) * (x + b)) / 2 + (b - a) / ((x + 1 + a) * (x + 1 + b)) / 2 := by
      field_simp
    linarith
  -- one row: `∑_{t<K} f + g(K) - 2(b-a)/M ≤ ∑_{t<M} f` for `K ≤ M`, `1 ≤ M`
  have hrow1 : ∀ a b : ℚ, 0 < a → a < b → ∀ M : ℕ, K ≤ M → 1 ≤ M →
      ∑ t ∈ range K, f a b t + g a b K - 2 * (b - a) / M ≤ ∑ t ∈ range M, f a b t := by
    intro a b ha hab M hKM hM
    have hb : 0 < b := ha.trans hab
    have htel : ∀ M : ℕ, K ≤ M →
        ∑ t ∈ range K, f a b t + g a b K ≤ ∑ t ∈ range M, f a b t + g a b M := by
      intro M hKM
      induction M, hKM using Nat.le_induction with
      | base => exact le_rfl
      | succ m _ ih =>
        rw [Finset.sum_range_succ]
        have := hstep a b ha hab m (Nat.cast_nonneg m)
        push_cast
        linarith
    have hgM : g a b M ≤ 2 * (b - a) / M := by
      have hM0 : (1 : ℚ) ≤ M := by exact_mod_cast hM
      have hMa : 0 < (M : ℚ) + a := by positivity
      have hMb : 0 < (M : ℚ) + b := by linarith
      have ef : f a b M = (b - a) / ((M + a) * (M + b)) := by
        simp only [f]; field_simp; ring
      simp only [g]
      rw [ef]
      have i1 : 2 * (b - a) / (2 * (M : ℚ) + a + b) ≤ 2 * (b - a) / (2 * M) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
      have i2 : (b - a) / (((M : ℚ) + a) * (M + b)) ≤ (b - a) / (M * 1) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity)
          (mul_le_mul (by linarith) (by linarith) (by norm_num) (by positivity))
      have e3 : 2 * (b - a) / (2 * (M : ℚ)) = (b - a) / M := by field_simp
      have e4 : 2 * (b - a) / (M : ℚ) = (b - a) / M + (b - a) / M := by ring
      rw [mul_one] at i2
      rw [e3] at i1
      have : 0 ≤ (b - a) / (M : ℚ) := div_nonneg (by linarith) (by positivity)
      linarith
    linarith [htel M hKM]
  -- all rows, with weights
  have hlist : ∀ l : List (ℚ × ℚ × ℕ), (∀ r ∈ l, 0 < r.1 ∧ r.1 < r.2.1) → ∀ M : ℕ, K ≤ M →
      1 ≤ M → rowSum l K + tailLB l K -
        (l.map fun r => (r.2.2 : ℚ) * (2 * (r.2.1 - r.1))).sum / M ≤ rowSum l M := by
    intro l hl M hKM hM
    induction l with
    | nil => simp [rowSum, tailLB]
    | cons r l ih =>
      have ih' := ih fun s hs => hl s (List.mem_cons_of_mem r hs)
      obtain ⟨ha, hab⟩ := hl r List.mem_cons_self
      have e1 : rowSum (r :: l) K = (r.2.2 : ℚ) * ∑ t ∈ range K, f r.1 r.2.1 t + rowSum l K := rfl
      have e2 : rowSum (r :: l) M = (r.2.2 : ℚ) * ∑ t ∈ range M, f r.1 r.2.1 t + rowSum l M := rfl
      have e3 : tailLB (r :: l) K = (r.2.2 : ℚ) * g r.1 r.2.1 K + tailLB l K := rfl
      have e4 : ((r :: l).map fun r => (r.2.2 : ℚ) * (2 * (r.2.1 - r.1))).sum =
          (r.2.2 : ℚ) * (2 * (r.2.1 - r.1)) +
            (l.map fun r => (r.2.2 : ℚ) * (2 * (r.2.1 - r.1))).sum := rfl
      have h := mul_le_mul_of_nonneg_left (hrow1 r.1 r.2.1 ha hab M hKM hM)
        (Nat.cast_nonneg r.2.2 : (0 : ℚ) ≤ r.2.2)
      rw [e1, e2, e3, e4, add_div]
      have e5 : (r.2.2 : ℚ) * (2 * (r.2.1 - r.1)) / M = (r.2.2 : ℚ) * (2 * (r.2.1 - r.1) / M) := by
        ring
      rw [e5]
      nlinarith
  -- choose `M`
  intro η hη
  set C := (rows.map fun r => (r.2.2 : ℚ) * (2 * (r.2.1 - r.1))).sum
  filter_upwards [eventually_ge_atTop (max (max K 1) ⌈(C : ℝ) / η⌉₊)] with M hM
  have hKM : K ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hM1 : 1 ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hCM : (C : ℝ) / η ≤ M :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hM)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hCη : (C : ℝ) / M ≤ η := by
    rw [div_le_iff₀ hη] at hCM
    rw [div_le_iff₀ hM0]
    linarith
  have h := hlist rows hbd M hKM hM1
  have hR : ((rowSum rows K + tailLB rows K - C / M : ℚ) : ℝ) ≤ (rowSum rows M : ℝ) := by
    exact_mod_cast h
  push_cast at hR ⊢
  linarith

/-- **[8] The exact rational certificate** `30.45854724 < γ_LB(1000)`.
* Proved (≈ 85 lines here + the helper `LogGnewGe_Cert.lean`, ≈ 95 lines: each term and each
  tail is rounded down to `⌊10¹⁶ ·⌋` by `ℕ` division (zeta2 directed-rounding pattern); the three
  family sums over `t < 1000` and the tails are evaluated by `decide +kernel` (a few seconds) and
  give `γ_LB(1000) ≥ 30.4585472438030979`, a margin `3.80 · 10⁻⁹` over `γ_new`).
* Directly from the PDF: partially (the paper certifies `γ_new ≥ 30.45854724380549` at
  `K = 1000` with atanh enclosures of `log((K+b)/(K+a))` and exact rational remainders; this
  bound replaces the logarithm by the first atanh term, a loss below `10⁻¹⁰`, against the margin
  `≈ 3.8 · 10⁻⁹`). -/
theorem gamma_cert : (3045854724 / 10 ^ 8 : ℚ) < gammaLB := by
  open LogGnewGeCert in
  -- the directed rounding `natTerm`, `natTail` (helper `LogGnewGe_Cert.lean`) is a lower bound
  have hsc : (0 : ℚ) < scale := by unfold scale; positivity
  have hterm : ∀ c : Row5, RowOK c → ∀ t : ℕ, (natTerm t c : ℚ) ≤
      scale * ((toRow c).2.2 * (1 / ((t : ℚ) + (toRow c).1) - 1 / ((t : ℚ) + (toRow c).2.1))) := by
    rintro ⟨an, ad, bn, bd, v⟩ ⟨h1, h2, h3, h4⟩ t
    simp only [natTerm, toRow] at h1 h2 h3 h4 ⊢
    have hbn : 0 < bn := by
      rcases Nat.eq_zero_or_pos bn with h | h
      · subst h; have := Nat.mul_pos h1 h3; omega
      · exact h
    have hX : (0 : ℚ) < (t : ℚ) * ad + an := by positivity
    have hY : (0 : ℚ) < (t : ℚ) * bd + bn := by positivity
    have hd : (0 : ℚ) < ad := by exact_mod_cast h2
    have he : (0 : ℚ) < bd := by exact_mod_cast h3
    refine (Nat.cast_div_le).trans (le_of_eq ?_)
    push_cast [Nat.cast_sub h4]
    field_simp
    ring
  have htail : ∀ c : Row5, RowOK c → ∀ K : ℕ, (natTail K c : ℚ) ≤
      scale * ((toRow c).2.2 * (2 * ((toRow c).2.1 - (toRow c).1) /
        (2 * (K : ℚ) + (toRow c).1 + (toRow c).2.1) +
        (1 / ((K : ℚ) + (toRow c).1) - 1 / ((K : ℚ) + (toRow c).2.1)) / 2)) := by
    rintro ⟨an, ad, bn, bd, v⟩ ⟨h1, h2, h3, h4⟩ K
    simp only [natTail, toRow] at h1 h2 h3 h4 ⊢
    have hbn : 0 < bn := by
      rcases Nat.eq_zero_or_pos bn with h | h
      · subst h; have := Nat.mul_pos h1 h3; omega
      · exact h
    have hX : (0 : ℚ) < (K : ℚ) * ad + an := by positivity
    have hY : (0 : ℚ) < (K : ℚ) * bd + bn := by positivity
    have hd : (0 : ℚ) < ad := by exact_mod_cast h2
    have he : (0 : ℚ) < bd := by exact_mod_cast h3
    have hZ : (0 : ℚ) < 2 * K * ad * bd + an * bd + bn * ad := by positivity
    push_cast
    refine (add_le_add Nat.cast_div_le Nat.cast_div_le).trans (le_of_eq ?_)
    push_cast [Nat.cast_sub h4]
    field_simp
    ring
  have hrow : ∀ l : List Row5, (∀ c ∈ l, RowOK c) → ∀ K : ℕ,
      ((∑ t ∈ range K, periodNat l t : ℕ) : ℚ) / scale + (tailNat l K : ℚ) / scale ≤
        rowSum (l.map toRow) K + tailLB (l.map toRow) K := by
    intro l hl K
    induction l with
    | nil => simp [periodNat, tailNat, rowSum, tailLB]
    | cons c l ih =>
      have hc := hl c List.mem_cons_self
      have ih' := ih fun d hd => hl d (List.mem_cons_of_mem c hd)
      have e1 : ∑ t ∈ range K, periodNat (c :: l) t =
          ∑ t ∈ range K, natTerm t c + ∑ t ∈ range K, periodNat l t := by
        rw [← Finset.sum_add_distrib]; rfl
      have e2 : tailNat (c :: l) K = natTail K c + tailNat l K := rfl
      have e3 : rowSum ((c :: l).map toRow) K = (toRow c).2.2 *
          ∑ t ∈ range K, (1 / ((t : ℚ) + (toRow c).1) - 1 / ((t : ℚ) + (toRow c).2.1)) +
          rowSum (l.map toRow) K := rfl
      have e4 : tailLB ((c :: l).map toRow) K = (toRow c).2.2 * (2 * ((toRow c).2.1 - (toRow c).1) /
          (2 * (K : ℚ) + (toRow c).1 + (toRow c).2.1) +
          (1 / ((K : ℚ) + (toRow c).1) - 1 / ((K : ℚ) + (toRow c).2.1)) / 2) +
          tailLB (l.map toRow) K := rfl
      have s1 : ((∑ t ∈ range K, natTerm t c : ℕ) : ℚ) / scale ≤ (toRow c).2.2 *
          ∑ t ∈ range K, (1 / ((t : ℚ) + (toRow c).1) - 1 / ((t : ℚ) + (toRow c).2.1)) := by
        rw [div_le_iff₀ hsc, Finset.mul_sum, Finset.sum_mul, Nat.cast_sum]
        exact Finset.sum_le_sum fun t _ => by rw [mul_comm _ (scale : ℚ)]; exact hterm c hc t
      have s2 := htail c hc K
      rw [e1, e2, e3, e4]
      push_cast at ih' ⊢
      rw [← div_le_iff₀' hsc] at s2
      push_cast at s1
      rw [add_div, add_div]
      linarith
  have hS : unitRows shellRows = dShell.map toRow := shell_eq
  have hW : unitRows windowRows = dWin.map toRow := win_eq
  have bP := hrow dPsi psi_ok 1000
  have bS := hrow dShell shell_ok 1000
  have bW := hrow dWin win_ok 1000
  rw [psi_sum, psi_tail] at bP
  rw [shell_sum, shell_tail] at bS
  rw [win_sum, win_tail] at bW
  unfold gammaLB
  rw [psi_eq, hS, hW]
  unfold scale at bP bS bW
  norm_num at bP bS bW ⊢
  linarith

/-! ### The node -/

/-- **Density of the divisor** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[8]. -/
theorem log_Gnew_ge :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (gammaNew - ε) * n ≤ Real.log (Gnew n) := by
  intro ε hε
  -- the prime number theorem in two-sided form (zeta34 `pnt_bounds`)
  have hbounds : ∀ δ : ℝ, 0 < δ → ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x ≥ X₀,
      (1 - δ) * x ≤ Chebyshev.theta x ∧ Chebyshev.theta x ≤ (1 + δ) * x := by
    intro δ hδ
    obtain ⟨X, hX⟩ := Metric.tendsto_atTop.mp prime_number_theorem δ hδ
    refine ⟨max X 1, le_max_right _ _, fun x hx => ?_⟩
    have hx0 : 0 < x := by linarith [le_max_right X 1]
    have h := hX x (le_trans (le_max_left _ _) hx)
    rw [Real.dist_eq, abs_lt] at h
    constructor
    · have : 1 - δ < Chebyshev.theta x / x := by linarith [h.1]
      exact ((lt_div_iff₀ hx0).mp this).le
    · have : Chebyshev.theta x / x < 1 + δ := by linarith [h.2]
      exact ((div_lt_iff₀ hx0).mp this).le
  -- the interval form (pfq54 `pnt_interval`)
  have hP : PNTi := by
    intro a b ha hab ε hε
    have hb : 0 < b := ha.trans hab
    set δ := ε / (1 / a + 1 / b) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨X₀, -, hX⟩ := hbounds δ hδ0
    have hlim : Tendsto (fun n : ℕ => (n : ℝ) / b) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const hb
    filter_upwards [hlim.eventually_ge_atTop X₀] with n hn
    have hna : X₀ ≤ (n : ℝ) / a :=
      hn.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg _) ha hab.le)
    obtain ⟨h1, -⟩ := hX _ hna
    obtain ⟨-, h2⟩ := hX _ hn
    have hsum : δ * ((n : ℝ) / a + n / b) = ε * n := by
      rw [hδ]; field_simp
    linarith
  have hE := excluded_small
  -- row bounds of the three families
  have hbdψ : ∀ r ∈ psiRows, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1 := by decide +kernel
  have hbdS : ∀ r ∈ unitRows shellRows, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1 := by
    decide +kernel
  have hbdT : ∀ r ∈ unitRows windowRows, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1 := by
    decide +kernel
  have pos : ∀ rows : List (ℚ × ℚ × ℕ),
      (∀ r ∈ rows, 1 / 19 ≤ r.1 ∧ r.1 < r.2.1 ∧ r.2.1 ≤ 1) → ∀ r ∈ rows, 0 < r.1 ∧ r.1 < r.2.1 :=
    fun rows h r hr => ⟨lt_of_lt_of_le (by norm_num) (h r hr).1, (h r hr).2.1⟩
  -- the bookkeeping constant
  set η := ε / 7 with hη
  have hη0 : 0 < η := by positivity
  -- a common number of periods `M` reaching the `K = 1000` bound up to `η` in each family
  obtain ⟨M, hMψ, hMS, hMT⟩ := ((tail_bound psiRows (pos _ hbdψ) 1000 η hη0).and
    ((tail_bound _ (pos _ hbdS) 1000 η hη0).and (tail_bound _ (pos _ hbdT) 1000 η hη0))).exists
  have hcert : gammaNew < (gammaLB : ℝ) := by
    have h : ((3045854724 / 10 ^ 8 : ℚ) : ℝ) < (gammaLB : ℝ) := Rat.cast_lt.mpr gamma_cert
    unfold gammaNew
    push_cast at h
    exact h
  have hLB : (gammaLB : ℝ) = 6 + ((rowSum psiRows 1000 + tailLB psiRows 1000 : ℚ) : ℝ) +
      ((rowSum (unitRows shellRows) 1000 + tailLB (unitRows shellRows) 1000 : ℚ) : ℝ) +
      ((rowSum (unitRows windowRows) 1000 + tailLB (unitRows windowRows) 1000 : ℚ) : ℝ) := by
    unfold gammaLB
    push_cast
    ring
  filter_upwards [rows_density hP hE psiRows hbdψ M η hη0,
    rows_density hP hE (unitRows shellRows) hbdS M η hη0,
    rows_density hP hE (unitRows windowRows) hbdT M η hη0,
    hgain_density hP hE η hη0] with n h1 h2 h3 h4
  rw [log_Gnew_eq]
  -- pointwise: `gExp ≥ rowWeight(ψ) + h₀ + rowWeight(𝒮) + rowWeight(𝒯)`
  have hpt : ∀ p ∈ eligSet n,
      (rowWeight psiRows ((n : ℚ) / p) : ℝ) * Real.log p + (hgain n p : ℝ) * Real.log p +
        (rowWeight (unitRows shellRows) ((n : ℚ) / p) : ℝ) * Real.log p +
        (rowWeight (unitRows windowRows) ((n : ℚ) / p) : ℝ) * Real.log p ≤
      (gExp n p : ℝ) * Real.log p := by
    intro p _
    obtain ⟨hS, hT⟩ := unit_weight_le ((n : ℚ) / p)
    have hψ : rowWeight psiRows ((n : ℚ) / p) = psi ((n : ℚ) / p) := rfl
    have hnat : rowWeight psiRows ((n : ℚ) / p) + hgain n p +
        rowWeight (unitRows shellRows) ((n : ℚ) / p) +
        rowWeight (unitRows windowRows) ((n : ℚ) / p) ≤ gExp n p := by
      unfold gExp
      omega
    have hreal : ((rowWeight psiRows ((n : ℚ) / p) + hgain n p +
        rowWeight (unitRows shellRows) ((n : ℚ) / p) +
        rowWeight (unitRows windowRows) ((n : ℚ) / p) : ℕ) : ℝ) ≤ (gExp n p : ℝ) := by
      exact_mod_cast hnat
    have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    rw [← add_mul, ← add_mul, ← add_mul]
    refine mul_le_mul_of_nonneg_right ?_ hlog
    push_cast at hreal
    exact hreal
  have hsum := Finset.sum_le_sum hpt
  simp only [Finset.sum_add_distrib] at hsum
  -- the `ε`-bookkeeping
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  push_cast at hMψ hMS hMT hLB
  have hconst : gammaNew - ε ≤ ((rowSum psiRows M : ℝ) - η) + (6 - η) +
      ((rowSum (unitRows shellRows) M : ℝ) - η) + ((rowSum (unitRows windowRows) M : ℝ) - η) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_right hconst hn0
  linarith

end Meijer5255.LogGnewGe
