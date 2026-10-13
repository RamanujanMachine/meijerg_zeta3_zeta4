/-
# Node blueprint: `carry_facts` (paper §5 (E),(D); §7 last paragraph; §10)

Target (restated verbatim from `Blueprint_5255.lean`): for `n ≥ 1`, eligible `p` and `x = n/p`,
  `v_p(C_n) = c(x)`, `v_p(d_{19n}) = 1` if `p ≤ 19n`, on the shells and windows
  `ψ(x) = c(x) + 1` and `h₀ = 0`, and the windows lie inside the shells.

Strategy. (1) Every factorial argument of `C_n = (15n)!²/(10n)!³` is `≤ 15n < p²`, so Legendre's
formula has one term, `v_p(m!) = ⌊m/p⌋` ([1]), and `⌊15n/p⌋ = ⌊15x⌋`, `⌊10n/p⌋ = ⌊10x⌋`
(`Rat.floor_natCast_div_natCast`).  (2) For `p ≤ 19n < p²` exactly one multiple of `p`, and no
multiple of `p²`, lies in `[1, 19n]` ([2]).  (3) Put `f = {x}`; it is not a Farey fraction of
order `29` ([4], from `p > 29`, `p ∤ n`), so the finite chamber statement [5] (`ψ = c + 1` on all
47 + 9 open Farey-29 cells of the shells and windows) applies at `f`, and `c(x) = c(f)` ([3]).
If `h₀(x) ≠ 0` then `16n < p`, so `{x} = x < 1/16`, while every shell/window row starts at
`≥ 1/11`: hence `h₀ = 0` there.  (4) `(1/10, 2/19) ⊂ (1/11, 1/8)` and
`(11/12, 15/16) ⊂ (10/11, 16/17)`.  Steps (3)–(4) (the `inRows` unfolding, the floor
computation and the interval arithmetic) are the glue below.

Supporting lemmas (5), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `padicValNat_factorial_small` | 6 | yes ("Legendre's formula has just its first term") |
| 2 | `padicValNat_dlcm` | 40 | yes (§11/§10: `v_p(d_{19n}) = 1` as `p² > 19n`) |
| 3 | `cfun_fract` | 10 | yes ("`c(f)` is unchanged by the lift", §7) |
| 4 | `fract_not_farey` | 25 | yes ("Condition (E) prevents `x` from lying on its boundaries", §5) |
| 5 | `psi_eq_cfun_succ_on_cells` | 150 | partially (§7 last paragraph / §10 assert it as certificate output) |

Reuse: pfq54 `pairing_bound.lean` (`padicValNat_factorial_small`, proved there in 6 lines),
`G_dvd_Z.lean` (`padicValRat_Cn`), `upper_range_bound.lean` (`padicValRat_D`: `v_p(d_{19n}) = 1`);
zeta34 `Chamber_dsl.lean`, `Chamber_reduce.lean` and pfq54 `profile_aux.lean` (`grid`, `okF`,
`chkL_sound`) for the chamber certificate pattern of [5].
-/
import Meijer5255.definitions
import Meijer5255.CarryFacts_Cells

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.CarryFacts

open Meijer5255

/-! ### Supporting lemmas -/

/-- **[1] Legendre's formula below `p²`.** `v_p(m!) = ⌊m/p⌋` for `m < p²`.
* Proved (≈ 6 lines).
* Directly from the PDF: yes ("Legendre's formula has just its first term", §5). -/
theorem padicValNat_factorial_small (p m : ℕ) [Fact p.Prime] (hm : m < p ^ 2) :
    padicValNat p m.factorial = m / p := by
  -- provenance: pfq54 `pairing_bound.padicValNat_factorial_small`
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow (by omega) hm
  rw [padicValNat_factorial hlog]
  simp

/-- **[2] `v_p(d_m) = 1` in the range `p ≤ m < p²`.** `v_p(lcm(1..m)) = max_{k ≤ m} v_p(k)`, the
maximum is attained at `k = p` (value `1`) and no `k ≤ m < p²` has `v_p(k) ≥ 2`.
* Proved (≈ 6 lines).
* Directly from the PDF: yes (`log d_{19n}` and the `d_{19n}` normalization; for `p ≤ 19n` with
  `p² > 30n` the exponent is one). -/
theorem padicValNat_dlcm (p m : ℕ) (hp : p.Prime) (h1 : p ≤ m) (h2 : m < p ^ 2) :
    padicValNat p (dlcm m) = 1 := by
  -- `dlcm = Nat.lcmUpto` and `v_p(lcm(1..m)) = ⌊log_p m⌋` (Mathlib `Nat.factorization_lcmUpto`)
  have h := Nat.factorization_lcmUpto m hp
  rw [Nat.factorization_def _ hp] at h
  change padicValNat p (Nat.lcmUpto m) = 1
  rw [h, Nat.log_eq_one_iff']
  exact ⟨h1, by rwa [← pow_two]⟩

/-- **[3] `c` is `1`-periodic.** `c(x) = c({x})`: with `x = t + f`, `t ∈ ℤ`,
`⌊15x⌋ = 15t + ⌊15f⌋`, `⌊10x⌋ = 10t + ⌊10f⌋` and `2·15t - 3·10t = 0`.
* Proved (≈ 7 lines).
* Directly from the PDF: yes ("The normalization valuation `c(f)` is unchanged by the lift",
  §7). -/
theorem cfun_fract (x : ℚ) : cfun x = cfun (Int.fract x) := by
  have h : ∀ k : ℤ, ⌊(k : ℚ) * x⌋ = ⌊(k : ℚ) * Int.fract x⌋ + k * ⌊x⌋ := fun k => by
    rw [← Int.floor_add_intCast]; congr 1; rw [Int.fract]; push_cast; ring
  have h15 := h 15
  have h10 := h 10
  push_cast at h15 h10
  unfold cfun; rw [h15, h10]; ring

/-- **[4] `{n/p}` avoids the Farey walls of order `29`.** For eligible `p`,
`{n/p} = (n mod p)/p` has reduced denominator `p > 29` (as `p ∤ n`), so it is not of the form
`a/b` with `0 < b ≤ 29`.
* Proved (≈ 18 lines).
* Directly from the PDF: yes ("Condition (E) prevents `x` from lying on its boundaries",
  §5; "excluded by (E)", appendix). -/
theorem fract_not_farey (n p : ℕ) (hp : Eligible n p) (a b : ℕ) (hb0 : 0 < b) (hb : b ≤ 29) :
    Int.fract ((n : ℚ) / p) ≠ (a : ℚ) / b := by
  obtain ⟨hpr, h29, -, hnd⟩ := hp
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  intro heq
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  have hb0' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  rw [div_eq_div_iff hp0 hb0'] at heq
  have heqN : n % p * b = a * p := by exact_mod_cast heq
  have hdvd : p ∣ n % p * b := heqN ▸ dvd_mul_left p a
  rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
  · have hlt : n % p < p := Nat.mod_lt _ hpr.pos
    have h0 : n % p = 0 := by
      by_contra hne
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h) (by omega)
    exact hnd (Nat.dvd_of_mod_eq_zero h0)
  · have := Nat.le_of_dvd hb0 h
    omega

/-- **[5] The baseline profile on the shells and windows.** For `0 < f < 1` off the Farey walls
of order `29`, if `f` lies in one of the fourteen shells or the two windows, then
`ψ(f) = c(f) + 1`.  Finite case split over the 47 + 9 open Farey-29 cells of these sixteen
intervals: on each cell `⌊15f⌋`, `⌊10f⌋` and the `psiRows` row containing `f` are constant
(`Int.floor_eq_iff`, `norm_num` at the cell endpoints), and the values match.
* Proved (≈ 30 lines here, plus ≈ 160 lines in the helper `CarryFacts_Cells.lean`: 68 cells
  between 69 sorted breakpoints, midpoint values checked by `decide +kernel`, generic transfer).
* Directly from the PDF: partially (§7 last paragraph: "On the table intervals the baseline
  profile is exactly `c(f)+1` … The same rational certificate checks these equalities"; §10:
  "on these cells the baseline exponent is `c+1`"; the cell-by-cell check is the certificate's). -/
theorem psi_eq_cfun_succ_on_cells (f : ℚ) (h0 : 0 < f) (h1 : f < 1)
    (hf : ∀ a b : ℕ, 0 < b → b ≤ 29 → f ≠ (a : ℚ) / b)
    (hS : inRows shellRows f ∨ inRows windowRows f) :
    (psi f : ℤ) = cfun f + 1 := by
  -- certificate and generic cell lemmas in `CarryFacts_Cells.lean`
  have hfB : f ∉ Cells.cellPts := fun hm => by
    rw [Cells.cellPts, List.mem_map] at hm
    obtain ⟨⟨a, b⟩, hp, he⟩ := hm
    exact hf a b (Cells.cellPairs_den _ hp).1 (Cells.cellPairs_den _ hp).2 he.symm
  -- `f` lies in a cell `(l, r)` of consecutive breakpoints; `g` is its midpoint
  obtain ⟨p, hp, hp1, hp2⟩ := Cells.locate _ Cells.cellPts_sorted f hfB
    ⟨0, Cells.cellPts_zero, h0⟩ ⟨1, Cells.cellPts_one, h1⟩
  have hcons := Cells.consecutive _ Cells.cellPts_sorted p hp
  obtain ⟨g, hg⟩ : ∃ g : ℚ, g = (p.1 + p.2) / 2 := ⟨_, rfl⟩
  have hlg : p.1 < g := by rw [hg]; linarith
  have hgr : g < p.2 := by rw [hg]; linarith
  have hgB : g ∉ Cells.cellPts := fun hm => by rcases hcons g hm with h | h <;> linarith
  have hT : ∀ q ∈ Cells.cellPts, q < f ↔ q < g := fun q hq => by
    rcases hcons q hq with h | h
    · exact iff_of_true (by linarith) (by linarith)
    · exact iff_of_false (by linarith) (by linarith)
  have hg0 : 0 < g := by rcases hcons 0 Cells.cellPts_zero with h | h <;> linarith
  have hg1 : g < 1 := by rcases hcons 1 Cells.cellPts_one with h | h <;> linarith
  obtain ⟨hpsi, hc, hs, hw⟩ := Cells.transfer f g h0 h1 hg0 hg1 hfB hgB hT
  have hc' := List.all_eq_true.1 Cells.cells_check p hp
  rw [← hg] at hc'
  have hor : (inRows shellRows g || inRows windowRows g) = true := by
    rw [hs, hw] at hS
    rcases hS with h | h <;> simp only [h, Bool.true_or, Bool.or_true]
  rw [hor, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hc'
  rw [hpsi, hc]
  exact hc'

/-! ### The node -/

/-- **Carry facts** (statement verbatim from `Blueprint_5255.lean`), proved from [1]–[5]. -/
theorem carry_facts (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) :
    padicValRat p (Cn n) = cfun ((n : ℚ) / p) ∧
      (p ≤ 19 * n → padicValRat p (dlcm (19 * n)) = 1) ∧
      ((inRows shellRows ((n : ℚ) / p) ∨ inRows windowRows ((n : ℚ) / p)) →
        (psi ((n : ℚ) / p) : ℤ) = cfun ((n : ℚ) / p) + 1 ∧ hgain n p = 0) ∧
      (inRows windowRows ((n : ℚ) / p) → inRows shellRows ((n : ℚ) / p)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.1.pos
  have hsq := hp.2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  -- (1) `v_p(C_n) = 2⌊15n/p⌋ - 3⌊10n/p⌋`
  · have key : ∀ e : ℕ, e ≤ 30 →
        padicValRat p (((e * n).factorial : ℕ) : ℚ) = ⌊(e : ℚ) * ((n : ℚ) / p)⌋ := by
      intro e he
      rw [padicValRat.of_nat, padicValNat_factorial_small p _ (by nlinarith)]
      rw [show (e : ℚ) * ((n : ℚ) / p) = ((e * n : ℕ) : ℚ) / (p : ℕ) by push_cast; ring,
        Rat.floor_natCast_div_natCast, Int.natCast_div]
    have k15 := key 15 (by norm_num)
    have k10 := key 10 (by norm_num)
    push_cast at k15 k10
    unfold Cn cfun
    rw [padicValRat.div (by positivity) (by positivity), padicValRat.pow, padicValRat.pow, k15,
      k10]
    push_cast; ring
  -- (2) `v_p(d_{19n}) = 1`
  · intro h19
    rw [padicValRat.of_nat, padicValNat_dlcm p (19 * n) hp.1 h19 (by omega)]
    rfl
  -- (3) shells and windows
  · intro hS
    set f := Int.fract ((n : ℚ) / p) with hf_def
    have hfx : Int.fract f = f := Int.fract_fract _
    have hf0 : 0 < f := by
      have hne := fract_not_farey n p hp 0 1 one_pos (by norm_num)
      simp only [Nat.cast_zero, zero_div] at hne
      exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne)
    have hf1 : f < 1 := Int.fract_lt_one _
    have hpsi : psi f = psi ((n : ℚ) / p) := by simp only [psi, hf_def, Int.fract_fract]
    have hrow : ∀ rows, inRows rows f = inRows rows ((n : ℚ) / p) := fun rows => by
      simp only [inRows, hf_def, Int.fract_fract]
    have hS' : inRows shellRows f ∨ inRows windowRows f := by rw [hrow, hrow]; exact hS
    refine ⟨?_, ?_⟩
    · rw [← hpsi, cfun_fract ((n : ℚ) / p), ← hf_def]
      exact psi_eq_cfun_succ_on_cells f hf0 hf1 (fun a b hb0 hb => fract_not_farey n p hp a b hb0 hb)
        hS'
    · -- every row starts at `≥ 1/11`, while `h₀ ≠ 0` forces `{n/p} = n/p < 1/16`
      have hlow : 1 / 11 < f := by
        rcases hS' with h | h
        · simp only [inRows, shellRows, hfx, List.any_cons, List.any_nil, Bool.or_false,
            Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ |
            ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
        · simp only [inRows, windowRows, hfx, List.any_cons, List.any_nil, Bool.or_false,
            Bool.or_eq_true, decide_eq_true_eq] at h
          rcases h with ⟨h, -⟩ | ⟨h, -⟩ <;> linarith
      by_contra hg
      have h16 : 16 * n < p := by unfold hgain at hg; split_ifs at hg <;> omega
      have hx0 : 0 ≤ (n : ℚ) / p := by positivity
      have hx16 : (n : ℚ) / p < 1 / 16 := by
        rw [div_lt_iff₀ hp0]; have : ((16 * n : ℕ) : ℚ) < p := by exact_mod_cast h16
        push_cast at this; linarith
      have hfeq : f = (n : ℚ) / p := Int.fract_eq_self.2 ⟨hx0, by linarith⟩
      linarith
  -- (4) `(1/10, 2/19) ⊂ (1/11, 1/8)` and `(11/12, 15/16) ⊂ (10/11, 16/17)`
  · intro hW
    simp only [inRows, windowRows, shellRows, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, decide_eq_true_eq] at hW ⊢
    rcases hW with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by linarith, by linarith⟩
    · iterate 13 refine Or.inr ?_
      exact ⟨by linarith, by linarith⟩

end Meijer5255.CarryFacts
