/-
# Node blueprint: `baseline_profile` (paper §5 and appendix; handoff §5.4 pairing route)

Target (restated verbatim from `Blueprint_5255.lean`): for `n ≥ 1` and eligible `p`, every entry
of both integer forms `Z3v n`, `Z4v n` has `p`-adic valuation `≥ ψ({n/p}) + h₀(n/p)`.

Strategy (handoff §5.4, avoiding the paper's harmonic test `ℓ(x,y)`).
* Case `h₀(n/p) = 0`.  The profile `ψ` equals (at eligible primes) the maximum `φ₁₀` of `0` and
  the ten pairing values `c(x) - ∑_{d∈D} ⌊dx⌋ + ∑_{l∈L} ⌊lx⌋` ([6], [1]).  If `φ₁₀ = 0` the
  bound is the integrality of `baseline_integrality`.  Otherwise the maximizing pairing `(L, D)`
  is realized by a permutation `b = shift ∘ σ` of the shifts `(-2..2)` ([2]); the factorial ratio
  `λ_{n,b}` satisfies `λ_{n,b} Z ∈ ℤ` ([3]), `λ_{n,b} ≠ 0` ([5]) and, by Legendre with one term,
  `v_p(λ_{n,b}) = -(row value)` ([4]); hence `v_p(Z) ≥ -v_p(λ) = φ₁₀ = ψ`.
* Case `h₀(n/p) ≠ 0`, i.e. `16n < p < 19n`: then `{n/p} = n/p < 1/16 < 1/15`, so `ψ = 0` ([7],
  first row `(0, 1/15, 0)` of the appendix table), and the upper harmonic range bound [8] gives
  valuation `≥ h₀`.
The valuation transfer `l ≠ 0, l x ∈ ℤ ⟹ v_p(x) ≥ -v_p(l)`, the case analysis and the `ValGE`
bookkeeping are done in the glue below; it uses the blueprint node `baseline_integrality`
(a logical prerequisite in the paper).

Supporting lemmas (8), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `phi10_cases` | 15 | no (the pairing description is new, handoff §5.4) |
| 2 | `pairing_realized` | 35 | no (new; ten explicit permutations) |
| 3 | `permutation_lemma` | 300 | partially (paper §4 argument applied to permuted factorials) |
| 4 | `padicValRat_lam` | 30 | yes (Legendre with one term, §5) |
| 5 | `lam_ne_zero` | 4 | yes (quotient of factorials) |
| 6 | `psi_eq_phi10` | 250 | no (new finding; Farey-29 chamber certificate) |
| 7 | `psi_eq_zero_low` | 15 | yes (appendix table, row `(0, 1/15, 0)`) |
| 8 | `upper_range_bound` | 200 | partially (paper (V) + certificate give `g₃ = g₄`; pfq54 proves `r = 4`) |

Reuse: pfq54 `pairing_bound.lean` (`rowVal`, `rowValPerm`, `phi_cases`, `pairing_realized`,
`padicValRat_lam`, `lam_ne_zero`, `valGE_of_lam_mul`, `pairing_bound` — the eight-pairing
version, proved there), `permutation_lemma.lean` (`permutation_lemma`, `coeffJetPerm_integral`),
`upper_range_bound.lean` (`padicValRat_D`, `harm_valGE`, `U_V_valuation_active`,
`U_V_valuation_all`, `upper_range_bound` for `r = 4`), `Pfq54_defs.lean` (`shift`, `lam`,
`pairings`, `phi`), `log_G_aux3.lean` (`table_of_check`) for the chamber pattern of [6].
-/
import Meijer5255.definitions
import Meijer5255.BaselineIntegrality
import Meijer5255.BaselineProfile_Cells
import Meijer5255.BaselineProfile_Upper

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.BaselineProfile

open Meijer5255

/-! ### Objects -/

/-- The five shifts `(-2,-1,0,1,2)`; a permutation `σ` gives `b_i = shift (σ i)`. -/
def shift : Fin 5 → ℤ := ![-2, -1, 0, 1, 2]

/-- The factorial ratio `λ_{n,b} = (10n)!³ ∏_{e ∈ J_b} (en)! / ((15n)!² ∏_{l ∈ L_b} (ln)!)`,
with `L_b = (10+b₀, 11+b₁, 12+b₂)`, `J_b = (16-b₃, 17-b₄)`, `b = shift ∘ σ` (pfq54 `lam`), i.e.
`C_n⁻¹ · ∏_{J_b} (en)! / ∏_{L_b} (ln)!`: the permuted binomial product is `λ_{n,b}` times the
unpermuted one. -/
def lam (σ : Equiv.Perm (Fin 5)) (n : ℕ) : ℚ :=
  let b : Fin 5 → ℤ := fun i => shift (σ i)
  let fac : ℤ → ℚ := fun e => ((e * n).toNat.factorial : ℚ)
  fac 10 ^ 3 * fac (16 - b 3) * fac (17 - b 4) /
    (fac 15 ^ 2 * fac (10 + b 0) * fac (11 + b 1) * fac (12 + b 2))

/-- The ten factorial pairings `(L, D)`: pfq54's eight plus `([9,9,14],[15,17])` and
`([8,13,13],[16,18])` (handoff §5.4). -/
def pairings10 : List (List ℤ × List ℤ) :=
  [([8, 13, 13], [17, 17]), ([11, 11, 11], [14, 19]), ([9, 9, 14], [16, 16]),
   ([12, 12, 12], [18, 18]), ([11, 11, 14], [18, 18]), ([9, 9, 12], [14, 16]),
   ([10, 10, 10], [14, 16]), ([9, 11, 14], [17, 17]), ([9, 9, 14], [15, 17]),
   ([8, 13, 13], [16, 18])]

/-- The value of a pairing row `(L, D)` at `x`: `c(x) - ∑_{d∈D} ⌊dx⌋ + ∑_{l∈L} ⌊lx⌋`. -/
def rowVal (LD : List ℤ × List ℤ) (x : ℚ) : ℤ :=
  cfun x - (LD.2.map fun d => ⌊(d : ℚ) * x⌋).sum + (LD.1.map fun l => ⌊(l : ℚ) * x⌋).sum

/-- The same value for the lengths `L_b = (10+b₀, 11+b₁, 12+b₂)`, `J_b = (16-b₃, 17-b₄)` of the
permutation `b = shift ∘ σ`. -/
def rowValPerm (σ : Equiv.Perm (Fin 5)) (x : ℚ) : ℤ :=
  let b : Fin 5 → ℤ := fun i => shift (σ i)
  cfun x - ⌊((16 - b 3 : ℤ) : ℚ) * x⌋ - ⌊((17 - b 4 : ℤ) : ℚ) * x⌋ +
    ⌊((10 + b 0 : ℤ) : ℚ) * x⌋ + ⌊((11 + b 1 : ℤ) : ℚ) * x⌋ + ⌊((12 + b 2 : ℤ) : ℚ) * x⌋

/-- The ten-pairing profile `φ₁₀(x) = max(0, max_{(L,D) ∈ pairings10} rowVal (L,D) x)`. -/
def phi10 (x : ℚ) : ℤ :=
  pairings10.foldr (fun LD m => max m (rowVal LD x)) 0

/-! ### Supporting lemmas -/

/-- **[1] The profile is a maximum of row values.** `φ₁₀(x) ≥ 0`, and `φ₁₀(x)` is `0` or the
value of one of the ten rows.
* Proved (≈ 20 lines; pfq54 `phi_cases`, verbatim with `pairings10`).
* Directly from the PDF: no (the pairing description of `ψ` is new, handoff §5.4). -/
theorem phi10_cases (x : ℚ) :
    0 ≤ phi10 x ∧ (phi10 x = 0 ∨ ∃ LD ∈ pairings10, phi10 x = rowVal LD x) := by
  -- provenance: pfq54 `pairing_bound.phi_cases`
  have key : ∀ l : List (List ℤ × List ℤ),
      0 ≤ l.foldr (fun LD m => max m (rowVal LD x)) 0 ∧
        (l.foldr (fun LD m => max m (rowVal LD x)) 0 = 0 ∨
          ∃ LD ∈ l, l.foldr (fun LD m => max m (rowVal LD x)) 0 = rowVal LD x) := by
    intro l
    induction l with
    | nil => exact ⟨le_rfl, Or.inl rfl⟩
    | cons a l ih =>
      obtain ⟨h0, h1⟩ := ih
      rw [List.foldr_cons]
      refine ⟨le_max_of_le_left h0, ?_⟩
      rcases max_choice (l.foldr (fun LD m => max m (rowVal LD x)) 0) (rowVal a x) with h | h <;>
        rw [h]
      · rcases h1 with h1 | ⟨LD, hLD, h1⟩
        · exact Or.inl h1
        · exact Or.inr ⟨LD, List.mem_cons_of_mem _ hLD, h1⟩
      · exact Or.inr ⟨a, List.mem_cons_self, rfl⟩
  exact key pairings10

/-- **[2] Every pairing row is realized by a permutation of the shifts.** The eight rows of
pfq54 as there; `([9,9,14],[15,17])` by `b = (-1,-2,2,1,0)` and `([8,13,13],[16,18])` by
`b = (-2,2,1,0,-1)`.
* Proved (≈ 25 lines; pfq54 `pairing_realized` plus the two new rows).
* Directly from the PDF: no (new; the paper uses the `ℓ(x,y)` test instead). -/
theorem pairing_realized :
    ∀ LD ∈ pairings10, ∃ σ : Equiv.Perm (Fin 5), ∀ x, rowVal LD x = rowValPerm σ x := by
  -- provenance: pfq54 `pairing_bound.pairing_realized` (rows 1–8); `σ i = b_i + 2`
  intro LD hLD
  simp only [pairings10, List.mem_cons, List.not_mem_nil, or_false] at hLD
  rcases hLD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Equiv.ofBijective ![0, 4, 3, 1, 2] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![3, 2, 1, 4, 0] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![1, 0, 4, 2, 3] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![4, 3, 2, 0, 1] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![3, 2, 4, 0, 1] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![1, 0, 2, 4, 3] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![2, 1, 0, 4, 3] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · exact ⟨Equiv.ofBijective ![3, 0, 4, 1, 2] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · -- `b = (-1,-2,2,1,0)`
    exact ⟨Equiv.ofBijective ![1, 0, 4, 3, 2] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩
  · -- `b = (-2,2,1,0,-1)`
    exact ⟨Equiv.ofBijective ![0, 4, 3, 2, 1] (by decide), fun x => by
      norm_num [rowVal, rowValPerm, shift]; ring⟩

/-- **[3] Permutation lemma.** For every `σ` and `n ≥ 1`, `λ_{n,b}` times each entry of both
integer forms is an integer.  The permuted binomial product
`∏_{i<3} C(j+(10+i)n-ε, (10+i+bᵢ)n) · C((16-b₃)n, j-b₃n-ε) · C((17-b₄)n, j-b₄n-ε)` equals
`λ_{n,b}` times the unpermuted one (`(-1)^n C_n (a_j, b_j)` as a jet), and the integrality
argument of §4 (integer value, derivative cleared by `d_{19n}`; harmonic numbers cleared by
`d_{19n}^s`) applies to it verbatim.
* Proved (≈ 2 lines here, plus ≈ 330 lines in the helper `BaselineProfile_Jets.lean` — the
  bridge `(C_n a_j, C_n b_j) = (-1)^n (U_{n,j}, V_{n,j})` from `aCoef_formula`, `bCoef_formula`
  of `BaselineIntegrality` — and ≈ 400 lines in `BaselineProfile_Perm.lean`: pfq54
  `permutation_lemma.lean` + `Z_integral.lean` and the readout for `Z3v`, `Z4v`).
* Directly from the PDF: partially (§4 proves the unpermuted case; the permutation identity is
  pfq54's). -/
theorem permutation_lemma (σ : Equiv.Perm (Fin 5)) (n : ℕ) (hn : 1 ≤ n) :
    (∀ i, ∃ z : ℤ, lam σ n * Z3v n i = z) ∧ (∀ i, ∃ z : ℤ, lam σ n * Z4v n i = z) :=
  -- `lam` is `Jets.lamJ` (verbatim copy)
  Jets.permutation_lemma σ n hn

/-- **[4] The valuation of `λ_{n,b}` at an eligible prime.** All factorial arguments are
`≤ 19n < p²`, so `v_p(m!) = ⌊m/p⌋` and `v_p(λ_{n,b}) = -rowValPerm σ (n/p)`.
* Proved (≈ 40 lines; pfq54 `padicValRat_lam`, verbatim).
* Directly from the PDF: yes ("Legendre's formula has just its first term", §5). -/
theorem padicValRat_lam (σ : Equiv.Perm (Fin 5)) (n p : ℕ) (hp : Eligible n p) :
    padicValRat p (lam σ n) = -rowValPerm σ ((n : ℚ) / p) := by
  -- provenance: pfq54 `pairing_bound.padicValRat_lam` (and `padicValNat_factorial_small`)
  have : Fact p.Prime := ⟨hp.1⟩
  have hleg : ∀ m : ℕ, m < p ^ 2 → padicValNat p m.factorial = m / p := fun m hm => by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow (by omega) hm
    rw [padicValNat_factorial hlog]
    simp
  have hb : ∀ i, -2 ≤ shift i ∧ shift i ≤ 2 := by intro i; fin_cases i <;> decide
  have hsq : 19 * n < p ^ 2 := lt_of_le_of_lt (by omega) hp.2.2.1
  have key : ∀ e : ℤ, 0 ≤ e → e ≤ 19 →
      padicValRat p (((e * n).toNat.factorial : ℕ) : ℚ) = ⌊(e : ℚ) * ((n : ℚ) / p)⌋ := by
    intro e h0 h1
    have hm : (e * n).toNat ≤ 19 * n := Int.toNat_le.mpr (by push_cast; nlinarith)
    rw [padicValRat.of_nat, hleg _ (lt_of_le_of_lt hm hsq)]
    have hc : (e : ℚ) * ((n : ℚ) / p) = (((e * n).toNat : ℕ) : ℚ) / (p : ℕ) := by
      rw [show (((e * n).toNat : ℕ) : ℚ) = ((e * n : ℤ) : ℚ) by
        exact_mod_cast Int.toNat_of_nonneg (mul_nonneg h0 (Int.natCast_nonneg n))]
      push_cast; ring
    rw [hc, Rat.floor_natCast_div_natCast, Int.natCast_div]
  have k10 := key 10 (by norm_num) (by norm_num)
  have k15 := key 15 (by norm_num) (by norm_num)
  have kA := key (16 - shift (σ 3)) (by linarith [hb (σ 3)]) (by linarith [hb (σ 3)])
  have kB := key (17 - shift (σ 4)) (by linarith [hb (σ 4)]) (by linarith [hb (σ 4)])
  have kC := key (10 + shift (σ 0)) (by linarith [hb (σ 0)]) (by linarith [hb (σ 0)])
  have kD := key (11 + shift (σ 1)) (by linarith [hb (σ 1)]) (by linarith [hb (σ 1)])
  have kE := key (12 + shift (σ 2)) (by linarith [hb (σ 2)]) (by linarith [hb (σ 2)])
  simp only [Int.cast_ofNat] at k10 k15
  unfold lam rowValPerm cfun
  dsimp only
  rw [padicValRat.div (by positivity) (by positivity), padicValRat.mul (by positivity)
    (by positivity), padicValRat.mul (by positivity) (by positivity), padicValRat.pow,
    padicValRat.mul (by positivity) (by positivity), padicValRat.mul (by positivity)
    (by positivity), padicValRat.mul (by positivity) (by positivity), padicValRat.pow,
    k10, k15, kA, kB, kC, kD, kE]
  push_cast
  ring

/-- **[5] `λ_{n,b} ≠ 0`** (a quotient of factorials).
* Proved (≈ 3 lines).
* Directly from the PDF: yes. -/
theorem lam_ne_zero (σ : Equiv.Perm (Fin 5)) (n : ℕ) : lam σ n ≠ 0 := by
  unfold lam
  dsimp only
  positivity

/-- **[6] The carry table is the ten-pairing profile.** For eligible `p`, `ψ({n/p}) = φ₁₀(n/p)`.
`φ₁₀` is `1`-periodic (`∑ L = ∑ D` in every row), its breakpoints and those of `ψ` are Farey
fractions of order `≤ 19`, and `n/p` is off the Farey-29 walls; on each of the 120 open
Farey-19 cells of `(0,1)` both sides are constant and agree.
* Proved (≈ 15 lines here, plus ≈ 270 lines in the helper `BaselineProfile_Cells.lean`: 120
  cells between the 121 Farey-19 breakpoints, midpoint values checked by `decide +kernel`,
  generic transfer, periodicity of `φ₁₀`).
* Directly from the PDF: no (new finding of the handoff; the paper's (G) gives `ψ` through
  (D), (LD), (V) instead). -/
theorem psi_eq_phi10 (n p : ℕ) (hp : Eligible n p) :
    (psi ((n : ℚ) / p) : ℤ) = phi10 ((n : ℚ) / p) := by
  set f := Int.fract ((n : ℚ) / p) with hf_def
  have hpsi : psi f = psi ((n : ℚ) / p) := by simp only [psi, hf_def, Int.fract_fract]
  have hphi : phi10 ((n : ℚ) / p) = Cells.phiC f := Cells.phiC_fract _
  have hf0 : 0 < f := by
    have hne := Cells.fract_not_farey n p hp 0 1 one_pos (by norm_num)
    simp only [Nat.cast_zero, zero_div] at hne
    exact lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hne)
  rw [← hpsi, hphi]
  exact Cells.psi_eq_phiC f hf0 (Int.fract_lt_one _)
    (fun a b hb0 hb => Cells.fract_not_farey n p hp a b hb0 hb)

/-- **[7] `ψ` vanishes below `1/15`.** If `{x} < 1/15` then `ψ(x) = 0`: every row of `psiRows`
starts at `≥ 1/15`, so no indicator fires.
* Proved (≈ 6 lines).
* Directly from the PDF: yes (appendix table, row `(0, 1/15, 0)`). -/
theorem psi_eq_zero_low (x : ℚ) (hx : Int.fract x < 1 / 15) : psi x = 0 := by
  have hlow : ∀ r ∈ psiRows, 1 / 15 ≤ r.1 := by decide +kernel
  unfold psi
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hy
  exact ite_eq_right fun h => absurd (lt_of_le_of_lt (hlow r hr) h.1) (by linarith)

/-- **[8] Upper harmonic range bound.** For eligible `p` with `16n < p < 19n`, every entry of
both integer forms has valuation `≥ h₀(n/p)` (`3, 2, 1` on `(18n,19n), (17n,18n), (16n,17n)`).
`v_p(d_{19n}) = 1`; active indices `j + 2n ≥ p` have `j > 14n`, `a_j` gains `h₀` and `b_j`
gains `h₀ - 1` from the numerator factorials `(j+10n)!, (j+11n)!, (j+12n)!`, which offsets the
harmonic loss `v_p(H^{(r)}_{j+2n}) ≥ -r`; inactive indices have `p`-integral harmonic numbers.
* Proved (≈ 1 line here, plus ≈ 420 lines in the helper `BaselineProfile_Upper.lean`: pfq54
  `upper_range_bound.lean`, `uv_aux.lean`, `jet_aux.lean` through the bridge
  `C_n a_j = (-1)^n U_{n,j}`, `C_n b_j = (-1)^n V_{n,j}`; at inactive `j` (`j + 2n < p`) the
  jets are integral with derivative cleared by `d_{p-1}`, a `p`-unit, so `v_p(C_n b_j) ≥ 0`,
  which the order-three form needs when `h₀ = 3`).
* Directly from the PDF: partially (the paper's (V) table with `l = 1` and the certificate give
  `g₃ = g₄ = h₀` on `(1/19, 1/16)`; the per-term valuations are not written out). -/
theorem upper_range_bound (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (hlo : 16 * n < p)
    (hhi : p < 19 * n) :
    (∀ i, ValGE p (hgain n p : ℤ) (Z3v n i)) ∧ (∀ i, ValGE p (hgain n p : ℤ) (Z4v n i)) :=
  Jets.upper_range n p hn hp hlo hhi

/-! ### The node -/

/-- **Baseline carry profile** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[8] and the blueprint node `baseline_integrality`. -/
theorem baseline_profile (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) :
    (∀ i, ValGE p (psi ((n : ℚ) / p) + hgain n p : ℕ) (Z3v n i)) ∧
      (∀ i, ValGE p (psi ((n : ℚ) / p) + hgain n p : ℕ) (Z4v n i)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  -- valuation transfer: `l ≠ 0`, `l x ∈ ℤ` ⟹ `v_p(x) ≥ -v_p(l)`
  have transfer : ∀ l x : ℚ, l ≠ 0 → (∃ z : ℤ, l * x = z) → ValGE p (-padicValRat p l) x := by
    rintro l x hl ⟨z, hz⟩
    rcases eq_or_ne x 0 with hx | hx
    · exact Or.inl hx
    right
    have h1 : padicValRat p (l * x) = padicValRat p l + padicValRat p x := padicValRat.mul hl hx
    have h2 : 0 ≤ padicValRat p (l * x) := by
      rw [hz, padicValRat.of_int]; exact Nat.cast_nonneg _
    linarith
  have mono : ∀ (a b : ℤ) (x : ℚ), a ≤ b → ValGE p b x → ValGE p a x :=
    fun a b x hab h => h.imp_right fun h => le_trans hab h
  -- the profile `ψ` bounds every integer `x` all of whose `λ`-multiples are integers
  have hpsi : ∀ x : ℚ, (∃ z : ℤ, x = z) → (∀ σ, ∃ z : ℤ, lam σ n * x = z) →
      ValGE p (psi ((n : ℚ) / p) : ℤ) x := by
    intro x ⟨z, hz⟩ hlam
    rw [psi_eq_phi10 n p hp]
    obtain ⟨-, h | ⟨LD, hLD, hrow⟩⟩ := phi10_cases ((n : ℚ) / p)
    · have h0 := transfer 1 x one_ne_zero ⟨z, by rw [one_mul, hz]⟩
      rw [padicValRat.one, neg_zero] at h0
      rwa [h]
    · obtain ⟨σ, hσ⟩ := pairing_realized LD hLD
      refine mono _ _ _ (le_of_eq ?_) (transfer _ x (lam_ne_zero σ n) (hlam σ))
      rw [padicValRat_lam σ n p hp, neg_neg, ← hσ, hrow]
  obtain ⟨-, -, h3, h4, -⟩ := BaselineIntegrality.baseline_integrality n hn
  by_cases hg : hgain n p = 0
  · -- no upper harmonic gain: the pairing bound
    simp only [hg, add_zero]
    exact ⟨fun i => hpsi _ (h3 i) fun σ => (permutation_lemma σ n hn).1 i,
      fun i => hpsi _ (h4 i) fun σ => (permutation_lemma σ n hn).2 i⟩
  · -- `16n < p < 19n`: then `ψ = 0` and the upper range bound applies
    have h16 : 16 * n < p ∧ p < 19 * n := by
      unfold hgain at hg; split_ifs at hg <;> omega
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.1.pos
    have hx0 : 0 ≤ (n : ℚ) / p := by positivity
    have hx16 : (n : ℚ) / p < 1 / 16 := by
      rw [div_lt_iff₀ hp0]
      have : ((16 * n : ℕ) : ℚ) < p := by exact_mod_cast h16.1
      push_cast at this; linarith
    have hfr : Int.fract ((n : ℚ) / p) = (n : ℚ) / p := Int.fract_eq_self.2 ⟨hx0, by linarith⟩
    have hpsi0 : psi ((n : ℚ) / p) = 0 := psi_eq_zero_low _ (by rw [hfr]; linarith)
    simp only [hpsi0, zero_add]
    exact upper_range_bound n p hn hp h16.1 h16.2

end Meijer5255.BaselineProfile
