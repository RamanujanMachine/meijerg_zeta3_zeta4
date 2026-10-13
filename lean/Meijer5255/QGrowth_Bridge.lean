/-
# Bridge between the copied zeta34/pfq54 layer and this repository's readouts

Shared helper of `Meijer5255.QGrowth` and `Meijer5255.LinformError` (new code, not copied).

* `Fn_eq`: pfq54's kernel `PF.Fn n = lin (nR n) (dR n)` is this repository's
  `rootPoly (numRoots n) / rootPoly (denRoots n)`.
* `aF_eq`, `bF_eq`: the Laurent coefficients of `F_n` at `-j` (zeta34's `pfCoeff`, orders 2 and 1)
  are this repository's closed-form coefficients `aCoef n j`, `bCoef n j` (`pfCoeff` of
  `definitions.lean`): at a pole of order `m ≤ 2` the top coefficient is `N(x)/E(x)` and the next
  one is `(N/E)'(x) = (N/E)(x) (∑ 1/(x-z) - ∑ 1/(x-y))` (logarithmic derivative).
* `Lfun_Fn_three`, `Lfun_Fn_zero`, `Mfun_Fn_zero`: the endpoint values `2Q_n`, `-2P_{3,n}`,
  `-6P_{4,n}` (pfq54 `pf_aux`).
* `weighted_L`, `weighted_M`: pfq54's weighted dual readouts (`star_aux`), with the weight
  reduced to the scalar `Del n` (`Lfun_W`, `Mfun_W`).
-/
import Meijer5255.definitions
import Meijer5255.QGrowth_Star
import Meijer5255.QGrowth_growth_estimates

open Polynomial Finset
open scoped RatFunc

noncomputable section

namespace Meijer5255.QGA.Bridge

open Meijer5255.QGA.ZetasIrr.CMF (lp lin lp_eval_ne_zero)
open Meijer5255.QGA.Pfq54.PF (Fn aF bF Lsq)
open Meijer5255.QGA.Pfq54.RA (nR dR)

/-- zeta34's `lp` is this repository's `rootPoly` (the latter coerces the multiset to `ℚ` first). -/
theorem lp_eq_rootPoly (S : Multiset ℤ) : lp S = rootPoly S := by
  rw [Meijer5255.QGA.ZetasIrr.CMF.lp_eq_map, rootPoly]
  congr 2
  show _ = Multiset.bind S fun a => {(a : ℚ)}
  rw [Multiset.bind_singleton]

theorem nR_eq (n : ℕ) : nR n = numRoots n := rfl

theorem dR_eq (n : ℕ) : dR n = denRoots n := rfl

/-- pfq54's kernel is this repository's `F_n`. -/
theorem Fn_eq (n : ℕ) :
    Fn n = algebraMap ℚ[X] ℚ⟮X⟯ (rootPoly (numRoots n)) /
      algebraMap ℚ[X] ℚ⟮X⟯ (rootPoly (denRoots n)) := by
  rw [Fn, lin, lp_eq_rootPoly, lp_eq_rootPoly, nR_eq, dR_eq]

/-- The generic identification of the two partial-fraction conventions at a pole `h ∉ Z` of
order `≤ 2`. -/
theorem pfCoeff_lin_two (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) (hP : P.count h ≤ 2) :
    ZetasIrr.pfCoeff (lin Z P) (h : ℚ) 2 = (pfCoeff Z P h).1 := by
  unfold pfCoeff
  simp only
  split_ifs with h2 h1
  · have := Pfq54.PF.pfCoeff_lin_top Z P h hZ
    rw [h2] at this
    rw [this, lp_eq_rootPoly, lp_eq_rootPoly]
  · exact Pfq54.PF.pfCoeff_lin_gt Z P h hZ 2 (by omega)
  · exact Pfq54.PF.pfCoeff_lin_gt Z P h hZ 2 (by omega)

theorem pfCoeff_lin_one (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) (hP : P.count h ≤ 2) :
    ZetasIrr.pfCoeff (lin Z P) (h : ℚ) 1 = (pfCoeff Z P h).2 := by
  unfold pfCoeff
  simp only
  split_ifs with h2 h1
  · have := Pfq54.PF.pfCoeff_lin_sub Z P h hZ (by omega)
    rw [h2] at this
    rw [this]
    have hE : ∀ z ∈ P.filter (· ≠ h), (z : ℚ) ≠ (h : ℚ) := fun z hz e =>
      (Multiset.mem_filter.mp hz).2 (by exact_mod_cast e)
    have hZ' : ∀ z ∈ Z, (z : ℚ) ≠ (h : ℚ) := fun z hz e => hZ (by
      rw [show h = z by exact_mod_cast e.symm]; exact hz)
    have hE0 : (lp (P.filter (· ≠ h))).eval (h : ℚ) ≠ 0 := lp_eval_ne_zero _ _ hE
    rw [eval_sub, eval_mul, eval_mul, ← lp_eq_rootPoly, ← lp_eq_rootPoly,
      Pfq54.PF.deriv_lp_eval Z _ hZ', Pfq54.PF.deriv_lp_eval _ _ hE]
    field_simp
  · have := Pfq54.PF.pfCoeff_lin_top Z P h hZ
    rw [h1] at this
    rw [this, lp_eq_rootPoly, lp_eq_rootPoly]
  · exact Pfq54.PF.pfCoeff_lin_gt Z P h hZ 1 (by omega)

theorem neg_cast (j : ℕ) : (-(j : ℚ)) = ((-(j : ℤ) : ℤ) : ℚ) := by push_cast; ring

theorem dR_count_le (n j : ℕ) : (dR n).count (-(j : ℤ)) ≤ 2 := Pfq54.PF.dR_count_le n _

/-- The double-pole Laurent coefficient of `F_n` at `-j` is `aCoef n j`. -/
theorem aF_eq (n j : ℕ) : aF n j = aCoef n j := by
  rw [aF, neg_cast]
  exact pfCoeff_lin_two _ _ _ (Pfq54.PF.neg_not_mem_nR n j) (dR_count_le n j)

/-- The simple-pole Laurent coefficient of `F_n` at `-j` is `bCoef n j`. -/
theorem bF_eq (n j : ℕ) : bF n j = bCoef n j := by
  rw [bF, neg_cast]
  exact pfCoeff_lin_one _ _ _ (Pfq54.PF.neg_not_mem_nR n j) (dR_count_le n j)

theorem count_zero_of_lt (n j : ℕ) (hj : j < n) : (dR n).count (-(j : ℤ)) = 0 := by
  rw [Pfq54.PF.dR_count]
  split_ifs <;> omega

theorem aF_eq_zero (n j : ℕ) (hj : j < n) : aF n j = 0 := by
  rw [aF, neg_cast]
  exact Pfq54.PF.pfCoeff_lin_gt _ _ _ (Pfq54.PF.neg_not_mem_nR n j) 2
    (by rw [count_zero_of_lt n j hj]; omega)

theorem bF_eq_zero (n j : ℕ) (hj : j < n) : bF n j = 0 := by
  rw [bF, neg_cast]
  exact Pfq54.PF.pfCoeff_lin_gt _ _ _ (Pfq54.PF.neg_not_mem_nR n j) 1
    (by rw [count_zero_of_lt n j hj]; omega)

/-- A sum over `range (17n+1)` whose terms vanish for `j < n` is a sum over `Icc n (17n)`. -/
theorem sum_range_eq_Icc (n : ℕ) (f : ℕ → ℚ) (hf : ∀ j, j < n → f j = 0) :
    ∑ j ∈ range (17 * n + 1), f j = ∑ j ∈ Icc n (17 * n), f j := by
  symm
  refine Finset.sum_subset (fun j hj => ?_) (fun j hj hj' => hf j ?_)
  · simp only [Finset.mem_Icc] at hj
    exact Finset.mem_range.mpr (by omega)
  · simp only [Finset.mem_range, Finset.mem_Icc, not_and, not_le] at hj hj'
    by_contra h
    exact absurd (hj' (by omega)) (by omega)

theorem harm_eq (r m : ℕ) : Pfq54.harm r m = Meijer5255.harm r m := rfl

/-- `[Z₃] 𝓛_{2n}[F_n] = 2Q_n`. -/
theorem Lfun_Fn_three (n : ℕ) : ZetasIrr.Lfun (2 * n) (Fn n) 3 = 2 * Q n := by
  rw [Pfq54.PF.Lfun_Fn_three, sum_range_eq_Icc n _ (fun j hj => aF_eq_zero n j hj), Q]
  simp only [aF_eq]

/-- `[Z₀] 𝓛_{2n}[F_n] = -2P_{3,n}`. -/
theorem Lfun_Fn_zero (n : ℕ) : ZetasIrr.Lfun (2 * n) (Fn n) 0 = -2 * P3 n := by
  rw [Pfq54.PF.Lfun_Fn_zero, sum_range_eq_Icc n _ (fun j hj => by
    rw [aF_eq_zero n j hj, bF_eq_zero n j hj]; ring), P3]
  simp only [aF_eq, bF_eq, harm_eq]

/-- `[Z₀] 𝓜_{2n}[F_n] = -6P_{4,n}`. -/
theorem Mfun_Fn_zero (n : ℕ) : ZetasIrr.Mfun (2 * n) (Fn n) 0 = -6 * P4 n := by
  rw [Pfq54.PF.Mfun_Fn_zero, sum_range_eq_Icc n _ (fun j hj => by
    rw [aF_eq_zero n j hj, bF_eq_zero n j hj]; ring), P4]
  simp only [aF_eq, bF_eq, harm_eq]

/-- pfq54 `star_aux.weighted_L` combined with `Lfun_W`. -/
theorem weighted_L (n : ℕ) :
    ∑ j : Fin 3, Pfq54.ST.hv n j • (ZetasIrr.q n j • ZetasIrr.Zsym 3 -
        ZetasIrr.p3 n j • ZetasIrr.Zsym 0) =
      ((-1 : ℚ) ^ n * 3 * Pfq54.ST.Del n) • ZetasIrr.Lfun (2 * n) (Fn n) := by
  rw [Pfq54.ST.weighted_L, Pfq54.ST.Lfun_W, smul_smul]

/-- pfq54 `star_aux.weighted_M` combined with `Mfun_W`. -/
theorem weighted_M (n : ℕ) :
    ∑ j : Fin 3, Pfq54.ST.hv n j • (ZetasIrr.q n j • ZetasIrr.Zsym 4 -
        ZetasIrr.p4 n j • ZetasIrr.Zsym 0) =
      ((-1 : ℚ) ^ n * Pfq54.ST.Del n) • ZetasIrr.Mfun (2 * n) (Fn n) := by
  rw [Pfq54.ST.weighted_M, Pfq54.ST.Mfun_W, smul_smul]

/-- Polynomial factors are subexponential: `(10n+1)² ≤ e^{εn}` for all large `n`
(from `x³/3! ≤ eˣ`). -/
theorem poly_absorb (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, (10 * (n : ℝ) + 1) ^ 2 ≤ Real.exp (ε * n) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (726 / ε ^ 3)
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hnN : 726 / ε ^ 3 < n := lt_of_lt_of_le hN (by exact_mod_cast le_of_max_le_left hn)
  have hε3 : 0 < ε ^ 3 := by positivity
  have h726 : 726 ≤ ε ^ 3 * n := by
    rw [div_lt_iff₀ hε3] at hnN; linarith
  have he := Real.pow_div_factorial_le_exp (ε * n) (by positivity) 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6, mul_pow] at he
  have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have key : 726 * (n : ℝ) ^ 2 ≤ ε ^ 3 * n ^ 3 := by
    have := mul_le_mul_of_nonneg_right h726 hsq
    nlinarith
  nlinarith

end Meijer5255.QGA.Bridge
