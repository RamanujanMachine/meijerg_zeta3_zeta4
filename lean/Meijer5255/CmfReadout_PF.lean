/-
# Partial fractions of `F_n` and its two endpoint moments (for `Meijer5255.CmfReadout`)

`FL n = lin (numRoots n) (denRoots n)` is the kernel `F_n` of `definitions.lean`. We identify its
Laurent coefficients at the poles `-j` with the coefficients `aCoef n j`, `bCoef n j` of
`definitions.lean`, show `∑ⱼ bCoef n j = 0` (`F_n = O(t⁻²)`), and compute the coordinates of the
zeta34 functionals `𝓛_{2n}[F_n]`, `𝓜_{2n}[F_n]`:
`𝓛 = 2Q_n Z₃ + 0·Z₂ - 2P_{3,n}`, `𝓜 = 6Q_n Z₄ + 0·Z₃ - 6P_{4,n}`.

Provenance: adapted from `../zetas_irr/pfq54_formalization_handoff/pf_aux.lean` (the generic
Laurent-coefficient lemmas `pfCoeff_lin_*`, `deriv_lp_eval`, `Lfun_Fn_*`, `Mfun_Fn_*`,
`rfDeriv_*`) and `residue_aux4.lean` (`count_Icc`, `card_nR`, `card_dR`). The pfq54 coefficients
`aC`, `bC` (closed factorial formulas) are replaced by the direct values `aCoef`, `bCoef`, and the
`Z₂`/`Z₃` coordinates (`∑ bⱼ = 0`, via zeta34 `residue_sum_eq_zero`) are new.
-/
import Meijer5255.definitions
import Meijer5255.QGrowth_CMF_basic

open Polynomial Finset
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace Meijer5255.CmfReadout

open Meijer5255
open Meijer5255.QGA.ZetasIrr (Lfun Mfun Zsym rfDeriv FormalZ ppSum DegLE exists_eq_ppSum pfCoeff_ppSum
  residue_sum_eq_zero polyPart_eq_zero_of_proper X_sub_C_pow_eq_algebraMap DegLE.ppSum)
open Meijer5255.QGA.ZetasIrr.CMF (lin lp lp_ne_zero lp_eval lp_eval_ne_zero lp_cons lp_zero lin_laurent
  lin_roots_le lin_split lin_denom_dvd lp_eq_map lp_roots)

/-! ### Generic Laurent coefficients of `lin Z P` (pfq54 `pf_aux.lean`) -/

/-- `∑_{z ∈ S} 1/(x - z)`. -/
def Lsq (S : Multiset ℤ) (x : ℚ) : ℚ := (S.map fun z : ℤ => 1 / (x - (z : ℚ))).sum

theorem Lsq_cons (z : ℤ) (S : Multiset ℤ) (x : ℚ) :
    Lsq (z ::ₘ S) x = 1 / (x - z) + Lsq S x := by
  simp only [Lsq, Multiset.map_cons, Multiset.sum_cons]

theorem lp_eval_ne_zero' (S : Multiset ℤ) (h : ℤ) (hS : h ∉ S) : (lp S).eval (h : ℚ) ≠ 0 :=
  lp_eval_ne_zero S h fun z hz e => hS (by rw [show h = z by exact_mod_cast e.symm]; exact hz)

theorem deriv_lp_eval (S : Multiset ℤ) (x : ℚ) (hS : ∀ z ∈ S, (z : ℚ) ≠ x) :
    (derivative (lp S)).eval x = (lp S).eval x * Lsq S x := by
  induction S using Multiset.induction_on with
  | empty => simp [lp_zero, Lsq]
  | cons z S ih =>
    have hz : (z : ℚ) ≠ x := hS z (Multiset.mem_cons_self z S)
    have hx : x - z ≠ 0 := sub_ne_zero.mpr hz.symm
    rw [lp_cons, Lsq_cons]
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, one_mul]
    rw [ih fun w hw => hS w (Multiset.mem_cons_of_mem hw)]
    field_simp
    try ring

theorem lp_coeff_zero (S : Multiset ℤ) : (lp S).coeff 0 = (lp S).eval 0 :=
  Polynomial.coeff_zero_eq_eval_zero _

theorem lp_coeff_one (S : Multiset ℤ) (hS : ∀ z ∈ S, (z : ℚ) ≠ 0) :
    (lp S).coeff 1 = (lp S).eval 0 * Lsq S 0 := by
  rw [← deriv_lp_eval S 0 hS, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp

theorem lp_constantCoeff_ne_zero (P : Multiset ℤ) (hP : (0 : ℤ) ∉ P) :
    PowerSeries.constantCoeff (lp P : PowerSeries ℚ) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, lp_coeff_zero]
  exact_mod_cast lp_eval_ne_zero' P 0 hP

/-- The Laurent coefficients of `lin Z (0^m + P)` at `0` when `0 ∉ Z`, `0 ∉ P`. -/
theorem pfCoeff_lin_zero (Z P : Multiset ℤ) (m : ℕ) (_hZ : (0 : ℤ) ∉ Z) (hP : (0 : ℤ) ∉ P)
    (r : ℕ) :
    QGA.ZetasIrr.pfCoeff (lin Z (Multiset.replicate m 0 + P)) 0 r =
      if r ≤ m then PowerSeries.coeff (m - r)
        ((lp Z : PowerSeries ℚ) * (lp P : PowerSeries ℚ)⁻¹) else 0 := by
  have hPc := lp_constantCoeff_ne_zero P hP
  have hcoe : algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (RatFunc.laurent 0 (lin Z (Multiset.replicate m 0 + P))) =
      HahnSeries.single (-(m : ℤ)) 1 *
        (((lp Z : PowerSeries ℚ) * (lp P : PowerSeries ℚ)⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
    rw [RatFunc.laurent_at_zero, lin, QGA.ZetasIrr.CMF.lp_add, QGA.ZetasIrr.CMF.lp_replicate, Int.cast_zero,
      map_zero, sub_zero, map_mul, map_div₀, map_mul, QGA.ZetasIrr.Aux.coe_algebraMap_poly,
      QGA.ZetasIrr.Aux.coe_algebraMap_poly, QGA.ZetasIrr.Aux.coe_algebraMap_poly, Polynomial.coe_pow,
      Polynomial.coe_X, PowerSeries.coe_pow, PowerSeries.coe_X, PowerSeries.coe_mul]
    have hinv : ((lp P : PowerSeries ℚ) : ℚ⸨X⸩)⁻¹ =
        (((lp P : PowerSeries ℚ)⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel _ hPc, PowerSeries.coe_one]
    rw [div_eq_mul_inv, mul_inv, hinv, HahnSeries.single_pow, one_pow, HahnSeries.inv_single]
    simp only [nsmul_eq_mul, mul_one, inv_one]
    ring
  unfold QGA.ZetasIrr.pfCoeff
  rw [hcoe, show -(r : ℤ) = ((m : ℤ) - r) + -(m : ℤ) by ring, HahnSeries.coeff_single_mul_add,
    one_mul, PowerSeries.coeff_coe]
  split_ifs with h1 h2 h2
  · exact absurd h1 (by omega)
  · rfl
  · rw [← Nat.cast_sub h2, Int.natAbs_natCast]
  · exact absurd (by omega) h2

theorem coeff_zero_mul_inv (A B : PowerSeries ℚ) :
    PowerSeries.coeff 0 (A * B⁻¹) = PowerSeries.coeff 0 A / PowerSeries.coeff 0 B := by
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_inv,
    div_eq_mul_inv]

theorem coeff_one_inv (B : PowerSeries ℚ) :
    PowerSeries.coeff 1 B⁻¹ = -(PowerSeries.coeff 1 B / PowerSeries.coeff 0 B ^ 2) := by
  rw [PowerSeries.coeff_inv]
  simp only [one_ne_zero, ↓reduceIte, Finset.Nat.sum_antidiagonal_succ,
    Finset.Nat.antidiagonal_zero, Finset.sum_singleton, lt_self_iff_false, zero_add, zero_lt_one,
    PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv]
  try ring

theorem coeff_one_mul_inv (A B : PowerSeries ℚ) :
    PowerSeries.coeff 1 (A * B⁻¹) =
      PowerSeries.coeff 0 A * (-(PowerSeries.coeff 1 B / PowerSeries.coeff 0 B ^ 2)) +
        PowerSeries.coeff 1 A / PowerSeries.coeff 0 B := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
    Finset.sum_singleton, coeff_one_inv]
  try simp only [zero_add, PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv,
    div_eq_mul_inv]

theorem pfCoeff_lin_zero_top (Z P : Multiset ℤ) (m : ℕ) (hZ : (0 : ℤ) ∉ Z) (hP : (0 : ℤ) ∉ P) :
    QGA.ZetasIrr.pfCoeff (lin Z (Multiset.replicate m 0 + P)) 0 m = (lp Z).eval 0 / (lp P).eval 0 := by
  rw [pfCoeff_lin_zero Z P m hZ hP m, ite_eq_left le_rfl, Nat.sub_self, coeff_zero_mul_inv,
    Polynomial.coeff_coe, Polynomial.coeff_coe, lp_coeff_zero, lp_coeff_zero]

theorem pfCoeff_lin_zero_sub (Z P : Multiset ℤ) (m : ℕ) (hm : 1 ≤ m) (hZ : (0 : ℤ) ∉ Z)
    (hP : (0 : ℤ) ∉ P) :
    QGA.ZetasIrr.pfCoeff (lin Z (Multiset.replicate m 0 + P)) 0 (m - 1) =
      (lp Z).eval 0 / (lp P).eval 0 * (Lsq Z 0 - Lsq P 0) := by
  have hZ0 : (lp Z).eval (0 : ℚ) ≠ 0 := by exact_mod_cast lp_eval_ne_zero' Z 0 hZ
  have hP0 : (lp P).eval (0 : ℚ) ≠ 0 := by exact_mod_cast lp_eval_ne_zero' P 0 hP
  have hZ' : ∀ z ∈ Z, (z : ℚ) ≠ 0 := fun z hz e =>
    hZ (by rw [show (0 : ℤ) = z by exact_mod_cast e.symm]; exact hz)
  have hP' : ∀ z ∈ P, (z : ℚ) ≠ 0 := fun z hz e =>
    hP (by rw [show (0 : ℤ) = z by exact_mod_cast e.symm]; exact hz)
  rw [pfCoeff_lin_zero Z P m hZ hP (m - 1), ite_eq_left (Nat.sub_le m 1),
    show m - (m - 1) = 1 by omega, coeff_one_mul_inv, Polynomial.coeff_coe,
    Polynomial.coeff_coe, Polynomial.coeff_coe, Polynomial.coeff_coe, lp_coeff_zero, lp_coeff_zero,
    lp_coeff_one Z hZ', lp_coeff_one P hP']
  field_simp
  try ring

theorem lp_eval_map_sub (S : Multiset ℤ) (h : ℤ) :
    (lp (S.map (· - h))).eval (0 : ℚ) = (lp S).eval (h : ℚ) := by
  rw [lp_eval, lp_eval, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Int.cast_sub]
  ring

theorem Lsq_map_sub (S : Multiset ℤ) (h : ℤ) : Lsq (S.map (· - h)) 0 = Lsq S h := by
  unfold Lsq
  rw [Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun z _ => ?_
  simp only [Function.comp_apply, Int.cast_sub]
  ring

theorem map_sub_eq (P : Multiset ℤ) (h : ℤ) :
    P.map (· - h) = Multiset.replicate (P.count h) 0 + (P.filter (· ≠ h)).map (· - h) := by
  conv_lhs => rw [← Multiset.filter_add_not (fun a => a = h) P]
  rw [Multiset.filter_eq', Multiset.map_add, Multiset.map_replicate, sub_self]

theorem not_mem_map_sub (S : Multiset ℤ) (h : ℤ) (hS : h ∉ S) : (0 : ℤ) ∉ S.map (· - h) := by
  intro h0
  obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0
  exact hS (by rw [show h = z by omega]; exact hz)

theorem not_mem_filter_map (P : Multiset ℤ) (h : ℤ) :
    (0 : ℤ) ∉ (P.filter (· ≠ h)).map (· - h) := by
  intro h0
  obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.mp h0
  exact (Multiset.mem_filter.mp hz).2 (by omega)

theorem pfCoeff_shift (f : ℚ⟮X⟯) (h : ℤ) (r : ℕ) :
    QGA.ZetasIrr.pfCoeff f (h : ℚ) r = QGA.ZetasIrr.pfCoeff (RatFunc.laurent (h : ℚ) f) 0 r := by
  rw [QGA.ZetasIrr.Aux.pfCoeff_laurent, zero_add]

theorem pfCoeff_lin_gt (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) (r : ℕ) (hr : P.count h < r) :
    QGA.ZetasIrr.pfCoeff (lin Z P) h r = 0 := by
  rw [pfCoeff_shift, lin_laurent, map_sub_eq P h,
    pfCoeff_lin_zero _ _ _ (not_mem_map_sub Z h hZ) (not_mem_filter_map P h),
    ite_eq_right (by omega)]

theorem pfCoeff_lin_top (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) :
    QGA.ZetasIrr.pfCoeff (lin Z P) h (P.count h) =
      (lp Z).eval (h : ℚ) / (lp (P.filter (· ≠ h))).eval (h : ℚ) := by
  rw [pfCoeff_shift, lin_laurent, map_sub_eq P h,
    pfCoeff_lin_zero_top _ _ _ (not_mem_map_sub Z h hZ) (not_mem_filter_map P h),
    lp_eval_map_sub, lp_eval_map_sub]

theorem pfCoeff_lin_sub (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) (hm : 1 ≤ P.count h) :
    QGA.ZetasIrr.pfCoeff (lin Z P) h (P.count h - 1) =
      (lp Z).eval (h : ℚ) / (lp (P.filter (· ≠ h))).eval (h : ℚ) *
        (Lsq Z h - Lsq (P.filter (· ≠ h)) h) := by
  rw [pfCoeff_shift, lin_laurent, map_sub_eq P h,
    pfCoeff_lin_zero_sub _ _ _ hm (not_mem_map_sub Z h hZ) (not_mem_filter_map P h),
    lp_eval_map_sub, lp_eval_map_sub, Lsq_map_sub, Lsq_map_sub]

/-! ### The kernel `F_n` -/

/-- `rootPoly` (whose `Multiset.map` elaborates through a coercion `ℤ → ℚ`) is the zeta34 `lp`. -/
theorem rootPoly_eq_lp (s : Multiset ℤ) : rootPoly s = lp s := by
  simp [rootPoly, QGA.ZetasIrr.CMF.lp]

/-- `F_n` as `lin` (it is `Fn n` of `CmfReadout.lean`, see `rootPoly_eq_lp`). -/
def FL (n : ℕ) : ℚ⟮X⟯ := lin (numRoots n) (denRoots n)

theorem count_Icc (a b t : ℤ) : (Icc a b).val.count t = if a ≤ t ∧ t ≤ b then 1 else 0 := by
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [ite_eq_left h]
    exact Multiset.count_eq_one_of_mem (Finset.nodup _) (Finset.mem_val.mpr (mem_Icc.mpr h))
  · rw [ite_eq_right h]
    exact Multiset.count_eq_zero.mpr fun hm => h (mem_Icc.mp (Finset.mem_val.mp hm))

theorem card_numRoots (n : ℕ) : Multiset.card (numRoots n) = 30 * n := by
  rw [numRoots, Multiset.card_add, Multiset.card_add, Finset.card_val, Finset.card_val,
    Finset.card_val, Int.card_Icc, Int.card_Icc, Int.card_Icc]
  omega

theorem card_denRoots (n : ℕ) : Multiset.card (denRoots n) = 30 * n + 2 := by
  rw [denRoots, Multiset.card_add, Finset.card_val, Finset.card_val, Int.card_Icc, Int.card_Icc]
  omega

theorem numRoots_pos (n : ℕ) (z : ℤ) (hz : z ∈ numRoots n) : 1 ≤ z := by
  simp only [numRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hz
  omega

theorem neg_not_mem_numRoots (n j : ℕ) : -(j : ℤ) ∉ numRoots n := fun h => by
  have := numRoots_pos n _ h
  omega

theorem denRoots_count (n j : ℕ) : (denRoots n).count (-(j : ℤ)) =
    (if n ≤ j ∧ j ≤ 17 * n then 1 else 0) + (if 2 * n ≤ j ∧ j ≤ 16 * n then 1 else 0) := by
  rw [denRoots, Multiset.count_add, count_Icc, count_Icc]
  split_ifs <;> omega

theorem neg_cast (j : ℕ) : (-(j : ℚ)) = ((-(j : ℤ) : ℤ) : ℚ) := by push_cast; ring

theorem pfCoeff_FL_gt (n j r : ℕ) (hr : 3 ≤ r) : QGA.ZetasIrr.pfCoeff (FL n) (-(j : ℚ)) r = 0 := by
  rw [neg_cast]
  apply pfCoeff_lin_gt _ _ _ (neg_not_mem_numRoots n j)
  rw [denRoots_count]
  split_ifs <;> omega

theorem pfCoeff_FL_two (n j : ℕ) : QGA.ZetasIrr.pfCoeff (FL n) (-(j : ℚ)) 2 = aCoef n j := by
  rw [neg_cast]
  have hc := denRoots_count n j
  by_cases h1 : 2 * n ≤ j ∧ j ≤ 16 * n
  · have h2 : (denRoots n).count (-(j : ℤ)) = 2 := by rw [hc]; split_ifs <;> omega
    have := pfCoeff_lin_top (numRoots n) (denRoots n) (-(j : ℤ)) (neg_not_mem_numRoots n j)
    rw [h2] at this
    rw [FL, this, aCoef, pfCoeff, if_pos h2]
    simp only [rootPoly_eq_lp]
  · have h2 : (denRoots n).count (-(j : ℤ)) < 2 := by rw [hc]; split_ifs <;> omega
    rw [FL, pfCoeff_lin_gt _ _ _ (neg_not_mem_numRoots n j) 2 h2, aCoef, pfCoeff,
      if_neg (by omega)]
    split_ifs <;> rfl

theorem pfCoeff_FL_one (n j : ℕ) : QGA.ZetasIrr.pfCoeff (FL n) (-(j : ℚ)) 1 = bCoef n j := by
  rw [neg_cast]
  have hc := denRoots_count n j
  have hN := neg_not_mem_numRoots n j
  by_cases h1 : 2 * n ≤ j ∧ j ≤ 16 * n
  · have h2 : (denRoots n).count (-(j : ℤ)) = 2 := by rw [hc]; split_ifs <;> omega
    have := pfCoeff_lin_sub (numRoots n) (denRoots n) (-(j : ℤ)) hN (by omega)
    rw [h2] at this
    rw [FL, this, bCoef, pfCoeff, if_pos h2]
    simp only
    simp only [rootPoly_eq_lp]
    have hE : (lp ((denRoots n).filter (· ≠ -(j : ℤ)))).eval ((-(j : ℤ) : ℤ) : ℚ) ≠ 0 :=
      lp_eval_ne_zero' _ _ fun h => (Multiset.mem_filter.mp h).2 rfl
    have hdN := deriv_lp_eval (numRoots n) ((-(j : ℤ) : ℤ) : ℚ) fun z hz e =>
      hN (by rw [show -(j : ℤ) = z by exact_mod_cast e.symm]; exact hz)
    have hdE := deriv_lp_eval ((denRoots n).filter (· ≠ -(j : ℤ))) ((-(j : ℤ) : ℤ) : ℚ)
      fun z hz e => (Multiset.mem_filter.mp hz).2 (by exact_mod_cast e)
    rw [eval_sub, eval_mul, eval_mul, hdN, hdE]
    field_simp
  · by_cases h3 : (denRoots n).count (-(j : ℤ)) = 1
    · have := pfCoeff_lin_top (numRoots n) (denRoots n) (-(j : ℤ)) hN
      rw [h3] at this
      rw [FL, this, bCoef, pfCoeff, if_neg (by omega), if_pos h3]
      simp only [rootPoly_eq_lp]
    · have h2 : (denRoots n).count (-(j : ℤ)) < 1 := by rw [hc] at h3 ⊢; split_ifs at h3 ⊢ <;> omega
      rw [FL, pfCoeff_lin_gt _ _ _ hN 1 h2, bCoef, pfCoeff, if_neg (by omega), if_neg h3]

theorem lp_natDegree (S : Multiset ℤ) : (lp S).natDegree = Multiset.card S := by
  rw [lp_eq_map, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

theorem FL_denom_natDegree_le (n : ℕ) : (FL n).denom.natDegree ≤ 30 * n + 2 :=
  (Polynomial.natDegree_le_of_dvd (lin_denom_dvd _ _) (lp_ne_zero _)).trans
    (by rw [lp_natDegree, card_denRoots])

theorem FL_intDegree (n : ℕ) : (FL n).intDegree = -2 := by
  unfold FL lin
  rw [RatFunc.intDegree_div (QGA.ZetasIrr.Aux.algebraMap_ne_zero' (lp_ne_zero _))
    (QGA.ZetasIrr.Aux.algebraMap_ne_zero' (lp_ne_zero _)), RatFunc.intDegree_polynomial,
    RatFunc.intDegree_polynomial, lp_natDegree, lp_natDegree, card_numRoots, card_denRoots]
  push_cast
  ring

theorem FL_proper (n : ℕ) : (FL n).num.natDegree < (FL n).denom.natDegree := by
  have h := FL_intDegree n
  unfold RatFunc.intDegree at h
  omega

theorem FL_polyPart (n : ℕ) : QGA.ZetasIrr.polyPart (FL n) = 0 :=
  polyPart_eq_zero_of_proper _ (FL_proper n)

/-- The candidate poles `-j`, `0 ≤ j ≤ 17n`. -/
def Tn (n : ℕ) : Finset ℚ := (range (17 * n + 1)).image fun j : ℕ => -(j : ℚ)

theorem FL_roots_subset (n : ℕ) : (FL n).denom.roots.toFinset ⊆ Tn n := by
  intro h hh
  have hmem := Multiset.mem_of_le (lin_roots_le _ _) (Multiset.mem_toFinset.mp hh)
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hmem
  simp only [denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hp
  refine Finset.mem_image.mpr ⟨(-p).toNat, Finset.mem_range.mpr (by omega), ?_⟩
  have e : (((-p).toNat : ℕ) : ℤ) = -p := Int.toNat_of_nonneg (by omega)
  rw [← Int.cast_natCast (R := ℚ), e, Int.cast_neg, neg_neg]

theorem Tn_inj (n : ℕ) : ∀ a ∈ range (17 * n + 1), ∀ b ∈ range (17 * n + 1),
    (fun j : ℕ => -(j : ℚ)) a = (fun j : ℕ => -(j : ℚ)) b → a = b :=
  fun a _ b _ h => by exact_mod_cast neg_injective h

theorem mem_Tn (n j : ℕ) (hj : j < 17 * n + 1) : -(j : ℚ) ∈ Tn n :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

theorem Lfun_FL_eq (n : ℕ) : Lfun (2 * n) (FL n) = ∑ h ∈ Tn n, ∑ r ∈ range (30 * n + 3),
    ((r : ℚ) * QGA.ZetasIrr.pfCoeff (FL n) h r) •
      (Zsym (r + 1) - QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - h⌋ • Zsym 0) := by
  rw [QGA.ZetasIrr.Aux.Lfun_eq_general (2 * n) (FL n) (Tn n) (FL_roots_subset n) (30 * n + 2)
    (FL_denom_natDegree_le n), FL_polyPart]
  simp only [QGA.ZetasIrr.Aux.bsum, Polynomial.sum_zero_index, zero_smul, zero_add]

theorem term_apply (c H : ℚ) (r k : ℕ) :
    ((c • (Zsym (r + 1) - H • Zsym 0)) : FormalZ) k =
      c * ((if r + 1 = k then 1 else 0) - H * (if k = 0 then 1 else 0)) := by
  simp only [Finsupp.smul_apply, Finsupp.sub_apply, Zsym, Finsupp.single_apply, smul_eq_mul,
    eq_comm (a := (0 : ℕ))]

theorem floor_eq (n j : ℕ) : ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ = ((j + 2 * n : ℕ) : ℤ) := by
  rw [show ((2 * n : ℤ) : ℚ) - (-(j : ℚ)) = ((j + 2 * n : ℕ) : ℚ) by push_cast; ring,
    Int.floor_natCast]

theorem harm_eq (r m : ℕ) : QGA.ZetasIrr.harm r ((m : ℕ) : ℤ) = harm r m := by
  unfold QGA.ZetasIrr.harm harm
  rw [Int.toNat_natCast]

theorem sum_range_three (f : ℕ → ℚ) (M : ℕ) (hM : 3 ≤ M) (hf : ∀ r, 3 ≤ r → f r = 0) :
    ∑ r ∈ range M, f r = f 0 + f 1 + f 2 := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hM) (fun r _ hr => hf r (by
    simp only [Finset.mem_range, not_lt] at hr; omega))]
  simp [Finset.sum_range_succ]

theorem inner_FL (n j k : ℕ) :
    (∑ r ∈ range (30 * n + 3), ((r : ℚ) * QGA.ZetasIrr.pfCoeff (FL n) (-(j : ℚ)) r) •
      (Zsym (r + 1) - QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ • Zsym 0)) k =
      bCoef n j * ((if 2 = k then 1 else 0) - harm 2 (j + 2 * n) * (if k = 0 then 1 else 0)) +
        2 * aCoef n j *
          ((if 3 = k then 1 else 0) - harm 3 (j + 2 * n) * (if k = 0 then 1 else 0)) := by
  rw [Finsupp.finsetSum_apply]
  simp only [term_apply, floor_eq, harm_eq]
  rw [sum_range_three _ _ (by omega) (fun r hr => by
    rw [pfCoeff_FL_gt n j r hr]; ring)]
  simp only [pfCoeff_FL_two, pfCoeff_FL_one]
  push_cast
  ring

/-- `∑ⱼ bⱼ = 0`: the residues of `F_n = O(t⁻²)` sum to zero. -/
def cF (n : ℕ) : ℚ → ℕ → ℚ := fun h r => QGA.ZetasIrr.pfCoeff (FL n) h r

theorem denRoots_count_le (n : ℕ) (p : ℤ) : (denRoots n).count p ≤ 2 := by
  rw [denRoots, Multiset.count_add, count_Icc, count_Icc]
  split_ifs <;> omega

theorem FL_count_le (n : ℕ) (h : ℚ) : (FL n).denom.roots.count h ≤ 2 := by
  refine (Multiset.count_le_of_le h (lin_roots_le _ _)).trans ?_
  by_cases hh : ∃ p : ℤ, (p : ℚ) = h
  · obtain ⟨p, rfl⟩ := hh
    rw [Multiset.count_map_eq_count' _ _ Int.cast_injective]
    exact denRoots_count_le n p
  · rw [Multiset.count_eq_zero.mpr]
    · omega
    · intro hm
      obtain ⟨p, _, hp⟩ := Multiset.mem_map.mp hm
      exact hh ⟨p, hp⟩

theorem FL_eq_ppSum (n : ℕ) : FL n = ppSum (Tn n) (fun _ => 2) (cF n) := by
  obtain ⟨c, hc⟩ := exists_eq_ppSum (FL n) (FL_proper n) (lin_split _ _)
  set R := (FL n).denom.roots.toFinset with hR
  set b : ℚ → ℕ := fun h => (FL n).denom.roots.count h with hb
  have hpf : ∀ h ∈ R, ∀ r, 1 ≤ r → QGA.ZetasIrr.pfCoeff (FL n) h r = if r ≤ b h then c h r else 0 :=
    fun h hh r hr => by
      have := pfCoeff_ppSum R b c hh hr
      rwa [← hc] at this
  have step1 : ppSum R b c = ppSum R (fun _ => 2) (cF n) := by
    unfold ppSum
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right (FL_count_le n h))]
    · refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
      rw [cF, hpf h hh r hr1, ite_eq_left hr2]
    · intro r hr hr'
      have hr1 := (Finset.mem_Icc.mp hr).1
      have hlt : b h < r := by
        by_contra hle
        exact hr' (Finset.mem_Icc.mpr ⟨hr1, not_lt.mp hle⟩)
      rw [cF, QGA.ZetasIrr.Aux.pfCoeff_eq_zero_of_rootMultiplicity_lt _ _ _ (by
        rw [← Polynomial.count_roots]; exact hlt), map_zero, zero_mul]
  have step2 : ppSum R (fun _ => 2) (cF n) = ppSum (Tn n) (fun _ => 2) (cF n) := by
    unfold ppSum
    refine Finset.sum_subset (FL_roots_subset n) fun h _ hR => Finset.sum_eq_zero fun r hr => ?_
    rw [cF, QGA.ZetasIrr.Aux.pfCoeff_eq_zero_of_eval_ne_zero _ _ ?_ r (Finset.mem_Icc.mp hr).1, map_zero,
      zero_mul]
    intro h0
    exact hR (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (RatFunc.denom_ne_zero _)).mpr h0))
  rw [hc, step1, step2]

theorem sum_bCoef (n : ℕ) : ∑ j ∈ range (17 * n + 1), bCoef n j = 0 := by
  have hdeg : DegLE (-2) (ppSum (Tn n) (fun _ => 2) (cF n)) := by
    rw [← FL_eq_ppSum]; exact Or.inr (FL_intDegree n).le
  have h := residue_sum_eq_zero (Tn n) (fun _ => 2) (cF n) hdeg
  simp only [show (1 : ℕ) ≤ 2 by norm_num, ite_true, Tn, Finset.sum_image (Tn_inj n), cF,
    pfCoeff_FL_one] at h
  exact h

/-! ### The readouts as sums over `range (17n+1)` -/

theorem aCoef_eq_zero (n j : ℕ) (hj : j < n ∨ 17 * n < j) : aCoef n j = 0 := by
  have hc := denRoots_count n j
  rw [aCoef, pfCoeff, if_neg (by rw [hc]; split_ifs <;> omega),
    if_neg (by rw [hc]; split_ifs <;> omega)]

theorem bCoef_eq_zero (n j : ℕ) (hj : j < n ∨ 17 * n < j) : bCoef n j = 0 := by
  have hc := denRoots_count n j
  rw [bCoef, pfCoeff, if_neg (by rw [hc]; split_ifs <;> omega),
    if_neg (by rw [hc]; split_ifs <;> omega)]

theorem sum_Icc_eq_range (n : ℕ) (f : ℕ → ℚ) (hf : ∀ j, j < n → f j = 0) :
    ∑ j ∈ Icc n (17 * n), f j = ∑ j ∈ range (17 * n + 1), f j := by
  refine Finset.sum_subset (fun j hj => ?_) fun j hj hj' => hf j ?_
  · simp only [Finset.mem_Icc] at hj; exact Finset.mem_range.mpr (by omega)
  · simp only [Finset.mem_range] at hj; simp only [Finset.mem_Icc, not_and, not_le] at hj'
    by_contra h; exact absurd (hj' (by omega)) (by omega)

theorem Q_eq_sum (n : ℕ) : Q n = ∑ j ∈ range (17 * n + 1), aCoef n j :=
  sum_Icc_eq_range n _ fun j hj => aCoef_eq_zero n j (Or.inl hj)

theorem P3_eq_sum (n : ℕ) : P3 n = ∑ j ∈ range (17 * n + 1),
    (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2) :=
  sum_Icc_eq_range n _ fun j hj => by
    rw [aCoef_eq_zero n j (Or.inl hj), bCoef_eq_zero n j (Or.inl hj)]; ring

theorem P4_eq_sum (n : ℕ) : P4 n = ∑ j ∈ range (17 * n + 1),
    (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3) :=
  sum_Icc_eq_range n _ fun j hj => by
    rw [aCoef_eq_zero n j (Or.inl hj), bCoef_eq_zero n j (Or.inl hj)]; ring

/-! ### `𝓛_{2n}[F_n]` -/

theorem Lfun_FL_apply (n k : ℕ) : Lfun (2 * n) (FL n) k = ∑ j ∈ range (17 * n + 1),
    (bCoef n j * ((if 2 = k then 1 else 0) - harm 2 (j + 2 * n) * (if k = 0 then 1 else 0)) +
      2 * aCoef n j *
        ((if 3 = k then 1 else 0) - harm 3 (j + 2 * n) * (if k = 0 then 1 else 0))) := by
  rw [Lfun_FL_eq, Finsupp.finsetSum_apply, Tn, Finset.sum_image (Tn_inj n)]
  exact Finset.sum_congr rfl fun j _ => inner_FL n j k

theorem Lfun_FL_three (n : ℕ) : Lfun (2 * n) (FL n) 3 = 2 * Q n := by
  rw [Lfun_FL_apply, Q_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  norm_num

theorem Lfun_FL_two (n : ℕ) : Lfun (2 * n) (FL n) 2 = 0 := by
  rw [Lfun_FL_apply]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans (sum_bCoef n)
  norm_num

theorem Lfun_FL_zero (n : ℕ) : Lfun (2 * n) (FL n) 0 = -2 * P3 n := by
  rw [Lfun_FL_apply, P3_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  norm_num
  ring

/-! ### `𝓜_{2n}[F_n]` -/

theorem rfDeriv_zero : rfDeriv (0 : ℚ⟮X⟯) = 0 := by
  have h := QGA.ZetasIrr.Aux.rfDeriv_add (0 : ℚ⟮X⟯) 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem rfDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ⟮X⟯) :
    rfDeriv (∑ i ∈ s, f i) = ∑ i ∈ s, rfDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rfDeriv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, QGA.ZetasIrr.Aux.rfDeriv_add, ih]

theorem rfDeriv_inv_pow (h : ℚ) (s : ℕ) :
    rfDeriv (((RatFunc.X - RatFunc.C h) ^ (s + 1))⁻¹) =
      RatFunc.C (-((s + 1 : ℕ) : ℚ)) * ((RatFunc.X - RatFunc.C h) ^ (s + 2))⁻¹ := by
  have hq : (X - C h : ℚ[X]) ^ (s + 1) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero h)
  have hq' : (X - C h : ℚ[X]) ≠ 0 := X_sub_C_ne_zero h
  rw [X_sub_C_pow_eq_algebraMap, X_sub_C_pow_eq_algebraMap, ← one_div,
    ← map_one (algebraMap ℚ[X] ℚ⟮X⟯), QGA.ZetasIrr.Aux.rfDeriv_div _ _ hq, derivative_one, zero_mul,
    one_mul, zero_sub, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero,
    mul_one, Nat.add_sub_cancel,
    div_eq_iff (QGA.ZetasIrr.Aux.algebraMap_ne_zero' (pow_ne_zero _ hq))]
  set q := algebraMap ℚ[X] ℚ⟮X⟯ (X - C h) with hqdef
  have hq0 : q ≠ 0 := QGA.ZetasIrr.Aux.algebraMap_ne_zero' hq'
  have e : (q ^ (s + 1)) ^ 2 = q ^ (s + 2) * q ^ s := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  simp only [map_neg, map_mul, map_pow, RatFunc.algebraMap_C, ← hqdef]
  rw [e, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hq0)]
  ring

/-- The principal-part coefficients of `F_n'`. -/
def cD (n : ℕ) : ℚ → ℕ → ℚ :=
  fun h r => if r = 0 then 0 else -((r - 1 : ℕ) : ℚ) * cF n h (r - 1)

theorem Icc12 : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
theorem Icc13 : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by decide

theorem rfDeriv_FL (n : ℕ) : rfDeriv (FL n) = ppSum (Tn n) (fun _ => 3) (cD n) := by
  rw [FL_eq_ppSum, ppSum, ppSum, rfDeriv_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [rfDeriv_sum, Icc12, Icc13, Finset.sum_pair (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide), QGA.ZetasIrr.Aux.rfDeriv_C_mul, QGA.ZetasIrr.Aux.rfDeriv_C_mul,
    rfDeriv_inv_pow h 0, rfDeriv_inv_pow h 1]
  simp only [cD, cF, Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    zero_mul, map_zero, map_neg, map_mul, map_one, zero_add, one_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero]
  ring

theorem rfDeriv_FL_eq_div (n : ℕ) : rfDeriv (FL n) =
    algebraMap ℚ[X] ℚ⟮X⟯ (derivative (lp (numRoots n)) * lp (denRoots n) -
        lp (numRoots n) * derivative (lp (denRoots n))) /
      algebraMap ℚ[X] ℚ⟮X⟯ (lp (denRoots n) ^ 2) := by
  rw [FL, lin, QGA.ZetasIrr.Aux.rfDeriv_div _ _ (lp_ne_zero _)]

theorem rfDeriv_FL_denom_natDegree_le (n : ℕ) :
    (rfDeriv (FL n)).denom.natDegree ≤ 60 * n + 4 := by
  rw [rfDeriv_FL_eq_div]
  refine (Polynomial.natDegree_le_of_dvd (RatFunc.denom_div_dvd _ _)
    (pow_ne_zero _ (lp_ne_zero _))).trans ?_
  rw [Polynomial.natDegree_pow, lp_natDegree, card_denRoots]
  omega

theorem rfDeriv_FL_polyPart (n : ℕ) : QGA.ZetasIrr.polyPart (rfDeriv (FL n)) = 0 := by
  apply QGA.ZetasIrr.Aux.polyPart_eq_of
  rw [map_zero, sub_zero, rfDeriv_FL]
  exact DegLE.ppSum _ _ _

theorem pfCoeff_rfDeriv_FL (n : ℕ) (h : ℚ) (hh : h ∈ Tn n) (r : ℕ) (hr : 1 ≤ r) :
    QGA.ZetasIrr.pfCoeff (rfDeriv (FL n)) h r = if r ≤ 3 then cD n h r else 0 := by
  rw [rfDeriv_FL]
  exact pfCoeff_ppSum _ _ _ hh hr

theorem rfDeriv_FL_roots_subset (n : ℕ) : (rfDeriv (FL n)).denom.roots.toFinset ⊆ Tn n := by
  intro h hh
  rw [rfDeriv_FL_eq_div] at hh
  have hmem := Multiset.mem_of_le (Polynomial.roots.le_of_dvd (pow_ne_zero 2 (lp_ne_zero _))
    (RatFunc.denom_div_dvd _ _)) (Multiset.mem_toFinset.mp hh)
  rw [Polynomial.roots_pow, lp_roots] at hmem
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_nsmul hmem)
  simp only [denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hp
  refine Finset.mem_image.mpr ⟨(-p).toNat, Finset.mem_range.mpr (by omega), ?_⟩
  have e : (((-p).toNat : ℕ) : ℤ) = -p := Int.toNat_of_nonneg (by omega)
  rw [← Int.cast_natCast (R := ℚ), e, Int.cast_neg, neg_neg]

theorem Lfun_dFL_eq (n : ℕ) : Lfun (2 * n) (rfDeriv (FL n)) =
    ∑ h ∈ Tn n, ∑ r ∈ range (60 * n + 5), ((r : ℚ) * QGA.ZetasIrr.pfCoeff (rfDeriv (FL n)) h r) •
      (Zsym (r + 1) - QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - h⌋ • Zsym 0) := by
  rw [QGA.ZetasIrr.Aux.Lfun_eq_general (2 * n) (rfDeriv (FL n)) (Tn n) (rfDeriv_FL_roots_subset n)
    (60 * n + 4) (rfDeriv_FL_denom_natDegree_le n), rfDeriv_FL_polyPart]
  simp only [QGA.ZetasIrr.Aux.bsum, Polynomial.sum_zero_index, zero_smul, zero_add]

theorem sum_range_four (f : ℕ → ℚ) (M : ℕ) (hM : 4 ≤ M) (hf : ∀ r, 4 ≤ r → f r = 0) :
    ∑ r ∈ range M, f r = f 0 + f 1 + f 2 + f 3 := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hM) (fun r _ hr => hf r (by
    simp only [Finset.mem_range, not_lt] at hr; omega))]
  simp [Finset.sum_range_succ]

theorem dinner_FL (n j k : ℕ) (hj : j < 17 * n + 1) :
    (∑ r ∈ range (60 * n + 5), ((r : ℚ) * QGA.ZetasIrr.pfCoeff (rfDeriv (FL n)) (-(j : ℚ)) r) •
      (Zsym (r + 1) - QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ • Zsym 0)) k =
      -(2 * bCoef n j *
          ((if 3 = k then 1 else 0) - harm 3 (j + 2 * n) * (if k = 0 then 1 else 0)) +
        6 * aCoef n j *
          ((if 4 = k then 1 else 0) - harm 4 (j + 2 * n) * (if k = 0 then 1 else 0))) := by
  rw [Finsupp.finsetSum_apply]
  simp only [term_apply, floor_eq, harm_eq]
  rw [sum_range_four _ _ (by omega) (fun r hr => by
    rw [pfCoeff_rfDeriv_FL n _ (mem_Tn n j hj) r (by omega), ite_eq_right (by omega)]; ring)]
  rw [pfCoeff_rfDeriv_FL n _ (mem_Tn n j hj) 1 le_rfl, pfCoeff_rfDeriv_FL n _ (mem_Tn n j hj) 2
    (by norm_num), pfCoeff_rfDeriv_FL n _ (mem_Tn n j hj) 3 (by norm_num)]
  simp only [cD, cF, pfCoeff_FL_two, pfCoeff_FL_one, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero]
  norm_num
  push_cast
  ring

theorem Mfun_FL_apply (n k : ℕ) : Mfun (2 * n) (FL n) k = ∑ j ∈ range (17 * n + 1),
    (2 * bCoef n j * ((if 3 = k then 1 else 0) - harm 3 (j + 2 * n) * (if k = 0 then 1 else 0)) +
      6 * aCoef n j *
        ((if 4 = k then 1 else 0) - harm 4 (j + 2 * n) * (if k = 0 then 1 else 0))) := by
  rw [Mfun, Finsupp.neg_apply, Lfun_dFL_eq, Finsupp.finsetSum_apply, Tn,
    Finset.sum_image (Tn_inj n), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dinner_FL n j k (Finset.mem_range.mp hj), neg_neg]

theorem Mfun_FL_four (n : ℕ) : Mfun (2 * n) (FL n) 4 = 6 * Q n := by
  rw [Mfun_FL_apply, Q_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  norm_num

theorem Mfun_FL_three (n : ℕ) : Mfun (2 * n) (FL n) 3 = 0 := by
  rw [Mfun_FL_apply]
  refine (Finset.sum_congr rfl fun j _ => ?_).trans
    (show ∑ j ∈ range (17 * n + 1), 2 * bCoef n j = 0 by rw [← Finset.mul_sum, sum_bCoef, mul_zero])
  norm_num

theorem Mfun_FL_zero (n : ℕ) : Mfun (2 * n) (FL n) 0 = -6 * P4 n := by
  rw [Mfun_FL_apply, P4_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  norm_num
  ring

/-! ### The initial moments at `w₀` (`R = t⁻²`, cutoff `0`) -/

/-- `𝓛_0[P + c t^{-q}] = bsum P · 1 + q c Z_{q+1}` for `1 ≤ q ≤ 4`. -/
theorem Lfun0_simple (P : ℚ[X]) (q : ℕ) (hq1 : 1 ≤ q) (hq4 : q ≤ 4) (c : ℚ) :
    Lfun 0 (algebraMap ℚ[X] (RatFunc ℚ) P + RatFunc.C c * ((RatFunc.X - RatFunc.C 0) ^ q)⁻¹) =
      QGA.ZetasIrr.Aux.bsum 1 P • Zsym 0 + ((q : ℚ) * c) • Zsym (q + 1) := by
  have hX : (RatFunc.X - RatFunc.C 0 : RatFunc ℚ) = algebraMap ℚ[X] (RatFunc ℚ) X := by simp
  have hXq : (algebraMap ℚ[X] (RatFunc ℚ) X) ^ q ≠ 0 :=
    pow_ne_zero _ (by simp [RatFunc.X_ne_zero])
  have hg : algebraMap ℚ[X] (RatFunc ℚ) P + RatFunc.C c * ((RatFunc.X - RatFunc.C 0) ^ q)⁻¹ =
      algebraMap ℚ[X] (RatFunc ℚ) (P * X ^ q + Polynomial.C c) /
        algebraMap ℚ[X] (RatFunc ℚ) (X ^ q) := by
    rw [hX, map_add, map_mul, map_pow, RatFunc.algebraMap_C, add_div, mul_div_cancel_right₀ _ hXq,
      div_eq_mul_inv]
  have hden : (algebraMap ℚ[X] (RatFunc ℚ) P +
      RatFunc.C c * ((RatFunc.X - RatFunc.C 0) ^ q)⁻¹).denom ∣ X ^ 4 := by
    rw [hg]; exact (RatFunc.denom_div_dvd _ _).trans (pow_dvd_pow _ hq4)
  rw [QGA.ZetasIrr.Aux.Lfun_zero_of_decomp _ hden P (fun k => if k = q then c else 0)]
  · congr 1
    simp only [mul_ite, mul_zero, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 4) q, if_pos (Finset.mem_Icc.mpr ⟨hq1, hq4⟩)]
  · congr 1
    simp only [apply_ite RatFunc.C, map_zero, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' (Finset.Icc 1 4) q, if_pos (Finset.mem_Icc.mpr ⟨hq1, hq4⟩)]

theorem rfDeriv_algebraMap (P : ℚ[X]) :
    rfDeriv (algebraMap ℚ[X] (RatFunc ℚ) P) = algebraMap ℚ[X] (RatFunc ℚ) (derivative P) := by
  have := QGA.ZetasIrr.Aux.rfDeriv_div P 1 one_ne_zero
  simpa using this

/-- `𝓜_0[P + c t^{-(s+1)}] = -(bsum P' · 1 - (s+2)(s+1) c Z_{s+3})` for `s ≤ 2`. -/
theorem Mfun0_simple (P : ℚ[X]) (s : ℕ) (hs : s ≤ 2) (c : ℚ) :
    Mfun 0 (algebraMap ℚ[X] (RatFunc ℚ) P + RatFunc.C c * ((RatFunc.X - RatFunc.C 0) ^ (s + 1))⁻¹) =
      -(QGA.ZetasIrr.Aux.bsum 1 (derivative P) • Zsym 0 +
        (((s + 2 : ℕ) : ℚ) * (-((s + 1 : ℕ) : ℚ) * c)) • Zsym (s + 2 + 1)) := by
  rw [Mfun, QGA.ZetasIrr.Aux.rfDeriv_add, QGA.ZetasIrr.Aux.rfDeriv_C_mul, rfDeriv_inv_pow,
    rfDeriv_algebraMap, ← mul_assoc, ← map_mul, Lfun0_simple _ _ (by omega) (by omega)]
  ring_nf

theorem bsum_zero : QGA.ZetasIrr.Aux.bsum 1 (0 : ℚ[X]) = 0 := by
  simp [QGA.ZetasIrr.Aux.bsum]
theorem bsum_one : QGA.ZetasIrr.Aux.bsum 1 (1 : ℚ[X]) = 1 := by
  rw [QGA.ZetasIrr.Aux.bsum_eq_range 1 1 0 (by simp)]; simp
theorem bsum_negX : QGA.ZetasIrr.Aux.bsum 1 (-X : ℚ[X]) = -1 / 2 := by
  rw [QGA.ZetasIrr.Aux.bsum_eq_range 1 _ 1 (by simp)]
  simp [Finset.sum_range_succ]
  norm_num
theorem bsum_negone : QGA.ZetasIrr.Aux.bsum 1 (-1 : ℚ[X]) = -1 := by
  rw [QGA.ZetasIrr.Aux.bsum_eq_range 1 _ 0 (by simp)]; simp

theorem col0 : (-RatFunc.X : RatFunc ℚ) ^ 0 * (RatFunc.X ^ 2)⁻¹ =
    algebraMap ℚ[X] (RatFunc ℚ) 0 + RatFunc.C 1 * ((RatFunc.X - RatFunc.C 0) ^ (1 + 1))⁻¹ := by
  simp
theorem col1 : (-RatFunc.X : RatFunc ℚ) ^ 1 * (RatFunc.X ^ 2)⁻¹ =
    algebraMap ℚ[X] (RatFunc ℚ) 0 + RatFunc.C (-1) * ((RatFunc.X - RatFunc.C 0) ^ (0 + 1))⁻¹ := by
  simp; field_simp
theorem col2 : (-RatFunc.X : RatFunc ℚ) ^ 2 * (RatFunc.X ^ 2)⁻¹ =
    algebraMap ℚ[X] (RatFunc ℚ) 1 + RatFunc.C 0 * ((RatFunc.X - RatFunc.C 0) ^ (0 + 1))⁻¹ := by
  simp [RatFunc.X_ne_zero]
theorem col3 : (-RatFunc.X : RatFunc ℚ) ^ 3 * (RatFunc.X ^ 2)⁻¹ =
    algebraMap ℚ[X] (RatFunc ℚ) (-X) + RatFunc.C 0 * ((RatFunc.X - RatFunc.C 0) ^ (0 + 1))⁻¹ := by
  simp; field_simp

end Meijer5255.CmfReadout
