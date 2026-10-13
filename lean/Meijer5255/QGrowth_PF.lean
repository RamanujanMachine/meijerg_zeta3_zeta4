-- Adapted from ../zetas_irr/pfq54_formalization_handoff/pf_aux.lean (zetas_irr commit d9d5223),
-- together with the definitions `nR`, `dR` (`residue_aux.lean`), `count_Icc`, `card_nR`, `card_dR`
-- (`residue_aux4.lean`) and `prod_Icc_8_12` (`Pfq54_aux.lean`), for the analytic input of
-- `Meijer5255.QGrowth` / `Meijer5255.LinformError`. Changes: namespace `Pfq54` renamed to
-- `Meijer5255.QGA.Pfq54`, `ZetasIrr` to `Meijer5255.QGA.ZetasIrr`; the identification of the
-- Laurent coefficients of `F_n` with pfq54's jets `U`, `V` (which needs the long `residue_aux`
-- chain) is dropped: the coefficients are kept abstract as `aF n j = pfCoeff (Fn n) (-j) 2`,
-- `bF n j = pfCoeff (Fn n) (-j) 1` (identified with `Meijer5255.aCoef`, `bCoef` in
-- `QGrowth_Bridge.lean`), and the readouts are stated as sums of these.
import Meijer5255.QGrowth_CMF_main

open Polynomial Finset
open scoped RatFunc LaurentSeries Matrix

noncomputable section

namespace Meijer5255.QGA.Pfq54.RA

/-- Roots of the numerator of `F_n` (same as `numRoots`). -/
def nR (n : ℕ) : Multiset ℤ :=
  (Icc (1 : ℤ) (10 * n)).val + (Icc ((n : ℤ) + 1) (11 * n)).val +
    (Icc (2 * (n : ℤ) + 1) (12 * n)).val

/-- Roots of the denominator of `F_n` (same as `denRoots`). -/
def dR (n : ℕ) : Multiset ℤ :=
  (Icc (-(17 * n : ℤ)) (-n)).val + (Icc (-(16 * n : ℤ)) (-(2 * n))).val

theorem count_Icc (a b t : ℤ) : (Icc a b).val.count t = if a ≤ t ∧ t ≤ b then 1 else 0 := by
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [ite_eq_left h]
    exact Multiset.count_eq_one_of_mem (Finset.nodup _) (Finset.mem_val.mpr (mem_Icc.mpr h))
  · rw [ite_eq_right h]
    exact Multiset.count_eq_zero.mpr fun hm => h (mem_Icc.mp (Finset.mem_val.mp hm))

theorem card_nR (n : ℕ) : Multiset.card (nR n) = 30 * n := by
  rw [nR, Multiset.card_add, Multiset.card_add, Finset.card_val, Finset.card_val,
    Finset.card_val, Int.card_Icc, Int.card_Icc, Int.card_Icc]
  omega

theorem card_dR (n : ℕ) : Multiset.card (dR n) = 30 * n + 2 := by
  rw [dR, Multiset.card_add, Finset.card_val, Finset.card_val, Int.card_Icc, Int.card_Icc]
  omega

end Meijer5255.QGA.Pfq54.RA

namespace Meijer5255.QGA.Pfq54

/-- pfq54's generalised harmonic number `H^{(r)}_m = ∑_{k=1}^m k^{-r}` (`Pfq54_defs.harm`). -/
def harm (r m : ℕ) : ℚ := ∑ k ∈ Icc 1 m, 1 / (k : ℚ) ^ r

end Meijer5255.QGA.Pfq54

namespace Meijer5255.QGA.Pfq54.Aux

theorem prod_Icc_8_12 {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ u ∈ Icc 8 12, f u = f 8 * f 9 * f 10 * f 11 * f 12 := by
  rw [show Icc 8 12 = {8, 9, 10, 11, 12} by decide, prod_insert (by decide),
    prod_insert (by decide), prod_insert (by decide), prod_insert (by decide), prod_singleton]
  simp only [mul_assoc]

end Meijer5255.QGA.Pfq54.Aux

namespace Meijer5255.QGA.Pfq54.PF

open Meijer5255.QGA.Pfq54 Meijer5255.QGA.Pfq54.RA Meijer5255.QGA.ZetasIrr Meijer5255.QGA.ZetasIrr.CMF

def Fn (n : ℕ) : ℚ⟮X⟯ := lin (nR n) (dR n)

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
  exact lp_eval_ne_zero' P 0 hP

/-- The Laurent coefficients of `lin Z (0^m + P)` at `0` when `0 ∉ Z`, `0 ∉ P`. -/
theorem pfCoeff_lin_zero (Z P : Multiset ℤ) (m : ℕ) (hZ : (0 : ℤ) ∉ Z) (hP : (0 : ℤ) ∉ P)
    (r : ℕ) :
    pfCoeff (lin Z (Multiset.replicate m 0 + P)) 0 r =
      if r ≤ m then PowerSeries.coeff (m - r)
        ((lp Z : PowerSeries ℚ) * (lp P : PowerSeries ℚ)⁻¹) else 0 := by
  have hPc := lp_constantCoeff_ne_zero P hP
  have hcoe : algebraMap ℚ⟮X⟯ ℚ⸨X⸩ (RatFunc.laurent 0 (lin Z (Multiset.replicate m 0 + P))) =
      HahnSeries.single (-(m : ℤ)) 1 *
        (((lp Z : PowerSeries ℚ) * (lp P : PowerSeries ℚ)⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
    rw [RatFunc.laurent_at_zero, lin, lp_add, lp_replicate, Int.cast_zero, map_zero, sub_zero,
      map_mul, map_div₀, map_mul, Aux.coe_algebraMap_poly, Aux.coe_algebraMap_poly,
      Aux.coe_algebraMap_poly, Polynomial.coe_pow, Polynomial.coe_X, PowerSeries.coe_pow,
      PowerSeries.coe_X, PowerSeries.coe_mul]
    have hinv : ((lp P : PowerSeries ℚ) : ℚ⸨X⸩)⁻¹ =
        (((lp P : PowerSeries ℚ)⁻¹ : PowerSeries ℚ) : ℚ⸨X⸩) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← PowerSeries.coe_mul, PowerSeries.mul_inv_cancel _ hPc, PowerSeries.coe_one]
    rw [div_eq_mul_inv, mul_inv, hinv, HahnSeries.single_pow, one_pow, HahnSeries.inv_single]
    simp only [nsmul_eq_mul, mul_one, inv_one]
    ring
  unfold pfCoeff
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
    pfCoeff (lin Z (Multiset.replicate m 0 + P)) 0 m = (lp Z).eval 0 / (lp P).eval 0 := by
  rw [pfCoeff_lin_zero Z P m hZ hP m, ite_eq_left le_rfl, Nat.sub_self, coeff_zero_mul_inv,
    Polynomial.coeff_coe, Polynomial.coeff_coe, lp_coeff_zero, lp_coeff_zero]

theorem pfCoeff_lin_zero_sub (Z P : Multiset ℤ) (m : ℕ) (hm : 1 ≤ m) (hZ : (0 : ℤ) ∉ Z)
    (hP : (0 : ℤ) ∉ P) :
    pfCoeff (lin Z (Multiset.replicate m 0 + P)) 0 (m - 1) =
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
    pfCoeff f (h : ℚ) r = pfCoeff (RatFunc.laurent (h : ℚ) f) 0 r := by
  rw [Aux.pfCoeff_laurent, zero_add]

theorem pfCoeff_lin_gt (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) (r : ℕ) (hr : P.count h < r) :
    pfCoeff (lin Z P) h r = 0 := by
  rw [pfCoeff_shift, lin_laurent, map_sub_eq P h,
    pfCoeff_lin_zero _ _ _ (not_mem_map_sub Z h hZ) (not_mem_filter_map P h),
    ite_eq_right (by omega)]

theorem pfCoeff_lin_top (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) :
    pfCoeff (lin Z P) h (P.count h) =
      (lp Z).eval (h : ℚ) / (lp (P.filter (· ≠ h))).eval (h : ℚ) := by
  rw [pfCoeff_shift, lin_laurent, map_sub_eq P h,
    pfCoeff_lin_zero_top _ _ _ (not_mem_map_sub Z h hZ) (not_mem_filter_map P h),
    lp_eval_map_sub, lp_eval_map_sub]

theorem pfCoeff_lin_sub (Z P : Multiset ℤ) (h : ℤ) (hZ : h ∉ Z) (hm : 1 ≤ P.count h) :
    pfCoeff (lin Z P) h (P.count h - 1) =
      (lp Z).eval (h : ℚ) / (lp (P.filter (· ≠ h))).eval (h : ℚ) *
        (Lsq Z h - Lsq (P.filter (· ≠ h)) h) := by
  rw [pfCoeff_shift, lin_laurent, map_sub_eq P h,
    pfCoeff_lin_zero_sub _ _ _ hm (not_mem_map_sub Z h hZ) (not_mem_filter_map P h),
    lp_eval_map_sub, lp_eval_map_sub, Lsq_map_sub, Lsq_map_sub]


/-! ### The coefficients of `F_n` -/

/-- The double-pole coefficient `a_j` of `F_n` at `t = -j`. -/
def aF (n j : ℕ) : ℚ := pfCoeff (Fn n) (-(j : ℚ)) 2

/-- The simple-pole coefficient `b_j` of `F_n` at `t = -j`. -/
def bF (n j : ℕ) : ℚ := pfCoeff (Fn n) (-(j : ℚ)) 1

theorem pfCoeff_Fn_two (n j : ℕ) : pfCoeff (Fn n) (-(j : ℚ)) 2 = aF n j := rfl

theorem pfCoeff_Fn_one (n j : ℕ) : pfCoeff (Fn n) (-(j : ℚ)) 1 = bF n j := rfl

theorem nR_pos (n : ℕ) (z : ℤ) (hz : z ∈ nR n) : 1 ≤ z := by
  simp only [nR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hz
  omega

theorem neg_not_mem_nR (n j : ℕ) : -(j : ℤ) ∉ nR n := fun h => by
  have := nR_pos n _ h
  omega

theorem dR_count (n j : ℕ) : (dR n).count (-(j : ℤ)) =
    (if n ≤ j ∧ j ≤ 17 * n then 1 else 0) + (if 2 * n ≤ j ∧ j ≤ 16 * n then 1 else 0) := by
  rw [dR, Multiset.count_add, count_Icc, count_Icc]
  split_ifs <;> omega

theorem neg_cast (j : ℕ) : (-(j : ℚ)) = ((-(j : ℤ) : ℤ) : ℚ) := by push_cast; ring

theorem pfCoeff_Fn_gt (n j r : ℕ) (hr : 3 ≤ r) : pfCoeff (Fn n) (-(j : ℚ)) r = 0 := by
  rw [neg_cast]
  apply pfCoeff_lin_gt _ _ _ (neg_not_mem_nR n j)
  rw [dR_count]
  split_ifs <;> omega

/-! ### Degrees, poles and the polynomial part -/

theorem lp_natDegree (S : Multiset ℤ) : (lp S).natDegree = Multiset.card S := by
  rw [lp_eq_map, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map]

theorem Fn_denom_natDegree_le (n : ℕ) : (Fn n).denom.natDegree ≤ 30 * n + 2 :=
  (Polynomial.natDegree_le_of_dvd (lin_denom_dvd _ _) (lp_ne_zero _)).trans
    (by rw [lp_natDegree, card_dR])

theorem Fn_proper (n : ℕ) : (Fn n).num.natDegree < (Fn n).denom.natDegree := by
  have h : (Fn n).intDegree = (30 * n : ℤ) - (30 * n + 2) := by
    unfold Fn lin
    rw [RatFunc.intDegree_div (Aux.algebraMap_ne_zero' (lp_ne_zero _))
      (Aux.algebraMap_ne_zero' (lp_ne_zero _)), RatFunc.intDegree_polynomial,
      RatFunc.intDegree_polynomial, lp_natDegree, lp_natDegree, card_nR, card_dR]
    push_cast
    ring
  unfold RatFunc.intDegree at h
  omega

theorem Fn_polyPart (n : ℕ) : polyPart (Fn n) = 0 :=
  polyPart_eq_zero_of_proper _ (Fn_proper n)

def Tn (n : ℕ) : Finset ℚ := (range (17 * n + 1)).image fun j : ℕ => -(j : ℚ)

theorem Fn_roots_subset (n : ℕ) : (Fn n).denom.roots.toFinset ⊆ Tn n := by
  intro h hh
  have hmem := Multiset.mem_of_le (lin_roots_le _ _) (Multiset.mem_toFinset.mp hh)
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hmem
  simp only [dR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hp
  refine Finset.mem_image.mpr ⟨(-p).toNat, Finset.mem_range.mpr (by omega), ?_⟩
  have e : (((-p).toNat : ℕ) : ℤ) = -p := Int.toNat_of_nonneg (by omega)
  rw [← Int.cast_natCast (R := ℚ), e, Int.cast_neg, neg_neg]

theorem Tn_inj (n : ℕ) : ∀ a ∈ range (17 * n + 1), ∀ b ∈ range (17 * n + 1),
    (fun j : ℕ => -(j : ℚ)) a = (fun j : ℕ => -(j : ℚ)) b → a = b :=
  fun a _ b _ h => by exact_mod_cast neg_injective h

theorem Lfun_Fn_eq (n : ℕ) : Lfun (2 * n) (Fn n) = ∑ h ∈ Tn n, ∑ r ∈ range (30 * n + 3),
    ((r : ℚ) * pfCoeff (Fn n) h r) •
      (Zsym (r + 1) - Meijer5255.QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - h⌋ • Zsym 0) := by
  rw [Aux.Lfun_eq_general (2 * n) (Fn n) (Tn n) (Fn_roots_subset n) (30 * n + 2)
    (Fn_denom_natDegree_le n), Fn_polyPart]
  simp only [Aux.bsum, Polynomial.sum_zero_index, zero_smul, zero_add]

theorem term_apply (c H : ℚ) (r k : ℕ) :
    ((c • (Zsym (r + 1) - H • Zsym 0)) : FormalZ) k =
      c * ((if r + 1 = k then 1 else 0) - H * (if k = 0 then 1 else 0)) := by
  simp only [Finsupp.smul_apply, Finsupp.sub_apply, Zsym, Finsupp.single_apply, smul_eq_mul,
    eq_comm (a := (0 : ℕ))]

theorem floor_eq (n j : ℕ) : ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ = ((2 * n + j : ℕ) : ℤ) := by
  rw [show ((2 * n : ℤ) : ℚ) - (-(j : ℚ)) = ((2 * n + j : ℕ) : ℚ) by push_cast; ring,
    Int.floor_natCast]

theorem harm_eq (r m : ℕ) : Meijer5255.QGA.ZetasIrr.harm r ((m : ℕ) : ℤ) = Meijer5255.QGA.Pfq54.harm r m := by
  unfold Meijer5255.QGA.ZetasIrr.harm Meijer5255.QGA.Pfq54.harm
  rw [Int.toNat_natCast]

theorem sum_range_three (f : ℕ → ℚ) (M : ℕ) (hM : 3 ≤ M) (hf : ∀ r, 3 ≤ r → f r = 0) :
    ∑ r ∈ range M, f r = f 0 + f 1 + f 2 := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hM) (fun r _ hr => hf r (by
    simp only [Finset.mem_range, not_lt] at hr; omega))]
  simp [Finset.sum_range_succ]

theorem inner_three (n j : ℕ) :
    (∑ r ∈ range (30 * n + 3), ((r : ℚ) * pfCoeff (Fn n) (-(j : ℚ)) r) •
      (Zsym (r + 1) - Meijer5255.QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ • Zsym 0)) 3 =
      2 * aF n j := by
  rw [Finsupp.finsetSum_apply]
  simp only [term_apply]
  rw [sum_range_three _ _ (by omega) (fun r hr => by
    rw [pfCoeff_Fn_gt n j r hr]; ring)]
  simp [pfCoeff_Fn_two]

theorem inner_zero (n j : ℕ) :
    (∑ r ∈ range (30 * n + 3), ((r : ℚ) * pfCoeff (Fn n) (-(j : ℚ)) r) •
      (Zsym (r + 1) - Meijer5255.QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ • Zsym 0)) 0 =
      -(bF n j * Meijer5255.QGA.Pfq54.harm 2 (2 * n + j) + 2 * aF n j * Meijer5255.QGA.Pfq54.harm 3 (2 * n + j)) := by
  rw [Finsupp.finsetSum_apply]
  simp only [term_apply, floor_eq, harm_eq]
  rw [sum_range_three _ _ (by omega) (fun r hr => by
    rw [pfCoeff_Fn_gt n j r hr]; ring)]
  simp [pfCoeff_Fn_two, pfCoeff_Fn_one]
  ring

/-! ### The second functional -/

def cF (n : ℕ) : ℚ → ℕ → ℚ := fun h r => pfCoeff (Fn n) h r

theorem dR_count_le (n : ℕ) (p : ℤ) : (dR n).count p ≤ 2 := by
  rw [dR, Multiset.count_add, count_Icc, count_Icc]
  split_ifs <;> omega

theorem Fn_count_le (n : ℕ) (h : ℚ) : (Fn n).denom.roots.count h ≤ 2 := by
  refine (Multiset.count_le_of_le h (lin_roots_le _ _)).trans ?_
  by_cases hh : ∃ p : ℤ, (p : ℚ) = h
  · obtain ⟨p, rfl⟩ := hh
    rw [Multiset.count_map_eq_count' _ _ Int.cast_injective]
    exact dR_count_le n p
  · rw [Multiset.count_eq_zero.mpr]
    · omega
    · intro hm
      obtain ⟨p, _, hp⟩ := Multiset.mem_map.mp hm
      exact hh ⟨p, hp⟩

theorem Fn_eq_ppSum (n : ℕ) : Fn n = ppSum (Tn n) (fun _ => 2) (cF n) := by
  obtain ⟨c, hc⟩ := exists_eq_ppSum (Fn n) (Fn_proper n) (lin_split _ _)
  set R := (Fn n).denom.roots.toFinset with hR
  set b : ℚ → ℕ := fun h => (Fn n).denom.roots.count h with hb
  have hpf : ∀ h ∈ R, ∀ r, 1 ≤ r → pfCoeff (Fn n) h r = if r ≤ b h then c h r else 0 :=
    fun h hh r hr => by
      have := pfCoeff_ppSum R b c hh hr
      rwa [← hc] at this
  have step1 : ppSum R b c = ppSum R (fun _ => 2) (cF n) := by
    unfold ppSum
    refine Finset.sum_congr rfl fun h hh => ?_
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right (Fn_count_le n h))]
    · refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hr
      rw [cF, hpf h hh r hr1, ite_eq_left hr2]
    · intro r hr hr'
      have hr1 := (Finset.mem_Icc.mp hr).1
      have hlt : b h < r := by
        by_contra hle
        exact hr' (Finset.mem_Icc.mpr ⟨hr1, not_lt.mp hle⟩)
      rw [cF, Aux.pfCoeff_eq_zero_of_rootMultiplicity_lt _ _ _ (by
        rw [← Polynomial.count_roots]; exact hlt), map_zero, zero_mul]
  have step2 : ppSum R (fun _ => 2) (cF n) = ppSum (Tn n) (fun _ => 2) (cF n) := by
    unfold ppSum
    refine Finset.sum_subset (Fn_roots_subset n) fun h _ hR => Finset.sum_eq_zero fun r hr => ?_
    rw [cF, Aux.pfCoeff_eq_zero_of_eval_ne_zero _ _ ?_ r (Finset.mem_Icc.mp hr).1, map_zero,
      zero_mul]
    intro h0
    exact hR (Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (RatFunc.denom_ne_zero _)).mpr h0))
  rw [hc, step1, step2]

theorem rfDeriv_zero : rfDeriv (0 : ℚ⟮X⟯) = 0 := by
  have h := Aux.rfDeriv_add (0 : ℚ⟮X⟯) 0
  rw [add_zero] at h
  exact (add_eq_left.mp h.symm)

theorem rfDeriv_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ⟮X⟯) :
    rfDeriv (∑ i ∈ s, f i) = ∑ i ∈ s, rfDeriv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rfDeriv_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Aux.rfDeriv_add, ih]

theorem rfDeriv_inv_pow (h : ℚ) (s : ℕ) :
    rfDeriv (((RatFunc.X - RatFunc.C h) ^ (s + 1))⁻¹) =
      RatFunc.C (-((s + 1 : ℕ) : ℚ)) * ((RatFunc.X - RatFunc.C h) ^ (s + 2))⁻¹ := by
  have hq : (X - C h : ℚ[X]) ^ (s + 1) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero h)
  have hq' : (X - C h : ℚ[X]) ≠ 0 := X_sub_C_ne_zero h
  rw [X_sub_C_pow_eq_algebraMap, X_sub_C_pow_eq_algebraMap, ← one_div,
    ← map_one (algebraMap ℚ[X] ℚ⟮X⟯), Aux.rfDeriv_div _ _ hq, derivative_one, zero_mul, one_mul,
    zero_sub, derivative_pow, derivative_sub, derivative_X, derivative_C, sub_zero, mul_one,
    Nat.add_sub_cancel, div_eq_iff (Aux.algebraMap_ne_zero' (pow_ne_zero _ hq))]
  set q := algebraMap ℚ[X] ℚ⟮X⟯ (X - C h) with hqdef
  have hq0 : q ≠ 0 := Aux.algebraMap_ne_zero' hq'
  have e : (q ^ (s + 1)) ^ 2 = q ^ (s + 2) * q ^ s := by
    rw [← pow_mul, ← pow_add]
    congr 1
    ring
  simp only [map_neg, map_mul, map_pow, RatFunc.algebraMap_C, ← hqdef]
  rw [e, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hq0)]
  ring

def cD (n : ℕ) : ℚ → ℕ → ℚ :=
  fun h r => if r = 0 then 0 else -((r - 1 : ℕ) : ℚ) * cF n h (r - 1)

theorem Icc12 : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
theorem Icc13 : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by decide

theorem rfDeriv_Fn (n : ℕ) : rfDeriv (Fn n) = ppSum (Tn n) (fun _ => 3) (cD n) := by
  rw [Fn_eq_ppSum, ppSum, ppSum, rfDeriv_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [rfDeriv_sum, Icc12, Icc13, Finset.sum_pair (by decide), Finset.sum_insert (by decide),
    Finset.sum_pair (by decide), Aux.rfDeriv_C_mul, Aux.rfDeriv_C_mul, rfDeriv_inv_pow h 0,
    rfDeriv_inv_pow h 1]
  simp only [cD, cF, Nat.reduceSub, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    zero_mul, map_zero, map_neg, map_mul, map_one, zero_add, one_ne_zero, ↓reduceIte,
    OfNat.ofNat_ne_zero]
  ring

theorem rfDeriv_Fn_eq_div (n : ℕ) : rfDeriv (Fn n) =
    algebraMap ℚ[X] ℚ⟮X⟯ (derivative (lp (nR n)) * lp (dR n) - lp (nR n) * derivative (lp (dR n))) /
      algebraMap ℚ[X] ℚ⟮X⟯ (lp (dR n) ^ 2) := by
  rw [Fn, lin, Aux.rfDeriv_div _ _ (lp_ne_zero _)]

theorem rfDeriv_Fn_denom_natDegree_le (n : ℕ) :
    (rfDeriv (Fn n)).denom.natDegree ≤ 60 * n + 4 := by
  rw [rfDeriv_Fn_eq_div]
  refine (Polynomial.natDegree_le_of_dvd (RatFunc.denom_div_dvd _ _)
    (pow_ne_zero _ (lp_ne_zero _))).trans ?_
  rw [Polynomial.natDegree_pow, lp_natDegree, card_dR]
  omega

theorem rfDeriv_Fn_polyPart (n : ℕ) : polyPart (rfDeriv (Fn n)) = 0 := by
  apply Aux.polyPart_eq_of
  rw [map_zero, sub_zero, rfDeriv_Fn]
  exact DegLE.ppSum _ _ _

theorem pfCoeff_rfDeriv_Fn (n : ℕ) (h : ℚ) (hh : h ∈ Tn n) (r : ℕ) (hr : 1 ≤ r) :
    pfCoeff (rfDeriv (Fn n)) h r = if r ≤ 3 then cD n h r else 0 := by
  rw [rfDeriv_Fn]
  exact pfCoeff_ppSum _ _ _ hh hr

theorem rfDeriv_Fn_roots_subset (n : ℕ) : (rfDeriv (Fn n)).denom.roots.toFinset ⊆ Tn n := by
  intro h hh
  rw [rfDeriv_Fn_eq_div] at hh
  have hmem := Multiset.mem_of_le (Polynomial.roots.le_of_dvd (pow_ne_zero 2 (lp_ne_zero _))
    (RatFunc.denom_div_dvd _ _)) (Multiset.mem_toFinset.mp hh)
  rw [Polynomial.roots_pow, lp_roots] at hmem
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_mem_nsmul hmem)
  simp only [dR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hp
  refine Finset.mem_image.mpr ⟨(-p).toNat, Finset.mem_range.mpr (by omega), ?_⟩
  have e : (((-p).toNat : ℕ) : ℤ) = -p := Int.toNat_of_nonneg (by omega)
  rw [← Int.cast_natCast (R := ℚ), e, Int.cast_neg, neg_neg]

theorem Lfun_dFn_eq (n : ℕ) : Lfun (2 * n) (rfDeriv (Fn n)) =
    ∑ h ∈ Tn n, ∑ r ∈ range (60 * n + 5), ((r : ℚ) * pfCoeff (rfDeriv (Fn n)) h r) •
      (Zsym (r + 1) - Meijer5255.QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - h⌋ • Zsym 0) := by
  rw [Aux.Lfun_eq_general (2 * n) (rfDeriv (Fn n)) (Tn n) (rfDeriv_Fn_roots_subset n)
    (60 * n + 4) (rfDeriv_Fn_denom_natDegree_le n), rfDeriv_Fn_polyPart]
  simp only [Aux.bsum, Polynomial.sum_zero_index, zero_smul, zero_add]

theorem mem_Tn (n j : ℕ) (hj : j < 17 * n + 1) : -(j : ℚ) ∈ Tn n :=
  Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

theorem sum_range_four (f : ℕ → ℚ) (M : ℕ) (hM : 4 ≤ M) (hf : ∀ r, 4 ≤ r → f r = 0) :
    ∑ r ∈ range M, f r = f 0 + f 1 + f 2 + f 3 := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hM) (fun r _ hr => hf r (by
    simp only [Finset.mem_range, not_lt] at hr; omega))]
  simp [Finset.sum_range_succ]

theorem dinner_four (n j : ℕ) (hj : j < 17 * n + 1) :
    (∑ r ∈ range (60 * n + 5), ((r : ℚ) * pfCoeff (rfDeriv (Fn n)) (-(j : ℚ)) r) •
      (Zsym (r + 1) - Meijer5255.QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ • Zsym 0)) 4 =
      -6 * aF n j := by
  rw [Finsupp.finsetSum_apply]
  simp only [term_apply]
  rw [sum_range_four _ _ (by omega) (fun r hr => by
    rw [pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) r (by omega), ite_eq_right (by omega)]; ring)]
  rw [pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) 1 le_rfl, pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) 2
    (by norm_num), pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) 3 (by norm_num)]
  simp [cD, cF, pfCoeff_Fn_two]
  ring

theorem dinner_zero (n j : ℕ) (hj : j < 17 * n + 1) :
    (∑ r ∈ range (60 * n + 5), ((r : ℚ) * pfCoeff (rfDeriv (Fn n)) (-(j : ℚ)) r) •
      (Zsym (r + 1) - Meijer5255.QGA.ZetasIrr.harm (r + 1) ⌊((2 * n : ℤ) : ℚ) - (-(j : ℚ))⌋ • Zsym 0)) 0 =
      2 * bF n j * Meijer5255.QGA.Pfq54.harm 3 (2 * n + j) + 6 * aF n j * Meijer5255.QGA.Pfq54.harm 4 (2 * n + j) := by
  rw [Finsupp.finsetSum_apply]
  simp only [term_apply, floor_eq, harm_eq]
  rw [sum_range_four _ _ (by omega) (fun r hr => by
    rw [pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) r (by omega), ite_eq_right (by omega)]; ring)]
  rw [pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) 1 le_rfl, pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) 2
    (by norm_num), pfCoeff_rfDeriv_Fn n _ (mem_Tn n j hj) 3 (by norm_num)]
  simp only [cD, cF, pfCoeff_Fn_two, pfCoeff_Fn_one, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_zero]
  norm_num
  first | (left; ring) | ring1 | simp

/-! ### The readouts as sums of the Laurent coefficients
(pfq54 `Lfun_Fn_three`, `Lfun_Fn_zero`, `Mfun_Fn_zero`, with `Qa`, `P3a`, `P4a` replaced by their
expansions in `aF`, `bF`.) -/

theorem Lfun_Fn_three (n : ℕ) :
    Lfun (2 * n) (Fn n) 3 = 2 * ∑ j ∈ range (17 * n + 1), aF n j := by
  rw [Lfun_Fn_eq, Finsupp.finsetSum_apply, Tn, Finset.sum_image (Tn_inj n), Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => inner_three n j

theorem Lfun_Fn_zero (n : ℕ) : Lfun (2 * n) (Fn n) 0 = -2 * ∑ j ∈ range (17 * n + 1),
    (aF n j * Meijer5255.QGA.Pfq54.harm 3 (j + 2 * n) +
      bF n j * Meijer5255.QGA.Pfq54.harm 2 (j + 2 * n) / 2) := by
  rw [Lfun_Fn_eq, Finsupp.finsetSum_apply, Tn, Finset.sum_image (Tn_inj n), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_zero, add_comm j]
  ring

theorem Mfun_Fn_zero (n : ℕ) : Mfun (2 * n) (Fn n) 0 = -6 * ∑ j ∈ range (17 * n + 1),
    (aF n j * Meijer5255.QGA.Pfq54.harm 4 (j + 2 * n) +
      bF n j * Meijer5255.QGA.Pfq54.harm 3 (j + 2 * n) / 3) := by
  rw [Mfun, Finsupp.neg_apply, Lfun_dFn_eq, Finsupp.finsetSum_apply, Tn,
    Finset.sum_image (Tn_inj n), Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dinner_zero n j (Finset.mem_range.mp hj), add_comm j]
  ring

end Meijer5255.QGA.Pfq54.PF
