-- Copied from ../zetas_irr/pfq54_formalization_handoff/star_aux.lean, lines 1-227 (zetas_irr
-- commit d9d5223), for the analytic input of `Meijer5255.QGrowth` / `Meijer5255.LinformError`.
-- Changes: imports renamed (`pf_aux` -> `QGrowth_PF`, `pairing_identity` ->
-- `QGrowth_pairing_identity`), namespaces `Pfq54`, `ZetasIrr` prefixed with `Meijer5255.QGA`;
-- the readout corollaries `sum_q_hv`, `sum_p3_hv`, `sum_p4_hv` and the scalar part (`Rsc`, `kinv`,
-- `star`, which need pfq54's `Qa`, `E`, `T`) are omitted.
import Meijer5255.QGrowth_PF
import Meijer5255.QGrowth_pairing_identity

open Polynomial Finset
open scoped RatFunc Matrix

noncomputable section

namespace Meijer5255.QGA.Pfq54.ST

open Meijer5255.QGA.Pfq54 Meijer5255.QGA.Pfq54.RA Meijer5255.QGA.Pfq54.PF Meijer5255.QGA.ZetasIrr Meijer5255.QGA.ZetasIrr.CMF

/-! ### The parameter point of `F_n` and its companion relation -/

def wpt (n : ℕ) : Pt :=
  ⟨![-11 * (n : ℤ), -12 * (n : ℤ), 1 + 17 * (n : ℤ), 1 + 16 * (n : ℤ), -10 * (n : ℤ)],
   ![0, -(n : ℤ), -2 * (n : ℤ), (n : ℤ), 2 * (n : ℤ)]⟩

theorem wpt_a (n : ℕ) : (wpt n).a =
    ![-11 * (n : ℤ), -12 * (n : ℤ), 1 + 17 * (n : ℤ), 1 + 16 * (n : ℤ), -10 * (n : ℤ)] := rfl
theorem wpt_b (n : ℕ) : (wpt n).b = ![0, -(n : ℤ), -2 * (n : ℤ), (n : ℤ), 2 * (n : ℤ)] := rfl

theorem Zk_wpt (n : ℕ) : Zk (wpt n) = nR n := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Zk, wpt_a, wpt_b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Multiset.count_add, count_ival, nR, count_Icc]
  split_ifs <;> omega

theorem Pk_wpt (n : ℕ) : Pk (wpt n) = dR n := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Pk, wpt_a, wpt_b, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Multiset.count_add, count_ival, dR, count_Icc]
  split_ifs <;> omega

theorem wpt_ker (n : ℕ) : (wpt n).ker = Fn n := by
  rw [ker_eq_lin, Zk_wpt, Pk_wpt, Fn]

theorem VC_wpt (n ord : ℕ) (hord : ord ≤ 3) : VC ord (2 * n) (wpt n) := by
  refine ⟨fun q hq => ?_, ?_⟩
  · rw [Pk_wpt] at hq
    simp only [dR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hq
    omega
  · rw [Pk_wpt, Zk_wpt, Multiset.count_add, bro, wpt_b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
      Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton, dR, nR,
      Multiset.count_add, count_Icc]
    split_ifs <;> omega

theorem companion_L (n : ℕ) :
    ∑ k : Fin 5, (wpt n).dc k • mom Lfun (2 * n) (Fn n) k = 0 := by
  have := companion_of_VC isMom_Lfun (2 * n) (wpt n) (VC_wpt n 2 (by norm_num))
  rwa [wpt_ker] at this

theorem companion_M (n : ℕ) :
    ∑ k : Fin 5, (wpt n).dc k • mom Mfun (2 * n) (Fn n) k = 0 := by
  have := companion_of_VC isMom_Mfun (2 * n) (wpt n) (VC_wpt n 3 le_rfl)
  rwa [wpt_ker] at this

theorem dc4_wpt (n : ℕ) : (wpt n).dc 4 = 3 := by
  rw [Pt.dc, dc_four, wpt_a, wpt_b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  ring

/-! ### The dual kernel of `p_n` is `(t - 10n - 1) F_n(t)` -/

theorem Zk_dual (n : ℕ) : Zk (pN n).dual = ((10 * n + 1 : ℤ) ::ₘ nR n) := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Zk, Pt.dual_a, Pt.dual_b, pN_a, pN_b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Multiset.count_add, count_ival, nR, count_Icc, Multiset.count_cons]
  split_ifs <;> omega

theorem Pk_dual (n : ℕ) : Pk (pN n).dual = dR n := by
  refine Multiset.ext.mpr fun k => ?_
  simp only [Pk, Pt.dual_a, Pt.dual_b, pN_a, pN_b, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Multiset.count_add, count_ival, dR, count_Icc]
  split_ifs <;> omega

theorem dker_eq (n : ℕ) :
    (pN n).dual.ker = (RatFunc.X - RatFunc.C ((10 * n + 1 : ℤ) : ℚ)) * Fn n := by
  rw [ker_eq_lin, Zk_dual, Pk_dual, lin_cons_left, Fn]

/-! ### Monomial terms and the cutoff move -/

def mt (n r : ℕ) : ℚ⟮X⟯ := (-RatFunc.X) ^ r * (pN n).dual.ker

theorem mt_eq_lin (n r : ℕ) : mt n r = RatFunc.C ((-1 : ℚ) ^ r) *
    lin (Multiset.replicate r 0 + ((10 * n + 1 : ℤ) ::ₘ nR n)) (dR n) := by
  rw [mt, dker_eq, Fn, ← lin_cons_left, negX_pow_mul_lin]

theorem Lfun_cut_many (Z P : Multiset ℤ) (K : ℤ) (m : ℕ) (hP : ∀ p ∈ P, p ≤ K)
    (hZ : ∀ k : ℤ, K ≤ k → k < K + m → 2 ≤ Z.count (k + 1)) :
    Lfun (K + m) (lin Z P) = Lfun K (lin Z P) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, Lfun_cut (K + m) Z P
      (fun p hp => (hP p hp).trans (by omega)) (hZ (K + m) (by omega) (by push_cast; omega)),
      ih (fun k hk1 hk2 => hZ k hk1 (by push_cast at hk2 ⊢; omega))]

theorem Lfun_mt_cut (n r : ℕ) : Lfun (2 * n) (mt n r) = Lfun n (mt n r) := by
  rw [mt_eq_lin, Aux.Lfun_C_mul, Aux.Lfun_C_mul]
  congr 1
  rw [show (2 * n : ℤ) = (n : ℤ) + (n : ℕ) by push_cast; ring]
  refine Lfun_cut_many _ _ _ _ (fun p hp => ?_) (fun k hk1 hk2 => ?_)
  · simp only [dR, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hp
    omega
  · simp only [Multiset.count_add, Multiset.count_replicate, Multiset.count_cons, nR, count_Icc]
    split_ifs <;> omega

/-! ### The weighted readouts -/

def hv (n : ℕ) : Fin 3 → ℚ := ![1, 10 * (n : ℚ) + 1, (10 * (n : ℚ) + 1) ^ 2]

def Del (n : ℕ) : ℚ := ∏ j ∈ Icc (8 : ℕ) 12, ((j : ℚ) * n + 1)

theorem Del_pos (n : ℕ) : 0 < Del n := by unfold Del; positivity

def Jq (n : ℕ) (j : Fin 3) (r : Fin 4) : ℚ := (Jmat n (Fin.castSucc j) r : ℚ)

def Wj (n : ℕ) (j : Fin 3) : ℚ⟮X⟯ := ∑ r : Fin 4, RatFunc.C (Jq n j r) * mt n r

def W (n : ℕ) : ℚ⟮X⟯ := ∑ j : Fin 3, RatFunc.C (hv n j) * Wj n j

theorem Qmul_eq' (n : ℕ) (j : Fin 3) :
    algebraMap ℚ[X] ℚ⟮X⟯ (Qpoly n j) * RkerStar n =
      RatFunc.laurent ((12 * (n : ℤ) + 1 : ℤ) : ℚ) (Wj n j) := by
  rw [Qmul_eq, Wj]
  rfl

theorem identity_L (n : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ n * 3) • Lfun n (Wj n j) = q n j • Zsym 3 - p3 n j • Zsym 0 := by
  have h := dual_first_identity' n j
  rwa [Qmul_eq', Aux.Lfun_laurent, show (-11 * (n : ℤ) - 1 + (12 * n + 1)) = n by ring] at h

theorem identity_M (n : ℕ) (j : Fin 3) :
    ((-1 : ℚ) ^ n) • Mfun (2 * n) (Wj n j) = q n j • Zsym 4 - p4 n j • Zsym 0 := by
  have h := BP.pairing_identity n j
  rwa [Qmul_eq', Aux.Mfun_laurent, show (-10 * (n : ℤ) - 1 + (12 * n + 1)) = 2 * n by ring] at h

theorem Lfun_Wj_cut (n : ℕ) (j : Fin 3) : Lfun (2 * n) (Wj n j) = Lfun n (Wj n j) := by
  rw [Wj, isMom_Lfun.sum, isMom_Lfun.sum]
  exact Finset.sum_congr rfl fun r _ => by rw [Lfun_mt_cut]

theorem weighted_L (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 3 - p3 n j • Zsym 0) =
      ((-1 : ℚ) ^ n * 3) • Lfun (2 * n) (W n) := by
  rw [W, isMom_Lfun.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Lfun_Wj_cut, ← identity_L, smul_comm]

theorem weighted_M (n : ℕ) :
    ∑ j : Fin 3, hv n j • (q n j • Zsym 4 - p4 n j • Zsym 0) =
      ((-1 : ℚ) ^ n) • Mfun (2 * n) (W n) := by
  rw [W, isMom_Mfun.sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← identity_M, smul_comm]

/-! ### Reduction of the weight modulo the companion relation -/

theorem Phi_mt {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (n r : ℕ) :
    Φ (2 * n) (mt n r) =
      -mom Φ (2 * n) (Fn n) (r + 1) - (10 * (n : ℚ) + 1) • mom Φ (2 * n) (Fn n) r := by
  have h : mt n r = RatFunc.C (-1) * ((-RatFunc.X) ^ (r + 1) * Fn n) +
      RatFunc.C (-(10 * (n : ℚ) + 1)) * ((-RatFunc.X) ^ r * Fn n) := by
    rw [mt, dker_eq]
    push_cast
    simp only [map_neg, map_one, map_add, map_mul, map_natCast]
    ring
  rw [h, hΦ.add, hΦ.C_mul, hΦ.C_mul, neg_one_smul, neg_smul, sub_eq_add_neg]
  rfl

theorem Phi_W {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (n : ℕ) :
    Φ (2 * n) (W n) = ∑ j : Fin 3, hv n j • ∑ r : Fin 4, Jq n j r • Φ (2 * n) (mt n r) := by
  rw [W, hΦ.sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Wj, hΦ.sum]

theorem mom_zero_eq {Φ : ℤ → ℚ⟮X⟯ → FormalZ} (K : ℤ) (f : ℚ⟮X⟯) : Φ K f = mom Φ K f 0 := by
  rw [mom, pow_zero, one_mul]

theorem W_reduce {Φ : ℤ → ℚ⟮X⟯ → FormalZ} {ord : ℕ} (hΦ : IsMom Φ ord) (n : ℕ)
    (hcomp : ∑ k : Fin 5, (wpt n).dc k • mom Φ (2 * n) (Fn n) k = 0) :
    Φ (2 * n) (W n) = Del n • Φ (2 * n) (Fn n) := by
  set m := mom Φ (2 * n) (Fn n) with hm
  rw [Fin.sum_univ_five, dc4_wpt] at hcomp
  have h4 : m 4 = (-1 / 3 : ℚ) • ((wpt n).dc 0 • m 0 + (wpt n).dc 1 • m 1 +
      (wpt n).dc 2 • m 2 + (wpt n).dc 3 • m 3) := by
    have h3 : (3 : ℚ) • m 4 = -((wpt n).dc 0 • m 0 + (wpt n).dc 1 • m 1 +
        (wpt n).dc 2 • m 2 + (wpt n).dc 3 • m 3) := by
      rw [eq_neg_iff_add_eq_zero, ← hcomp]
      simp only [Fin.val_zero, Fin.val_one, Fin.val_two, fv3, fv4]
      abel
    rw [neg_div, neg_smul, ← smul_neg, ← h3, smul_smul]
    norm_num
  rw [Phi_W hΦ, mom_zero_eq (Φ := Φ) (2 * n) (Fn n), ← hm]
  simp only [Phi_mt hΦ, ← hm, Fin.sum_univ_three, Fin.sum_univ_four, Fin.val_zero, Fin.val_one,
    Fin.val_two, show ((3 : Fin 4) : ℕ) = 3 from rfl, zero_add]
  rw [h4]
  simp only [Jq, Jmat, hv, Pt.dc, dc, e1, e2, e3, e4, e5, al, bq, wpt_a, wpt_b, Del,
    Aux.prod_Icc_8_12, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, Fin.castSucc_zero, Fin.castSucc_one,
    show Fin.castSucc (2 : Fin 3) = (2 : Fin 4) from rfl, Matrix.cons_val']
  push_cast
  module

/-! ### Extracting the coefficients -/

theorem sum_apply (c u v : Fin 3 → ℚ) (a k : ℕ) :
    (∑ j : Fin 3, c j • (u j • Zsym a - v j • Zsym 0)) k =
      ∑ j : Fin 3, c j * (u j * (if a = k then 1 else 0) - v j * (if 0 = k then 1 else 0)) := by
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finsupp.smul_apply, Finsupp.sub_apply, Zsym, Finsupp.single_apply, smul_eq_mul]

theorem Lfun_W (n : ℕ) : Lfun (2 * n) (W n) = Del n • Lfun (2 * n) (Fn n) :=
  W_reduce isMom_Lfun n (companion_L n)

theorem Mfun_W (n : ℕ) : Mfun (2 * n) (W n) = Del n • Mfun (2 * n) (Fn n) :=
  W_reduce isMom_Mfun n (companion_M n)

end Meijer5255.QGA.Pfq54.ST
