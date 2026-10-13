/-
# Helper for `WindowReadout.lean`: the sum of residues of a proper rational function

For a polynomial `P` and a pole multiset `Dr` (multiplicities `≤ 2`) with
`deg P ≤ |Dr| - 2`, the residues of `P / rootPoly Dr` sum to zero:
`∑_{x ∈ Dr} resB P Dr x = 0`, where `resA, resB` are the double/simple-pole coefficients
(the same formulas as `pfCoeff`). Proof: Hermite interpolation
`P = ∑_x (resA·E_x + resB·G_x)` (`E_x = D/(X-x)^{e_x}`, `G_x = D/(X-x)`), checked by
divisibility by the coprime factors `(X-x)^{e_x}` and a degree count; then compare the
coefficients of `X^{|Dr|-1}`.
-/
import Meijer5255.definitions

open Polynomial Finset

noncomputable section

namespace Meijer5255.WindowReadout

open Meijer5255

/-! ### `rootPoly` basics -/

theorem rootPoly_eq (s : Multiset ℤ) :
    rootPoly s = (s.map fun z : ℤ => X - C (z : ℚ)).prod := by
  unfold rootPoly
  simp [Multiset.map_map]

theorem rootPoly_add (s t : Multiset ℤ) : rootPoly (s + t) = rootPoly s * rootPoly t := by
  simp [rootPoly_eq, Multiset.map_add, Multiset.prod_add]

theorem rootPoly_replicate (e : ℕ) (a : ℤ) :
    rootPoly (Multiset.replicate e a) = (X - C (a : ℚ)) ^ e := by
  simp [rootPoly_eq, Multiset.map_replicate, Multiset.prod_replicate]

theorem rootPoly_cons (a : ℤ) (s : Multiset ℤ) :
    rootPoly (a ::ₘ s) = (X - C (a : ℚ)) * rootPoly s := by
  simp [rootPoly_eq]

theorem rootPoly_monic (s : Multiset ℤ) : (rootPoly s).Monic := by
  rw [rootPoly_eq]
  exact monic_multiset_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem natDegree_rootPoly (s : Multiset ℤ) : (rootPoly s).natDegree = Multiset.card s := by
  rw [rootPoly_eq, natDegree_multiset_prod_of_monic _ fun f hf => ?_]
  · rw [Multiset.map_map]
    have : ∀ z : ℤ, ((fun f : ℚ[X] => f.natDegree) ∘ fun z : ℤ => X - C (z : ℚ)) z = 1 :=
      fun z => natDegree_X_sub_C _
    rw [Multiset.map_congr rfl fun z _ => this z]
    simp
  · obtain ⟨z, -, rfl⟩ := Multiset.mem_map.1 hf
    exact monic_X_sub_C _

theorem rootPoly_dvd {s t : Multiset ℤ} (h : s ≤ t) : rootPoly s ∣ rootPoly t := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.1 h
  rw [rootPoly_add]
  exact dvd_mul_right _ _

theorem eval_rootPoly (s : Multiset ℤ) (x : ℚ) :
    (rootPoly s).eval x = (s.map fun z : ℤ => x - (z : ℚ)).prod := by
  simp [rootPoly_eq, eval_multiset_prod, Multiset.map_map]

theorem eval_rootPoly_ne_zero (s : Multiset ℤ) (x : ℤ) (hx : x ∉ s) :
    (rootPoly s).eval (x : ℚ) ≠ 0 := by
  rw [eval_rootPoly]
  intro h
  rw [Multiset.prod_eq_zero_iff] at h
  obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.1 h
  have : x = z := by exact_mod_cast (sub_eq_zero.1 hz0)
  subst this
  exact hx hz

/-- `(X - a)² ∣ Q` from `Q(a) = Q'(a) = 0`. -/
theorem sq_dvd_of_eval (Q : ℚ[X]) (a : ℚ) (h0 : Q.eval a = 0)
    (h1 : (derivative Q).eval a = 0) : (X - C a) ^ 2 ∣ Q := by
  obtain ⟨Q1, rfl⟩ := dvd_iff_isRoot.2 h0
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at h1
  obtain ⟨Q2, rfl⟩ := dvd_iff_isRoot.2 h1
  exact ⟨Q2, by ring⟩

/-! ### Residues -/

/-- `E_x = ∏_{y ∈ Dr, y ≠ x} (X - y)`. -/
def resE (Dr : Multiset ℤ) (x : ℤ) : ℚ[X] := rootPoly (Dr.filter (· ≠ x))

/-- The double-pole coefficient of `P / rootPoly Dr` at `x`. -/
def resA (P : ℚ[X]) (Dr : Multiset ℤ) (x : ℤ) : ℚ :=
  if Dr.count x = 2 then P.eval (x : ℚ) / (resE Dr x).eval (x : ℚ) else 0

/-- The simple-pole coefficient (residue) of `P / rootPoly Dr` at `x`. -/
def resB (P : ℚ[X]) (Dr : Multiset ℤ) (x : ℤ) : ℚ :=
  if Dr.count x = 2 then
    (derivative P * resE Dr x - P * derivative (resE Dr x)).eval (x : ℚ) /
      (resE Dr x).eval (x : ℚ) ^ 2
  else P.eval (x : ℚ) / (resE Dr x).eval (x : ℚ)

theorem pfCoeff_eq (Nr Dr : Multiset ℤ) (x : ℤ) (h1 : 1 ≤ Dr.count x) (h2 : Dr.count x ≤ 2) :
    pfCoeff Nr Dr x = (resA (rootPoly Nr) Dr x, resB (rootPoly Nr) Dr x) := by
  unfold pfCoeff resA resB resE
  by_cases h2' : Dr.count x = 2
  · simp [h2']
  · have h1' : Dr.count x = 1 := by omega
    simp [h1']

theorem not_mem_filter_ne (Dr : Multiset ℤ) (x : ℤ) : x ∉ Dr.filter (· ≠ x) := by
  simp

theorem card_filter_ne (Dr : Multiset ℤ) (x : ℤ) :
    Multiset.card (Dr.filter (· ≠ x)) + Dr.count x = Multiset.card Dr := by
  have h := Multiset.filter_add_not (· = x) Dr
  rw [Multiset.filter_eq'] at h
  conv_rhs => rw [← h]
  rw [Multiset.card_add, Multiset.card_replicate, add_comm]

/-- **Sum of residues.** -/
theorem residue_sum (P : ℚ[X]) (Dr : Multiset ℤ) (hc : ∀ x, Dr.count x ≤ 2)
    (hdeg : P.natDegree + 2 ≤ Multiset.card Dr) :
    ∑ x ∈ Dr.toFinset, resB P Dr x = 0 := by
  set S := Dr.toFinset with hS
  let G : ℤ → ℚ[X] := fun x => rootPoly (Dr.erase x)
  let term : ℤ → ℚ[X] := fun x => C (resA P Dr x) * resE Dr x + C (resB P Dr x) * G x
  have hcard_erase : ∀ x ∈ S, Multiset.card (Dr.erase x) + 1 = Multiset.card Dr := by
    intro x hx
    rw [Multiset.card_erase_of_mem (Multiset.mem_toFinset.1 hx)]
    exact Nat.succ_pred_eq_of_pos
      (Multiset.card_pos_iff_exists_mem.2 ⟨x, Multiset.mem_toFinset.1 hx⟩)
  -- `rootPoly Dr` is the product of the coprime prime powers `(X - x)^{e_x}`
  have hD : rootPoly Dr = ∏ x ∈ S, (X - C (x : ℚ)) ^ Dr.count x := by
    rw [rootPoly_eq]
    exact Finset.prod_multiset_map_count Dr (fun x : ℤ => X - C (x : ℚ))
  -- Hermite interpolation, checked locally at every pole
  have hloc : ∀ x ∈ S, (X - C (x : ℚ)) ^ Dr.count x ∣ P - ∑ y ∈ S, term y := by
    intro x hx
    have hxm : x ∈ Dr := Multiset.mem_toFinset.1 hx
    have hx1 : 1 ≤ Dr.count x := Multiset.one_le_count_iff_mem.2 hxm
    have hrest : (X - C (x : ℚ)) ^ Dr.count x ∣ ∑ y ∈ S.erase x, term y := by
      refine Finset.dvd_sum fun y hy => ?_
      have hyx : y ≠ x := Finset.ne_of_mem_erase hy
      rw [← rootPoly_replicate]
      refine dvd_add (dvd_mul_of_dvd_right (rootPoly_dvd ?_) _)
        (dvd_mul_of_dvd_right (rootPoly_dvd ?_) _)
      · rw [Multiset.le_iff_count]
        intro z
        by_cases hz : z = x
        · subst hz
          rw [Multiset.count_replicate_self,
            Multiset.count_filter_of_pos (p := (· ≠ y)) (show z ≠ y from hyx.symm)]
        · rw [Multiset.count_replicate]
          simp [Ne.symm hz]
      · rw [Multiset.le_iff_count]
        intro z
        by_cases hz : z = x
        · subst hz
          rw [Multiset.count_replicate_self, Multiset.count_erase_of_ne hyx.symm]
        · rw [Multiset.count_replicate]
          simp [Ne.symm hz]
    rw [← Finset.add_sum_erase S _ hx, ← sub_sub]
    refine dvd_sub ?_ hrest
    have hE0 : (resE Dr x).eval (x : ℚ) ≠ 0 :=
      eval_rootPoly_ne_zero _ _ (not_mem_filter_ne _ _)
    have hcx := hc x
    rcases (by omega : Dr.count x = 1 ∨ Dr.count x = 2) with h1 | h2
    · -- simple pole
      have hG : Dr.erase x = Dr.filter (· ≠ x) := by
        ext z
        by_cases hz : z = x
        · subst hz
          rw [Multiset.count_erase_self, h1, Multiset.count_eq_zero.2 (not_mem_filter_ne _ _)]
        · rw [Multiset.count_erase_of_ne hz,
            Multiset.count_filter_of_pos (p := (· ≠ x)) (show z ≠ x from hz)]
      rw [h1, pow_one, dvd_iff_isRoot]
      have h12 : Dr.count x ≠ 2 := by omega
      simp only [term, G, hG, IsRoot, resA, resB, h12, ite_false, eval_sub, eval_add, eval_mul,
        eval_C, zero_mul, zero_add]
      rw [← resE]
      field_simp
      ring
    · -- double pole
      have hG : Dr.erase x = x ::ₘ Dr.filter (· ≠ x) := by
        ext z
        by_cases hz : z = x
        · subst hz
          rw [Multiset.count_erase_self, h2, Multiset.count_cons_self,
            Multiset.count_eq_zero.2 (not_mem_filter_ne _ _)]
        · rw [Multiset.count_erase_of_ne hz, Multiset.count_cons_of_ne hz,
            Multiset.count_filter_of_pos (p := (· ≠ x)) (show z ≠ x from hz)]
      rw [h2]
      apply sq_dvd_of_eval
      · simp only [term, G, hG, rootPoly_cons, resA, resB, h2, ite_true, eval_sub, eval_add,
          eval_mul, eval_C, eval_X, sub_self, zero_mul, mul_zero, add_zero]
        field_simp
        ring
      · simp only [term, G, hG, rootPoly_cons, resA, resB, h2, ite_true, derivative_sub,
          derivative_add, derivative_mul, derivative_C, derivative_X, zero_mul, zero_add,
          sub_zero, one_mul, eval_sub, eval_add, eval_mul, eval_C, eval_X, sub_self,
          add_zero]
        try rw [← resE]
        field_simp
        ring
  -- hence `P = ∑ term` (degree count)
  have hR : P - ∑ y ∈ S, term y = 0 := by
    have hdvd : rootPoly Dr ∣ P - ∑ y ∈ S, term y := by
      rw [hD]
      refine Finset.prod_dvd_of_coprime ?_ hloc
      intro a _ b _ hab
      exact (isCoprime_X_sub_C_of_isUnit_sub
        (isUnit_iff_ne_zero.2 (sub_ne_zero.2 (by exact_mod_cast hab)))).pow
    apply eq_zero_of_dvd_of_natDegree_lt hdvd
    rw [natDegree_rootPoly]
    have hT : (∑ y ∈ S, term y).natDegree ≤ Multiset.card Dr - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun y hy => ?_
      have hy1 : 1 ≤ Dr.count y :=
        Multiset.one_le_count_iff_mem.2 (Multiset.mem_toFinset.1 hy)
      have hEy := card_filter_ne Dr y
      have hGy := hcard_erase y hy
      refine natDegree_add_le_of_degree_le ((natDegree_C_mul_le _ _).trans ?_)
        ((natDegree_C_mul_le _ _).trans ?_)
      · rw [resE, natDegree_rootPoly]; omega
      · simp only [G]; rw [natDegree_rootPoly]; omega
    have := natDegree_sub_le P (∑ y ∈ S, term y)
    omega
  -- compare the coefficients of `X^{|Dr| - 1}`
  have hcoef := congrArg (fun Q => Q.coeff (Multiset.card Dr - 1)) hR
  simp only [coeff_sub, coeff_zero, finsetSum_coeff, term, coeff_add, coeff_C_mul] at hcoef
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_sub, neg_eq_zero] at hcoef
  rw [← hcoef]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hEy := card_filter_ne Dr y
  have hGy := hcard_erase y hy
  have hG1 : (G y).coeff (Multiset.card Dr - 1) = 1 := by
    have hm := rootPoly_monic (Dr.erase y)
    have hnd := natDegree_rootPoly (Dr.erase y)
    simp only [G]
    rw [show Multiset.card Dr - 1 = (rootPoly (Dr.erase y)).natDegree by omega]
    exact hm.coeff_natDegree
  have hA0 : resA P Dr y * (resE Dr y).coeff (Multiset.card Dr - 1) = 0 := by
    unfold resA
    split_ifs with h2
    · rw [coeff_eq_zero_of_natDegree_lt, mul_zero]
      rw [resE, natDegree_rootPoly]; omega
    · rw [zero_mul]
  rw [hA0, hG1, zero_add, mul_one]

/-- Residues of `Q · P / D` in terms of those of `P / D`. -/
theorem res_mul (Q P : ℚ[X]) (Dr : Multiset ℤ) (x : ℤ) :
    resA (Q * P) Dr x = Q.eval (x : ℚ) * resA P Dr x ∧
      resB (Q * P) Dr x =
        Q.eval (x : ℚ) * resB P Dr x + (derivative Q).eval (x : ℚ) * resA P Dr x := by
  have hE0 : (resE Dr x).eval (x : ℚ) ≠ 0 := eval_rootPoly_ne_zero _ _ (not_mem_filter_ne _ _)
  unfold resA resB
  split_ifs with h2
  · constructor
    · simp only [eval_mul]; ring
    · simp only [derivative_mul, eval_sub, eval_add, eval_mul]
      field_simp
      ring
  · constructor
    · ring
    · simp only [eval_mul]; ring

/-! ### Application to `F_n` -/

theorem card_numRoots (n : ℕ) : Multiset.card (numRoots n) = 30 * n := by
  simp only [numRoots, Multiset.card_add, Finset.card_val, Int.card_Icc]
  omega

theorem card_denRoots (n : ℕ) : Multiset.card (denRoots n) = 30 * n + 2 := by
  simp only [denRoots, Multiset.card_add, Finset.card_val, Int.card_Icc]
  omega

theorem denRoots_count_le (n : ℕ) (x : ℤ) : (denRoots n).count x ≤ 2 := by
  simp only [denRoots, Multiset.count_add]
  have h1 := Multiset.nodup_iff_count_le_one.1 (Icc (-(17 * n : ℤ)) (-(n : ℤ))).nodup x
  have h2 := Multiset.nodup_iff_count_le_one.1 (Icc (-(16 * n : ℤ)) (-(2 * n : ℤ))).nodup x
  omega

theorem mem_denRoots (n : ℕ) (x : ℤ) : x ∈ denRoots n ↔ -(17 * n : ℤ) ≤ x ∧ x ≤ -(n : ℤ) := by
  simp only [denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc]
  omega

theorem denRoots_toFinset (n : ℕ) :
    (denRoots n).toFinset = (Icc n (17 * n)).image (fun j : ℕ => -(j : ℤ)) := by
  ext x
  rw [Multiset.mem_toFinset, mem_denRoots, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(-x).toNat, Finset.mem_Icc.2 ⟨by omega, by omega⟩, by omega⟩
  · rintro ⟨j, hj, rfl⟩
    rw [Finset.mem_Icc] at hj
    omega

/-- The residue identity at a zero `m ∈ [2n+1, 10n]` of `F_n` (of order `3 ≥ k + 1`):
`∑_j (b_j/(-(j+m))^{k+1} - (k+1) a_j/(-(j+m))^{k+2}) = 0` (`k ≤ 2`). -/
theorem incr_gen (n m k : ℕ) (hk : k ≤ 2) (hm1 : 2 * n + 1 ≤ m) (hm2 : m ≤ 10 * n) :
    ∑ j ∈ Icc n (17 * n), (bCoef n j / (-(((j + m : ℕ) : ℚ))) ^ (k + 1) -
      (k + 1) * aCoef n j / (-(((j + m : ℕ) : ℚ))) ^ (k + 2)) = 0 := by
  set Nr := numRoots n
  set Dr := denRoots n
  have hcm : 3 ≤ Nr.count (m : ℤ) := by
    simp only [Nr, numRoots, Multiset.count_add]
    rw [Multiset.count_eq_one_of_mem (Finset.nodup _) (by simp; omega),
      Multiset.count_eq_one_of_mem (Finset.nodup _) (by simp; omega),
      Multiset.count_eq_one_of_mem (Finset.nodup _) (by simp; omega)]
  have hle : Multiset.replicate (k + 1) (m : ℤ) ≤ Nr := by
    rw [Multiset.le_iff_count]
    intro z
    rw [Multiset.count_replicate]
    split_ifs with h
    · subst h; omega
    · exact Nat.zero_le _
  obtain ⟨R, hR⟩ := Multiset.le_iff_exists_add.1 hle
  have hN : rootPoly Nr = (X - C ((m : ℤ) : ℚ)) ^ (k + 1) * rootPoly R := by
    rw [hR, rootPoly_add, rootPoly_replicate]
  have hdeg : (rootPoly R).natDegree + 2 ≤ Multiset.card Dr := by
    have h1 := congrArg Multiset.card hR
    rw [Multiset.card_add, Multiset.card_replicate] at h1
    rw [natDegree_rootPoly, card_denRoots]
    have : Multiset.card Nr = 30 * n := card_numRoots n
    omega
  have hsum := residue_sum (rootPoly R) Dr (denRoots_count_le n) hdeg
  rw [denRoots_toFinset, Finset.sum_image (fun a _ b _ h => by simpa using h)] at hsum
  rw [← hsum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_Icc.1 hj
  have hx : -(j : ℤ) ∈ Dr := (mem_denRoots n _).2 ⟨by omega, by omega⟩
  have hpf := pfCoeff_eq Nr Dr (-(j : ℤ)) (Multiset.one_le_count_iff_mem.2 hx)
    (denRoots_count_le n _)
  have ha : aCoef n j = resA (rootPoly Nr) Dr (-(j : ℤ)) := by
    unfold aCoef; rw [hpf]
  have hb : bCoef n j = resB (rootPoly Nr) Dr (-(j : ℤ)) := by
    unfold bCoef; rw [hpf]
  obtain ⟨hA, hB⟩ := res_mul ((X - C ((m : ℤ) : ℚ)) ^ (k + 1)) (rootPoly R) Dr (-(j : ℤ))
  rw [← hN] at hA hB
  rw [ha, hb, hA, hB]
  simp only [derivative_X_sub_C_pow, eval_pow, eval_mul, eval_sub, eval_X, eval_C,
    Nat.add_sub_cancel]
  have hd : (-(((j + m : ℕ) : ℚ))) = ((-(j : ℤ) : ℤ) : ℚ) - ((m : ℤ) : ℚ) := by
    push_cast; ring
  rw [hd]
  have hd0 : ((-(j : ℤ) : ℤ) : ℚ) - ((m : ℤ) : ℚ) ≠ 0 := by
    rw [← hd]
    have : (0 : ℚ) < ((j + m : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < j + m)
    linarith
  generalize ((-(j : ℤ) : ℤ) : ℚ) - ((m : ℤ) : ℚ) = d at hd0 ⊢
  push_cast
  field_simp
  ring

end Meijer5255.WindowReadout
