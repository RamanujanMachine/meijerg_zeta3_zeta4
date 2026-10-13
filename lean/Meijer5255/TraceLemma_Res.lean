/-
# Helper for `TraceLemma.lean`: residue sums of rational functions with integer poles

Products `∏_{s ∈ S} (X - s)^{n_s}` over `ℚ` (value and logarithmic derivative off the nodes),
Lagrange interpolation at the nodes `S`, and the two residue-sum identities used for (RI):
* `res_sum_simple`: `∑_{k ∈ S} Q(k)/∏_{j ≠ k}(k - j) = 0` if `deg Q ≤ |S| - 2`;
* `res_sum_double`: the residue sum of `Q/((X - s)² H_S)` vanishes if `deg Q < |S|`, `s ∉ S`.
Generic; imported only by `TraceLemma*.lean`.
-/
import Meijer5255.definitions

open Finset Polynomial

noncomputable section

namespace Meijer5255.TraceAux

/-- `∏_{s ∈ S} (X - s)^{n_s}` over `ℚ`. -/
def rp (S : Finset ℤ) (n : ℤ → ℕ) : ℚ[X] := ∏ s ∈ S, (X - C (s : ℚ)) ^ n s

/-- `H_{S,k} = ∏_{j ∈ S, j ≠ k} (X - j)`. -/
def Hk (S : Finset ℤ) (k : ℤ) : ℚ[X] := ∏ j ∈ S.erase k, (X - C (j : ℚ))

/-- `W_{S,k} = ∏_{j ∈ S, j ≠ k} (k - j) = H_{S,k}(k)`. -/
def Wk (S : Finset ℤ) (k : ℤ) : ℚ := ∏ j ∈ S.erase k, ((k : ℚ) - j)

theorem rp_eval (S : Finset ℤ) (n : ℤ → ℕ) (x : ℚ) :
    (rp S n).eval x = ∏ s ∈ S, (x - s) ^ n s := by
  simp [rp, eval_prod]

theorem rp_natDegree (S : Finset ℤ) (n : ℤ → ℕ) : (rp S n).natDegree = ∑ s ∈ S, n s := by
  rw [rp, natDegree_prod_of_monic _ _ (fun s _ => (monic_X_sub_C _).pow _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]

/-- Logarithmic derivative of `∏ (X - s)^{n_s}` off the nodes. -/
theorem rp_deriv_eval (S : Finset ℤ) (n : ℤ → ℕ) (x : ℚ) (hx : ∀ s ∈ S, x ≠ s) :
    (derivative (rp S n)).eval x = (rp S n).eval x * ∑ s ∈ S, (n s : ℚ) / (x - s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rp]
  | insert a S ha ih =>
    have ih' := ih (fun s hs => hx s (Finset.mem_insert_of_mem hs))
    have hxa : x - a ≠ 0 := sub_ne_zero.2 (hx a (Finset.mem_insert_self a S))
    have e : rp (insert a S) n = (X - C (a : ℚ)) ^ n a * rp S n := by
      simp [rp, Finset.prod_insert ha]
    rw [e, derivative_mul, eval_add, eval_mul, eval_mul, ih', Finset.sum_insert ha, eval_mul,
      derivative_X_sub_C_pow]
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    rcases Nat.eq_zero_or_pos (n a) with h0 | hpos
    · simp [h0]
    · obtain ⟨m, hm⟩ : ∃ m, n a = m + 1 := ⟨n a - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel, pow_succ]
      field_simp

theorem Hk_eval_self (S : Finset ℤ) (k : ℤ) : (Hk S k).eval (k : ℚ) = Wk S k := by
  simp [Hk, Wk, eval_prod]

theorem Hk_eval_other (S : Finset ℤ) {k m : ℤ} (hm : m ∈ S) (hmk : m ≠ k) :
    (Hk S k).eval (m : ℚ) = 0 := by
  rw [Hk, eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hmk, hm⟩) (by simp)

theorem Hk_monic (S : Finset ℤ) (k : ℤ) : (Hk S k).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem Hk_natDegree (S : Finset ℤ) (k : ℤ) : (Hk S k).natDegree = (S.erase k).card := by
  rw [Hk, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

theorem Wk_ne_zero (S : Finset ℤ) (k : ℤ) : Wk S k ≠ 0 := by
  rw [Wk, Finset.prod_ne_zero_iff]
  intro j hj
  have : k ≠ j := (Finset.ne_of_mem_erase hj).symm
  exact sub_ne_zero.2 (by exact_mod_cast this)

/-- **Lagrange interpolation** at the integer nodes `S`. -/
theorem lagrange (S : Finset ℤ) (Q : ℚ[X]) (hQ : Q.degree < S.card) :
    Q = ∑ k ∈ S, C (Q.eval (k : ℚ) / Wk S k) * Hk S k := by
  classical
  have hcard : (S.image (fun s : ℤ => (s : ℚ))).card = S.card :=
    Finset.card_image_of_injective _ Int.cast_injective
  refine Polynomial.eq_of_degree_sub_lt_of_eval_finset_eq (S.image (fun s : ℤ => (s : ℚ))) ?_ ?_
  · rw [hcard, ← mem_degreeLT]
    refine Submodule.sub_mem _ (mem_degreeLT.2 hQ) (Submodule.sum_mem _ fun k hk => ?_)
    rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ (mem_degreeLT.2 ?_)
    rw [degree_eq_natDegree (Hk_monic S k).ne_zero, Hk_natDegree, Finset.card_erase_of_mem hk]
    have : 0 < S.card := Finset.card_pos.2 ⟨k, hk⟩
    exact_mod_cast Nat.sub_lt this one_pos
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hx
    rw [eval_finsetSum, Finset.sum_eq_single m]
    · rw [eval_mul, eval_C, Hk_eval_self, div_mul_cancel₀ _ (Wk_ne_zero S m)]
    · intro k _ hkm
      rw [eval_mul, Hk_eval_other S hm (Ne.symm hkm), mul_zero]
    · intro h; exact absurd hm h

/-- **Simple residues.** `∑_{k ∈ S} Q(k)/W_{S,k} = 0` if `deg Q + 2 ≤ |S|`. -/
theorem res_sum_simple (S : Finset ℤ) (Q : ℚ[X]) (hQ : Q.natDegree + 2 ≤ S.card) :
    ∑ k ∈ S, Q.eval (k : ℚ) / Wk S k = 0 := by
  have hdeg : Q.degree < S.card := by
    refine (degree_le_natDegree).trans_lt ?_
    exact_mod_cast (by omega : Q.natDegree < S.card)
  have h := congrArg (fun P : ℚ[X] => P.coeff (S.card - 1)) (lagrange S Q hdeg)
  simp only [finsetSum_coeff, coeff_C_mul] at h
  rw [coeff_eq_zero_of_natDegree_lt (by omega)] at h
  rw [h]
  refine Finset.sum_congr rfl fun k hk => ?_
  have := (Hk_monic S k).coeff_natDegree
  rw [Hk_natDegree, Finset.card_erase_of_mem hk] at this
  rw [this, mul_one]

/-- `Q' H - Q H' = -∑ c_k H_k²` for the Lagrange form. -/
theorem wronskian_lagrange (S : Finset ℤ) (Q : ℚ[X]) (hQ : Q.degree < S.card) :
    derivative Q * (∏ j ∈ S, (X - C (j : ℚ))) - Q * derivative (∏ j ∈ S, (X - C (j : ℚ))) =
      -∑ k ∈ S, C (Q.eval (k : ℚ) / Wk S k) * Hk S k ^ 2 := by
  conv_lhs => rw [lagrange S Q hQ]
  rw [derivative_sum, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.mul_prod_erase S _ hk]
  simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_X_sub_C, one_mul]
  rw [show ∏ j ∈ S.erase k, (X - C (j : ℚ)) = Hk S k from rfl]
  ring

/-- **Residues with one double pole.** For `s ∉ S` and `deg Q < |S|`, the residues of
`Q / ((X - s)² H_S)` at the nodes of `S` add up to minus the residue at `s`. -/
theorem res_sum_double (S : Finset ℤ) (s : ℤ) (hs : s ∉ S) (Q : ℚ[X]) (hQ : Q.degree < S.card) :
    ∑ k ∈ S, Q.eval (k : ℚ) / (Wk S k * ((k : ℚ) - s) ^ 2) =
      -((derivative Q).eval (s : ℚ) * (∏ j ∈ S, ((s : ℚ) - j)) -
          Q.eval (s : ℚ) * (derivative (∏ j ∈ S, (X - C (j : ℚ)))).eval (s : ℚ)) /
        (∏ j ∈ S, ((s : ℚ) - j)) ^ 2 := by
  have hH : (∏ j ∈ S, ((s : ℚ) - j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.2 (by exact_mod_cast (fun h : s = j => hs (h ▸ hj)))
  have hw := congrArg (fun P : ℚ[X] => P.eval (s : ℚ)) (wronskian_lagrange S Q hQ)
  simp only [eval_sub, eval_mul, eval_prod, eval_neg, eval_finsetSum, eval_C, eval_pow,
    eval_X] at hw
  rw [hw, neg_neg, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hks : (k : ℚ) - s ≠ 0 := sub_ne_zero.2 (by exact_mod_cast fun h : k = s => hs (h ▸ hk))
  have hsplit : ∏ j ∈ S, ((s : ℚ) - j) = ((s : ℚ) - k) * (Hk S k).eval (s : ℚ) := by
    rw [← Finset.mul_prod_erase S _ hk, Hk, eval_prod]; simp
  rw [hsplit]
  have hsk : (s : ℚ) - k ≠ 0 := by intro h; apply hks; linarith
  have hHk : (Hk S k).eval (s : ℚ) ≠ 0 := by
    intro h; rw [hsplit, h, mul_zero] at hH; exact hH rfl
  field_simp
  ring

/-- The node terms `Q(k)/W_{S,k}` of `Q = ∏ (X - t)^{n_t}`: `∏_{t ≠ k} (k - t)^{n_t - 1}` if
`n_k = 0`, and `0` otherwise. -/
theorem rp_eval_div_Wk (S : Finset ℤ) (n : ℤ → ℕ) {k : ℤ} (hk : k ∈ S) :
    (rp S n).eval (k : ℚ) / Wk S k =
      if n k = 0 then ∏ t ∈ S.erase k, ((k : ℚ) - t) ^ ((n t : ℤ) - 1) else 0 := by
  rw [rp_eval, ← Finset.mul_prod_erase S _ hk, sub_self]
  split_ifs with h0
  · rw [h0, pow_zero, one_mul, Wk, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    have hne : (k : ℚ) - t ≠ 0 :=
      sub_ne_zero.2 (by exact_mod_cast (Finset.ne_of_mem_erase ht).symm)
    rw [zpow_sub_one₀ hne, zpow_natCast, div_eq_mul_inv]
  · rw [zero_pow h0, zero_mul, zero_div]

end Meijer5255.TraceAux
