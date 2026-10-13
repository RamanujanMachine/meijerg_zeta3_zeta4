/-
# Helper lemmas for `BaselineIntegrality.lean` (sorry-free)

* `mul_choose_dvd_lcm`, `lcm_choose_div`: Kummer-type divisibility `k C(n,k) ∣ d_n` and the
  resulting integrality of `d_L C(N,M)/(N-s)` (adapted from pfq54 `Pfq54_aux.lean` and
  `Z_integral.lean`, `upperJet_integral`).
* `G a M = ∏_{t<M} (X - (a+1+t))`: value and derivative at `-j` (the binomial factors of `P`).
* `Qp S k = ∏_{l ∈ S \ {k}} (X + l)`: the Lagrange identity `∑_k ρ_c(k) Q_k = (15n)!` and its
  consequences at `-j` (`ρ_c(j) e = (15n)!`, `σ_c(j) e = (15n)!` off the support,
  `σ_c(j) e = -ρ_c(j) e'` on it).
* `denRoots` re-paired as `[n,16n] + [2n,17n]`, and `numRoots` as three `G`'s.
-/
import Meijer5255.definitions

open Finset Polynomial

noncomputable section

namespace Meijer5255.BaselineIntegrality.Aux

open Meijer5255

/-! ### Divisibility by `d_L` -/

theorem dlcm_mono {M L : ℕ} (h : M ≤ L) : dlcm M ∣ dlcm L :=
  Finset.lcm_mono (Finset.Icc_subset_Icc le_rfl h)

/-- `k · C(n,k)` divides `d_n` for `1 ≤ k ≤ n` (Kummer).
(Adapted from pfq54 `Pfq54_aux.lean`, `mul_choose_dvd_lcm`.) -/
theorem mul_choose_dvd_lcm {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    k * n.choose k ∣ dlcm n := by
  have hc := (Nat.choose_pos hkn).ne'
  rw [show dlcm n = Nat.lcmUpto n from rfl,
    ← Nat.factorization_prime_le_iff_dvd (Nat.mul_ne_zero (by omega) hc)
      (Nat.lcmUpto_ne_zero n)]
  intro p hp
  rw [Nat.factorization_lcmUpto n hp, Nat.factorization_mul (by omega) hc,
    Finsupp.add_apply]
  have hdisj : Disjoint {i ∈ Ico 1 (Nat.log p n).succ | p ^ i ≤ k % p ^ i + (n - k) % p ^ i}
      {i ∈ Ico 1 (Nat.log p n).succ | p ^ i ∣ k} := by
    simp +contextual [Finset.disjoint_right, Nat.dvd_iff_mod_eq_zero,
      Nat.mod_lt _ (pow_pos hp.pos _)]
  rw [Nat.factorization_choose hp hkn (Nat.lt_succ_self _),
    Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega)
      (lt_of_le_of_lt hkn (Nat.lt_pow_succ_log_self hp.one_lt n)),
    add_comm, ← card_union_of_disjoint hdisj, filter_union_right]
  exact (card_filter_le _ _).trans_eq (Nat.card_Ico _ _)

/-- `d_L C(N,M)/(N-s) ∈ ℕ` for `s < M ≤ N`, `M ≤ L`.
(Adapted from pfq54 `Z_integral.lean`, `upperJet_integral`.) -/
theorem lcm_choose_div (N M L s : ℕ) (hs : s < M) (hMN : M ≤ N) (hML : M ≤ L) :
    ∃ z : ℕ, (dlcm L : ℚ) * ((N.choose M : ℚ) / ((N - s : ℕ) : ℚ)) = z := by
  have h1 := Nat.choose_mul (n := N) (k := M) (s := s + 1) (by omega)
  have h2 := Nat.choose_succ_right_eq N s
  have hid : (s + 1) * M.choose (s + 1) * N.choose M =
      (N - s) * (N.choose s * (N - s - 1).choose (M - s - 1)) := by
    rw [show N - s - 1 = N - (s + 1) by omega, show M - s - 1 = M - (s + 1) by omega]
    calc (s + 1) * M.choose (s + 1) * N.choose M
        = (s + 1) * (N.choose M * M.choose (s + 1)) := by ring
      _ = (s + 1) * (N.choose (s + 1) * (N - (s + 1)).choose (M - (s + 1))) := by rw [h1]
      _ = (N.choose (s + 1) * (s + 1)) * (N - (s + 1)).choose (M - (s + 1)) := by ring
      _ = _ := by rw [h2]; ring
  obtain ⟨q, hq⟩ := (mul_choose_dvd_lcm (by omega) (by omega : s + 1 ≤ M)).trans
    (dlcm_mono hML)
  refine ⟨N.choose s * (N - s - 1).choose (M - s - 1) * q, ?_⟩
  have hNs : ((N - s : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hcast : (((s + 1) * M.choose (s + 1) : ℕ) : ℚ) * (N.choose M : ℚ) =
      ((N - s : ℕ) : ℚ) * ((N.choose s * (N - s - 1).choose (M - s - 1) : ℕ) : ℚ) := by
    exact_mod_cast hid
  rw [hq, Nat.cast_mul _ q]
  field_simp
  push_cast at hcast ⊢
  linear_combination (q : ℚ) * hcast

/-- `d_M^s H^{(s)}_m ∈ ℤ` for `m ≤ M`. (pfq54 `Z_integral.lean`, `harm_integral`, verbatim.) -/
theorem harm_int (s m M : ℕ) (h : m ≤ M) : ∃ z : ℤ, (dlcm M : ℚ) ^ s * harm s m = z := by
  set L := dlcm M
  have hdiv : ∀ k ∈ Icc 1 m, k ∣ L := fun k hk => by
    have : k ∈ Icc 1 M := by simp only [Finset.mem_Icc] at hk ⊢; omega
    exact Finset.dvd_lcm (f := id) this
  refine ⟨∑ k ∈ Icc 1 m, ((L / k : ℕ) : ℤ) ^ s, ?_⟩
  rw [harm, Finset.mul_sum]
  simp only [Int.cast_sum, Int.cast_pow, Int.cast_natCast]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (Finset.mem_Icc.mp hk).1; omega)
  rw [Nat.cast_div (hdiv k hk) hk0, div_pow, mul_one_div]

/-! ### The binomial factors `G a M = ∏_{t<M} (X - (a+1+t))` -/

/-- `G a M = ∏_{t<M} (X - (a+1+t))`, so that `G a M / M! = C(X - a - 1, M)`. -/
def G (a M : ℕ) : ℚ[X] := ∏ t ∈ range M, (X - C ((a : ℚ) + 1 + t))

theorem prod_range_neg (b M : ℕ) :
    ∏ t ∈ range M, (-((b : ℚ) + 1 + t)) = (-1) ^ M * (M.factorial * (b + M).choose M) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, ih]
    have h := Nat.add_one_mul_choose_eq (b + M) M
    have hq : ((b + M + 1 : ℕ) : ℚ) * ((b + M).choose M : ℚ) =
        ((b + M + 1).choose (M + 1) : ℚ) * ((M + 1 : ℕ) : ℚ) := by exact_mod_cast h
    rw [Nat.factorial_succ, show b + (M + 1) = b + M + 1 by ring]
    push_cast at hq ⊢
    linear_combination -(-1 : ℚ) ^ M * (M.factorial : ℚ) * hq

theorem G_eval (a M j : ℕ) :
    (G a M).eval (-(j : ℚ)) = (-1) ^ M * (M.factorial * (j + a + M).choose M) := by
  rw [G, eval_prod, ← prod_range_neg]
  refine prod_congr rfl fun t _ => ?_
  simp only [eval_sub, eval_X, eval_C]
  push_cast; ring

/-- Logarithmic derivative of a product of linear factors. -/
theorem deriv_prod_eval (c : ℕ → ℚ) (x : ℚ) (M : ℕ) (h : ∀ t < M, x ≠ c t) :
    (derivative (∏ t ∈ range M, (X - C (c t)))).eval x =
      (∏ t ∈ range M, (x - c t)) * ∑ t ∈ range M, 1 / (x - c t) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [prod_range_succ, derivative_mul, eval_add, eval_mul, eval_mul, ih fun t ht => h t (by omega),
      derivative_X_sub_C, eval_one, eval_sub, eval_X, eval_C, eval_prod, prod_range_succ,
      sum_range_succ]
    simp only [eval_sub, eval_X, eval_C]
    have hM : x - c M ≠ 0 := sub_ne_zero.mpr (h M (by omega))
    field_simp

theorem G_deriv_eval (a M j : ℕ) :
    (derivative (G a M)).eval (-(j : ℚ)) =
      -((-1) ^ M * (M.factorial * ∑ t ∈ range M,
        ((j + a + M).choose M : ℚ) / ((j + a + 1 + t : ℕ) : ℚ))) := by
  rw [G, deriv_prod_eval _ _ _ fun t _ h => by
    have : (0 : ℚ) < (j : ℚ) + a + 1 + t := by positivity
    linarith]
  have e := G_eval a M j
  rw [G, eval_prod] at e
  simp only [eval_sub, eval_X, eval_C] at e
  rw [e, mul_sum, mul_sum, mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun t _ => ?_
  have : ((j : ℚ) + a + 1 + t) ≠ 0 := by positivity
  rw [show (-(j : ℚ)) - ((a : ℚ) + 1 + t) = -((j : ℚ) + a + 1 + t) by ring]
  push_cast
  field_simp

/-- `d_L G'(-j) / M! ∈ ℤ` for `M ≤ L`. -/
theorem G_deriv_int (a M j L : ℕ) (hML : M ≤ L) :
    ∃ z : ℤ, (dlcm L : ℚ) * (derivative (G a M)).eval (-(j : ℚ)) = M.factorial * z := by
  have key : ∀ t ∈ range M, ∃ z : ℕ, (dlcm L : ℚ) *
      (((j + a + M).choose M : ℚ) / ((j + a + 1 + t : ℕ) : ℚ)) = z := fun t ht => by
    have ht := mem_range.mp ht
    obtain ⟨z, hz⟩ := lcm_choose_div (j + a + M) M L (M - 1 - t) (by omega) (by omega) hML
    rw [show j + a + M - (M - 1 - t) = j + a + 1 + t by omega] at hz
    exact ⟨z, hz⟩
  choose! f hf using key
  refine ⟨-((-1) ^ M * ∑ t ∈ range M, (f t : ℤ)), ?_⟩
  have hs : (dlcm L : ℚ) * ∑ t ∈ range M,
      (((j + a + M).choose M : ℚ) / ((j + a + 1 + t : ℕ) : ℚ)) = ∑ t ∈ range M, (f t : ℚ) := by
    rw [mul_sum]; exact sum_congr rfl hf
  rw [G_deriv_eval]
  push_cast
  push_cast at hs
  linear_combination (-(-1 : ℚ) ^ M * (M.factorial : ℚ)) * hs

/-! ### Root multisets as products -/

/-- `rootPoly` without the `Multiset ℤ → Multiset ℚ` coercion. -/
theorem rootPoly_eq (s : Multiset ℤ) : rootPoly s = (s.map fun x : ℤ => X - C (x : ℚ)).prod := by
  unfold rootPoly
  simp [Multiset.bind_singleton]

theorem rootPoly_add (s t : Multiset ℤ) : rootPoly (s + t) = rootPoly s * rootPoly t := by
  simp [rootPoly, Multiset.map_add, Multiset.prod_add]

theorem rootPoly_Icc (lo hi : ℤ) (a M : ℕ) (hlo : lo = a + 1) (hhi : hi = a + M) :
    rootPoly (Icc lo hi).val = G a M := by
  have hS : Icc lo hi = (range M).image fun t : ℕ => lo + t := by
    ext x
    simp only [mem_Icc, mem_image, mem_range]
    constructor
    · intro hx; exact ⟨(x - lo).toNat, by omega, by omega⟩
    · rintro ⟨t, ht, rfl⟩; omega
  have e : rootPoly (Icc lo hi).val = ∏ x ∈ Icc lo hi, (X - C (x : ℚ)) := by
    rw [rootPoly_eq, prod_eq_multiset_prod]
  rw [e, hS, prod_image fun x _ y _ h => by simpa using h, G]
  refine prod_congr rfl fun t _ => ?_
  rw [hlo]; push_cast; ring_nf


theorem rootPoly_numRoots (n : ℕ) :
    rootPoly (numRoots n) = G 0 (10 * n) * G n (10 * n) * G (2 * n) (10 * n) := by
  unfold numRoots
  rw [rootPoly_add, rootPoly_add, rootPoly_Icc _ _ 0 (10 * n) (by simp) (by push_cast; ring),
    rootPoly_Icc _ _ n (10 * n) rfl (by push_cast; ring),
    rootPoly_Icc _ _ (2 * n) (10 * n) (by push_cast; ring) (by push_cast; ring)]

/-! ### The products `∏_{l ∈ S \ {k}} (X + l)` over `S = [c, c+m]` -/

/-- Copy of the node file's `rho` (the node file proves `rho = rhoA` by `rfl`). -/
def rhoA (n c j : ℕ) : ℤ :=
  if c ≤ j ∧ j ≤ c + 15 * n then (-1) ^ (j - c) * ((15 * n).choose (j - c) : ℤ) else 0

/-- Copy of the node file's `sig` (the node file proves `sig = sigA` by `rfl`). -/
def sigA (n c j : ℕ) : ℚ :=
  ∑ k ∈ (Icc c (c + 15 * n)).erase j, (rhoA n c k : ℚ) / ((k : ℚ) - j)

/-- `Qp S k = ∏_{l ∈ S \ {k}} (X + l)`. -/
def Qp (S : Finset ℕ) (k : ℕ) : ℚ[X] := ∏ l ∈ S.erase k, (X + C (l : ℚ))

theorem Qp_eval (S : Finset ℕ) (k : ℕ) (x : ℚ) :
    (Qp S k).eval x = ∏ l ∈ S.erase k, (x + l) := by
  simp [Qp, eval_prod]

theorem Qp_eval_ne_zero (S : Finset ℕ) (j : ℕ) : (Qp S j).eval (-(j : ℚ)) ≠ 0 := by
  rw [Qp_eval, prod_ne_zero_iff]
  intro l hl
  have : l ≠ j := ne_of_mem_erase hl
  have : (l : ℚ) ≠ j := by exact_mod_cast this
  intro h; apply this; linarith

theorem prod_lower (i : ℕ) : ∏ t ∈ range i, ((t : ℚ) - i) = (-1) ^ i * i.factorial := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [prod_range_succ']
    have e : ∏ t ∈ range i, (((t + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) =
        ∏ t ∈ range i, ((t : ℚ) - i) := prod_congr rfl fun t _ => by push_cast; ring
    rw [e, ih, Nat.factorial_succ]
    push_cast; ring

/-- `∏_{k ∈ [c,c+m] \ {j}} (k - j) = (-1)^{j-c} (j-c)! (c+m-j)!`. -/
theorem e_formula (c j m : ℕ) (h1 : c ≤ j) (h2 : j ≤ c + m) :
    ∏ k ∈ (Icc c (c + m)).erase j, (-(j : ℚ) + k) =
      (-1) ^ (j - c) * ((j - c).factorial * (c + m - j).factorial) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = c + i := ⟨j - c, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, m = i + r := ⟨m - i, by omega⟩
  induction r with
  | zero =>
    rw [show c + (i + 0) = c + i by ring, Icc_erase_right, prod_Ico_eq_prod_range,
      show c + i - c = i by omega, show c + i - (c + i) = 0 by omega]
    have e : ∏ t ∈ range i, (-((c + i : ℕ) : ℚ) + ((c + t : ℕ) : ℚ)) =
        ∏ t ∈ range i, ((t : ℚ) - i) := prod_congr rfl fun t _ => by push_cast; ring
    rw [e, prod_lower]; simp
  | succ r ih =>
    rw [show c + (i + (r + 1)) = c + (i + r) + 1 by ring,
      ← insert_Icc_right_eq_Icc_add_one (by omega), erase_insert_of_ne (by omega),
      prod_insert (by simp), ih (by omega), show c + (i + r) + 1 - (c + i) = r + 1 by omega,
      show c + (i + r) - (c + i) = r by omega, Nat.factorial_succ]
    push_cast; ring

/-- `ρ_c(j) · ∏_{k ≠ j} (k - j) = (15n)!` for `j ∈ [c, c+15n]`. -/
theorem rho_mul_e (n c j : ℕ) (h1 : c ≤ j) (h2 : j ≤ c + 15 * n) :
    (rhoA n c j : ℚ) * ∏ k ∈ (Icc c (c + 15 * n)).erase j, (-(j : ℚ) + k) =
      ((15 * n).factorial : ℚ) := by
  rw [e_formula c j (15 * n) h1 h2, rhoA, ite_eq_left ⟨h1, h2⟩]
  have h := Nat.choose_mul_factorial_mul_factorial (n := 15 * n) (k := j - c) (by omega)
  rw [show 15 * n - (j - c) = c + 15 * n - j by omega] at h
  have hq : ((15 * n).choose (j - c) : ℚ) * (j - c).factorial * (c + 15 * n - j).factorial =
      (15 * n).factorial := by exact_mod_cast h
  push_cast
  rw [← hq]
  have : ((-1 : ℚ) ^ (j - c)) ^ 2 = 1 := by rw [← pow_mul]; exact Even.neg_one_pow ⟨j - c, by ring⟩
  linear_combination ((15 * n).choose (j - c) : ℚ) * (j - c).factorial *
    (c + 15 * n - j).factorial * this

/-- The Lagrange identity `∑_{k ∈ [c,c+15n]} ρ_c(k) Q_k = (15n)!` (interpolation of `1` at the
nodes `-k`). -/
theorem lagrange_id (n c : ℕ) :
    ∑ k ∈ Icc c (c + 15 * n), C (rhoA n c k : ℚ) * Qp (Icc c (c + 15 * n)) k =
      C ((15 * n).factorial : ℚ) := by
  set S := Icc c (c + 15 * n)
  have hsum := Lagrange.sum_basis (s := S) (v := fun k : ℕ => -(k : ℚ))
    (fun x _ y _ h => by simpa using h) ⟨c, by simp [S]⟩
  have hb : ∀ k ∈ S, Lagrange.basis S (fun k : ℕ => -(k : ℚ)) k =
      C ((rhoA n c k : ℚ) / ((15 * n).factorial : ℚ)) * Qp S k := fun k hk => by
    have hk' := mem_Icc.mp hk
    have he := rho_mul_e n c k hk'.1 hk'.2
    have hf : ((15 * n).factorial : ℚ) ≠ 0 := by positivity
    have hne : ∏ l ∈ S.erase k, (-(k : ℚ) + l) ≠ 0 := by
      have := Qp_eval_ne_zero S k; rwa [Qp_eval] at this
    rw [Lagrange.basis, Qp]
    simp only [Lagrange.basisDivisor]
    rw [prod_mul_distrib, ← map_prod]
    congr 1
    · congr 1
      have e : ∏ l ∈ S.erase k, (-(k : ℚ) - -(l : ℚ)) = ∏ l ∈ S.erase k, (-(k : ℚ) + l) :=
        prod_congr rfl fun l _ => by ring
      rw [prod_inv_distrib, eq_div_iff hf, ← he, e]
      field_simp
      exact mul_comm _ _
    · exact prod_congr rfl fun l _ => by simp [sub_eq_add_neg]
  rw [sum_congr rfl hb] at hsum
  have := congrArg (fun p => C ((15 * n).factorial : ℚ) * p) hsum
  simp only [mul_sum, mul_one] at this
  rw [← this]
  refine sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← C_mul]
  congr 2
  field_simp


/-- Off the support (`j ∉ [c, c+15n]`): `σ_c(j) ∏_k (k - j) = (15n)!`
(evaluate the Lagrange identity at `-j`). -/
theorem sig_mul_e_out (n c j : ℕ) (h : ¬ (c ≤ j ∧ j ≤ c + 15 * n)) :
    sigA n c j * (Qp (Icc c (c + 15 * n)) j).eval (-(j : ℚ)) = ((15 * n).factorial : ℚ) := by
  set S := Icc c (c + 15 * n)
  have hj : j ∉ S := fun h' => h (mem_Icc.mp h')
  have hid := congrArg (eval (-(j : ℚ))) (lagrange_id n c)
  simp only [eval_finsetSum, eval_mul, eval_C] at hid
  rw [← hid, sigA, erase_eq_of_notMem hj, sum_mul]
  refine sum_congr rfl fun k hk => ?_
  rw [Qp_eval, Qp_eval, erase_eq_of_notMem hj, ← mul_prod_erase S _ hk]
  have : (k : ℚ) - j ≠ 0 := by
    have hkj : k ≠ j := fun h' => hj (h' ▸ hk)
    have : (k : ℚ) ≠ j := by exact_mod_cast hkj
    exact sub_ne_zero.mpr this
  field_simp
  ring

/-- On the support (`j ∈ [c, c+15n]`): `σ_c(j) e = -ρ_c(j) e'`, where `e = Q_j(-j)`,
`e' = Q_j'(-j)` (differentiate the Lagrange identity at `-j`). -/
theorem sig_mul_e_in (n c j : ℕ) (h1 : c ≤ j) (h2 : j ≤ c + 15 * n) :
    sigA n c j * (Qp (Icc c (c + 15 * n)) j).eval (-(j : ℚ)) =
      -(rhoA n c j : ℚ) * (derivative (Qp (Icc c (c + 15 * n)) j)).eval (-(j : ℚ)) := by
  set S := Icc c (c + 15 * n)
  have hjS : j ∈ S := mem_Icc.mpr ⟨h1, h2⟩
  have hid := congrArg (fun p => (derivative p).eval (-(j : ℚ))) (lagrange_id n c)
  simp only [derivative_sum, derivative_C_mul, derivative_C, eval_finsetSum, eval_mul, eval_C,
    eval_zero] at hid
  rw [← add_sum_erase S _ hjS] at hid
  have key : ∀ k ∈ S.erase j, (derivative (Qp S k)).eval (-(j : ℚ)) =
      ∏ l ∈ (S.erase k).erase j, (-(j : ℚ) + l) := fun k hk => by
    have hj' : j ∈ S.erase k := mem_erase.mpr ⟨(ne_of_mem_erase hk).symm, hjS⟩
    rw [Qp, ← mul_prod_erase (S.erase k) _ hj', derivative_mul, derivative_X_add_C]
    simp [eval_prod]
  have hs : sigA n c j * (Qp S j).eval (-(j : ℚ)) =
      ∑ k ∈ S.erase j, (rhoA n c k : ℚ) * (derivative (Qp S k)).eval (-(j : ℚ)) := by
    rw [sigA, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    rw [key k hk, Qp_eval, ← mul_prod_erase (S.erase j) _ (mem_erase.mpr
      ⟨ne_of_mem_erase hk, mem_of_mem_erase hk⟩), erase_right_comm]
    have : (k : ℚ) - j ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast ne_of_mem_erase hk)
    field_simp
    ring
  rw [hs]
  linear_combination hid


/-! ### The denominator re-paired as `[n,16n] + [2n,17n]` -/

theorem negCast_inj : Function.Injective fun k : ℕ => -(k : ℤ) := fun a b h => by simpa using h

theorem Icc_neg_val (a b : ℕ) :
    (Icc (-(b : ℤ)) (-(a : ℤ))).val = (Icc a b).val.map fun k : ℕ => -(k : ℤ) := by
  refine (Multiset.Nodup.ext (Finset.nodup _) ((Finset.nodup _).map negCast_inj)).mpr fun x => ?_
  simp only [mem_val, mem_Icc, Multiset.mem_map]
  constructor
  · intro hx; exact ⟨(-x).toNat, by omega, by omega⟩
  · rintro ⟨k, hk, rfl⟩; omega

theorem denRoots_eq (n : ℕ) :
    denRoots n = ((Icc n (n + 15 * n)).val + (Icc (2 * n) (2 * n + 15 * n)).val).map
      fun k : ℕ => -(k : ℤ) := by
  have e1 := Icc_neg_val n (17 * n)
  have e2 := Icc_neg_val (2 * n) (16 * n)
  push_cast at e1 e2
  have hN : (Icc n (17 * n)).val + (Icc (2 * n) (16 * n)).val =
      (Icc n (n + 15 * n)).val + (Icc (2 * n) (2 * n + 15 * n)).val := by
    ext x
    simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), mem_val, mem_Icc]
    split_ifs <;> omega
  rw [denRoots, e1, e2, ← Multiset.map_add, hN]

theorem rootPoly_map_negCast (A : Finset ℕ) :
    rootPoly (A.val.map fun k : ℕ => -(k : ℤ)) = ∏ k ∈ A, (X + C (k : ℚ)) := by
  rw [rootPoly_eq, Multiset.map_map, prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun k _ => ?_
  simp [sub_eq_add_neg]

theorem rootPoly_den_filter (n j : ℕ) :
    rootPoly ((denRoots n).filter (· ≠ -(j : ℤ))) =
      Qp (Icc n (n + 15 * n)) j * Qp (Icc (2 * n) (2 * n + 15 * n)) j := by
  rw [denRoots_eq, Multiset.filter_map]
  have hf : ∀ s : Multiset ℕ, s.filter ((· ≠ -(j : ℤ)) ∘ fun k : ℕ => -(k : ℤ)) =
      s.filter (· ≠ j) := fun s => Multiset.filter_congr fun k _ => by simp
  rw [hf, Multiset.filter_add, ← Finset.filter_val, ← Finset.filter_val, filter_ne', filter_ne',
    Multiset.map_add, rootPoly_add, rootPoly_map_negCast, rootPoly_map_negCast, Qp, Qp]

theorem denRoots_count (n j : ℕ) :
    (denRoots n).count (-(j : ℤ)) =
      (if n ≤ j ∧ j ≤ n + 15 * n then 1 else 0) +
        (if 2 * n ≤ j ∧ j ≤ 2 * n + 15 * n then 1 else 0) := by
  rw [denRoots_eq, Multiset.count_map_eq_count' _ _ negCast_inj, Multiset.count_add,
    Multiset.count_eq_of_nodup (Finset.nodup _), Multiset.count_eq_of_nodup (Finset.nodup _)]
  simp only [mem_val, mem_Icc]


end Meijer5255.BaselineIntegrality.Aux
