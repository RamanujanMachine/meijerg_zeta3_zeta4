/-
# Helper for `BaselineProfile` [3]: the permutation lemma

* Integrality of the jets (pfq54 `Z_integral.lean`: `upperJet_integral`, `lowerJet_integral`,
  `jet_mul_integral`, `coeffJet_eq_zero`), for `d_L = dlcm L`.
* The permutation identity `𝒯^b = λ_{n,b} 𝒯` through `γ`-normalized Gamma jets and the
  integrality of `𝒯^b` (pfq54 `permutation_lemma.lean`, verbatim up to names).
* The readout: if `w U_{n,j} ∈ ℤ` and `d_{19n} w V_{n,j} ∈ ℤ` for all `j`, then `w` times every
  entry of `Z3v n`, `Z4v n` is an integer (via the bridge `C_n a_j = (-1)^n U_{n,j}`,
  `C_n b_j = (-1)^n V_{n,j}` of `BaselineProfile_Jets.lean`).

`shiftJ`, `lamJ` are verbatim copies of the node file's `shift`, `lam` (identified by `rfl`).
-/
import Meijer5255.BaselineProfile_Jets

open Finset Polynomial

noncomputable section

namespace Meijer5255.BaselineProfile.Jets

open Meijer5255

/-! ### Integrality of the jets (pfq54 `Z_integral.lean`, `Pfq54_aux.lean`) -/

theorem fst_upperJet (N M : ℕ) : (upperJet N M).fst = (N.choose M : ℚ) := by
  unfold upperJet
  split_ifs with h
  · exact jet_fst _ _
  · rw [jet_fst, Nat.choose_eq_zero_of_lt (not_le.mp h), Nat.cast_zero]

theorem fst_lowerJet (M : ℕ) (m : ℤ) :
    (lowerJet M m).fst = if 0 ≤ m ∧ m ≤ M then (M.choose m.toNat : ℚ) else 0 := by
  unfold lowerJet
  split_ifs <;> exact jet_fst _ _

/-- `H_N - H_{N-M} = ∑_{s<M} 1/(N-s)` (pfq54 `Aux.harm_sub`). -/
theorem harm_sub (N M : ℕ) (h : M ≤ N) :
    harm 1 N - harm 1 (N - M) = ∑ s ∈ range M, 1 / ((N - s : ℕ) : ℚ) := by
  induction M with
  | zero => rw [Nat.sub_zero, sub_self, sum_range_zero]
  | succ M ih =>
    rw [sum_range_succ, ← ih (by omega)]
    have e : N - M = (N - (M + 1)) + 1 := by omega
    rw [e, harm_succ, pow_one, ← e]
    ring

/-- `d_L · M!(r-1)!/(M+r)! ∈ ℤ` for `r ≥ 1`, `M + r ≤ L` (pfq54 `Aux.lcm_mul_inv_choose`). -/
theorem lcm_mul_inv_choose (M r L : ℕ) (hr : 1 ≤ r) (hL : M + r ≤ L) :
    ∃ z : ℤ, (dlcm L : ℚ) * ((M.factorial : ℚ) * (r - 1).factorial / (M + r).factorial) = z := by
  have hdvd : r * (M + r).choose r ∣ dlcm L :=
    (BaselineIntegrality.Aux.mul_choose_dvd_lcm hr (by omega)).trans
      (BaselineIntegrality.Aux.dlcm_mono hL)
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, ?_⟩
  have hf : (M + r).factorial = r * (M + r).choose r * ((r - 1).factorial * M.factorial) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left r M)
    rw [Nat.add_sub_cancel] at h1
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [← h1, Nat.factorial_succ, Nat.add_sub_cancel]
    ring
  rw [hq, hf]
  push_cast
  have h1 : ((r - 1).factorial : ℚ) ≠ 0 := by positivity
  have h2 : (M.factorial : ℚ) ≠ 0 := by positivity
  have h3 : (r : ℚ) * ((M + r).choose r : ℚ) ≠ 0 := by
    have : 0 < r * (M + r).choose r := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
    exact_mod_cast this.ne'
  have h4 : ((M + r).choose r : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp

/-- Upper jets: integral value, derivative cleared by `d_L` for `M ≤ L`. -/
theorem upperJet_integral (N M L : ℕ) (hML : M ≤ L) :
    (∃ z : ℤ, (upperJet N M).fst = z) ∧ ∃ z : ℤ, (dlcm L : ℚ) * (upperJet N M).snd = z := by
  refine ⟨⟨N.choose M, by rw [fst_upperJet]; exact (Int.cast_natCast _).symm⟩, ?_⟩
  unfold upperJet
  split_ifs with h
  · rw [jet_snd, harm_sub N M h]
    have key : ∀ s ∈ range M, ∃ z : ℕ,
        (dlcm L : ℚ) * ((N.choose M : ℚ) / ((N - s : ℕ) : ℚ)) = z := fun s hs =>
      BaselineIntegrality.Aux.lcm_choose_div N M L s (mem_range.mp hs) h hML
    choose! f hf using key
    refine ⟨-∑ s ∈ range M, (f s : ℤ), ?_⟩
    rw [Int.cast_neg, Int.cast_sum, neg_mul, mul_neg, mul_sum, mul_sum]
    congr 1
    refine sum_congr rfl fun s hs => ?_
    rw [Int.cast_natCast, ← hf s hs]
    ring
  · obtain ⟨z, hz⟩ := lcm_mul_inv_choose N (M - N) L (by omega) (by omega)
    rw [show N + (M - N) = M by omega, show M - N - 1 = M - 1 - N by omega] at hz
    refine ⟨(-1) ^ (M - N) * z, ?_⟩
    rw [jet_snd, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← hz]
    ring

/-- Lower jets: integral value; derivative cleared by `d_L` whenever `M ≤ L` and `m` lies at
most `L - M` outside `[0, M]`. -/
theorem lowerJet_integral (M L : ℕ) (m : ℤ) (h1 : M ≤ L) (h2 : -m ≤ (L : ℤ) - M)
    (h3 : m ≤ L) :
    (∃ z : ℤ, (lowerJet M m).fst = z) ∧ ∃ z : ℤ, (dlcm L : ℚ) * (lowerJet M m).snd = z := by
  refine ⟨?_, ?_⟩
  · rw [fst_lowerJet]
    split_ifs
    · exact ⟨M.choose m.toNat, (Int.cast_natCast _).symm⟩
    · exact ⟨0, Int.cast_zero.symm⟩
  unfold lowerJet
  split_ifs with ha hb
  · obtain ⟨z1, hz1⟩ := BaselineIntegrality.harm_int 1 m.toNat L (by omega)
    obtain ⟨z2, hz2⟩ := BaselineIntegrality.harm_int 1 (M - m.toNat) L (by omega)
    rw [pow_one] at hz1 hz2
    refine ⟨(M.choose m.toNat : ℤ) * (z1 - z2), ?_⟩
    rw [jet_snd, Int.cast_mul, Int.cast_sub, ← hz1, ← hz2, Int.cast_natCast]
    ring
  · obtain ⟨z, hz⟩ := lcm_mul_inv_choose M (-m).toNat L (by omega) (by omega)
    refine ⟨(-1) ^ (-m).toNat * z, ?_⟩
    rw [jet_snd, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← hz]
    ring
  · obtain ⟨z, hz⟩ := lcm_mul_inv_choose M (m - M).toNat L (by omega) (by omega)
    refine ⟨(-1) ^ ((m - M).toNat - 1) * z, ?_⟩
    rw [jet_snd, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, ← hz]
    ring

/-- Product rule for jets with integral value and `d`-cleared derivative. -/
theorem jet_mul_integral (d : ℚ) (a b : Jet) (ha : ∃ z : ℤ, a.fst = z)
    (ha' : ∃ z : ℤ, d * a.snd = z) (hb : ∃ z : ℤ, b.fst = z) (hb' : ∃ z : ℤ, d * b.snd = z) :
    (∃ z : ℤ, (a * b).fst = z) ∧ ∃ z : ℤ, d * (a * b).snd = z := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨x', hx'⟩ := ha'
  obtain ⟨y, hy⟩ := hb
  obtain ⟨y', hy'⟩ := hb'
  refine ⟨⟨x * y, by rw [TrivSqZeroExt.fst_mul, hx, hy, Int.cast_mul]⟩, ⟨x * y' + x' * y, ?_⟩⟩
  rw [DualNumber.snd_mul, Int.cast_add, Int.cast_mul, Int.cast_mul, ← hx, ← hy, ← hx', ← hy']
  ring

/-- For `j > 17n` the coefficient jet vanishes. -/
theorem coeffJet_eq_zero (n j : ℕ) (hj : 17 * n < j) : coeffJet n j = 0 := by
  unfold coeffJet
  set P := ∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n)
  have h1 : (lowerJet (15 * n) ((j : ℤ) - n)).fst = 0 := by
    rw [fst_lowerJet]; exact ite_eq_right_iff.2 fun h => absurd h (by omega)
  have h2 : (lowerJet (15 * n) ((j : ℤ) - 2 * n)).fst = 0 := by
    rw [fst_lowerJet]; exact ite_eq_right_iff.2 fun h => absurd h (by omega)
  have h3 : (P * lowerJet (15 * n) ((j : ℤ) - n)).fst = 0 := by
    rw [TrivSqZeroExt.fst_mul, h1, mul_zero]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [TrivSqZeroExt.fst_mul, h2, mul_zero]; rfl
  · rw [DualNumber.snd_mul, h3, h2, zero_mul, mul_zero, add_zero]; rfl

/-! ### The permutation identity (pfq54 `permutation_lemma.lean`) -/

/-- Copy of the node file's `shift`. -/
def shiftJ : Fin 5 → ℤ := ![-2, -1, 0, 1, 2]

/-- Copy of the node file's `lam`. -/
def lamJ (σ : Equiv.Perm (Fin 5)) (n : ℕ) : ℚ :=
  let b : Fin 5 → ℤ := fun i => shiftJ (σ i)
  let fac : ℤ → ℚ := fun e => ((e * n).toNat.factorial : ℚ)
  fac 10 ^ 3 * fac (16 - b 3) * fac (17 - b 4) /
    (fac 15 ^ 2 * fac (10 + b 0) * fac (11 + b 1) * fac (12 + b 2))

/-- The permuted coefficient product `𝒯^b_{n,j}(ε)`. -/
def coeffJetPerm (σ : Equiv.Perm (Fin 5)) (n j : ℕ) : Jet :=
  let b : Fin 5 → ℤ := fun i => shiftJ (σ i)
  upperJet (j + 10 * n) ((10 + b 0) * n).toNat * upperJet (j + 11 * n) ((11 + b 1) * n).toNat *
    upperJet (j + 12 * n) ((12 + b 2) * n).toNat *
    lowerJet ((16 - b 3) * n).toNat ((j : ℤ) - b 3 * n) *
    lowerJet ((17 - b 4) * n).toNat ((j : ℤ) - b 4 * n)

/-- Jet of `ε ↦ e^{-γε} Γ(x+1-ε)`. -/
def gJet (x : ℕ) : Jet := jet (x.factorial : ℚ) (-(x.factorial : ℚ) * harm 1 x)

/-- Jet of `ε ↦ e^{γε} / Γ(x+1-ε)`. -/
def rgJet (x : ℤ) : Jet :=
  if 0 ≤ x then jet ((x.toNat.factorial : ℚ)⁻¹) (harm 1 x.toNat / x.toNat.factorial)
  else jet 0 ((-1 : ℚ) ^ (-x).toNat * ((-x).toNat - 1).factorial)

/-- Jet of `ε ↦ e^{-γε} / Γ(y+1+ε)`. -/
def rgpJet (y : ℤ) : Jet :=
  if 0 ≤ y then jet ((y.toNat.factorial : ℚ)⁻¹) (-harm 1 y.toNat / y.toNat.factorial)
  else jet 0 ((-1 : ℚ) ^ ((-y).toNat - 1) * ((-y).toNat - 1).factorial)

/-- The permutation-invariant part of `𝒯^b_{n,j}`. -/
def core (n j : ℕ) : Jet :=
  gJet (j + 10 * n) * gJet (j + 11 * n) * gJet (j + 12 * n) *
    (∏ k : Fin 5, rgJet ((j : ℤ) - shiftJ k * n)) *
    rgpJet (16 * n - (j : ℤ)) * rgpJet (17 * n - (j : ℤ))

/-- The constant factorials of `𝒯^b`. -/
def permConst (σ : Equiv.Perm (Fin 5)) (n : ℕ) : ℚ :=
  let b : Fin 5 → ℤ := fun i => shiftJ (σ i)
  let fac : ℤ → ℚ := fun e => ((e * n).toNat.factorial : ℚ)
  fac (16 - b 3) * fac (17 - b 4) / (fac (10 + b 0) * fac (11 + b 1) * fac (12 + b 2))

theorem upperJet_eq_gamma (N M : ℕ) :
    upperJet N M = (M.factorial : ℚ)⁻¹ • (gJet N * rgJet ((N : ℤ) - M)) := by
  have hM : (M.factorial : ℚ) ≠ 0 := by positivity
  unfold upperJet gJet rgJet
  by_cases h : M ≤ N
  · have h0 : (0 : ℤ) ≤ (N : ℤ) - M := by omega
    rw [ite_eq_left h, ite_eq_left h0, show ((N : ℤ) - M).toNat = N - M by omega]
    have hNM : ((N - M).factorial : ℚ) ≠ 0 := by positivity
    have hc : (N.choose M : ℚ) * M.factorial * (N - M).factorial = N.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial h
    rw [jet_mul, jet_smul, ← hc]
    congr 1
    · field_simp
    · field_simp
      ring
  · have h0 : ¬ (0 : ℤ) ≤ (N : ℤ) - M := by omega
    rw [ite_eq_right h, ite_eq_right h0, show (-((N : ℤ) - M)).toNat = M - N by omega,
      show M - 1 - N = M - N - 1 by omega, jet_mul, jet_smul]
    congr 1
    · ring
    · field_simp
      ring

theorem lowerJet_eq_gamma (M : ℕ) (m : ℤ) :
    lowerJet M m = (M.factorial : ℚ) • (rgJet m * rgpJet ((M : ℤ) - m)) := by
  unfold lowerJet rgJet rgpJet
  by_cases h1 : 0 ≤ m ∧ m ≤ M
  · rw [ite_eq_left h1, ite_eq_left h1.1, ite_eq_left (by omega : (0 : ℤ) ≤ (M : ℤ) - m),
      show ((M : ℤ) - m).toNat = M - m.toNat by omega]
    have hc : (M.choose m.toNat : ℚ) * m.toNat.factorial * (M - m.toNat).factorial =
        M.factorial := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
    have h2 : (m.toNat.factorial : ℚ) ≠ 0 := by positivity
    have h3 : ((M - m.toNat).factorial : ℚ) ≠ 0 := by positivity
    rw [jet_mul, jet_smul, ← hc]
    congr 1
    · field_simp
    · field_simp
      ring
  rw [ite_eq_right h1]
  by_cases h2 : m < 0
  · rw [ite_eq_left h2, ite_eq_right (by omega : ¬ (0 : ℤ) ≤ m),
      ite_eq_left (by omega : (0 : ℤ) ≤ (M : ℤ) - m),
      show ((M : ℤ) - m).toNat = M + (-m).toNat by omega, jet_mul, jet_smul]
    have : ((M + (-m).toNat).factorial : ℚ) ≠ 0 := by positivity
    congr 1
    · ring
    · field_simp
      ring
  · rw [ite_eq_right h2, ite_eq_left (by omega : (0 : ℤ) ≤ m),
      ite_eq_right (by omega : ¬ (0 : ℤ) ≤ (M : ℤ) - m),
      show (-((M : ℤ) - m)).toNat = (m - M).toNat by omega,
      show m.toNat = M + (m - M).toNat by omega, jet_mul, jet_smul]
    have : ((M + (m - M).toNat).factorial : ℚ) ≠ 0 := by positivity
    congr 1
    · ring
    · field_simp
      ring

theorem coeffJetPerm_eq_core (σ : Equiv.Perm (Fin 5)) (n j : ℕ) :
    coeffJetPerm σ n j = permConst σ n • core n j := by
  have hb : ∀ i, -2 ≤ shiftJ i ∧ shiftJ i ≤ 2 := by intro i; fin_cases i <;> decide
  have hnn : ∀ e : ℤ, 0 ≤ e → ((e * n).toNat : ℤ) = e * n := fun e he =>
    Int.toNat_of_nonneg (mul_nonneg he (Int.natCast_nonneg n))
  unfold coeffJetPerm core permConst
  dsimp only
  rw [upperJet_eq_gamma, upperJet_eq_gamma, upperJet_eq_gamma, lowerJet_eq_gamma,
    lowerJet_eq_gamma, hnn _ (by linarith [(hb (σ 0)).1]), hnn _ (by linarith [(hb (σ 1)).1]),
    hnn _ (by linarith [(hb (σ 2)).1]), hnn _ (by linarith [(hb (σ 3)).2]),
    hnn _ (by linarith [(hb (σ 4)).2]),
    show ((j + 10 * n : ℕ) : ℤ) - (10 + shiftJ (σ 0)) * n = j - shiftJ (σ 0) * n by
      push_cast; ring,
    show ((j + 11 * n : ℕ) : ℤ) - (11 + shiftJ (σ 1)) * n = j - shiftJ (σ 1) * n by
      push_cast; ring,
    show ((j + 12 * n : ℕ) : ℤ) - (12 + shiftJ (σ 2)) * n = j - shiftJ (σ 2) * n by
      push_cast; ring,
    show (16 - shiftJ (σ 3)) * (n : ℤ) - (j - shiftJ (σ 3) * n) = 16 * n - j by ring,
    show (17 - shiftJ (σ 4)) * (n : ℤ) - (j - shiftJ (σ 4) * n) = 17 * n - j by ring,
    ← Equiv.prod_comp σ (fun k => rgJet ((j : ℤ) - shiftJ k * n)), Fin.prod_univ_five]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  · ring
  · ring

theorem coeffJet_eq_perm_ref (n j : ℕ) : coeffJet n j = coeffJetPerm (Equiv.swap 0 2) n j := by
  have e0 : shiftJ (Equiv.swap (0 : Fin 5) 2 0) = 0 := by decide
  have e1 : shiftJ (Equiv.swap (0 : Fin 5) 2 1) = -1 := by decide
  have e2 : shiftJ (Equiv.swap (0 : Fin 5) 2 2) = -2 := by decide
  have e3 : shiftJ (Equiv.swap (0 : Fin 5) 2 3) = 1 := by decide
  have e4 : shiftJ (Equiv.swap (0 : Fin 5) 2 4) = 2 := by decide
  unfold coeffJet coeffJetPerm
  dsimp only
  rw [e0, e1, e2, e3, e4, prod_Icc_10_12, show ((10 + 0) * (n : ℤ)).toNat = 10 * n by omega,
    show ((11 + -1) * (n : ℤ)).toNat = 10 * n by omega,
    show ((12 + -2) * (n : ℤ)).toNat = 10 * n by omega,
    show ((16 - 1) * (n : ℤ)).toNat = 15 * n by omega,
    show ((17 - 2) * (n : ℤ)).toNat = 15 * n by omega, one_mul]

theorem lam_eq (σ : Equiv.Perm (Fin 5)) (n : ℕ) :
    lamJ σ n = permConst σ n / permConst (Equiv.swap 0 2) n := by
  have e0 : shiftJ (Equiv.swap (0 : Fin 5) 2 0) = 0 := by decide
  have e1 : shiftJ (Equiv.swap (0 : Fin 5) 2 1) = -1 := by decide
  have e2 : shiftJ (Equiv.swap (0 : Fin 5) 2 2) = -2 := by decide
  have e3 : shiftJ (Equiv.swap (0 : Fin 5) 2 3) = 1 := by decide
  have e4 : shiftJ (Equiv.swap (0 : Fin 5) 2 4) = 2 := by decide
  unfold lamJ permConst
  dsimp only
  rw [e0, e1, e2, e3, e4, show ((10 + 0) * (n : ℤ)).toNat = 10 * n by omega,
    show ((11 + -1) * (n : ℤ)).toNat = 10 * n by omega,
    show ((12 + -2) * (n : ℤ)).toNat = 10 * n by omega,
    show ((16 - 1) * (n : ℤ)).toNat = 15 * n by omega,
    show ((17 - 2) * (n : ℤ)).toNat = 15 * n by omega,
    show (10 * (n : ℤ)).toNat = 10 * n by omega, show (15 * (n : ℤ)).toNat = 15 * n by omega]
  field_simp

theorem permConst_ne_zero (σ : Equiv.Perm (Fin 5)) (n : ℕ) : permConst σ n ≠ 0 := by
  unfold permConst
  dsimp only
  positivity

theorem coeffJetPerm_integral (σ : Equiv.Perm (Fin 5)) (n j : ℕ) (hj : j ≤ 17 * n) :
    (∃ z : ℤ, (coeffJetPerm σ n j).fst = z) ∧
      ∃ z : ℤ, (dlcm (19 * n) : ℚ) * (coeffJetPerm σ n j).snd = z := by
  have hb : ∀ i, -2 ≤ shiftJ i ∧ shiftJ i ≤ 2 := by intro i; fin_cases i <;> decide
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg n
  let Q : Jet → Prop := fun c =>
    (∃ z : ℤ, c.fst = z) ∧ ∃ z : ℤ, (dlcm (19 * n) : ℚ) * c.snd = z
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := fun a b ha hb =>
    jet_mul_integral _ a b ha.1 ha.2 hb.1 hb.2
  have hup : ∀ (c : ℤ) (i : Fin 5) (N : ℕ), c ≤ 12 →
      Q (upperJet N ((c + shiftJ (σ i)) * n).toNat) := fun c i N hc =>
    upperJet_integral _ _ _ (Int.toNat_le.mpr (by push_cast; nlinarith [hb (σ i)]))
  have hlo : ∀ (c : ℤ) (i : Fin 5), (c = 16 ∨ c = 17) →
      Q (lowerJet ((c - shiftJ (σ i)) * n).toNat ((j : ℤ) - shiftJ (σ i) * n)) := by
    intro c i hc
    have hb' := hb (σ i)
    have h0 : 0 ≤ (c - shiftJ (σ i)) * (n : ℤ) := mul_nonneg (by omega) hn
    refine lowerJet_integral _ (19 * n) _
      (Int.toNat_le.mpr (by push_cast; rcases hc with rfl | rfl <;> nlinarith)) ?_ ?_
    · rw [Int.toNat_of_nonneg h0]; push_cast; rcases hc with rfl | rfl <;> nlinarith
    · push_cast; nlinarith
  unfold coeffJetPerm
  dsimp only
  exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hup 10 0 _ (by norm_num))
    (hup 11 1 _ (by norm_num))) (hup 12 2 _ (by norm_num))) (hlo 16 3 (Or.inl rfl)))
    (hlo 17 4 (Or.inr rfl))

/-- `λ U_{n,j} ∈ ℤ` and `d_{19n} λ V_{n,j} ∈ ℤ` for all `j` and all `σ`. -/
theorem lam_UV_integral (σ : Equiv.Perm (Fin 5)) (n j : ℕ) :
    (∃ z : ℤ, lamJ σ n * U n j = z) ∧ ∃ z : ℤ, (dlcm (19 * n) : ℚ) * lamJ σ n * V n j = z := by
  have hid : coeffJetPerm σ n j = lamJ σ n • coeffJet n j := by
    rw [coeffJet_eq_perm_ref n j, coeffJetPerm_eq_core, coeffJetPerm_eq_core, smul_smul,
      lam_eq, div_mul_cancel₀ _ (permConst_ne_zero _ n)]
  rcases le_or_gt j (17 * n) with hj | hj
  · obtain ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ := coeffJetPerm_integral σ n j hj
    refine ⟨⟨z, ?_⟩, ⟨z', ?_⟩⟩
    · rw [← hz, hid, TrivSqZeroExt.fst_smul, smul_eq_mul, U]
    · rw [← hz', hid, TrivSqZeroExt.snd_smul, smul_eq_mul, V, mul_assoc]
  · exact ⟨⟨0, by simp [U, coeffJet_eq_zero n j hj]⟩, ⟨0, by simp [V, coeffJet_eq_zero n j hj]⟩⟩

/-! ### The readout -/

/-- If `w U_{n,j} ∈ ℤ` and `d_{19n} w V_{n,j} ∈ ℤ` for all `j`, then `w` times every entry of
the two integer forms is an integer. -/
theorem readout (n : ℕ) (hn : 1 ≤ n) (w : ℚ) (hU : ∀ j, ∃ z : ℤ, w * U n j = z)
    (hV : ∀ j, ∃ z : ℤ, (dlcm (19 * n) : ℚ) * w * V n j = z) :
    (∀ i, ∃ z : ℤ, w * Z3v n i = z) ∧ (∀ i, ∃ z : ℤ, w * Z4v n i = z) := by
  set R := (Int.castRingHom ℚ).range
  have mem : ∀ x : ℚ, (∃ z : ℤ, x = z) → x ∈ R := fun x ⟨z, hz⟩ => ⟨z, hz.symm⟩
  have out : ∀ x : ℚ, x ∈ R → ∃ z : ℤ, x = z := fun x ⟨z, hz⟩ => ⟨z, hz.symm⟩
  have hk : ∀ k : ℕ, (k : ℚ) ∈ R := fun k => ⟨k, map_natCast _ _⟩
  have hsg : ((-1 : ℚ) ^ n) ∈ R := R.pow_mem (R.neg_mem R.one_mem) n
  set d : ℚ := (dlcm (19 * n) : ℚ) with hd_def
  have hd : d ∈ R := hk _
  have hA : ∀ j, w * (Cn n * aCoef n j) ∈ R := fun j => by
    rw [aCoef_eq n hn j, show w * ((-1) ^ n * U n j) = (-1) ^ n * (w * U n j) by ring]
    exact R.mul_mem hsg (mem _ (hU j))
  have hB : ∀ j, d * (w * (Cn n * bCoef n j)) ∈ R := fun j => by
    rw [bCoef_eq n hn j, show d * (w * ((-1) ^ n * V n j)) = (-1) ^ n * (d * w * V n j) by ring]
    exact R.mul_mem hsg (mem _ (hV j))
  have hH : ∀ s j, j ∈ Icc n (17 * n) → d ^ s * harm s (j + 2 * n) ∈ R := fun s j hj =>
    mem _ (BaselineIntegrality.harm_int s (j + 2 * n) (19 * n)
      (by simp only [mem_Icc] at hj; omega))
  have hQ : ∀ r : ℕ, w * (6 * Cn n * d ^ r * Q n) ∈ R := fun r => by
    rw [Q, mul_sum, mul_sum]
    refine R.sum_mem fun j _ => ?_
    rw [show w * (6 * Cn n * d ^ r * aCoef n j) = 6 * d ^ r * (w * (Cn n * aCoef n j)) by ring]
    exact R.mul_mem (R.mul_mem (hk 6) (R.pow_mem hd r)) (hA j)
  have hP3 : ∀ r : ℕ, w * (6 * Cn n * d ^ (r + 3) * P3 n) ∈ R := fun r => by
    rw [P3, mul_sum, mul_sum]
    refine R.sum_mem fun j hj => ?_
    rw [show w * (6 * Cn n * d ^ (r + 3) *
        (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2)) =
        6 * d ^ r * (w * (Cn n * aCoef n j)) * (d ^ 3 * harm 3 (j + 2 * n)) +
          3 * d ^ r * (d * (w * (Cn n * bCoef n j))) * (d ^ 2 * harm 2 (j + 2 * n)) by ring]
    exact R.add_mem (R.mul_mem (R.mul_mem (R.mul_mem (hk 6) (R.pow_mem hd r)) (hA j))
        (hH 3 j hj))
      (R.mul_mem (R.mul_mem (R.mul_mem (hk 3) (R.pow_mem hd r)) (hB j)) (hH 2 j hj))
  have hP4 : w * (6 * Cn n * d ^ 4 * P4 n) ∈ R := by
    rw [P4, mul_sum, mul_sum]
    refine R.sum_mem fun j hj => ?_
    rw [show w * (6 * Cn n * d ^ 4 *
        (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3)) =
        6 * (w * (Cn n * aCoef n j)) * (d ^ 4 * harm 4 (j + 2 * n)) +
          2 * (d * (w * (Cn n * bCoef n j))) * (d ^ 3 * harm 3 (j + 2 * n)) by ring]
    exact R.add_mem (R.mul_mem (R.mul_mem (hk 6) (hA j)) (hH 4 j hj))
      (R.mul_mem (R.mul_mem (hk 2) (hB j)) (hH 3 j hj))
  refine ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact out _ (hQ 3)
    · exact out _ (hP3 0)
  · fin_cases i
    · exact out _ (hQ 4)
    · exact out _ (hP3 1)
    · exact out _ hP4

/-- **Permutation lemma** (for the copy `lamJ` of `lam`). -/
theorem permutation_lemma (σ : Equiv.Perm (Fin 5)) (n : ℕ) (hn : 1 ≤ n) :
    (∀ i, ∃ z : ℤ, lamJ σ n * Z3v n i = z) ∧ (∀ i, ∃ z : ℤ, lamJ σ n * Z4v n i = z) :=
  readout n hn _ (fun j => (lam_UV_integral σ n j).1) (fun j => (lam_UV_integral σ n j).2)

end Meijer5255.BaselineProfile.Jets
