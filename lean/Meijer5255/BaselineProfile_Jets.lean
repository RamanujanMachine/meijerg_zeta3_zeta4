/-
# Helper for `BaselineProfile` [3], [8]: the coefficient jets

pfq54's jets (`Pfq54_defs.lean`: `jet`, `upperJet`, `lowerJet`, `coeffJet`; `Z_integral.lean`:
the integrality lemmas), copied for `Meijer5255.harm`, and the bridge to the partial-fraction
coefficients of `F_n`:

  `jet (C_n a_j) (C_n b_j) = (-1)^n • coeffJet n j`   (`bridge`),

obtained from the formulas `aCoef_formula`, `bCoef_formula` of `BaselineIntegrality`
(`C_n F_n = P L_n L_{2n}`): the jet of `P` at `-j` is the product of the three upper jets
(`pjet_Pbin`), and the jet `(ρ_c(j), σ_c(j))` of `L_c` is `(-1)^{j+c}` times the lower jet
`C(15n, j - c - ε)` (`rs_jet`; interior, below and above the support).
-/
import Meijer5255.definitions
import Meijer5255.BaselineIntegrality

open Finset Polynomial

noncomputable section

namespace Meijer5255.BaselineProfile.Jets

open Meijer5255
open Meijer5255.BaselineIntegrality (Pbin rho sig aCoef_formula bCoef_formula)

/-! ### Jets (pfq54 `Pfq54_defs.lean`, `Pfq54_aux.lean`) -/

/-- Jets: dual numbers over `ℚ`. -/
abbrev Jet := DualNumber ℚ

/-- The jet with value `a` and derivative `a'`. -/
def jet (a a' : ℚ) : Jet := TrivSqZeroExt.inl a + TrivSqZeroExt.inr a'

theorem jet_fst (a a' : ℚ) : (jet a a').fst = a := add_zero a

theorem jet_snd (a a' : ℚ) : (jet a a').snd = a' := zero_add a'

theorem jet_ext {x y : Jet} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  TrivSqZeroExt.ext h1 h2

theorem jet_mul (a a' b b' : ℚ) : jet a a' * jet b b' = jet (a * b) (a * b' + a' * b) :=
  jet_ext (by rw [TrivSqZeroExt.fst_mul, jet_fst, jet_fst, jet_fst])
    (by rw [DualNumber.snd_mul, jet_fst, jet_fst, jet_snd, jet_snd, jet_snd])

theorem jet_smul (c a a' : ℚ) : c • jet a a' = jet (c * a) (c * a') :=
  jet_ext (by rw [TrivSqZeroExt.fst_smul, jet_fst, jet_fst, smul_eq_mul])
    (by rw [TrivSqZeroExt.snd_smul, jet_snd, jet_snd, smul_eq_mul])

/-- Upper jet: the jet of `ε ↦ C(N - ε, M)`. -/
def upperJet (N M : ℕ) : Jet :=
  if M ≤ N then jet (N.choose M) (-(N.choose M : ℚ) * (harm 1 N - harm 1 (N - M)))
  else jet 0 ((-1 : ℚ) ^ (M - N) * N.factorial * (M - 1 - N).factorial / M.factorial)

/-- Lower jet: the jet of `ε ↦ C(M, m - ε)`. -/
def lowerJet (M : ℕ) (m : ℤ) : Jet :=
  if 0 ≤ m ∧ m ≤ M then
    jet (M.choose m.toNat) (M.choose m.toNat * (harm 1 m.toNat - harm 1 (M - m.toNat)))
  else if m < 0 then
    jet 0 ((-1 : ℚ) ^ (-m).toNat * M.factorial * ((-m).toNat - 1).factorial /
      (M + (-m).toNat).factorial)
  else
    jet 0 ((-1 : ℚ) ^ ((m - M).toNat - 1) * M.factorial * ((m - M).toNat - 1).factorial /
      (M + (m - M).toNat).factorial)

/-- The jet of the five-binomial product
`∏_{u=10}^{12} C(j+un-ε, 10n) · C(15n, j-n-ε) · C(15n, j-2n-ε)`. -/
def coeffJet (n j : ℕ) : Jet :=
  (∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n)) *
    lowerJet (15 * n) ((j : ℤ) - n) * lowerJet (15 * n) ((j : ℤ) - 2 * n)

/-- `U_{n,j}`, the value of the coefficient jet. -/
def U (n j : ℕ) : ℚ := (coeffJet n j).fst

/-- `V_{n,j}`, the derivative of the coefficient jet. -/
def V (n j : ℕ) : ℚ := (coeffJet n j).snd

theorem prod_Icc_10_12 {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ u ∈ Icc 10 12, f u = f 10 * f 11 * f 12 := by
  rw [show Icc 10 12 = {10, 11, 12} by decide, prod_insert (by decide), prod_insert (by decide),
    prod_singleton, mul_assoc]

theorem harm_succ (r m : ℕ) : harm r (m + 1) = harm r m + 1 / ((m + 1 : ℕ) : ℚ) ^ r := by
  unfold harm
  rw [sum_Icc_succ_top (Nat.le_add_left 1 m)]

/-! ### The jet of `P` at `-j` -/

/-- The jet of a polynomial at `x`. -/
def pjet (P : ℚ[X]) (x : ℚ) : Jet := jet (P.eval x) ((derivative P).eval x)

theorem pjet_mul (P Q : ℚ[X]) (x : ℚ) : pjet (P * Q) x = pjet P x * pjet Q x := by
  rw [pjet, pjet, pjet, jet_mul, derivative_mul, eval_add, eval_mul, eval_mul, eval_mul]
  congr 1; ring

theorem pjet_C_mul (a : ℚ) (P : ℚ[X]) (x : ℚ) : pjet (C a * P) x = a • pjet P x := by
  rw [pjet, pjet, jet_smul, derivative_C_mul, eval_mul, eval_mul, eval_C]

theorem sum_inv_shift (b M : ℕ) :
    ∑ t ∈ range M, 1 / ((b + 1 + t : ℕ) : ℚ) = harm 1 (b + M) - harm 1 b := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih, show b + (M + 1) = b + M + 1 by ring, harm_succ,
      show b + 1 + M = b + M + 1 by ring, pow_one]
    ring

theorem pjet_G (a M j : ℕ) :
    pjet (BaselineIntegrality.Aux.G a M) (-(j : ℚ)) =
      ((-1 : ℚ) ^ M * M.factorial) • upperJet (j + a + M) M := by
  have hs : ∑ t ∈ range M, ((j + a + M).choose M : ℚ) / ((j + a + 1 + t : ℕ) : ℚ) =
      ((j + a + M).choose M : ℚ) * (harm 1 (j + a + M) - harm 1 (j + a)) := by
    rw [← sum_inv_shift, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  rw [pjet, BaselineIntegrality.Aux.G_eval, BaselineIntegrality.Aux.G_deriv_eval, upperJet,
    ite_eq_left (by omega), jet_smul, show j + a + M - M = j + a by omega, hs]
  congr 1 <;> ring

/-- The jet of `P = ∏_u C(t-un-1, 10n)` at `-j` is the product of the three upper jets. -/
theorem pjet_Pbin (n j : ℕ) :
    pjet (Pbin n) (-(j : ℚ)) = ∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n) := by
  have hs : (-1 : ℚ) ^ (10 * n) = 1 := Even.neg_one_pow ⟨5 * n, by ring⟩
  have hF : ((10 * n).factorial : ℚ) ≠ 0 := by positivity
  rw [Pbin, pjet_C_mul, BaselineIntegrality.Aux.rootPoly_numRoots, pjet_mul, pjet_mul, pjet_G,
    pjet_G, pjet_G, hs, one_mul, smul_mul_smul_comm, smul_mul_smul_comm, smul_smul,
    prod_Icc_10_12, show j + 0 + 10 * n = j + 10 * n by ring,
    show j + n + 10 * n = j + 11 * n by ring, show j + 2 * n + 10 * n = j + 12 * n by ring]
  have hK : (((10 * n).factorial : ℚ) ^ 3)⁻¹ *
      ((10 * n).factorial * (10 * n).factorial * (10 * n).factorial) = 1 := by
    field_simp
  rw [hK, one_smul]

/-! ### The jets of `L_c` at `-j` -/

/-- Logarithmic derivative of `∏_{l ∈ s} (X + l)`. -/
theorem deriv_prod_add_eval (s : Finset ℕ) (x : ℚ) (h : ∀ l ∈ s, x + l ≠ 0) :
    (derivative (∏ l ∈ s, (X + C (l : ℚ)))).eval x =
      (∏ l ∈ s, (x + l)) * ∑ l ∈ s, 1 / (x + l) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, derivative_mul, eval_add, eval_mul, eval_mul,
      ih (fun l hl => h l (mem_insert_of_mem hl)), prod_insert ha, sum_insert ha, eval_prod]
    simp only [derivative_add, derivative_X, derivative_C, add_zero, eval_one, eval_add, eval_X,
      eval_C]
    have := h a (mem_insert_self a s)
    field_simp

theorem sum_range_inv_sub (i : ℕ) : ∑ t ∈ range i, 1 / ((t : ℚ) - i) = -harm 1 i := by
  induction i with
  | zero => simp [harm]
  | succ i ih =>
    rw [sum_range_succ', harm_succ, pow_one]
    have e : ∑ t ∈ range i, 1 / (((t + 1 : ℕ) : ℚ) - ((i + 1 : ℕ) : ℚ)) =
        ∑ t ∈ range i, 1 / ((t : ℚ) - i) := sum_congr rfl fun t _ => by push_cast; ring
    rw [e, ih]
    push_cast
    rw [zero_sub, div_neg]
    ring

/-- `∑_{l ∈ [c, c+i+r] \ {c+i}} 1/(l - (c+i)) = H_r - H_i`. -/
theorem sum_erase_inv (c i r : ℕ) :
    ∑ l ∈ (Icc c (c + (i + r))).erase (c + i), 1 / (-((c + i : ℕ) : ℚ) + l) =
      harm 1 r - harm 1 i := by
  induction r with
  | zero =>
    rw [show c + (i + 0) = c + i by ring, Icc_erase_right, sum_Ico_eq_sum_range,
      show c + i - c = i by omega]
    have e : ∑ t ∈ range i, 1 / (-((c + i : ℕ) : ℚ) + ((c + t : ℕ) : ℚ)) =
        ∑ t ∈ range i, 1 / ((t : ℚ) - i) := sum_congr rfl fun t _ => by push_cast; ring
    rw [e, sum_range_inv_sub]
    simp [harm]
  | succ r ih =>
    rw [show c + (i + (r + 1)) = c + (i + r) + 1 by ring,
      ← insert_Icc_right_eq_Icc_add_one (by omega), erase_insert_of_ne (by omega),
      sum_insert (by simp), ih, harm_succ, pow_one]
    push_cast
    ring

/-- `σ_c(j) = ρ_c(j) (H_{j-c} - H_{c+15n-j})` on the support. -/
theorem sig_in (n c j : ℕ) (h1 : c ≤ j) (h2 : j ≤ c + 15 * n) :
    sig n c j = (rho n c j : ℚ) * (harm 1 (j - c) - harm 1 (c + 15 * n - j)) := by
  have he := BaselineIntegrality.Aux.sig_mul_e_in n c j h1 h2
  have hne := BaselineIntegrality.Aux.Qp_eval_ne_zero (Icc c (c + 15 * n)) j
  set S := Icc c (c + 15 * n)
  have hd : (derivative (BaselineIntegrality.Aux.Qp S j)).eval (-(j : ℚ)) =
      (BaselineIntegrality.Aux.Qp S j).eval (-(j : ℚ)) *
        ∑ l ∈ S.erase j, 1 / (-(j : ℚ) + l) := by
    rw [BaselineIntegrality.Aux.Qp_eval, BaselineIntegrality.Aux.Qp,
      deriv_prod_add_eval _ _ fun l hl => ?_]
    have : (l : ℚ) ≠ j := by exact_mod_cast ne_of_mem_erase hl
    intro h; apply this; linarith
  obtain ⟨i, rfl⟩ : ∃ i, j = c + i := ⟨j - c, by omega⟩
  obtain ⟨r, hr⟩ : ∃ r, 15 * n = i + r := ⟨15 * n - i, by omega⟩
  have hsum := sum_erase_inv c i r
  rw [← hr] at hsum
  rw [hd, hsum] at he
  rw [show c + i - c = i by omega, show c + 15 * n - (c + i) = r by omega]
  change sig n c (c + i) * _ = -(rho n c (c + i) : ℚ) * _ at he
  apply mul_right_cancel₀ hne
  linear_combination he

/-- `(r-1)! ∏_{l ∈ [c, c+M]} (l - j) = (r+M)!` for `r = c - j ≥ 1`. -/
theorem prod_low (c M j : ℕ) (h : j < c) :
    ((c - j - 1).factorial : ℚ) * ∏ l ∈ Icc c (c + M), (-(j : ℚ) + l) =
      (c - j + M).factorial := by
  induction M with
  | zero =>
    rw [add_zero, Icc_self, prod_singleton, add_zero]
    have h1 : ((c - j : ℕ) : ℚ) = -(j : ℚ) + c := by push_cast [Nat.cast_sub h.le]; ring
    rw [← h1, ← Nat.mul_factorial_pred (by omega : c - j ≠ 0)]
    push_cast; ring
  | succ M ih =>
    rw [show c + (M + 1) = c + M + 1 by ring, ← insert_Icc_right_eq_Icc_add_one (by omega),
      prod_insert (by simp), show c - j + (M + 1) = (c - j + M) + 1 by ring, Nat.factorial_succ]
    have h1 : (((c - j + M) + 1 : ℕ) : ℚ) = -(j : ℚ) + ((c + M + 1 : ℕ) : ℚ) := by
      push_cast [Nat.cast_sub h.le]; ring
    push_cast at h1 ⊢
    rw [← ih]
    linear_combination (-(((c - j - 1).factorial : ℚ) * ∏ l ∈ Icc c (c + M), (-(j : ℚ) + l))) * h1

/-- `(r-1)! ∏_{l ∈ [c, c+M]} (l - j) = (-1)^{M+1} (j-c)!` for `r = j - c - M ≥ 1`. -/
theorem prod_high (M : ℕ) : ∀ c j : ℕ, c + M < j →
    ((j - c - M - 1).factorial : ℚ) * ∏ l ∈ Icc c (c + M), (-(j : ℚ) + l) =
      (-1) ^ (M + 1) * (j - c).factorial := by
  induction M with
  | zero =>
    intro c j h
    rw [add_zero, Icc_self, prod_singleton, Nat.sub_zero]
    have h1 : ((j - c : ℕ) : ℚ) = (j : ℚ) - c := by push_cast [Nat.cast_sub (by omega : c ≤ j)]; ring
    rw [← Nat.mul_factorial_pred (by omega : j - c ≠ 0)]
    push_cast [h1]; ring
  | succ M ih =>
    intro c j h
    rw [← insert_Icc_add_one_left_eq_Icc (by omega), prod_insert (by simp),
      show c + (M + 1) = c + 1 + M by ring]
    have ih' := ih (c + 1) j (by omega)
    rw [show j - (c + 1) - M - 1 = j - c - (M + 1) - 1 by omega] at ih'
    have h1 : ((j - c : ℕ) : ℚ) = (j : ℚ) - c := by push_cast [Nat.cast_sub (by omega : c ≤ j)]; ring
    rw [← Nat.mul_factorial_pred (by omega : j - c ≠ 0), show j - c - 1 = j - (c + 1) by omega]
    have e : ((j - c - (M + 1) - 1).factorial : ℚ) * ((-(j : ℚ) + ((c : ℕ) : ℚ)) *
        ∏ l ∈ Icc (c + 1) (c + 1 + M), (-(j : ℚ) + l)) =
        (-(j : ℚ) + c) * (((j - c - (M + 1) - 1).factorial : ℚ) *
          ∏ l ∈ Icc (c + 1) (c + 1 + M), (-(j : ℚ) + l)) := by ring
    rw [e, ih']
    push_cast [h1]; ring

/-- The jet `(ρ_c(j), σ_c(j))` of `(t+j) L_c(t)` at `-j` is `(-1)^{j+c}` times the lower jet
`C(15n, j - c - ε)`, for every `j`. -/
theorem rs_jet (n c j : ℕ) :
    jet (rho n c j) (sig n c j) = ((-1 : ℚ) ^ (j + c)) • lowerJet (15 * n) ((j : ℤ) - c) := by
  have hrho : ∀ h : ¬ (c ≤ j ∧ j ≤ c + 15 * n), rho n c j = 0 := fun h => by
    unfold rho; exact ite_eq_right h
  by_cases h1 : c ≤ j ∧ j ≤ c + 15 * n
  · -- interior
    have hr : rho n c j = (-1) ^ (j - c) * ((15 * n).choose (j - c) : ℤ) := by
      unfold rho; exact ite_eq_left h1
    rw [lowerJet, ite_eq_left ⟨by omega, by omega⟩, show ((j : ℤ) - c).toNat = j - c by omega,
      jet_smul, sig_in n c j h1.1 h1.2, show 15 * n - (j - c) = c + 15 * n - j by omega, hr,
      show j + c = (j - c) + 2 * c by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
    push_cast
    congr 1; ring
  by_cases h2 : j < c
  · -- below the support: `σ_c(j) = (15n)! (r-1)!/(r+15n)!`, `r = c - j`
    have hS : j ∉ Icc c (c + 15 * n) := by simp only [mem_Icc]; omega
    have he := BaselineIntegrality.Aux.sig_mul_e_out n c j h1
    rw [BaselineIntegrality.Aux.Qp_eval, erase_eq_of_notMem hS] at he
    have hp := prod_low c (15 * n) j h2
    have hP : ∏ l ∈ Icc c (c + 15 * n), (-(j : ℚ) + l) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hp; exact (Nat.factorial_ne_zero _) (by exact_mod_cast hp.symm)
    have hs : sig n c j = ((15 * n).factorial : ℚ) * (c - j - 1).factorial /
        (c - j + 15 * n).factorial := by
      rw [← hp, eq_div_iff (by rw [hp]; positivity)]
      change BaselineIntegrality.Aux.sigA n c j * _ = _ at he
      change BaselineIntegrality.Aux.sigA n c j * _ = _
      linear_combination ((c - j - 1).factorial : ℚ) * he
    rw [lowerJet, ite_eq_right (by omega), ite_eq_left (by omega), show (-((j : ℤ) - c)).toNat = c - j by omega,
      jet_smul, hrho h1, hs, show j + c = (c - j) + 2 * j by omega, pow_add, pow_mul, neg_one_sq,
      one_pow, mul_one]
    have hsq : ((-1 : ℚ) ^ (c - j)) * (-1) ^ (c - j) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    push_cast
    congr 1
    · ring
    · rw [show 15 * n + (c - j) = c - j + 15 * n by ring]
      linear_combination (-((15 * n).factorial : ℚ) * ((c - j - 1).factorial : ℚ) /
        ((c - j + 15 * n).factorial : ℚ)) * hsq
  · -- above the support: `σ_c(j) = (-1)^{15n+1} (15n)! (r-1)!/(j-c)!`, `r = j - c - 15n`
    have hS : j ∉ Icc c (c + 15 * n) := by simp only [mem_Icc]; omega
    have he := BaselineIntegrality.Aux.sig_mul_e_out n c j h1
    rw [BaselineIntegrality.Aux.Qp_eval, erase_eq_of_notMem hS] at he
    have hp := prod_high (15 * n) c j (by omega)
    obtain ⟨r, hr⟩ : ∃ r, j - c - 15 * n = r + 1 := ⟨j - c - 15 * n - 1, by omega⟩
    have hs : sig n c j = (-1) ^ (15 * n + 1) * ((15 * n).factorial : ℚ) * r.factorial /
        (j - c).factorial := by
      rw [show j - c - 15 * n - 1 = r by omega] at hp
      have hsq : ((-1 : ℚ) ^ (15 * n + 1)) * (-1) ^ (15 * n + 1) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
      rw [eq_div_iff (by positivity)]
      change BaselineIntegrality.Aux.sigA n c j * _ = _ at he
      change BaselineIntegrality.Aux.sigA n c j * _ = _
      linear_combination ((-1 : ℚ) ^ (15 * n + 1) * (r.factorial : ℚ)) * he -
        BaselineIntegrality.Aux.sigA n c j * (-1) ^ (15 * n + 1) * hp -
        BaselineIntegrality.Aux.sigA n c j * (j - c).factorial * hsq
    rw [lowerJet, ite_eq_right (by omega), ite_eq_right (by omega),
      show ((j : ℤ) - c - (15 * n : ℕ)).toNat = r + 1 by omega, jet_smul, hrho h1, hs,
      show j + c = (15 * n + (r + 1)) + 2 * c by omega, pow_add (-1 : ℚ) _ (2 * c), pow_mul,
      neg_one_sq, one_pow, mul_one, show 15 * n + (r + 1) = j - c by omega, Nat.add_sub_cancel]
    have hsq : ((-1 : ℚ) ^ r) * (-1) ^ r = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    push_cast
    congr 1
    · ring
    · rw [show j - c = 15 * n + 1 + r by omega, pow_add]
      linear_combination (-((-1 : ℚ) ^ (15 * n + 1) * ((15 * n).factorial : ℚ) *
        (r.factorial : ℚ) / ((15 * n + 1 + r).factorial : ℚ))) * hsq

/-! ### The bridge -/

/-- **Bridge.** `(C_n a_j, C_n b_j) = (-1)^n (U_{n,j}, V_{n,j})` as jets. -/
theorem bridge (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    jet (Cn n * aCoef n j) (Cn n * bCoef n j) = ((-1 : ℚ) ^ n) • coeffJet n j := by
  have h1 : jet (Cn n * aCoef n j) (Cn n * bCoef n j) =
      pjet (Pbin n) (-(j : ℚ)) * jet (rho n n j) (sig n n j) *
        jet (rho n (2 * n) j) (sig n (2 * n) j) := by
    rw [aCoef_formula n hn j, bCoef_formula n hn j, pjet, jet_mul, jet_mul]
    congr 1 <;> ring
  have hs : ((-1 : ℚ) ^ (j + n)) * (-1) ^ (j + 2 * n) = (-1) ^ n := by
    rw [← pow_add, show j + n + (j + 2 * n) = n + 2 * (j + n) by ring, pow_add, pow_mul,
      neg_one_sq, one_pow, mul_one]
  rw [h1, pjet_Pbin, rs_jet, rs_jet, coeffJet, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
    smul_smul, mul_comm ((-1 : ℚ) ^ (j + 2 * n)), hs]
  push_cast
  rfl

theorem aCoef_eq (n : ℕ) (hn : 1 ≤ n) (j : ℕ) : Cn n * aCoef n j = (-1) ^ n * U n j := by
  have h := congrArg TrivSqZeroExt.fst (bridge n hn j)
  rwa [jet_fst, TrivSqZeroExt.fst_smul, smul_eq_mul] at h

theorem bCoef_eq (n : ℕ) (hn : 1 ≤ n) (j : ℕ) : Cn n * bCoef n j = (-1) ^ n * V n j := by
  have h := congrArg TrivSqZeroExt.snd (bridge n hn j)
  rwa [jet_snd, TrivSqZeroExt.snd_smul, smul_eq_mul] at h

end Meijer5255.BaselineProfile.Jets
