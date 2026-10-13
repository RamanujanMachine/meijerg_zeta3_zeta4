/-
# Helper for `BaselineProfile` [8]: the upper harmonic range bound

For eligible `16n < p < 19n` (pfq54 `upper_range_bound.lean`, `uv_aux.lean`, `jet_aux.lean`,
adapted to `Z3v`/`Z4v` through the bridge `C_n a_j = (-1)^n U_{n,j}`, `C_n b_j = (-1)^n V_{n,j}`):
* active indices `j + 2n ≥ p`: `v_p(U_{n,j}) ≥ h₀`, `v_p(V_{n,j}) ≥ h₀ - 1` (pfq54 `UV_active`);
* inactive indices `j + 2n < p` (`n ≤ j`): `U_{n,j}` and `V_{n,j}` are `p`-integral, since the
  jets are integral with derivative cleared by `d_{p-1}`, a `p`-unit (this sharpens pfq54's
  `v_p(V) ≥ -1`, as needed for the order-three form `Z3v`);
* `v_p(d_{19n}) = 1`, `v_p(H^{(s)}_m) ≥ -s` for `m < p²` and `≥ 0` for `m < p`.
The `ValGE` closure lemmas are those of zeta34 `ZetasAux.lean` (renamed `vmul`, `vadd`, …).
-/
import Meijer5255.BaselineProfile_Perm

open Finset Polynomial

noncomputable section

namespace Meijer5255.BaselineProfile.Jets

open Meijer5255

/-! ### `ValGE` closure (zeta34 `ZetasAux.lean`, `valuation_bound.lean`) -/

section ValGE

variable {p : ℕ} [Fact p.Prime]

theorem vmul {a b : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p b y) :
    ValGE p (a + b) (x * y) := by
  rcases hx with rfl | hx
  · left; simp
  rcases hy with rfl | hy
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  by_cases hy0 : y = 0
  · left; simp [hy0]
  right; rw [padicValRat.mul hx0 hy0]; omega

omit [Fact p.Prime] in
theorem vneg {a : ℤ} {x : ℚ} (hx : ValGE p a x) : ValGE p a (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [padicValRat.neg]

theorem vadd {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem vsub {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x - y) := by
  rw [sub_eq_add_neg]; exact vadd hx (vneg hy)

omit [Fact p.Prime] in
theorem vmono {a b : ℤ} (hab : b ≤ a) {x : ℚ} (hx : ValGE p a x) : ValGE p b x :=
  hx.imp id fun h => hab.trans h

theorem vsum {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℚ)
    (h : ∀ i ∈ s, ValGE p a (f i)) : ValGE p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact vadd (h x (Finset.mem_insert_self x s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fact p.Prime] in
theorem vint (z : ℤ) : ValGE p 0 (z : ℚ) := by
  rcases eq_or_ne z 0 with h | h
  · left; rw [h, Int.cast_zero]
  · right; rw [padicValRat.of_int]; exact Nat.cast_nonneg _

omit [Fact p.Prime] in
theorem vnat (m : ℕ) : ValGE p 0 (m : ℚ) := by
  have := vint (p := p) (m : ℤ); rwa [Int.cast_natCast] at this

omit [Fact p.Prime] in
/-- A positive integer below `p` is a `p`-unit. -/
theorem val_small (q : ℕ) (hq : 0 < q) (hqp : q < p) : padicValRat p (q : ℚ) = 0 := by
  rw [padicValRat.of_nat]
  exact_mod_cast padicValNat.eq_zero_of_not_dvd fun h => absurd (Nat.le_of_dvd hq h) (by omega)

theorem vunit_inv (q : ℕ) (hq : 0 < q) (hqp : q < p) : ValGE p 0 ((q : ℚ)⁻¹) :=
  Or.inr (by rw [padicValRat.inv, val_small q hq hqp, neg_zero])

theorem vsign (n : ℕ) : ValGE p 0 ((-1 : ℚ) ^ n) :=
  Or.inr (by rw [padicValRat.pow, padicValRat.neg, padicValRat.one, mul_zero])

/-- `v_p(H^{(s)}_m) ≥ -s` for `m < p²`, and `H^{(s)}_m` is `p`-integral for `m < p`. -/
theorem harm_val (s m : ℕ) (hm : m < p ^ 2) :
    ValGE p (-(s : ℤ)) (harm s m) ∧ (m < p → ValGE p 0 (harm s m)) := by
  have key : ∀ k ∈ Icc 1 m, ∀ b : ℕ, padicValNat p k ≤ b →
      ValGE p (-((s : ℤ) * b)) (1 / (k : ℚ) ^ s) := by
    intro k hk b hb
    have hk0 : k ≠ 0 := by simp only [mem_Icc] at hk; omega
    right
    rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
    have : ((padicValNat p k : ℕ) : ℤ) ≤ b := by exact_mod_cast hb
    nlinarith [(Nat.cast_nonneg s : (0 : ℤ) ≤ s)]
  refine ⟨vsum _ _ _ fun k hk => ?_, fun hmp => vsum _ _ _ fun k hk => ?_⟩
  · have hk0 : k ≠ 0 := by simp only [mem_Icc] at hk; omega
    have h1 : padicValNat p k ≤ 1 := by
      by_contra h
      have hd : p ^ 2 ∣ k := (padicValNat_dvd_iff_le hk0).2 (by omega)
      have := Nat.le_of_dvd (by omega) hd
      simp only [mem_Icc] at hk; omega
    have := key k hk 1 h1
    rwa [Nat.cast_one, mul_one] at this
  · have h0 : padicValNat p k ≤ 0 := by
      rw [padicValNat.eq_zero_of_not_dvd]
      intro h
      have := Nat.le_of_dvd (by simp only [mem_Icc] at hk; omega) h
      simp only [mem_Icc] at hk; omega
    have := key k hk 0 h0
    rwa [Nat.cast_zero, mul_zero, neg_zero] at this

/-- `v_p(d_m) = 1` for `p ≤ m < p²` (as `CarryFacts.padicValNat_dlcm`). -/
theorem val_dlcm (m : ℕ) (h1 : p ≤ m) (h2 : m < p ^ 2) : padicValRat p (dlcm m : ℚ) = 1 := by
  have hp : p.Prime := Fact.out
  have hv : padicValNat p (dlcm m) = 1 := by
    have h := Nat.factorization_lcmUpto m hp
    rw [Nat.factorization_def _ hp] at h
    change padicValNat p (Nat.lcmUpto m) = 1
    rw [h, Nat.log_eq_one_iff']
    exact ⟨h1, by rwa [← pow_two]⟩
  rw [padicValRat.of_nat, hv]; rfl

/-- `d_{p-1}` is a `p`-unit. -/
theorem val_dlcm_pred : padicValRat p (dlcm (p - 1) : ℚ) = 0 := by
  have hp : p.Prime := Fact.out
  have hv : padicValNat p (dlcm (p - 1)) = 0 := by
    have h := Nat.factorization_lcmUpto (p - 1) hp
    rw [Nat.factorization_def _ hp] at h
    change padicValNat p (Nat.lcmUpto (p - 1)) = 0
    rw [h, Nat.log_of_lt (by have := hp.pos; omega)]
  rw [padicValRat.of_nat, hv]; rfl

end ValGE

/-! ### Inactive indices: `U`, `V` are `p`-integral -/

/-- Integrality of the coefficient jet with `d_L`, for `n ≤ j ≤ L` and `16n ≤ L`. -/
theorem coeffJet_integral_L (n j L : ℕ) (hj1 : n ≤ j) (hjL : j ≤ L) (hL : 16 * n ≤ L) :
    (∃ z : ℤ, (coeffJet n j).fst = z) ∧ ∃ z : ℤ, (dlcm L : ℚ) * (coeffJet n j).snd = z := by
  let Q : Jet → Prop := fun c => (∃ z : ℤ, c.fst = z) ∧ ∃ z : ℤ, (dlcm L : ℚ) * c.snd = z
  have hmul : ∀ a b, Q a → Q b → Q (a * b) := fun a b ha hb =>
    jet_mul_integral _ a b ha.1 ha.2 hb.1 hb.2
  have hone : Q 1 := ⟨⟨1, by rw [TrivSqZeroExt.fst_one, Int.cast_one]⟩,
    ⟨0, by rw [TrivSqZeroExt.snd_one, mul_zero, Int.cast_zero]⟩⟩
  have hP : Q (∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n)) :=
    Finset.prod_induction _ Q hmul hone fun u _ => upperJet_integral _ _ _ (by omega)
  have hl1 : Q (lowerJet (15 * n) ((j : ℤ) - n)) :=
    lowerJet_integral (15 * n) L _ (by omega) (by omega) (by omega)
  have hl2 : Q (lowerJet (15 * n) ((j : ℤ) - 2 * n)) :=
    lowerJet_integral (15 * n) L _ (by omega) (by omega) (by omega)
  exact hmul _ _ (hmul _ _ hP hl1) hl2

theorem UV_inactive (n p j : ℕ) [Fact p.Prime] (hlo : 16 * n < p) (hj1 : n ≤ j)
    (hact : j + 2 * n < p) : ValGE p 0 (U n j) ∧ ValGE p 0 (V n j) := by
  obtain ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩ := coeffJet_integral_L n j (p - 1) hj1 (by omega) (by omega)
  refine ⟨by rw [U, hz]; exact vint z, ?_⟩
  rcases eq_or_ne (V n j) 0 with h | h
  · exact Or.inl h
  right
  have hd : (dlcm (p - 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.lcmUpto_ne_zero (p - 1))
  have h1 := padicValRat.mul (p := p) hd h
  rw [V, hz', padicValRat.of_int, val_dlcm_pred] at h1
  rw [V]
  have : (0 : ℤ) ≤ (padicValInt p z' : ℤ) := Nat.cast_nonneg _
  linarith

/-! ### Active indices (pfq54 `jet_aux.lean`, `uv_aux.lean`) -/

theorem jet_mul_log (a x b y : ℚ) :
    jet a (a * x) * jet b (b * y) = jet (a * b) (a * b * (x + y)) := by
  rw [jet_mul]; congr 1; ring

theorem jet_mul_zero (a x s : ℚ) : jet a x * jet 0 s = jet 0 (a * s) := by
  rw [jet_mul]; congr 1 <;> ring

theorem jet_zero_mul (s b y : ℚ) : jet 0 s * jet b y = jet 0 (s * b) := by
  rw [jet_mul]; congr 1 <;> ring

theorem upperJet_log (N M : ℕ) (h : M ≤ N) :
    upperJet N M = jet (N.choose M) (N.choose M * -(harm 1 N - harm 1 (N - M))) := by
  rw [upperJet, ite_eq_left h, neg_mul, mul_neg]

theorem lowerJet_log (M m : ℕ) (h : m ≤ M) :
    lowerJet M (m : ℤ) = jet (M.choose m) (M.choose m * (harm 1 m - harm 1 (M - m))) := by
  rw [lowerJet, ite_eq_left ⟨Int.natCast_nonneg m, Int.ofNat_le.mpr h⟩, Int.toNat_natCast]

theorem lowerJet_big (M d : ℕ) (hd : 0 < d) :
    lowerJet M ((M + d : ℕ) : ℤ) =
      jet 0 ((-1 : ℚ) ^ (d - 1) * M.factorial * (d - 1).factorial / (M + d).factorial) := by
  rw [lowerJet, ite_eq_right (by omega), ite_eq_right (by omega),
    show ((M + d : ℕ) : ℤ) - M = d by push_cast; ring, Int.toNat_natCast]

/-- The value of the three upper binomials. -/
def Cu (n j : ℕ) : ℚ :=
  ((j + 10 * n).choose (10 * n) : ℚ) * ((j + 11 * n).choose (10 * n) : ℚ) *
    ((j + 12 * n).choose (10 * n) : ℚ)

/-- The logarithmic derivative of the three upper binomials. -/
def Xu (n j : ℕ) : ℚ :=
  -(harm 1 (j + 10 * n) - harm 1 (j + 10 * n - 10 * n)) +
    -(harm 1 (j + 11 * n) - harm 1 (j + 11 * n - 10 * n)) +
      -(harm 1 (j + 12 * n) - harm 1 (j + 12 * n - 10 * n))

theorem upper_jets (n j : ℕ) :
    ∏ u ∈ Icc 10 12, upperJet (j + u * n) (10 * n) = jet (Cu n j) (Cu n j * Xu n j) := by
  rw [prod_Icc_10_12, upperJet_log (j + 10 * n) (10 * n) (by omega),
    upperJet_log (j + 11 * n) (10 * n) (by omega), upperJet_log (j + 12 * n) (10 * n) (by omega),
    jet_mul_log, jet_mul_log]
  rfl

section Active

variable (p : ℕ) [hp : Fact p.Prime]

theorem padicValNat_factorial_small (m : ℕ) (hm : m < p ^ 2) :
    padicValNat p m.factorial = m / p := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp
  have hlog : Nat.log p m < 2 := Nat.log_lt_of_lt_pow (by omega) hm
  rw [padicValNat_factorial hlog]
  simp

theorem div_two (m : ℕ) (hm : m < 2 * p) : m / p = if p ≤ m then 1 else 0 := by
  have hp0 := hp.out.pos
  split_ifs with h
  · exact Nat.div_eq_of_lt_le (by omega) (by omega)
  · exact Nat.div_eq_of_lt (by omega)

/-- `v_p C(N, M) = 𝟙_{p ≤ N} - 𝟙_{p ≤ N - M}` for `M < p` and `N < 2p`. -/
theorem val_choose (N M : ℕ) (hMN : M ≤ N) (hN : N < 2 * p) (hM : M < p) :
    padicValRat p ((N.choose M : ℕ) : ℚ) =
      (if p ≤ N then 1 else 0) - (if p ≤ N - M then 1 else 0) := by
  have h2 : 2 * p ≤ p ^ 2 := by
    have := hp.out.two_le
    nlinarith
  have key := Nat.choose_mul_factorial_mul_factorial hMN
  have hc : N.choose M ≠ 0 := (Nat.choose_pos hMN).ne'
  have e := congrArg (padicValNat p) key
  rw [padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero M)) (Nat.factorial_ne_zero _),
    padicValNat.mul hc (Nat.factorial_ne_zero M), padicValNat_factorial_small p _ (by omega),
    padicValNat_factorial_small p _ (by omega), padicValNat_factorial_small p _ (by omega),
    Nat.div_eq_of_lt hM, div_two p _ (by omega), div_two p _ hN] at e
  rw [padicValRat.of_nat]
  split_ifs at e ⊢ <;> omega

/-- The three upper binomials. -/
theorem val_Cu (n j : ℕ) (h10 : 10 * n < p) (hlo : p ≤ j + 10 * n) (hhi : j + 12 * n < 2 * p) :
    ValGE p (3 - ((if p ≤ j then 1 else 0) + (if p ≤ j + n then 1 else 0) +
      (if p ≤ j + 2 * n then 1 else 0))) (Cu n j) := by
  right
  have c10 : ((j + 10 * n).choose (10 * n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c11 : ((j + 11 * n).choose (10 * n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have c12 : ((j + 12 * n).choose (10 * n) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  unfold Cu
  rw [padicValRat.mul (mul_ne_zero c10 c11) c12, padicValRat.mul c10 c11,
    val_choose p _ _ (by omega) (by omega) h10, val_choose p _ _ (by omega) (by omega) h10,
    val_choose p _ _ (by omega) (by omega) h10, show j + 10 * n - 10 * n = j by omega,
    show j + 11 * n - 10 * n = j + n by omega, show j + 12 * n - 10 * n = j + 2 * n by omega,
    ite_eq_left (by omega : p ≤ j + 10 * n), ite_eq_left (by omega : p ≤ j + 11 * n),
    ite_eq_left (by omega : p ≤ j + 12 * n)]
  omega

/-- **The upper ranges** (pfq54 `UV.UV_active`): double poles keep `3 - t` powers in `U` and
lose one in `V`; at the simple poles `U = 0` and `V` keeps `3 - t`. -/
theorem UV_active (n j : ℕ) (hH : ∀ m, m < p ^ 2 → ValGE p (-1) (harm 1 m))
    (h15 : 16 * n < p) (h2p : 29 * n < 2 * p) (hsq : 29 * n < p ^ 2) (hj : j ≤ 17 * n)
    (hact : p ≤ j + 2 * n) :
    (j ≤ 16 * n → ValGE p (3 - ((if p ≤ j then 1 else 0) + (if p ≤ j + n then 1 else 0) + 1))
      (U n j) ∧ ValGE p (2 - ((if p ≤ j then 1 else 0) + (if p ≤ j + n then 1 else 0) + 1))
      (V n j)) ∧
    (16 * n < j → U n j = 0 ∧ ValGE p (3 - ((if p ≤ j then 1 else 0) +
      (if p ≤ j + n then 1 else 0) + 1)) (V n j)) := by
  have hCu := val_Cu p n j (by omega) (by omega) (by omega)
  rw [ite_eq_left hact] at hCu
  have hH' : ∀ m, m ≤ 29 * n → ValGE p (-1) (harm 1 m) := fun m hm => hH m (by omega)
  refine ⟨fun h2 => ?_, fun h2 => ?_⟩
  · have hJ : coeffJet n j = jet (Cu n j * ((15 * n).choose (j - n) : ℚ) *
        ((15 * n).choose (j - 2 * n) : ℚ))
        (Cu n j * ((15 * n).choose (j - n) : ℚ) * ((15 * n).choose (j - 2 * n) : ℚ) *
          (Xu n j + (harm 1 (j - n) - harm 1 (15 * n - (j - n))) +
            (harm 1 (j - 2 * n) - harm 1 (15 * n - (j - 2 * n))))) := by
      unfold coeffJet
      rw [upper_jets, show (j : ℤ) - n = ((j - n : ℕ) : ℤ) by omega,
        show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
        lowerJet_log (15 * n) (j - n) (by omega), lowerJet_log (15 * n) (j - 2 * n) (by omega),
        jet_mul_log, jet_mul_log]
    have hU := vmul (vmul hCu (vnat (p := p) ((15 * n).choose (j - n))))
      (vnat (p := p) ((15 * n).choose (j - 2 * n)))
    rw [add_zero, add_zero] at hU
    have hL : ValGE p (-1) (Xu n j + (harm 1 (j - n) - harm 1 (15 * n - (j - n))) +
        (harm 1 (j - 2 * n) - harm 1 (15 * n - (j - 2 * n)))) := by
      unfold Xu
      exact vadd (vadd (vadd (vadd (vneg (vsub (hH' _ (by omega)) (hH' _ (by omega))))
        (vneg (vsub (hH' _ (by omega)) (hH' _ (by omega)))))
          (vneg (vsub (hH' _ (by omega)) (hH' _ (by omega)))))
            (vsub (hH' _ (by omega)) (hH' _ (by omega))))
              (vsub (hH' _ (by omega)) (hH' _ (by omega)))
    refine ⟨by rw [U, hJ, jet_fst]; exact hU, ?_⟩
    rw [V, hJ, jet_snd]
    exact vmono (by omega) (vmul hU hL)
  · have hJ : coeffJet n j = jet 0 (Cu n j * ((-1 : ℚ) ^ (j - 16 * n - 1) *
        (15 * n).factorial * (j - 16 * n - 1).factorial / (15 * n + (j - 16 * n)).factorial) *
          ((15 * n).choose (j - 2 * n) : ℚ)) := by
      unfold coeffJet
      rw [upper_jets, show (j : ℤ) - n = ((15 * n + (j - 16 * n) : ℕ) : ℤ) by omega,
        show (j : ℤ) - 2 * n = ((j - 2 * n : ℕ) : ℤ) by omega,
        lowerJet_big (15 * n) (j - 16 * n) (by omega),
        lowerJet_log (15 * n) (j - 2 * n) (by omega), jet_mul_zero, jet_zero_mul]
    have hden : ValGE p 0 (((15 * n + (j - 16 * n)).factorial : ℚ))⁻¹ := by
      right
      rw [padicValRat.inv, padicValRat.of_nat, padicValNat_factorial_small p _ (by omega),
        Nat.div_eq_of_lt (by omega), Nat.cast_zero, neg_zero]
    have hs1 := vmul (vmul (vmul (vsign (p := p) (j - 16 * n - 1))
      (vnat (p := p) (15 * n).factorial)) (vnat (p := p) (j - 16 * n - 1).factorial)) hden
    rw [← div_eq_mul_inv] at hs1
    refine ⟨by rw [U, hJ, jet_fst], ?_⟩
    rw [V, hJ, jet_snd]
    exact vmono (by omega) (vmul (vmul hCu hs1) (vnat (p := p) ((15 * n).choose (j - 2 * n))))

end Active

/-! ### The bound -/

/-- Per-index valuations in the upper range: with `d_{19n}^r` (`r ≥ 3`) and the harmonic
numbers attached, every term gains `h₀`. -/
theorem upper_terms (n p : ℕ) (hp : Eligible n p) (hlo : 16 * n < p) (hhi : p < 19 * n)
    (j : ℕ) (hj : j ∈ Icc n (17 * n)) :
    (∀ r : ℕ, 3 ≤ r → ValGE p (hgain n p) ((dlcm (19 * n) : ℚ) ^ r * U n j)) ∧
      (∀ r s : ℕ, 3 ≤ r → s ≤ r →
        ValGE p (hgain n p) ((dlcm (19 * n) : ℚ) ^ r * U n j * harm s (j + 2 * n))) ∧
      (∀ r s : ℕ, 3 ≤ r → s + 1 ≤ r →
        ValGE p (hgain n p) ((dlcm (19 * n) : ℚ) ^ r * V n j * harm s (j + 2 * n))) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hsq : 30 * n < p ^ 2 := hp.2.2.1
  simp only [mem_Icc] at hj
  have hdr : ∀ r : ℕ, ValGE p r ((dlcm (19 * n) : ℚ) ^ r) := fun r => Or.inr (by
    rw [padicValRat.pow,
      val_dlcm (19 * n) (by omega) (by nlinarith)]; simp)
  have hh3 : hgain n p ≤ 3 := by unfold hgain; split_ifs <;> omega
  rcases lt_or_ge (j + 2 * n) p with hact | hact
  · -- inactive
    obtain ⟨hU, hV⟩ := UV_inactive n p j (by omega) hj.1 hact
    have hH := fun s => (harm_val (p := p) s (j + 2 * n) (by nlinarith)).2 hact
    exact ⟨fun r hr => vmono (by omega) (vmul (hdr r) hU),
      fun r s hr _ => vmono (by omega) (vmul (vmul (hdr r) hU) (hH s)),
      fun r s hr _ => vmono (by omega) (vmul (vmul (hdr r) hV) (hH s))⟩
  · -- active
    have hH1 : ∀ m, m < p ^ 2 → ValGE p (-1) (harm 1 m) := fun m hm => by
      have := (harm_val (p := p) 1 m hm).1; rwa [Nat.cast_one] at this
    obtain ⟨hd, hs⟩ := UV_active p n j hH1 hlo (by omega) (by nlinarith) hj.2 hact
    have hUV : ValGE p (hgain n p) (U n j) ∧ ValGE p ((hgain n p : ℤ) - 1) (V n j) := by
      unfold hgain
      rcases le_or_gt j (16 * n) with h1 | h1
      · obtain ⟨hU, hV⟩ := hd h1
        split_ifs <;> exact ⟨vmono (by split_ifs <;> omega) hU, vmono (by split_ifs <;> omega) hV⟩
      · obtain ⟨hU, hV⟩ := hs h1
        split_ifs <;> exact ⟨Or.inl hU, vmono (by split_ifs <;> omega) hV⟩
    have hH := fun s => (harm_val (p := p) s (j + 2 * n) (by nlinarith)).1
    refine ⟨fun r hr => vmono (by omega) (vmul (hdr r) hUV.1), fun r s _ hs' => ?_,
      fun r s hr hs' => ?_⟩
    · exact vmono (by omega) (vmul (vmul (hdr r) hUV.1) (hH s))
    · exact vmono (by omega) (vmul (vmul (hdr r) hUV.2) (hH s))

/-- **Upper harmonic range bound** for both integer forms. -/
theorem upper_range (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (hlo : 16 * n < p)
    (hhi : p < 19 * n) :
    (∀ i, ValGE p (hgain n p : ℤ) (Z3v n i)) ∧ (∀ i, ValGE p (hgain n p : ℤ) (Z4v n i)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hc : ∀ m : ℕ, ValGE p 0 ((-1 : ℚ) ^ n * (m : ℚ)) := fun m =>
    vmono (by norm_num) (vmul (vsign n) (vnat m))
  have c6 : ValGE p 0 ((-1 : ℚ) ^ n * 6) := by have := hc 6; rwa [Nat.cast_ofNat] at this
  have c3 : ValGE p 0 ((-1 : ℚ) ^ n * 3) := by have := hc 3; rwa [Nat.cast_ofNat] at this
  have c2 : ValGE p 0 ((-1 : ℚ) ^ n * 2) := by have := hc 2; rwa [Nat.cast_ofNat] at this
  have hT := fun j hj => upper_terms n p hp hlo hhi j hj
  set d : ℚ := (dlcm (19 * n) : ℚ) with hd_def
  have hQ : ∀ r : ℕ, 3 ≤ r → ValGE p (hgain n p) (6 * Cn n * d ^ r * Q n) := fun r hr => by
    rw [Q, mul_sum]
    refine vsum _ _ _ fun j hj => ?_
    have e : 6 * Cn n * d ^ r * aCoef n j = ((-1 : ℚ) ^ n * 6) * (d ^ r * U n j) := by
      linear_combination (6 * d ^ r) * aCoef_eq n hn j
    rw [e]
    exact vmono (by omega) (vmul c6 ((hT j hj).1 r hr))
  have hP3 : ∀ r : ℕ, 3 ≤ r → ValGE p (hgain n p) (6 * Cn n * d ^ r * P3 n) := fun r hr => by
    rw [P3, mul_sum]
    refine vsum _ _ _ fun j hj => ?_
    have e : 6 * Cn n * d ^ r * (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2) =
        ((-1 : ℚ) ^ n * 6) * (d ^ r * U n j * harm 3 (j + 2 * n)) +
          ((-1 : ℚ) ^ n * 3) * (d ^ r * V n j * harm 2 (j + 2 * n)) := by
      linear_combination (6 * d ^ r * harm 3 (j + 2 * n)) * aCoef_eq n hn j +
        (3 * d ^ r * harm 2 (j + 2 * n)) * bCoef_eq n hn j
    rw [e]
    exact vadd (vmono (by omega) (vmul c6 ((hT j hj).2.1 r 3 hr hr)))
      (vmono (by omega) (vmul c3 ((hT j hj).2.2 r 2 hr (by omega))))
  have hP4 : ValGE p (hgain n p) (6 * Cn n * d ^ 4 * P4 n) := by
    rw [P4, mul_sum]
    refine vsum _ _ _ fun j hj => ?_
    have e : 6 * Cn n * d ^ 4 * (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3) =
        ((-1 : ℚ) ^ n * 6) * (d ^ 4 * U n j * harm 4 (j + 2 * n)) +
          ((-1 : ℚ) ^ n * 2) * (d ^ 4 * V n j * harm 3 (j + 2 * n)) := by
      linear_combination (6 * d ^ 4 * harm 4 (j + 2 * n)) * aCoef_eq n hn j +
        (2 * d ^ 4 * harm 3 (j + 2 * n)) * bCoef_eq n hn j
    rw [e]
    exact vadd (vmono (by omega) (vmul c6 ((hT j hj).2.1 4 4 (by norm_num) le_rfl)))
      (vmono (by omega) (vmul c2 ((hT j hj).2.2 4 3 (by norm_num) (by norm_num))))
  refine ⟨fun i => ?_, fun i => ?_⟩
  · fin_cases i
    · exact hQ 3 le_rfl
    · exact hP3 3 le_rfl
  · fin_cases i
    · exact hQ 4 (by norm_num)
    · exact hP3 4 (by norm_num)
    · exact hP4

end Meijer5255.BaselineProfile.Jets
