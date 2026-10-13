/-
# Helper for `WindowReadout.lean`: individual bounds from the root counts

If every residue class `k ∈ [1, p]` has `|D_k| ≤ |N_k| + 1` (the window root data `h_k ≥ -1`),
then `a_j ∈ pℤ_(p)` and `b_j ∈ ℤ_(p)` for every `j` (`p` eligible). At a pole `x = -j`, every
factor `x - z` of `N(x)` and `E(x)` is a nonzero integer of absolute value `< 30n < p²`, so its
valuation is `1` or `0` according to `p ∣ x - z`; hence `v_p(N(x)/E(x)) = h_k + e_x`, and
`b = (N/E)(x) · (∑ 1/(x-z) - ∑ 1/(x-y))` (logarithmic derivative) loses at most one `p`.
-/
import Meijer5255.WindowReadout_Residue

open Polynomial Finset

noncomputable section

namespace Meijer5255.WindowReadoutAux

open Meijer5255 Meijer5255.WindowReadout

section ValGEcalc

variable {p : ℕ} [Fact p.Prime]

theorem valGE_mul {a b : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p b y) :
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

theorem valGE_add {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

omit [Fact p.Prime] in
theorem valGE_neg {a : ℤ} {x : ℚ} (hx : ValGE p a x) : ValGE p a (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [padicValRat.neg]

theorem valGE_msum (a : ℤ) (s : Multiset ℚ) (h : ∀ q ∈ s, ValGE p a q) : ValGE p a s.sum := by
  induction s using Multiset.induction_on with
  | empty => exact Or.inl (by simp)
  | cons q s ih =>
    rw [Multiset.sum_cons]
    exact valGE_add (h q (Multiset.mem_cons_self _ _))
      (ih fun r hr => h r (Multiset.mem_cons_of_mem hr))

/-- The valuation of a nonzero integer of absolute value `< p²`. -/
theorem padicValRat_small (d : ℤ) (hd : d ≠ 0) (hlt : d.natAbs < p ^ 2) :
    padicValRat p (d : ℚ) = if (p : ℤ) ∣ d then 1 else 0 := by
  rw [padicValRat.of_int]
  have h2 : ¬ 2 ≤ padicValInt p d := by
    intro h2
    rcases (padicValInt_dvd_iff 2 d).2 (Or.inr h2) with hdvd
    have := Nat.le_of_dvd (Int.natAbs_pos.2 hd)
      (by simpa [Int.natAbs_pow] using Int.natAbs_dvd_natAbs.2 hdvd)
    omega
  split_ifs with h
  · have h1 := ((padicValInt_dvd_iff 1 d).1 (by simpa using h)).resolve_left hd
    have : padicValInt p d = 1 := by omega
    rw [this]; rfl
  · have h0 : ¬ 1 ≤ padicValInt p d := fun h1 =>
      h (by simpa using (padicValInt_dvd_iff 1 d).2 (Or.inr h1))
    have : padicValInt p d = 0 := by omega
    rw [this]; rfl

/-- The valuation of `∏_{z ∈ s} (x - z)` counts the factors divisible by `p`. -/
theorem padicValRat_prod (x : ℤ) (s : Multiset ℤ)
    (hs : ∀ z ∈ s, z ≠ x ∧ (x - z).natAbs < p ^ 2) :
    padicValRat p (s.map fun z : ℤ => (x : ℚ) - (z : ℚ)).prod =
      Multiset.card (s.filter fun z => (p : ℤ) ∣ x - z) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := hs a (Multiset.mem_cons_self _ _)
    have ih' := ih fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have hxa : ((x : ℚ) - (a : ℚ)) = ((x - a : ℤ) : ℚ) := by push_cast; ring
    have hxa0 : (x - a : ℤ) ≠ 0 := sub_ne_zero.2 (Ne.symm ha.1)
    have hprod : (s.map fun z : ℤ => (x : ℚ) - (z : ℚ)).prod ≠ 0 := by
      intro h0
      rw [Multiset.prod_eq_zero_iff] at h0
      obtain ⟨z, hz, hz0⟩ := Multiset.mem_map.1 h0
      have : x = z := by exact_mod_cast (sub_eq_zero.1 hz0)
      exact (hs z (Multiset.mem_cons_of_mem hz)).1 this.symm
    rw [Multiset.map_cons, Multiset.prod_cons, padicValRat.mul _ hprod, ih', hxa,
      padicValRat_small _ hxa0 ha.2, Multiset.filter_cons]
    · split_ifs <;> simp; ring
    · rw [hxa]; exact_mod_cast hxa0

end ValGEcalc

/-- Logarithmic derivative of `rootPoly s` at a non-root. -/
theorem deriv_rootPoly_eval (s : Multiset ℤ) (x : ℤ) (hx : x ∉ s) :
    (derivative (rootPoly s)).eval (x : ℚ) =
      (rootPoly s).eval (x : ℚ) * (s.map fun z : ℤ => 1 / ((x : ℚ) - (z : ℚ))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp [rootPoly_eq]
  | cons a s ih =>
    have hxa : (x : ℚ) - (a : ℚ) ≠ 0 := by
      intro h0
      apply hx
      have : x = a := by exact_mod_cast sub_eq_zero.1 h0
      rw [this]
      exact Multiset.mem_cons_self _ _
    have ih' := ih fun h => hx (Multiset.mem_cons_of_mem h)
    rw [rootPoly_cons, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add,
      eval_mul, eval_sub, eval_X, eval_C, ih', Multiset.map_cons, Multiset.sum_cons]
    field_simp

/-- **Individual bounds from `h_k ≥ -1`.** -/
theorem indiv_of_hge (n p : ℕ) [Fact p.Prime] (hp : Eligible n p)
    (hge : ∀ k ∈ Icc 1 (p : ℤ), Multiset.card (hiRoots p k (denRoots n)) ≤
      Multiset.card (hiRoots p k (numRoots n)) + 1) (j : ℕ) :
    ValGE p 1 (aCoef n j) ∧ ValGE p 0 (bCoef n j) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.1.pos
  have h30 : 30 * n < p ^ 2 := hp.2.2.1
  set x : ℤ := -(j : ℤ) with hxdef
  set Nr := numRoots n
  set Dr := denRoots n
  by_cases hx : x ∈ Dr
  swap
  · -- not a pole: both coefficients vanish
    have h0 : Dr.count x = 0 := Multiset.count_eq_zero.2 hx
    have e : pfCoeff Nr Dr x = (0, 0) := by unfold pfCoeff; simp [h0]
    refine ⟨Or.inl ?_, Or.inl ?_⟩
    · show (pfCoeff Nr Dr x).1 = 0; rw [e]
    · show (pfCoeff Nr Dr x).2 = 0; rw [e]
  have hxr := (mem_denRoots n x).1 hx
  -- the representative `k ∈ [1, p]` of `x`
  set k : ℤ := (x - 1) % p + 1 with hkdef
  have hk : k ∈ Icc 1 (p : ℤ) := by
    have := Int.emod_nonneg (x - 1) hp0.ne'
    have := Int.emod_lt_of_pos (x - 1) hp0
    rw [Finset.mem_Icc]; omega
  have hpk : (p : ℤ) ∣ x - k := by
    have := Int.mul_ediv_add_emod (x - 1) p
    exact ⟨(x - 1) / p, by omega⟩
  have hh := hge k hk
  have hcls : ∀ z : ℤ, (p : ℤ) ∣ z - k ↔ (p : ℤ) ∣ x - z := by
    intro z
    constructor
    · intro h
      have := dvd_sub hpk h
      rw [show x - k - (z - k) = x - z by ring] at this
      exact this
    · intro h
      have := dvd_sub hpk h
      rw [show x - k - (x - z) = z - k by ring] at this
      exact this
  -- the counts
  set cN := Multiset.card (Nr.filter fun z => (p : ℤ) ∣ x - z)
  set Ex := Dr.filter (· ≠ x)
  set cE := Multiset.card (Ex.filter fun z => (p : ℤ) ∣ x - z)
  have hcN : Multiset.card (hiRoots p k Nr) = cN := by
    unfold hiRoots
    rw [Multiset.card_map, Multiset.filter_congr fun z _ => hcls z]
  have hcD : Multiset.card (hiRoots p k Dr) = cE + Dr.count x := by
    unfold hiRoots
    rw [Multiset.card_map, Multiset.filter_congr fun z _ => hcls z]
    set Df := Dr.filter fun z => (p : ℤ) ∣ x - z
    have h1 := Multiset.filter_add_not (· = x) Df
    rw [Multiset.filter_eq', Multiset.count_filter_of_pos (by simp)] at h1
    have h2 : Df.filter (fun z => ¬ z = x) = Ex.filter fun z => (p : ℤ) ∣ x - z := by
      simp only [Df, Ex, Multiset.filter_filter]
      exact Multiset.filter_congr fun z _ => and_comm
    rw [← h1, h2, Multiset.card_add, Multiset.card_replicate, add_comm]
  rw [hcN, hcD] at hh
  -- valuations of `N(x)` and `E(x)`
  have hNmem : ∀ z ∈ Nr, z ≠ x ∧ (x - z).natAbs < p ^ 2 := by
    intro z hz
    simp only [Nr, numRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hz
    constructor <;> omega
  have hEmem : ∀ z ∈ Ex, z ≠ x ∧ (x - z).natAbs < p ^ 2 := by
    intro z hz
    rw [Multiset.mem_filter] at hz
    have := (mem_denRoots n z).1 hz.1
    constructor <;> omega
  have hNv : padicValRat p ((rootPoly Nr).eval (x : ℚ)) = cN := by
    rw [eval_rootPoly]; exact padicValRat_prod x Nr hNmem
  have hEv : padicValRat p ((rootPoly Ex).eval (x : ℚ)) = cE := by
    rw [eval_rootPoly]; exact padicValRat_prod x Ex hEmem
  have hxN : x ∉ Nr := fun h => (hNmem x h).1 rfl
  have hN0 : (rootPoly Nr).eval (x : ℚ) ≠ 0 := eval_rootPoly_ne_zero _ _ hxN
  have hE0 : (rootPoly Ex).eval (x : ℚ) ≠ 0 := eval_rootPoly_ne_zero _ _ (not_mem_filter_ne _ _)
  have hv : padicValRat p ((rootPoly Nr).eval (x : ℚ) / (rootPoly Ex).eval (x : ℚ)) =
      (cN : ℤ) - cE := by
    rw [padicValRat.div hN0 hE0, hNv, hEv]
  -- the logarithmic-derivative sums are `ValGE (-1)`
  have hlog : ∀ s : Multiset ℤ, (∀ z ∈ s, z ≠ x ∧ (x - z).natAbs < p ^ 2) →
      ValGE p (-1) (s.map fun z : ℤ => 1 / ((x : ℚ) - (z : ℚ))).sum := by
    intro s hs
    refine valGE_msum _ _ fun q hq => ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hq
    obtain ⟨hzx, hzlt⟩ := hs z hz
    right
    have hxz : ((x : ℚ) - (z : ℚ)) = ((x - z : ℤ) : ℚ) := by push_cast; ring
    rw [one_div, padicValRat.inv, hxz, padicValRat_small _ (sub_ne_zero.2 (Ne.symm hzx)) hzlt]
    split_ifs <;> norm_num
  have hcnt : Dr.count x ≤ 2 := denRoots_count_le n x
  have hcnt1 : 1 ≤ Dr.count x := Multiset.one_le_count_iff_mem.2 hx
  rcases (by omega : Dr.count x = 1 ∨ Dr.count x = 2) with h1 | h2
  · -- simple pole: `a = 0`, `b = N/E`
    have e : pfCoeff Nr Dr x = (0, (rootPoly Nr).eval (x : ℚ) / (rootPoly Ex).eval (x : ℚ)) := by
      unfold pfCoeff; simp [h1, Ex]
    refine ⟨Or.inl ?_, Or.inr ?_⟩
    · show (pfCoeff Nr Dr x).1 = 0; rw [e]
    · show (0 : ℤ) ≤ padicValRat p (pfCoeff Nr Dr x).2
      have hle : cE ≤ cN := by rw [h1] at hh; exact Nat.le_of_add_le_add_right hh
      rw [e, hv]
      exact sub_nonneg.2 (by exact_mod_cast hle)
  · -- double pole: `a = N/E`, `b = (N/E)(∑ 1/(x-z) - ∑ 1/(x-y))`
    have e : pfCoeff Nr Dr x = ((rootPoly Nr).eval (x : ℚ) / (rootPoly Ex).eval (x : ℚ),
        (derivative (rootPoly Nr) * rootPoly Ex - rootPoly Nr * derivative (rootPoly Ex)).eval
          (x : ℚ) / (rootPoly Ex).eval (x : ℚ) ^ 2) := by
      unfold pfCoeff; simp [h2, Ex]
    have ha : ValGE p 1 ((rootPoly Nr).eval (x : ℚ) / (rootPoly Ex).eval (x : ℚ)) := by
      have hle : cE + 1 ≤ cN := by rw [h2] at hh; omega
      right
      rw [hv]
      have : ((cE : ℤ) + 1) ≤ cN := by exact_mod_cast hle
      linarith
    refine ⟨?_, ?_⟩
    · show ValGE p 1 (pfCoeff Nr Dr x).1
      rw [e]; exact ha
    · show ValGE p 0 (pfCoeff Nr Dr x).2
      rw [e]
      have hb : (derivative (rootPoly Nr) * rootPoly Ex - rootPoly Nr * derivative (rootPoly Ex)).eval
          (x : ℚ) / (rootPoly Ex).eval (x : ℚ) ^ 2 =
          (rootPoly Nr).eval (x : ℚ) / (rootPoly Ex).eval (x : ℚ) *
            ((Nr.map fun z : ℤ => 1 / ((x : ℚ) - (z : ℚ))).sum +
              -(Ex.map fun z : ℤ => 1 / ((x : ℚ) - (z : ℚ))).sum) := by
        rw [eval_sub, eval_mul, eval_mul, deriv_rootPoly_eval Nr x hxN,
          deriv_rootPoly_eval Ex x (not_mem_filter_ne _ _)]
        field_simp
        ring
      rw [hb]
      have := valGE_mul ha (valGE_add (hlog Nr hNmem) (valGE_neg (hlog Ex hEmem)))
      simpa using this

end Meijer5255.WindowReadoutAux
