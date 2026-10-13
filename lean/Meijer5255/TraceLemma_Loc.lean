/-
# Helper for `TraceLemma.lean`: local expansion of `pfCoeff` at a high pole

* `pfCoeff_eq`: the partial-fraction coefficients as explicit products/logarithmic sums
  (`Vf`, `Lf`, `alC`, `beC`);
* `pf_split`: splitting off the roots of one residue class `k` (scaled by `p`) at `x = k + pℓ`;
* `alC_min`, `alC_aff`: the comparison of the Laurent data of two classes whose root multisets
  satisfy the `minimal` / `affine` relations;
* `rest_FO`, `rest_lsum`: the first-order expansion modulo `p²` of the other classes.
Generic; imported only by `TraceLemma*.lean`.
-/
import Meijer5255.TraceLemma_Cls

open Finset Polynomial

noncomputable section

namespace Meijer5255.TraceAux

open Meijer5255

set_option linter.unusedSectionVars false

/-! ### Products and logarithmic sums over multisets of integer roots -/

/-- `∏_{y ∈ m} (x - y)`. -/
def vprod (m : Multiset ℤ) (x : ℚ) : ℚ := (m.map fun y : ℤ => x - (y : ℚ)).prod

/-- `∑_{y ∈ m} 1/(x - y)`. -/
def lsum (m : Multiset ℤ) (x : ℚ) : ℚ := (m.map fun y : ℤ => (x - (y : ℚ))⁻¹).sum

@[simp] theorem vprod_zero (x : ℚ) : vprod 0 x = 1 := by simp [vprod]
@[simp] theorem lsum_zero (x : ℚ) : lsum 0 x = 0 := by simp [lsum]
@[simp] theorem vprod_cons (a : ℤ) (m : Multiset ℤ) (x : ℚ) :
    vprod (a ::ₘ m) x = (x - a) * vprod m x := by simp [vprod]
@[simp] theorem lsum_cons (a : ℤ) (m : Multiset ℤ) (x : ℚ) :
    lsum (a ::ₘ m) x = (x - a)⁻¹ + lsum m x := by simp [lsum]
@[simp] theorem vprod_add (m m' : Multiset ℤ) (x : ℚ) :
    vprod (m + m') x = vprod m x * vprod m' x := by simp [vprod]
@[simp] theorem lsum_add (m m' : Multiset ℤ) (x : ℚ) :
    lsum (m + m') x = lsum m x + lsum m' x := by simp [lsum]

theorem vprod_ne_zero {m : Multiset ℤ} {x : ℚ} (h : ∀ y ∈ m, (y : ℚ) ≠ x) : vprod m x ≠ 0 := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [vprod_cons]
    exact mul_ne_zero (sub_ne_zero.2 (h a (Multiset.mem_cons_self a m)).symm)
      (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

theorem rootPoly_eval (m : Multiset ℤ) (x : ℚ) : (rootPoly m).eval x = vprod m x := by
  simp [rootPoly, vprod, eval_multiset_prod, Multiset.map_map]

theorem rootPoly_cons (a : ℤ) (m : Multiset ℤ) :
    rootPoly (a ::ₘ m) = (X - C (a : ℚ)) * rootPoly m := by
  simp [rootPoly]

theorem rootPoly_deriv_eval (m : Multiset ℤ) (x : ℚ) (hx : ∀ y ∈ m, (y : ℚ) ≠ x) :
    (derivative (rootPoly m)).eval x = vprod m x * lsum m x := by
  induction m using Multiset.induction_on with
  | empty => simp [rootPoly]
  | cons a m ih =>
    have ih' := ih fun y hy => hx y (Multiset.mem_cons_of_mem hy)
    have ha : x - a ≠ 0 := sub_ne_zero.2 (hx a (Multiset.mem_cons_self a m)).symm
    rw [rootPoly_cons, derivative_mul, derivative_X_sub_C, one_mul, eval_add, eval_mul, eval_sub,
      eval_X, eval_C, ih', rootPoly_eval, vprod_cons, lsum_cons]
    field_simp

/-! ### `pfCoeff` as explicit products -/

/-- `(N/E)(x)` with `E = D \ {x}`. -/
def Vf (N D : Multiset ℤ) (x : ℤ) : ℚ := vprod N x / vprod (D.filter (· ≠ x)) x

/-- `(N/E)'(x)/(N/E)(x)` with `E = D \ {x}`. -/
def Lf (N D : Multiset ℤ) (x : ℤ) : ℚ := lsum N x - lsum (D.filter (· ≠ x)) x

/-- The double-pole coefficient at `x`. -/
def alC (N D : Multiset ℤ) (x : ℤ) : ℚ := if D.count x = 2 then Vf N D x else 0

/-- The simple-pole coefficient at `x`. -/
def beC (N D : Multiset ℤ) (x : ℤ) : ℚ :=
  if D.count x = 2 then Vf N D x * Lf N D x else if D.count x = 1 then Vf N D x else 0

theorem pfCoeff_eq (Nr Dr : Multiset ℤ) (x : ℤ) (hx : x ∈ Dr → x ∉ Nr) :
    pfCoeff Nr Dr x = (alC Nr Dr x, beC Nr Dr x) := by
  have hE : ∀ y ∈ Dr.filter (· ≠ x), (y : ℚ) ≠ x := fun y hy => by
    have := (Multiset.mem_filter.1 hy).2; exact_mod_cast this
  have hE0 := vprod_ne_zero hE
  unfold pfCoeff alC beC Vf Lf
  simp only [rootPoly_eval]
  split_ifs with h2 h1
  · have hxD : x ∈ Dr := Multiset.count_pos.1 (by omega)
    have hN : ∀ y ∈ Nr, (y : ℚ) ≠ x := fun y hy h => hx hxD (by
      have : y = x := by exact_mod_cast h
      exact this ▸ hy)
    simp only [eval_sub, eval_mul, rootPoly_deriv_eval _ _ hN, rootPoly_deriv_eval _ _ hE,
      rootPoly_eval]
    congr 1
    field_simp
  · rfl
  · rfl

/-! ### Splitting off one residue class -/

theorem vprod_scale (p : ℕ) (k ℓ : ℤ) (N : Multiset ℤ) :
    vprod (N.map fun l => k + p * l) ((k + p * ℓ : ℤ) : ℚ) =
      (p : ℚ) ^ (Multiset.card N) * vprod N ℓ := by
  induction N using Multiset.induction_on with
  | empty => simp
  | cons a N ih => simp only [Multiset.map_cons, vprod_cons, ih, Multiset.card_cons]; push_cast; ring

theorem lsum_scale (p : ℕ) (_hp : (p : ℚ) ≠ 0) (k ℓ : ℤ) (N : Multiset ℤ) :
    lsum (N.map fun l => k + p * l) ((k + p * ℓ : ℤ) : ℚ) = (p : ℚ)⁻¹ * lsum N ℓ := by
  induction N using Multiset.induction_on with
  | empty => simp
  | cons a N ih =>
    simp only [Multiset.map_cons, lsum_cons, ih]
    push_cast
    rw [show (k : ℚ) + p * ℓ - (k + p * a) = p * (ℓ - a) by ring, mul_inv, mul_add]

theorem filter_ne_scale (p : ℕ) (hp : (p : ℤ) ≠ 0) (k ℓ : ℤ) (D : Multiset ℤ) :
    (D.map fun l => k + p * l).filter (· ≠ k + p * ℓ) =
      (D.filter (· ≠ ℓ)).map fun l => k + p * l := by
  rw [Multiset.filter_map]
  congr 1
  refine Multiset.filter_congr fun l _ => ?_
  simp only [Function.comp, ne_eq]
  constructor
  · intro h h'; exact h (by rw [h'])
  · intro h h'; exact h (by have := mul_left_cancel₀ hp (add_left_cancel h'); exact this)

theorem count_scale (p : ℕ) (hp : (p : ℤ) ≠ 0) (k ℓ : ℤ) (D : Multiset ℤ) :
    (D.map fun l => k + p * l).count (k + p * ℓ) = D.count ℓ :=
  Multiset.count_map_eq_count' _ _
    (fun _ _ h => mul_left_cancel₀ hp (add_left_cancel h)) _

theorem card_filter_ne (D : Multiset ℤ) (ℓ : ℤ) :
    ((D.filter (· ≠ ℓ)).card : ℤ) = D.card - D.count ℓ := by
  have h := Multiset.card_add (D.filter (· = ℓ)) (D.filter fun a => ¬ (a = ℓ))
  rw [Multiset.filter_add_not, Multiset.filter_eq', Multiset.card_replicate] at h
  have : D.filter (· ≠ ℓ) = D.filter fun a => ¬ (a = ℓ) := rfl
  rw [this]; omega

/-- **Splitting off the class `k`** at `x = k + pℓ`: the coefficients at `x` are those of the
class data `(N, D)` at `ℓ`, scaled by powers of `p`, times the contribution `g` of the other
roots (and `μ` for the logarithmic derivative). -/
theorem pf_split (p : ℕ) (hp : (p : ℚ) ≠ 0) (k ℓ : ℤ) (N D N' D' : Multiset ℤ)
    (hD' : k + p * ℓ ∉ D') :
    alC (N.map (fun l => k + p * l) + N') (D.map (fun l => k + p * l) + D') (k + p * ℓ) =
        (p : ℚ) ^ (((Multiset.card N : ℤ) - Multiset.card D) + 2) * alC N D ℓ *
          (vprod N' ((k + p * ℓ : ℤ) : ℚ) / vprod D' ((k + p * ℓ : ℤ) : ℚ)) ∧
    beC (N.map (fun l => k + p * l) + N') (D.map (fun l => k + p * l) + D') (k + p * ℓ) =
        (p : ℚ) ^ (((Multiset.card N : ℤ) - Multiset.card D) + 1) *
          (beC N D ℓ * (vprod N' ((k + p * ℓ : ℤ) : ℚ) / vprod D' ((k + p * ℓ : ℤ) : ℚ)) +
            alC N D ℓ * (vprod N' ((k + p * ℓ : ℤ) : ℚ) / vprod D' ((k + p * ℓ : ℤ) : ℚ)) *
              (p * (lsum N' ((k + p * ℓ : ℤ) : ℚ) - lsum D' ((k + p * ℓ : ℤ) : ℚ)))) := by
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp
  set x : ℤ := k + p * ℓ with hx
  set g := vprod N' (x : ℚ) / vprod D' (x : ℚ) with hg
  set μ := lsum N' (x : ℚ) - lsum D' (x : ℚ) with hμ
  have hcount : (D.map (fun l => k + p * l) + D').count x = D.count ℓ := by
    rw [Multiset.count_add, count_scale p hpz, Multiset.count_eq_zero.2 hD', add_zero]
  have hfilt : (D.map (fun l => k + p * l) + D').filter (· ≠ x) =
      (D.filter (· ≠ ℓ)).map (fun l => k + p * l) + D' := by
    rw [Multiset.filter_add, filter_ne_scale p hpz]
    congr 1
    exact Multiset.filter_eq_self.2 (fun y hy h => hD' (h ▸ hy))
  have hV : Vf (N.map (fun l => k + p * l) + N') (D.map (fun l => k + p * l) + D') x =
      (p : ℚ) ^ (((Multiset.card N : ℤ) - Multiset.card D) + D.count ℓ) * Vf N D ℓ * g := by
    rw [Vf, hfilt, vprod_add, vprod_add, hx, vprod_scale, vprod_scale, Vf, hg]
    have hcf := card_filter_ne D ℓ
    rw [show ((Multiset.card N : ℤ) - Multiset.card D) + D.count ℓ =
      (Multiset.card N : ℤ) - (Multiset.card (D.filter (· ≠ ℓ)) : ℤ) by omega, zpow_sub₀ hp,
      zpow_natCast, zpow_natCast]
    rw [div_mul_div_comm, div_mul_div_comm]
  have hL : Lf (N.map (fun l => k + p * l) + N') (D.map (fun l => k + p * l) + D') x =
      (p : ℚ)⁻¹ * Lf N D ℓ + μ := by
    rw [Lf, hfilt, lsum_add, lsum_add, hx, lsum_scale p hp, lsum_scale p hp, Lf, hμ]
    ring
  unfold alC beC
  rw [hcount, hV, hL]
  refine ⟨?_, ?_⟩
  · split_ifs with h2
    · rw [h2]; push_cast; ring
    · ring
  · split_ifs with h2 h1
    · rw [h2]
      have e1 : (p : ℚ) ^ ((((Multiset.card N : ℤ) - Multiset.card D)) + ((2 : ℕ) : ℤ)) =
          (p : ℚ) ^ (((Multiset.card N : ℤ) - Multiset.card D) + 1) * p := by
        rw [← zpow_add_one₀ hp]; push_cast; ring_nf
      rw [e1]
      field_simp
    · rw [h1]; push_cast; ring
    · ring

/-! ### Comparison of the class data (`minimal` / `affine` relations) -/

/-- Reduced root data are unique: `N + D₀ = N₀ + D` with disjoint supports forces
`N = N₀`, `D = D₀`. -/
theorem eq_of_rel {N D N₀ D₀ : Multiset ℤ} (h : N + D₀ = N₀ + D)
    (hd : ∀ v, N.count v = 0 ∨ D.count v = 0) (hd₀ : ∀ v, N₀.count v = 0 ∨ D₀.count v = 0) :
    N = N₀ ∧ D = D₀ := by
  have hc : ∀ v, N.count v + D₀.count v = N₀.count v + D.count v := fun v => by
    have := congrArg (Multiset.count v) h; simpa [Multiset.count_add] using this
  constructor <;> ext v <;> have := hc v <;> rcases hd v with h1 | h1 <;>
    rcases hd₀ v with h2 | h2 <;> omega

theorem Vf_cons_N (a ℓ : ℤ) (N D : Multiset ℤ) : Vf (a ::ₘ N) D ℓ = ((ℓ : ℚ) - a) * Vf N D ℓ := by
  rw [Vf, Vf, vprod_cons, mul_div_assoc]

theorem Lf_cons_N (a ℓ : ℤ) (N D : Multiset ℤ) : Lf (a ::ₘ N) D ℓ = ((ℓ : ℚ) - a)⁻¹ + Lf N D ℓ := by
  rw [Lf, Lf, lsum_cons]; ring

theorem filter_cons_ne {a ℓ : ℤ} (h : a ≠ ℓ) (D : Multiset ℤ) :
    (a ::ₘ D).filter (· ≠ ℓ) = a ::ₘ D.filter (· ≠ ℓ) := Multiset.filter_cons_of_pos _ h

theorem filter_cons_eq (ℓ : ℤ) (D : Multiset ℤ) :
    (ℓ ::ₘ D).filter (· ≠ ℓ) = D.filter (· ≠ ℓ) := Multiset.filter_cons_of_neg _ (by simp)

/-- The Laurent data of `(V - a) U` from those of `U`, when the root data satisfy
`N + D₀ = (a :: N₀) + D` (all supports disjoint, poles of order `≤ 2`). -/
theorem alC_aff {N D N₀ D₀ : Multiset ℤ} {a : ℤ} (h : N + D₀ = (a ::ₘ N₀) + D)
    (hd : ∀ v, N.count v = 0 ∨ D.count v = 0) (hd₀ : ∀ v, N₀.count v = 0 ∨ D₀.count v = 0)
    (hle : ∀ v, D₀.count v ≤ 2) (ℓ : ℤ) :
    alC N D ℓ = ((ℓ : ℚ) - a) * alC N₀ D₀ ℓ ∧
      beC N D ℓ = alC N₀ D₀ ℓ + ((ℓ : ℚ) - a) * beC N₀ D₀ ℓ := by
  have hc : ∀ v, N.count v + D₀.count v =
      N₀.count v + (if v = a then 1 else 0) + D.count v := fun v => by
    have := congrArg (Multiset.count v) h
    simp only [Multiset.count_add, Multiset.count_cons] at this; omega
  by_cases ha : D₀.count a = 0
  · -- case (i): `N = a :: N₀`, `D = D₀`
    have hN : N = a ::ₘ N₀ := by
      ext v; have := hc v; rw [Multiset.count_cons]
      by_cases hv : v = a
      · subst hv; rw [ite_eq_left rfl] at this ⊢; rcases hd v with h1 | h1 <;> omega
      · rw [ite_eq_right hv] at this ⊢; rcases hd v with h1 | h1 <;> rcases hd₀ v with h2 | h2 <;> omega
    have hD : D = D₀ := by
      ext v; have := hc v
      by_cases hv : v = a
      · subst hv; rw [ite_eq_left rfl] at this; rcases hd v with h1 | h1 <;> omega
      · rw [ite_eq_right hv] at this; rcases hd v with h1 | h1 <;> rcases hd₀ v with h2 | h2 <;> omega
    subst N D
    by_cases hla : ℓ = a
    · subst hla
      simp [alC, beC, ha]
    · have hne : (ℓ : ℚ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hla)
      have hi : ((ℓ : ℚ) - a) * ((ℓ : ℚ) - a)⁻¹ = 1 := mul_inv_cancel₀ hne
      unfold alC beC
      rw [Vf_cons_N, Lf_cons_N]
      constructor
      · split_ifs <;> ring
      · split_ifs
        · linear_combination Vf N₀ D₀ ℓ * hi
        · ring
        · ring
  · -- case (ii): `N = N₀`, `D₀ = a :: D`
    have hN : N = N₀ := by
      ext v; have := hc v
      by_cases hv : v = a
      · subst hv; rw [ite_eq_left rfl] at this
        rcases hd v with h1 | h1 <;> rcases hd₀ v with h2 | h2 <;> omega
      · rw [ite_eq_right hv] at this; rcases hd v with h1 | h1 <;> rcases hd₀ v with h2 | h2 <;> omega
    have hD : D₀ = a ::ₘ D := by
      ext v; have := hc v; rw [Multiset.count_cons]
      by_cases hv : v = a
      · subst hv; rw [ite_eq_left rfl] at this ⊢
        rcases hd v with h1 | h1 <;> rcases hd₀ v with h2 | h2 <;> omega
      · rw [ite_eq_right hv] at this ⊢; rcases hd v with h1 | h1 <;> rcases hd₀ v with h2 | h2 <;> omega
    subst hN hD
    by_cases hla : ℓ = a
    · subst hla
      have hl := hle ℓ
      rw [Multiset.count_cons_self] at hl
      unfold alC beC
      rw [Vf, Vf, Lf, filter_cons_eq, Multiset.count_cons_self]
      rcases (show D.count ℓ = 0 ∨ D.count ℓ = 1 by omega) with e | e <;> simp [e]
    · have hne : (ℓ : ℚ) - a ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hla)
      have hi : ((ℓ : ℚ) - a) * ((ℓ : ℚ) - a)⁻¹ = 1 := mul_inv_cancel₀ hne
      have hcnt : (a ::ₘ D).count ℓ = D.count ℓ := by
        rw [Multiset.count_cons, ite_eq_right hla, add_zero]
      have hV : Vf N (a ::ₘ D) ℓ = Vf N D ℓ * ((ℓ : ℚ) - a)⁻¹ := by
        rw [Vf, Vf, filter_cons_ne (Ne.symm hla), vprod_cons, div_eq_mul_inv, div_eq_mul_inv,
          mul_inv]; ring
      have hL : Lf N (a ::ₘ D) ℓ = Lf N D ℓ - ((ℓ : ℚ) - a)⁻¹ := by
        rw [Lf, Lf, filter_cons_ne (Ne.symm hla), lsum_cons]; ring
      unfold alC beC
      rw [hcnt, hV, hL]
      constructor
      · split_ifs
        · linear_combination -Vf N D ℓ * hi
        · ring
      · split_ifs
        · linear_combination (Vf N D ℓ * ((ℓ : ℚ) - a)⁻¹ - Vf N D ℓ * Lf N D ℓ) * hi
        · linear_combination -Vf N D ℓ * hi
        · ring

/-! ### Integrality of the class data -/

theorem Vf_int {p : ℕ} [Fact p.Prime] {N D : Multiset ℤ} {ℓ : ℤ}
    (hN : ∀ y ∈ N, ¬ (p : ℤ) ∣ ℓ - y) (hD : ∀ y ∈ D, y ≠ ℓ → ¬ (p : ℤ) ∣ ℓ - y) :
    IsPU p (Vf N D ℓ) ∧ ValGE p 0 (Lf N D ℓ) := by
  have hNu : IsPU p (vprod N ℓ) := by
   unfold vprod
   exact isPU_mprod _ fun z hz => by
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    have := isPU_int (p := p) (hN y hy); push_cast at this; exact this
  have hDu : IsPU p (vprod (D.filter (· ≠ ℓ)) ℓ) := by
   unfold vprod
   exact isPU_mprod _ fun z hz => by
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨hy, hyl⟩ := Multiset.mem_filter.1 hy
    have := isPU_int (p := p) (hD y hy hyl); push_cast at this; exact this
  refine ⟨hNu.div hDu, ?_⟩
  unfold Lf lsum
  refine vge_sub (vge_msum _ _ fun z hz => ?_) (vge_msum _ _ fun z hz => ?_)
  · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    have := (isPU_int (p := p) (hN y hy)).inv; push_cast at this; exact this.vge
  · obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
    obtain ⟨hy, hyl⟩ := Multiset.mem_filter.1 hy
    have := (isPU_int (p := p) (hD y hy hyl)).inv; push_cast at this; exact this.vge

theorem alC_int {p : ℕ} [Fact p.Prime] {N D : Multiset ℤ} {ℓ : ℤ}
    (hN : ℓ ∈ D → ∀ y ∈ N, ¬ (p : ℤ) ∣ ℓ - y)
    (hD : ℓ ∈ D → ∀ y ∈ D, y ≠ ℓ → ¬ (p : ℤ) ∣ ℓ - y) :
    ValGE p 0 (alC N D ℓ) ∧ ValGE p 0 (beC N D ℓ) := by
  by_cases hl : ℓ ∈ D
  · obtain ⟨hV, hL⟩ := Vf_int (hN hl) (hD hl)
    unfold alC beC
    refine ⟨?_, ?_⟩
    · split_ifs
      · exact hV.vge
      · exact vge_zero 0
    · split_ifs
      · simpa using vge_mul hV.vge hL
      · exact hV.vge
      · exact vge_zero 0
  · have h0 : D.count ℓ = 0 := Multiset.count_eq_zero.2 hl
    simp [alC, beC, h0, vge_zero]

/-! ### Residue classes of a multiset -/

theorem not_mem_rest (p : ℕ) (k ℓ : ℤ) (m : Multiset ℤ) :
    k + p * ℓ ∉ m.filter (fun y => ¬ (p : ℤ) ∣ y - k) := fun h =>
  (Multiset.mem_filter.1 h).2 (by simp)

theorem decomp_class (p : ℕ) [Fact p.Prime] (k : ℤ) (m : Multiset ℤ) :
    m = (hiRoots p k m).map (fun l => k + p * l) + m.filter (fun y => ¬ (p : ℤ) ∣ y - k) := by
  have := map_filter_class (p := p) k m id
  simp only [Multiset.map_id', id] at this
  rw [← this, Multiset.filter_add_not]

theorem count_hiRoots (p : ℕ) [Fact p.Prime] (k : ℤ) (m : Multiset ℤ) (v : ℤ) :
    (hiRoots p k m).count v = m.count (k + p * v) := by
  have hp : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  conv_rhs => rw [decomp_class p k m]
  rw [Multiset.count_add, count_scale p hp, Multiset.count_eq_zero.2 (not_mem_rest p k v m),
    add_zero]

theorem mem_hiRoots (p : ℕ) [Fact p.Prime] (k : ℤ) (m : Multiset ℤ) (v : ℤ) :
    v ∈ hiRoots p k m ↔ k + p * v ∈ m := by
  rw [← Multiset.count_pos, ← Multiset.count_pos, count_hiRoots p]

/-! ### The other classes, modulo `p²` -/

theorem vprod_fsum {ι : Type*} (S : Finset ι) (f : ι → Multiset ℤ) (x : ℚ) :
    vprod (∑ i ∈ S, f i) x = ∏ i ∈ S, vprod (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, vprod_add, ih]

theorem lsum_fsum {ι : Type*} (S : Finset ι) (f : ι → Multiset ℤ) (x : ℚ) :
    lsum (∑ i ∈ S, f i) x = ∑ i ∈ S, lsum (f i) x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, lsum_add, ih]

section Rest

variable {p : ℕ} [Fact p.Prime] {R : Finset ℤ}

theorem vprod_rest (hR : Complete p R) {k : ℤ} (hk : k ∈ R) (ℓ : ℤ) (m : Multiset ℤ) :
    vprod (m.filter (fun y => ¬ (p : ℤ) ∣ y - k)) ((k + p * ℓ : ℤ) : ℚ) =
      ∏ s ∈ R.erase k, (((hiRoots p s m).map fun l : ℤ => (ℓ : ℚ) - (l : ℚ)).map
        fun v => (((k - s : ℤ)) : ℚ) + p * v).prod := by
  rw [filter_not_class hR hk, vprod_fsum]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [vprod, map_filter_class, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun l _ => ?_
  simp only [Function.comp]; push_cast; ring

theorem lsum_rest (hR : Complete p R) {k : ℤ} (hk : k ∈ R) (ℓ : ℤ) (m : Multiset ℤ) :
    lsum (m.filter (fun y => ¬ (p : ℤ) ∣ y - k)) ((k + p * ℓ : ℤ) : ℚ) =
      ∑ s ∈ R.erase k, (((hiRoots p s m).map fun l : ℤ => (ℓ : ℚ) - (l : ℚ)).map
        fun v => ((((k - s : ℤ)) : ℚ) + p * v)⁻¹).sum := by
  rw [filter_not_class hR hk, lsum_fsum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [lsum, map_filter_class, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun l _ => ?_
  simp only [Function.comp]; push_cast; ring_nf

theorem msum_lin (M : Multiset ℤ) (ℓ : ℤ) (u : ℚ) :
    ((M.map fun l : ℤ => (ℓ : ℚ) - (l : ℚ)).map fun v => v / u).sum =
      ((Multiset.card M : ℚ) * ℓ - (M.sum : ℚ)) / u := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.card_cons]
    push_cast; ring

/-- The other classes: `g ≡ L_k (1 + p(ℓ A_k - B_k)) (mod p²)`. -/
theorem rest_FO (hR : Complete p R) {k : ℤ} (hk : k ∈ R) (ℓ : ℤ) (Nr Dr : Multiset ℤ) :
    FO p (vprod (Nr.filter (fun y => ¬ (p : ℤ) ∣ y - k)) ((k + p * ℓ : ℤ) : ℚ) /
        vprod (Dr.filter (fun y => ¬ (p : ℤ) ∣ y - k)) ((k + p * ℓ : ℤ) : ℚ))
      (∏ s ∈ R.erase k, (((k - s : ℤ)) : ℚ) ^
        (((hiRoots p s Nr).card : ℤ) - ((hiRoots p s Dr).card : ℤ)))
      (∑ s ∈ R.erase k, ((ℓ : ℚ) * (((hiRoots p s Nr).card : ℚ) - (hiRoots p s Dr).card) -
        (((hiRoots p s Nr).sum : ℚ) - (hiRoots p s Dr).sum)) / (((k - s : ℤ)) : ℚ)) := by
  rw [vprod_rest hR hk, vprod_rest hR hk, ← Finset.prod_div_distrib]
  refine FO.prod _ _ _ _ fun s hs => ?_
  have hu : IsPU p (((k - s : ℤ)) : ℚ) :=
    isPU_int (cl_ndvd hR hk (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs).symm)
  have hint : ∀ m : Multiset ℤ, ∀ v ∈ (hiRoots p s m).map (fun l : ℤ => (ℓ : ℚ) - (l : ℚ)),
      ValGE p 0 v := fun m v hv => by
    obtain ⟨l, _, rfl⟩ := Multiset.mem_map.1 hv
    exact_mod_cast vge_int (p := p) (ℓ - l)
  have hN := FO.mprod_linear hu _ (hint Nr)
  have hD := FO.mprod_linear hu _ (hint Dr)
  have hq := hN.mul (hD.inv (hu.pow _))
  rw [div_eq_mul_inv]
  refine hq.congr ?_ ?_
  · rw [zpow_sub₀ hu.1, zpow_natCast, zpow_natCast, div_eq_mul_inv, Multiset.card_map,
      Multiset.card_map]
  · rw [msum_lin, msum_lin]; ring

theorem lsum_cong (M : Multiset ℤ) (ℓ : ℤ) {u : ℚ} (hu : IsPU p u) :
    ValGE p 1 (((M.map fun l : ℤ => (ℓ : ℚ) - (l : ℚ)).map fun v => (u + p * v)⁻¹).sum -
      (Multiset.card M : ℚ) / u) := by
  induction M using Multiset.induction_on with
  | empty => simp [vge_zero]
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    have h1 := inv_cong_one hu (by exact_mod_cast vge_int (p := p) (ℓ - a))
    push_cast at h1
    have e : (u + p * ((ℓ : ℚ) - a))⁻¹ + ((M.map fun l : ℤ => (ℓ : ℚ) - (l : ℚ)).map
        fun v => (u + p * v)⁻¹).sum - ((Multiset.card M + 1 : ℕ) : ℚ) / u =
        ((u + p * ((ℓ : ℚ) - a))⁻¹ - u⁻¹) + (((M.map fun l : ℤ => (ℓ : ℚ) - (l : ℚ)).map
          fun v => (u + p * v)⁻¹).sum - (Multiset.card M : ℚ) / u) := by
      push_cast; ring
    rw [e]; exact vge_add h1 ih

/-- The other classes: `μ ≡ A_k (mod p)`. -/
theorem rest_lsum (hR : Complete p R) {k : ℤ} (hk : k ∈ R) (ℓ : ℤ) (Nr Dr : Multiset ℤ) :
    ValGE p 1 ((lsum (Nr.filter (fun y => ¬ (p : ℤ) ∣ y - k)) ((k + p * ℓ : ℤ) : ℚ) -
        lsum (Dr.filter (fun y => ¬ (p : ℤ) ∣ y - k)) ((k + p * ℓ : ℤ) : ℚ)) -
      ∑ s ∈ R.erase k, (((hiRoots p s Nr).card : ℚ) - (hiRoots p s Dr).card) /
        (((k - s : ℤ)) : ℚ)) := by
  rw [lsum_rest hR hk, lsum_rest hR hk, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine vge_sum _ _ _ fun s hs => ?_
  have hu : IsPU p (((k - s : ℤ)) : ℚ) :=
    isPU_int (cl_ndvd hR hk (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs).symm)
  have e : ∀ a b c d : ℚ, a - b - (c - d) / ((k - s : ℤ) : ℚ) =
      (a - c / ((k - s : ℤ) : ℚ)) - (b - d / ((k - s : ℤ) : ℚ)) := fun a b c d => by ring
  rw [e]
  exact vge_sub (lsum_cong _ ℓ hu) (lsum_cong _ ℓ hu)

end Rest

end Meijer5255.TraceAux
