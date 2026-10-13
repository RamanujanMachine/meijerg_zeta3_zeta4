/-
# Helper for `ShellFirstOrder` [4], [6], [7]: root products, valuations, local scaling

Generic lemmas on root products `∏_{x ∈ s} (t - x)` and log-derivative sums `∑ 1/(t - x)`, their
`p`-adic valuations and reductions modulo `p` (adapted from pfq54 `residue_aux2.lean`), the
partial-fraction coefficients `pfCoeff` in terms of them, and the *local scaling* of `pfCoeff` at
a pole `x ≡ k (mod p)` to the high roots of the class `k`.
-/
import Meijer5255.definitions

open Finset Polynomial

noncomputable section

namespace Meijer5255.ShellFirstOrder.Gen

open Meijer5255

/-! ### The `ValGE` calculus -/

section ValGEcalc

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
    exact vadd (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fact p.Prime] in
theorem vint (z : ℤ) : ValGE p 0 (z : ℚ) := by
  rcases eq_or_ne z 0 with h | h
  · left; simp [h]
  · right; rw [padicValRat.of_int]; positivity

theorem vdvd (z : ℤ) (h : (p : ℤ) ∣ z) : ValGE p 1 (z : ℚ) := by
  obtain ⟨w, rfl⟩ := h
  rcases eq_or_ne w 0 with hw | hw
  · left; rw [hw, mul_zero, Int.cast_zero]
  · right
    rw [Int.cast_mul, Int.cast_natCast, padicValRat.mul (Nat.cast_ne_zero.mpr
      (Fact.out : p.Prime).ne_zero) (Int.cast_ne_zero.mpr hw),
      padicValRat.self (Fact.out : p.Prime).one_lt, padicValRat.of_int]
    omega

/-- `x ∈ p^a ℤ_(p)` as a `zpow` multiple. -/
theorem vzpow (a : ℤ) : ValGE p a ((p : ℚ) ^ a) := by
  right
  rw [padicValRat.zpow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]

/-- A unit integer: `v_p(z⁻¹) = 0`. -/
theorem vinv_unit (z : ℤ) (hz : ¬ (p : ℤ) ∣ z) : ValGE p 0 ((z : ℚ)⁻¹) := by
  right
  have hz0 : z ≠ 0 := by rintro rfl; exact hz (dvd_zero _)
  rw [padicValRat.inv, padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hz]
  simp

end ValGEcalc

/-! ### Root products and log-derivative sums -/

/-- `∏_{x ∈ s} (t - x)`. -/
def pr (s : Multiset ℤ) (t : ℤ) : ℤ := (s.map fun x => t - x).prod

/-- `∑_{x ∈ s} 1/(t - x)`. -/
def Ls (s : Multiset ℤ) (t : ℤ) : ℚ := (s.map fun x => 1 / ((t - x : ℤ) : ℚ)).sum

theorem pr_add (s s' : Multiset ℤ) (t : ℤ) : pr (s + s') t = pr s t * pr s' t := by
  unfold pr; rw [Multiset.map_add, Multiset.prod_add]

theorem Ls_add (s s' : Multiset ℤ) (t : ℤ) : Ls (s + s') t = Ls s t + Ls s' t := by
  unfold Ls; rw [Multiset.map_add, Multiset.sum_add]

theorem pr_cons (x : ℤ) (s : Multiset ℤ) (t : ℤ) : pr (x ::ₘ s) t = (t - x) * pr s t := by
  unfold pr; rw [Multiset.map_cons, Multiset.prod_cons]

theorem Ls_cons (x : ℤ) (s : Multiset ℤ) (t : ℤ) :
    Ls (x ::ₘ s) t = 1 / ((t - x : ℤ) : ℚ) + Ls s t := by
  unfold Ls; rw [Multiset.map_cons, Multiset.sum_cons]

theorem pr_split (s : Multiset ℤ) (t : ℤ) (q : ℤ → Prop) [DecidablePred q] :
    pr s t = pr (s.filter q) t * pr (s.filter fun x => ¬ q x) t := by
  rw [← pr_add, Multiset.filter_add_not]

theorem Ls_split (s : Multiset ℤ) (t : ℤ) (q : ℤ → Prop) [DecidablePred q] :
    Ls s t = Ls (s.filter q) t + Ls (s.filter fun x => ¬ q x) t := by
  rw [← Ls_add, Multiset.filter_add_not]

/-- Root products are translation invariant. -/
theorem pr_shift (s : Multiset ℤ) (t e : ℤ) : pr (s.map (· + e)) (t + e) = pr s t := by
  unfold pr; rw [Multiset.map_map]; congr 1; exact Multiset.map_congr rfl fun x _ => by simp

theorem Ls_shift (s : Multiset ℤ) (t e : ℤ) : Ls (s.map (· + e)) (t + e) = Ls s t := by
  unfold Ls; rw [Multiset.map_map]; congr 1; exact Multiset.map_congr rfl fun x _ => by simp

/-- `rootPoly` with the coercion `ℤ → ℚ` made explicit (it elaborates through a monadic bind). -/
theorem rootPoly_def (s : Multiset ℤ) :
    rootPoly s = (s.map fun x : ℤ => X - C ((x : ℤ) : ℚ)).prod := by
  unfold rootPoly
  congr 1
  simp

theorem rootPoly_cons (x : ℤ) (s : Multiset ℤ) :
    rootPoly (x ::ₘ s) = (X - C (x : ℚ)) * rootPoly s := by
  rw [rootPoly_def, rootPoly_def, Multiset.map_cons, Multiset.prod_cons]

theorem rootPoly_eval (s : Multiset ℤ) (t : ℤ) :
    (rootPoly s).eval (t : ℚ) = ((pr s t : ℤ) : ℚ) := by
  induction s using Multiset.induction_on with
  | empty => simp [rootPoly_def, pr]
  | cons x s ih => rw [rootPoly_cons, eval_mul, ih, pr_cons]; simp

/-- The derivative of a root polynomial off its roots: `P'(t) = P(t) ∑ 1/(t - x)`. -/
theorem rootPoly_deriv (s : Multiset ℤ) (t : ℤ) (ht : t ∉ s) :
    (derivative (rootPoly s)).eval (t : ℚ) = ((pr s t : ℤ) : ℚ) * Ls s t := by
  induction s using Multiset.induction_on with
  | empty => simp [rootPoly_def, Ls]
  | cons x s ih =>
    have hx : t - x ≠ 0 := by
      intro h; exact ht (by rw [show t = x by omega]; exact Multiset.mem_cons_self _ _)
    have ih := ih fun h => ht (Multiset.mem_cons_of_mem h)
    rw [rootPoly_cons, derivative_mul, eval_add, eval_mul, eval_mul, ih, derivative_sub, derivative_X,
      derivative_C, sub_zero, eval_one, one_mul, eval_sub, eval_X, eval_C, rootPoly_eval,
      pr_cons, Ls_cons]
    have hx' : ((t - x : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hx
    push_cast at hx' ⊢
    field_simp

/-- `pfCoeff` in terms of root products and log-derivative sums (pole `x` off the numerator
roots). -/
theorem pfCoeff_eq (Nr Dr : Multiset ℤ) (x : ℤ) (hx : x ∉ Nr) :
    pfCoeff Nr Dr x =
      if Dr.count x = 2 then
        (((pr Nr x : ℤ) : ℚ) / ((pr (Dr.filter (· ≠ x)) x : ℤ) : ℚ),
          ((pr Nr x : ℤ) : ℚ) / ((pr (Dr.filter (· ≠ x)) x : ℤ) : ℚ) *
            (Ls Nr x - Ls (Dr.filter (· ≠ x)) x))
      else if Dr.count x = 1 then
        (0, ((pr Nr x : ℤ) : ℚ) / ((pr (Dr.filter (· ≠ x)) x : ℤ) : ℚ))
      else (0, 0) := by
  have hE : x ∉ Dr.filter (· ≠ x) := fun h => (Multiset.mem_filter.mp h).2 rfl
  have hE0 : ((pr (Dr.filter (· ≠ x)) x : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_ne_zero]
    unfold pr
    rw [Ne, Multiset.prod_eq_zero_iff]
    rintro hm
    obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp hm
    have : x = y := by omega
    subst this
    exact hE hy
  unfold pfCoeff
  simp only []
  split_ifs with h2 h1
  · rw [rootPoly_eval, rootPoly_eval, eval_sub, eval_mul, eval_mul, rootPoly_deriv _ _ hx,
      rootPoly_deriv _ _ hE, rootPoly_eval, rootPoly_eval]
    congr 1
    field_simp
  · rw [rootPoly_eval, rootPoly_eval]
  · rfl

/-! ### Splitting off the class of `k` -/

section Class

variable (p : ℕ) (k : ℤ)

theorem hiRoots_cons (y : ℤ) (s : Multiset ℤ) :
    hiRoots p k (y ::ₘ s) =
      if (p : ℤ) ∣ y - k then ((y - k) / p) ::ₘ hiRoots p k s else hiRoots p k s := by
  unfold hiRoots
  split_ifs with h
  · simp only [Multiset.filter_cons, h, ↓reduceIte, Multiset.singleton_add, Multiset.map_cons]
  · simp only [Multiset.filter_cons, h, ↓reduceIte, zero_add]

theorem hiRoots_add (s t : Multiset ℤ) : hiRoots p k (s + t) = hiRoots p k s + hiRoots p k t := by
  unfold hiRoots; rw [Multiset.filter_add, Multiset.map_add]

theorem card_hiRoots (s : Multiset ℤ) :
    Multiset.card (hiRoots p k s) = Multiset.card (s.filter fun y => (p : ℤ) ∣ y - k) := by
  unfold hiRoots; rw [Multiset.card_map]

/-- The class part of a root product. -/
theorem pr_class (s : Multiset ℤ) (x : ℤ) (hxk : (p : ℤ) ∣ x - k) :
    pr (s.filter fun y => (p : ℤ) ∣ y - k) x =
      (p : ℤ) ^ Multiset.card (hiRoots p k s) * pr (hiRoots p k s) ((x - k) / p) := by
  induction s using Multiset.induction_on with
  | empty => simp [hiRoots, pr]
  | cons y s ih =>
    rw [hiRoots_cons]
    split_ifs with h
    · simp only [Multiset.filter_cons, h, ↓reduceIte, Multiset.singleton_add]
      rw [pr_cons, pr_cons, Multiset.card_cons, ih, pow_succ]
      obtain ⟨a, ha⟩ := hxk
      obtain ⟨b, hb⟩ := h
      rcases Nat.eq_zero_or_pos p with hp | hp
      · subst hp; simp at ha hb ⊢
        left; omega
      have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      rw [ha, hb, Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ hp']
      have : x - y = p * a - p * b := by omega
      rw [this]; ring
    · simp only [Multiset.filter_cons, h, ↓reduceIte, zero_add]
      rw [ih]

theorem Ls_class (s : Multiset ℤ) (x : ℤ) (hxk : (p : ℤ) ∣ x - k) (hp : 0 < p) :
    Ls (s.filter fun y => (p : ℤ) ∣ y - k) x = Ls (hiRoots p k s) ((x - k) / p) / p := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  induction s using Multiset.induction_on with
  | empty => simp [hiRoots, Ls]
  | cons y s ih =>
    rw [hiRoots_cons]
    split_ifs with h
    · simp only [Multiset.filter_cons, h, ↓reduceIte, Multiset.singleton_add]
      rw [Ls_cons, Ls_cons, ih, add_div]
      congr 1
      obtain ⟨a, ha⟩ := hxk
      obtain ⟨b, hb⟩ := h
      rw [ha, hb, Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ hp']
      have : x - y = p * (a - b) := by linarith
      rw [this]; push_cast
      rw [one_div, one_div, mul_inv, div_eq_mul_inv, mul_comm]
    · simp only [Multiset.filter_cons, h, ↓reduceIte, zero_add]
      rw [ih]

/-- Removing the pole from the class part. -/
theorem hiRoots_filter_ne (s : Multiset ℤ) (x : ℤ) (hxk : (p : ℤ) ∣ x - k) (hp : 0 < p) :
    hiRoots p k (s.filter (· ≠ x)) = (hiRoots p k s).filter (· ≠ (x - k) / p) := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  induction s using Multiset.induction_on with
  | empty => simp [hiRoots]
  | cons y s ih =>
    by_cases hyx : y = x
    · subst hyx
      simp only [Multiset.filter_cons, ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      rw [ih, hiRoots_cons]
      simp [hxk]
    · simp only [Multiset.filter_cons, ne_eq, hyx, not_false_eq_true, ↓reduceIte,
        Multiset.singleton_add]
      rw [hiRoots_cons, hiRoots_cons]
      split_ifs with h
      · rw [Multiset.filter_cons, if_pos, ih, Multiset.singleton_add]
        intro he
        apply hyx
        obtain ⟨a, ha⟩ := hxk
        obtain ⟨b, hb⟩ := h
        rw [ha, hb, Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ hp'] at he
        subst he; omega
      · exact ih

theorem hi_eq_iff (x y : ℤ) (hxk : (p : ℤ) ∣ x - k) (hyk : (p : ℤ) ∣ y - k) (hp : 0 < p) :
    (y - k) / p = (x - k) / p ↔ y = x := by
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  obtain ⟨a, ha⟩ := hxk
  obtain ⟨b, hb⟩ := hyk
  rw [ha, hb, Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ hp']
  constructor
  · rintro rfl; omega
  · intro e; subst e; exact mul_left_cancel₀ hp' (ha.symm.trans hb).symm

/-- The multiplicity of the pole is that of its high root. -/
theorem count_hiRoots (s : Multiset ℤ) (x : ℤ) (hxk : (p : ℤ) ∣ x - k) (hp : 0 < p) :
    (hiRoots p k s).count ((x - k) / p) = s.count x := by
  induction s using Multiset.induction_on with
  | empty => simp [hiRoots]
  | cons y s ih =>
    rw [hiRoots_cons, Multiset.count_cons]
    by_cases h : (p : ℤ) ∣ y - k
    · have e := hi_eq_iff p k x y hxk h hp
      simp only [h, ↓reduceIte, Multiset.count_cons, ih, e]
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx, Ne.symm hyx]
        exact fun h' => hyx (e.mp h'.symm)
    · have hyx : y ≠ x := fun e => h (e ▸ hxk)
      simp [h, ih, hyx, Ne.symm hyx]

end Class

theorem card_filter_ne (s : Multiset ℤ) (a : ℤ) :
    Multiset.card s = Multiset.card (s.filter (· ≠ a)) + s.count a := by
  conv_lhs => rw [← Multiset.filter_add_not (· ≠ a) s]
  rw [Multiset.card_add, Multiset.count_eq_card_filter_eq]
  congr 2
  exact Multiset.filter_congr fun x _ => by simp [eq_comm]

/-- **Local scaling.** At a pole `x ≡ k (mod p)` (off the numerator roots), the
partial-fraction coefficients of `rootPoly Nr / rootPoly Dr` are those of the class-`k` kernel
`rootPoly N_k / rootPoly D_k` at `ℓ₀ = (x - k)/p`, scaled by `p^{h+2}` resp. `p^{h+1}`
(`h = |N_k| - |D_k|`) and by the unit part `u`, plus a term with the log-derivative `L` of the
unit part. -/
theorem scale (p : ℕ) (hp : 0 < p) (Nr Dr : Multiset ℤ) (x k : ℤ) (hxk : (p : ℤ) ∣ x - k)
    (hx : x ∉ Nr) :
    (pfCoeff Nr Dr x).1 =
        (p : ℚ) ^ ((Multiset.card (hiRoots p k Nr) : ℤ) - Multiset.card (hiRoots p k Dr) + 2) *
          (((pr (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) x : ℤ) : ℚ) /
            ((pr (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) x : ℤ) : ℚ)) *
          (pfCoeff (hiRoots p k Nr) (hiRoots p k Dr) ((x - k) / p)).1 ∧
      (pfCoeff Nr Dr x).2 =
        (p : ℚ) ^ ((Multiset.card (hiRoots p k Nr) : ℤ) - Multiset.card (hiRoots p k Dr) + 1) *
          (((pr (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) x : ℤ) : ℚ) /
            ((pr (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) x : ℤ) : ℚ)) *
          (pfCoeff (hiRoots p k Nr) (hiRoots p k Dr) ((x - k) / p)).2 +
        (p : ℚ) ^ ((Multiset.card (hiRoots p k Nr) : ℤ) - Multiset.card (hiRoots p k Dr) + 2) *
          (((pr (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) x : ℤ) : ℚ) /
            ((pr (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) x : ℤ) : ℚ)) *
          (pfCoeff (hiRoots p k Nr) (hiRoots p k Dr) ((x - k) / p)).1 *
          (Ls (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) x -
            Ls (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) x) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  set hN := hiRoots p k Nr
  set hD := hiRoots p k Dr
  set l0 := (x - k) / p
  set uN := pr (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) x
  set uD := pr (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) x
  set LN := Ls (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) x
  set LD := Ls (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) x
  have hl0 : l0 ∉ hN := by
    intro h
    obtain ⟨y, hy, hyl⟩ := Multiset.mem_map.mp h
    obtain ⟨hyN, hyk⟩ := Multiset.mem_filter.mp hy
    exact hx ((hi_eq_iff p k x y hxk hyk hp).mp hyl ▸ hyN)
  have hcount : hD.count l0 = Dr.count x := count_hiRoots p k Dr x hxk hp
  -- the unit part of `Dr` does not see the pole
  have hGD : ((Dr.filter (· ≠ x)).filter fun y => ¬ (p : ℤ) ∣ y - k) =
      Dr.filter fun y => ¬ (p : ℤ) ∣ y - k := by
    rw [Multiset.filter_filter]
    exact Multiset.filter_congr fun y _ => ⟨fun h => h.1, fun h => ⟨h, fun e => h (by rw [e]; exact hxk)⟩⟩
  have hPN : ((pr Nr x : ℤ) : ℚ) =
      (p : ℚ) ^ Multiset.card hN * ((pr hN l0 : ℤ) : ℚ) * (uN : ℚ) := by
    rw [pr_split Nr x (fun y => (p : ℤ) ∣ y - k), pr_class p k Nr x hxk]; push_cast; ring
  have hPE : ((pr (Dr.filter (· ≠ x)) x : ℤ) : ℚ) =
      (p : ℚ) ^ Multiset.card (hD.filter (· ≠ l0)) * ((pr (hD.filter (· ≠ l0)) l0 : ℤ) : ℚ) *
        (uD : ℚ) := by
    rw [pr_split (Dr.filter (· ≠ x)) x (fun y => (p : ℤ) ∣ y - k),
      pr_class p k _ x hxk, hiRoots_filter_ne p k Dr x hxk hp, hGD]; push_cast; ring
  have hLN : Ls Nr x = Ls hN l0 / p + LN := by
    rw [Ls_split Nr x (fun y => (p : ℤ) ∣ y - k), Ls_class p k Nr x hxk hp]
  have hLE : Ls (Dr.filter (· ≠ x)) x = Ls (hD.filter (· ≠ l0)) l0 / p + LD := by
    rw [Ls_split (Dr.filter (· ≠ x)) x (fun y => (p : ℤ) ∣ y - k), Ls_class p k _ x hxk hp,
      hiRoots_filter_ne p k Dr x hxk hp, hGD]
  have hcard := card_filter_ne hD l0
  rw [hcount] at hcard
  set c' := Multiset.card (hD.filter (· ≠ l0))
  set cN := Multiset.card hN
  have huD : (uD : ℚ) ≠ 0 := by
    rw [Int.cast_ne_zero]; unfold uD pr; rw [Ne, Multiset.prod_eq_zero_iff]
    intro hm
    obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp hm
    exact (Multiset.mem_filter.mp hy).2 (by rw [show y = x by omega]; exact hxk)
  have hPD : ((pr (hD.filter (· ≠ l0)) l0 : ℤ) : ℚ) ≠ 0 := by
    rw [Int.cast_ne_zero]; unfold pr; rw [Ne, Multiset.prod_eq_zero_iff]
    intro hm
    obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.mp hm
    exact (Multiset.mem_filter.mp hy).2 (by omega)
  have hz : ∀ a b : ℕ, (p : ℚ) ^ ((a : ℤ) - b) = (p : ℚ) ^ a / (p : ℚ) ^ b := fun a b => by
    rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
  rw [pfCoeff_eq Nr Dr x hx, pfCoeff_eq hN hD l0 hl0, hcount, hcard]
  split_ifs with h2 h1
  · rw [h2, show (cN : ℤ) - ((c' + 2 : ℕ) : ℤ) + 2 = (cN : ℤ) - c' by push_cast; ring,
      show (cN : ℤ) - ((c' + 2 : ℕ) : ℤ) + 1 = (cN : ℤ) - (c' + 1 : ℕ) by push_cast; ring,
      hz, hz, hPN, hPE, hLN, hLE]
    have : (p : ℚ) ^ (c' + 1) = (p : ℚ) ^ c' * p := pow_succ _ _
    rw [this]
    refine ⟨by field_simp, ?_⟩
    field_simp
    ring
  · rw [h1, show (cN : ℤ) - ((c' + 1 : ℕ) : ℤ) + 1 = (cN : ℤ) - c' by push_cast; ring, hz,
      hPN, hPE]
    refine ⟨by simp, ?_⟩
    field_simp
    ring
  · simp

/-! ### Residue counts, unit parts modulo `p` (adapted from pfq54 `residue_aux2.lean`) -/

/-- Number of elements congruent to `a` modulo `p` (same as `ShellFirstOrder.resCount`). -/
def rc (s : Multiset ℤ) (p a : ℕ) : ℕ := (s.filter fun x => x % (p : ℤ) = a).card

theorem dvd_iff_emod (p : ℕ) (hp : 0 < p) (k : ℕ) (hk : k < p) (y : ℤ) :
    (p : ℤ) ∣ y - k ↔ y % (p : ℤ) = k := by
  constructor
  · rintro ⟨c, hc⟩
    rw [show y = k + p * c by linarith, Int.add_mul_emod_self_left,
      Int.emod_eq_of_lt (by omega) (by omega)]
  · intro h
    exact ⟨y / p, by linarith [Int.emod_add_mul_ediv y p]⟩

theorem rc_eq_card_hiRoots (p : ℕ) (hp : 0 < p) (k : ℕ) (hk : k < p) (s : Multiset ℤ) :
    rc s p k = Multiset.card (hiRoots p k s) := by
  rw [card_hiRoots, rc]
  congr 1
  exact Multiset.filter_congr fun y _ => (dvd_iff_emod p hp k hk y).symm

theorem rc_cons (p : ℕ) (x : ℤ) (s : Multiset ℤ) (a : ℕ) :
    rc (x ::ₘ s) p a = rc s p a + if x % (p : ℤ) = a then 1 else 0 := by
  unfold rc
  by_cases h : x % (p : ℤ) = a
  · simp [Multiset.filter_cons, h, add_comm]
  · simp [Multiset.filter_cons, h]

section Modp

variable (p : ℕ) [hp : Fact p.Prime]

theorem cast_class (x : ℤ) : (x : ZMod p) = (((x % p).toNat : ℕ) : ZMod p) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)),
    ZMod.intCast_mod]

theorem class_lt (x : ℤ) : (x % p).toNat < p := by
  have := Int.emod_lt_of_pos x (by exact_mod_cast hp.out.pos : (0 : ℤ) < p)
  have := Int.emod_nonneg x (by exact_mod_cast hp.out.ne_zero : (p : ℤ) ≠ 0)
  omega

/-- The `p`-unit part of a root product modulo `p`, grouped by residue classes (pfq54
`unit_part`, with the class filter written as `p ∣ y - k`). -/
theorem unit_part (s : Multiset ℤ) (t : ℤ) (k : ℕ) (hk : k < p) (htk : (p : ℤ) ∣ t - k) :
    ((pr (s.filter fun y => ¬ (p : ℤ) ∣ y - k) t : ℤ) : ZMod p) =
      ∏ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc s p a := by
  have hk' := (dvd_iff_emod p hp.out.pos k hk t).mp htk
  have hfil : ∀ s : Multiset ℤ, (s.filter fun y => ¬ (p : ℤ) ∣ y - k) =
      s.filter fun y => ¬ y % (p : ℤ) = k := fun s =>
    Multiset.filter_congr fun y _ => not_congr (dvd_iff_emod p hp.out.pos k hk y)
  rw [hfil]
  induction s using Multiset.induction_on with
  | empty =>
    rw [Multiset.filter_zero]
    exact (Int.cast_one).trans (Finset.prod_eq_one fun a _ => by simp [rc]).symm
  | cons x s ih =>
    have e1 : ∀ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (x ::ₘ s) p a =
        ((k : ZMod p) - a) ^ rc s p a *
          ((k : ZMod p) - a) ^ (if x % (p : ℤ) = a then 1 else 0) := fun a _ => by
      rw [rc_cons, pow_add]
    rw [Finset.prod_congr rfl e1, Finset.prod_mul_distrib, ← ih]
    have hx : x % (p : ℤ) = ((x % p).toNat : ℕ) :=
      (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero))).symm
    by_cases hxk : x % (p : ℤ) = k
    · rw [Multiset.filter_cons_of_neg (p := fun y => ¬ y % (p : ℤ) = k) s (not_not.mpr hxk),
        Finset.prod_eq_one, mul_one]
      intro a ha
      rw [ite_eq_right fun h => (Finset.ne_of_mem_erase ha) (by rw [hxk] at h; exact_mod_cast h.symm),
        pow_zero]
    · rw [Multiset.filter_cons_of_pos (p := fun y => ¬ y % (p : ℤ) = k) s hxk, pr_cons,
        Int.cast_mul, mul_comm, Finset.prod_eq_single ((x % p).toNat)]
      · rw [ite_eq_left hx, pow_one, Int.cast_sub, cast_class p t, cast_class p x, hk']
        rfl
      · intro a _ hne
        rw [ite_eq_right fun h => hne (by rw [hx] at h; exact_mod_cast h.symm), pow_zero]
      · intro hn
        exfalso
        rcases Finset.mem_erase.not.mp hn |> not_and_or.mp with h | h
        · exact h fun h' => hxk (by rw [hx, h'])
        · exact h (mem_range.mpr (class_lt p x))

/-- Wilson: `∏_{a ≠ k} (k - a) = -1` in `𝔽_p` (pfq54 `prod_erase_sub`). -/
theorem prod_erase_sub (k : ℕ) (hk : k < p) :
    ∏ a ∈ (range p).erase k, ((k : ZMod p) - a) = -1 := by
  rw [← ZMod.prod_Ico_one_prime p]
  have hinj : ∀ a b : ℕ, a < p → b < p → (a : ZMod p) = b → a = b := fun a b ha hb h => by
    rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
  refine Finset.prod_nbij' (fun a => ((k : ZMod p) - a).val) (fun b => ((k : ZMod p) - b).val)
    (fun a ha => ?_) (fun b hb => ?_) (fun a ha => ?_) (fun b hb => ?_) (fun a _ => ?_)
  · obtain ⟨hak, ha⟩ := Finset.mem_erase.mp ha
    refine Finset.mem_Ico.mpr ⟨Nat.one_le_iff_ne_zero.mpr fun h0 => hak ?_, ZMod.val_lt _⟩
    rw [ZMod.val_eq_zero, sub_eq_zero] at h0
    exact (hinj k a hk (mem_range.mp ha) h0).symm
  · obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.mp hb
    refine Finset.mem_erase.mpr ⟨fun h => ?_, mem_range.mpr (ZMod.val_lt _)⟩
    have h' := congrArg (fun m : ℕ => (m : ZMod p)) h
    simp only [ZMod.natCast_zmod_val] at h'
    have : ((b : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
      rw [Nat.cast_zero]; exact (sub_eq_self.mp h')
    exact absurd (hinj b 0 hb2 hp.out.pos this) (by omega)
  · rw [ZMod.natCast_zmod_val, sub_sub_cancel, ZMod.val_cast_of_lt (mem_range.mp
      (Finset.mem_of_mem_erase ha))]
  · rw [ZMod.natCast_zmod_val, sub_sub_cancel, ZMod.val_cast_of_lt (Finset.mem_Ico.mp hb).2]
  · rw [ZMod.natCast_zmod_val]

/-- The residue counts add up to the cardinality (pfq54 `sum_rc`). -/
theorem sum_rc (s : Multiset ℤ) : ∑ a ∈ range p, rc s p a = Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => exact Finset.sum_eq_zero fun a _ => by rw [rc, Multiset.filter_zero]; rfl
  | cons x s ih =>
    have hx : x % (p : ℤ) = ((x % p).toNat : ℕ) :=
      (Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero))).symm
    rw [Finset.sum_congr rfl fun a _ => rc_cons p x s a, Finset.sum_add_distrib, ih,
      Finset.sum_eq_single ((x % p).toNat), ite_eq_left hx, Multiset.card_cons]
    · intro a _ hne
      exact ite_eq_right fun h => hne (by rw [hx] at h; exact_mod_cast h.symm)
    · exact fun h => absurd (mem_range.mpr (class_lt p x)) h

/-- A root product with no factor divisible by `p` is a `p`-adic unit. -/
theorem not_dvd_pr (s : Multiset ℤ) (t : ℤ) (h : ∀ y ∈ s, ¬ (p : ℤ) ∣ t - y) :
    ¬ (p : ℤ) ∣ pr s t := by
  intro hd
  have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  obtain ⟨z, hz, hdz⟩ := hpr.exists_mem_multiset_dvd hd
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  exact h y hy hdz

/-- A log-derivative sum with unit denominators is `p`-integral. -/
theorem vLs (s : Multiset ℤ) (t : ℤ) (h : ∀ y ∈ s, ¬ (p : ℤ) ∣ t - y) : ValGE p 0 (Ls s t) := by
  induction s using Multiset.induction_on with
  | empty => exact Or.inl (by simp [Ls])
  | cons x s ih =>
    rw [Ls_cons, one_div]
    exact vadd (vinv_unit _ (h x (Multiset.mem_cons_self _ _)))
      (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

/-- The local partial-fraction coefficients are `p`-integral when the other roots are at unit
distance from the pole. -/
theorem vpf_local (Nl Dl : Multiset ℤ) (l : ℤ) (hl : l ∉ Nl)
    (hsep : ∀ m ∈ Nl + Dl, m ≠ l → ¬ (p : ℤ) ∣ l - m) :
    ValGE p 0 (pfCoeff Nl Dl l).1 ∧ ValGE p 0 (pfCoeff Nl Dl l).2 := by
  have hN : ∀ m ∈ Nl, ¬ (p : ℤ) ∣ l - m := fun m hm =>
    hsep m (Multiset.mem_add.mpr (Or.inl hm)) fun e => hl (e ▸ hm)
  have hD : ∀ m ∈ Dl.filter (· ≠ l), ¬ (p : ℤ) ∣ l - m := fun m hm =>
    hsep m (Multiset.mem_add.mpr (Or.inr (Multiset.mem_of_mem_filter hm)))
      (Multiset.mem_filter.mp hm).2
  have hA : ValGE p 0 (((pr Nl l : ℤ) : ℚ) / ((pr (Dl.filter (· ≠ l)) l : ℤ) : ℚ)) := by
    rw [div_eq_mul_inv]
    simpa using vmul (vint (p := p) (pr Nl l)) (vinv_unit _ (not_dvd_pr p _ _ hD))
  rw [pfCoeff_eq Nl Dl l hl]
  split_ifs
  · refine ⟨hA, ?_⟩
    simpa using vmul hA (vsub (vLs p Nl l hN) (vLs p _ l hD))
  · exact ⟨Or.inl rfl, hA⟩
  · exact ⟨Or.inl rfl, Or.inl rfl⟩

end Modp

end Meijer5255.ShellFirstOrder.Gen

