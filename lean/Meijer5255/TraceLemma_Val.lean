/-
# Helper for `TraceLemma.lean`: the `ValGE` calculus

`p`-adic units, the first-order calculus modulo `p²` (`FO p x c t`: `x ≡ c (1 + p t)`), and the
unit expansion `(u + p v)⁻¹ ≡ u⁻¹ (1 - p v/u)`. Generic; imported only by `TraceLemma*.lean`.
The basic closure lemmas follow zeta34 `blueprints/ZetasAux.lean` (provenance).
-/
import Meijer5255.definitions

open Finset

noncomputable section

namespace Meijer5255.TraceAux

open Meijer5255

variable {p : ℕ} [Fact p.Prime]

set_option linter.unusedSectionVars false

/-! ### Closure lemmas -/

omit [Fact p.Prime] in
theorem vge_zero (k : ℤ) : ValGE p k 0 := Or.inl rfl

omit [Fact p.Prime] in
theorem vge_mono {j k : ℤ} {x : ℚ} (h : ValGE p k x) (hjk : j ≤ k) : ValGE p j x :=
  h.imp id fun h => le_trans hjk h

theorem vge_mul {a b : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p b y) :
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

theorem vge_mul' {a b c : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p b y) (h : c ≤ a + b) :
    ValGE p c (x * y) := vge_mono (vge_mul hx hy) h

omit [Fact p.Prime] in
theorem vge_neg {a : ℤ} {x : ℚ} (hx : ValGE p a x) : ValGE p a (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [padicValRat.neg]

theorem vge_add {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem vge_sub {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x - y) := by
  rw [sub_eq_add_neg]; exact vge_add hx (vge_neg hy)

theorem vge_sum {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℚ)
    (h : ∀ i ∈ s, ValGE p a (f i)) : ValGE p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact vge_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem vge_msum (a : ℤ) (m : Multiset ℚ) (h : ∀ x ∈ m, ValGE p a x) : ValGE p a m.sum := by
  induction m using Multiset.induction_on with
  | empty => exact Or.inl (by simp)
  | cons x m ih =>
    rw [Multiset.sum_cons]
    exact vge_add (h x (Multiset.mem_cons_self x m))
      (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

omit [Fact p.Prime] in
theorem vge_int (z : ℤ) : ValGE p 0 (z : ℚ) := by
  rcases eq_or_ne z 0 with h | h
  · left; simp [h]
  · right; rw [padicValRat.of_int]; positivity

omit [Fact p.Prime] in
theorem vge_one : ValGE p 0 (1 : ℚ) := by simpa using vge_int (p := p) 1

theorem vge_p : ValGE p 1 (p : ℚ) :=
  Or.inr (le_of_eq (padicValRat.self (Fact.out : p.Prime).one_lt).symm)

theorem vge_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, ValGE p 0 (f i)) :
    ValGE p 0 (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vge_one (p := p)
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    simpa using vge_mul (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem vge_mprod (m : Multiset ℚ) (h : ∀ x ∈ m, ValGE p 0 x) : ValGE p 0 m.prod := by
  induction m using Multiset.induction_on with
  | empty => simpa using vge_one (p := p)
  | cons x m ih =>
    rw [Multiset.prod_cons]
    simpa using vge_mul (h x (Multiset.mem_cons_self x m))
      (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

theorem vge_pow {k : ℤ} {x : ℚ} (h : ValGE p k x) (n : ℕ) : ValGE p (n * k) (x ^ n) := by
  induction n with
  | zero => simpa using vge_one (p := p)
  | succ n ih => rw [pow_succ]; exact vge_mono (vge_mul ih h) (by push_cast; linarith)

theorem vge_p_pow (n : ℕ) : ValGE p n ((p : ℚ) ^ n) := by
  simpa using vge_pow (vge_p (p := p)) n

theorem vge_p_mul {k : ℤ} {x : ℚ} (h : ValGE p k x) : ValGE p (k + 1) (p * x) := by
  have := vge_mul (vge_p (p := p)) h; rwa [add_comm] at this

/-- From `p x ∈ p^{k+1}`, `x ∈ p^k`. -/
theorem vge_of_p_mul {k : ℤ} {x : ℚ} (h : ValGE p (k + 1) (p * x)) : ValGE p k x := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rcases h with h | h
  · left; simpa [hp] using h
  by_cases hx : x = 0
  · left; exact hx
  right
  rw [padicValRat.mul hp hx, padicValRat.self (Fact.out : p.Prime).one_lt] at h
  omega

theorem vge_div_p {k : ℤ} {x : ℚ} (h : ValGE p (k + 1) x) : ValGE p k (x / p) := by
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  apply vge_of_p_mul
  rwa [mul_div_cancel₀ _ hp]

/-! ### Units -/

/-- `x` is a `p`-adic unit. -/
def IsPU (p : ℕ) (x : ℚ) : Prop := x ≠ 0 ∧ padicValRat p x = 0

omit [Fact p.Prime] in
theorem IsPU.vge {x : ℚ} (h : IsPU p x) : ValGE p 0 x := Or.inr h.2.ge

theorem isPU_int {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) : IsPU p (u : ℚ) := by
  refine ⟨by exact_mod_cast fun h => hu (by rw [h]; exact dvd_zero _), ?_⟩
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd hu]; rfl

theorem IsPU.inv {x : ℚ} (h : IsPU p x) : IsPU p x⁻¹ :=
  ⟨inv_ne_zero h.1, by rw [padicValRat.inv, h.2, neg_zero]⟩

theorem IsPU.mul {x y : ℚ} (hx : IsPU p x) (hy : IsPU p y) : IsPU p (x * y) :=
  ⟨mul_ne_zero hx.1 hy.1, by rw [padicValRat.mul hx.1 hy.1, hx.2, hy.2, add_zero]⟩

theorem IsPU.div {x y : ℚ} (hx : IsPU p x) (hy : IsPU p y) : IsPU p (x / y) := by
  rw [div_eq_mul_inv]; exact hx.mul hy.inv

theorem IsPU.zpow {x : ℚ} (hx : IsPU p x) (n : ℤ) : IsPU p (x ^ n) :=
  ⟨zpow_ne_zero _ hx.1, by rw [padicValRat.zpow, hx.2, mul_zero]⟩

theorem IsPU.pow {x : ℚ} (hx : IsPU p x) (n : ℕ) : IsPU p (x ^ n) := by
  simpa using hx.zpow (n : ℤ)

theorem isPU_one : IsPU p (1 : ℚ) := ⟨one_ne_zero, padicValRat.one⟩

theorem isPU_prod {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i ∈ s, IsPU p (f i)) :
    IsPU p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isPU_one (p := p)
  | insert x s hx ih =>
    rw [Finset.prod_insert hx]
    exact (h x (Finset.mem_insert_self x s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isPU_mprod (m : Multiset ℚ) (h : ∀ x ∈ m, IsPU p x) : IsPU p m.prod := by
  induction m using Multiset.induction_on with
  | empty => simpa using isPU_one (p := p)
  | cons x m ih =>
    rw [Multiset.prod_cons]
    exact (h x (Multiset.mem_cons_self x m)).mul (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))

/-- A unit plus an element of `p ℤ_(p)` is a unit. -/
theorem IsPU.add {u x : ℚ} (hu : IsPU p u) (hx : ValGE p 1 x) : IsPU p (u + x) := by
  rcases hx with rfl | hx
  · rwa [add_zero]
  by_cases hx0 : x = 0
  · rwa [hx0, add_zero]
  have hlt : padicValRat p u < padicValRat p x := by rw [hu.2]; omega
  have hne : u + x ≠ 0 := by
    intro h
    have : x = -u := by linarith
    rw [this, padicValRat.neg] at hlt
    exact lt_irrefl _ hlt
  exact ⟨hne, by rw [padicValRat.add_eq_of_lt hne hu.1 hx0 hlt, hu.2]⟩

theorem vge_div_unit {k : ℤ} {x u : ℚ} (hx : ValGE p k x) (hu : IsPU p u) :
    ValGE p k (x / u) := by
  rw [div_eq_mul_inv]; simpa using vge_mul hx hu.inv.vge

/-- The unit expansion `(u + p v)⁻¹ ≡ u⁻¹ (1 - p v / u) (mod p²)` for a unit `u`. -/
theorem unit_expansion_gen {u v : ℚ} (hu : IsPU p u) (hv : ValGE p 0 v) :
    ValGE p 2 ((u + p * v)⁻¹ - u⁻¹ * (1 - p * v / u)) := by
  have hw : IsPU p (u + p * v) := hu.add (by simpa using vge_p_mul hv)
  have e : (u + p * v)⁻¹ - u⁻¹ * (1 - p * v / u) =
      ((p : ℚ) ^ 2 * v ^ 2) * ((u + p * v)⁻¹ * (u⁻¹ * u⁻¹)) := by
    field_simp [hw.1, hu.1]
    ring
  rw [e]
  refine vge_mul' (vge_mul (vge_p_pow 2) (vge_pow hv 2))
    (hw.inv.mul (hu.inv.mul hu.inv)).vge (by norm_num)

/-- `1/(u + p v) ≡ 1/u (mod p)`. -/
theorem inv_cong_one {u v : ℚ} (hu : IsPU p u) (hv : ValGE p 0 v) :
    ValGE p 1 ((u + p * v)⁻¹ - u⁻¹) := by
  have hw : IsPU p (u + p * v) := hu.add (by simpa using vge_p_mul hv)
  have e : (u + p * v)⁻¹ - u⁻¹ = -((p : ℚ) * v) * ((u + p * v)⁻¹ * u⁻¹) := by
    field_simp [hw.1, hu.1]
    ring
  rw [e]
  exact vge_mul' (vge_neg (by simpa using vge_p_mul hv)) (hw.inv.mul hu.inv).vge (by norm_num)

/-! ### First-order calculus modulo `p²` -/

/-- `x ≡ c (1 + p t) (mod p²)`, with `c, t` `p`-integral. -/
def FO (p : ℕ) (x c t : ℚ) : Prop :=
  ValGE p 0 c ∧ ValGE p 0 t ∧ ValGE p 2 (x - c * (1 + p * t))

theorem FO.int {x c t : ℚ} (h : FO p x c t) : ValGE p 0 x := by
  have h1 : ValGE p 0 (c * (1 + p * t)) :=
    by simpa using vge_mul h.1 (vge_add vge_one (vge_mono (vge_p_mul h.2.1) (by norm_num)))
  have := vge_add (vge_mono h.2.2 (by norm_num)) h1
  rwa [sub_add_cancel] at this

/-- `x ≡ c (mod p)`. -/
theorem FO.cong1 {x c t : ℚ} (h : FO p x c t) : ValGE p 1 (x - c) := by
  have h1 : ValGE p 1 (c * (p * t)) := by simpa using vge_mul h.1 (vge_p_mul h.2.1)
  have e : x - c = (x - c * (1 + p * t)) + c * (p * t) := by ring
  rw [e]; exact vge_add (vge_mono h.2.2 (by norm_num)) h1

theorem FO.congr {x c t c' t' : ℚ} (h : FO p x c t) (hc : c = c') (ht : t = t') :
    FO p x c' t' := hc ▸ ht ▸ h

theorem FO.mul {x y c d s t : ℚ} (hx : FO p x c s) (hy : FO p y d t) :
    FO p (x * y) (c * d) (s + t) := by
  refine ⟨by simpa using vge_mul hx.1 hy.1, by simpa using vge_add hx.2.1 hy.2.1, ?_⟩
  have hyI := hy.int
  have hc1 : ValGE p 0 (c * (1 + p * s)) :=
    by simpa using vge_mul hx.1 (vge_add vge_one (vge_mono (vge_p_mul hx.2.1) (by norm_num)))
  have e : x * y - c * d * (1 + p * (s + t)) =
      (x - c * (1 + p * s)) * y + c * (1 + p * s) * (y - d * (1 + p * t)) +
        ((p : ℚ) ^ 2 * (c * d * s * t)) := by ring
  rw [e]
  refine vge_add (vge_add (by simpa using vge_mul hx.2.2 hyI) (by simpa using vge_mul hc1 hy.2.2))
    (vge_mul' (vge_p_pow 2) (by simpa using vge_mul (vge_mul (vge_mul hx.1 hy.1) hx.2.1) hy.2.1)
      (by norm_num))

theorem FO.one : FO p 1 1 0 := ⟨vge_one, vge_zero 0, by simp [vge_zero]⟩

theorem FO.prod {ι : Type*} (s : Finset ι) (x c t : ι → ℚ) (h : ∀ i ∈ s, FO p (x i) (c i) (t i)) :
    FO p (∏ i ∈ s, x i) (∏ i ∈ s, c i) (∑ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using FO.one (p := p)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The inverse of a first-order expansion with a unit leading term. -/
theorem FO.inv {x c t : ℚ} (h : FO p x c t) (hc : IsPU p c) : FO p x⁻¹ c⁻¹ (-t) := by
  have hx : IsPU p x := by
    have := hc.add h.cong1
    rwa [add_sub_cancel] at this
  refine ⟨hc.inv.vge, vge_neg h.2.1, ?_⟩
  set δ := x - c * (1 + p * t) with hδ
  have e : x⁻¹ - c⁻¹ * (1 + p * -t) =
      ((p : ℚ) ^ 2 * (c * t ^ 2) - δ * (1 - p * t)) * (x⁻¹ * c⁻¹) := by
    have hx' : x = δ + c * (1 + p * t) := by rw [hδ]; ring
    field_simp [hx.1, hc.1]
    rw [hx']; ring
  rw [e]
  have h1 : ValGE p 2 ((p : ℚ) ^ 2 * (c * t ^ 2)) :=
    vge_mul' (vge_p_pow 2) (by simpa using vge_mul hc.vge (vge_pow h.2.1 2)) (by norm_num)
  have h2 : ValGE p 2 (δ * (1 - p * t)) :=
    vge_mul' h.2.2 (vge_sub vge_one (vge_mono (vge_p_mul h.2.1) (by norm_num))) (by norm_num)
  exact vge_mul' (vge_sub h1 h2) (hx.inv.mul hc.inv).vge (by norm_num)

/-- The linear factor `u + p v = u (1 + p (v/u))`. -/
theorem FO.linear {u v : ℚ} (hu : IsPU p u) (hv : ValGE p 0 v) : FO p (u + p * v) u (v / u) := by
  refine ⟨hu.vge, vge_div_unit hv hu, ?_⟩
  have : u + p * v - u * (1 + p * (v / u)) = 0 := by field_simp [hu.1]; ring
  rw [this]; exact vge_zero 2

/-- Multiset product of linear factors `u + p v_i` with a fixed unit `u`. -/
theorem FO.mprod_linear {u : ℚ} (hu : IsPU p u) (m : Multiset ℚ) (hm : ∀ v ∈ m, ValGE p 0 v) :
    FO p (m.map fun v => u + p * v).prod (u ^ Multiset.card m) ((m.map fun v => v / u).sum) := by
  induction m using Multiset.induction_on with
  | empty => simpa using FO.one (p := p)
  | cons a m ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons, Multiset.card_cons]
    have := (FO.linear hu (hm a (Multiset.mem_cons_self a m))).mul
      (ih fun v hv => hm v (Multiset.mem_cons_of_mem hv))
    exact this.congr (by ring) rfl

end Meijer5255.TraceAux
