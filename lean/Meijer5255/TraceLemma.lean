/-
# Node blueprint: `trace_lemma` (paper §8, "A second-order trace identity")

Target (restated verbatim from `Blueprint_5255.lean`): under `TraceHyp p Nr Dr R NU DU`, for every
integral high pole `ℓ`,
  `ValGE p 3 (highPoleA p Nr Dr R ℓ) ∧ ValGE p 2 (highPoleB p Nr Dr R ℓ)`.

Strategy (paper §8 in the "Lean-friendly" form of `LEAN_HANDOFF.md` §5.6: no formal deformation
parameter, expand directly at `P = p` modulo `p²`). Fix `ℓ`. Write every root as `k' + pℓ'`
(`k' ∈ R`); put `h_k = |N_k| - |D_k|`, `σ_k = ΣN_k - ΣD_k`, and for the `P = 0` function
`F₀ = ∏_{s ∈ R} (z - s)^{h_s}`: `L_k = ∏_{s ≠ k} (k - s)^{h_s}` (its residue at a minimal class,
its value at a class with `h_k = 0`), `A_k = ∑_{s ≠ k} h_s/(k - s)`, `B_k = ∑_{s ≠ k} σ_s/(k - s)`.
At the class `k`, `p F(k + pV) = p^{h_k+1} U_k(V) G_k(V)` where `G_k` collects the factors of the
other classes; `G_k(ℓ) ≡ L_k(1 + p(ℓA_k - B_k))`, `G_k'(ℓ) ≡ p L_k A_k (mod p²)` by the unit
expansion `(u + pv)^{-1} ≡ u^{-1}(1 - pv/u)` ([2]). Hence, with `α_ℓ, β_ℓ` the (`p`-integral)
pole coefficients of the common kernel `U`, the class contributions to `A_ℓ/p` and `B_ℓ` are
explicit modulo `p²` ([3]). Summing over `k ∈ R` (glue), the exact residue identities
(RI) `∑_{h=-1} L_k = 0`, `∑_{h=-1} L_k(B_k + σ_*A_k) + ∑_{h=0} σ_k L_k = 0` ([1]) collapse the sums
to `p α_ℓ (ℓ+σ_*) D` and `p (α_ℓ + β_ℓ(ℓ+σ_*)) D` with `D = ∑_{h=-1} L_kA_k + ∑_{h=0} L_k`.
Finally `D ≡ -∑_{k∈R} Q̃'(k) (mod p)` ([5]) and `∑_{k∈R} Q̃'(k) ≡ 0` since
`deg Q̃' ≤ p - 3` ([4], [6]).

Glue (below): reindex `A_ℓ, B_ℓ` as sums over `k ∈ R`; case split `h_k = -1 / 0 / ≥ 1` on each
class to apply [3]; split the sums by `Finset.sum_filter`; the (RI) bookkeeping by
`linear_combination`; `D ≡ 0` from [4]–[6] and `natDegree_derivative_le`; `ValGE` arithmetic.

Supporting lemmas (6), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `residue_identities` | 150 | yes ((RI), residue theorem for `F₀` and `∂_P F_P`) |
| 2 | `unit_expansion` | 25 | partially (the PDF expands in the deformation parameter `P`) |
| 3 | `local_expansion` | 300 | partially (PDF: expansion in `P`; here directly at `P = p`) |
| 4 | `Qt_natDegree` | 40 | yes (`deg Q̃ = p - 2`) |
| 5 | `D_terms_congr` | 120 | yes (`L_kA_k ≡ -Q̃'(k)`, `L_k ≡ -Q̃'(k)`, `H ≡ z^p - z`) |
| 6 | `complete_sum_dvd` | 40 | yes (`deg Q̃' = p - 3 < p - 1`) |

Reuse: pfq54 `residue_block.sum_residues_dvd` (pattern for [6]), `residue_aux2.lean` (`pr`, `Ls`,
`unit_part`, `val_pr_rc`: products and logarithmic derivatives over a class), zeta34
`cross_product_readout.lean` (`exists_isPF`, `pfCoeff`: partial-fraction extraction),
`blueprints/ZetasAux.lean` (`ValGE` calculus), `valuation_bound.lean` (`ValGE_sum`).
-/
import Meijer5255.definitions
import Meijer5255.TraceLemma_Cls
import Meijer5255.TraceLemma_Res
import Meijer5255.TraceLemma_Loc

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.TraceLemma

open Meijer5255

/-! ### Objects -/

section Defs

variable (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ)

/-- `h_k = |N_k| - |D_k|`. -/
def hcl (k : ℤ) : ℤ := ((hiRoots p k Nr).card : ℤ) - ((hiRoots p k Dr).card : ℤ)

/-- `σ_k = ∑ N_k - ∑ D_k`. -/
def sig (k : ℤ) : ℤ := (hiRoots p k Nr).sum - (hiRoots p k Dr).sum

/-- `σ_* = ∑ NU - ∑ DU`, the common value of `σ_k` on the minimal classes. -/
def sigU (NU DU : Multiset ℤ) : ℤ := NU.sum - DU.sum

/-- `L_k = ∏_{s ∈ R, s ≠ k} (k - s)^{h_s}`: the residue of `F₀` at a minimal class, `F₀(k)` at a
class with `h_k = 0`. -/
def Lres (k : ℤ) : ℚ := ∏ s ∈ R.erase k, ((k - s : ℤ) : ℚ) ^ hcl p Nr Dr s

/-- `A_k = ∑_{s ≠ k} h_s/(k - s)` (the logarithmic derivative of `F₀ (z - k)^{-h_k}` at `k`). -/
def Acoef (k : ℤ) : ℚ := ∑ s ∈ R.erase k, (hcl p Nr Dr s : ℚ) / ((k - s : ℤ) : ℚ)

/-- `B_k = ∑_{s ≠ k} σ_s/(k - s)`. -/
def Bcoef (k : ℤ) : ℚ := ∑ s ∈ R.erase k, (sig p Nr Dr s : ℚ) / ((k - s : ℤ) : ℚ)

/-- `Q̃ = ∏_{s ∈ R} (X - s)^{h_s + 1}`, so that `F₀ = Q̃/H`, `H = ∏_{s∈R} (X - s)`. -/
def Qt : ℤ[X] := ∏ s ∈ R, (X - C s) ^ (hcl p Nr Dr s + 1).toNat

/-- The minimal classes `h_k = -1`. -/
def minR : Finset ℤ := R.filter fun k => hcl p Nr Dr k = -1

/-- The classes with `h_k = 0`. -/
def zeroR : Finset ℤ := R.filter fun k => hcl p Nr Dr k = 0

/-- `S₀ = ∑_{h=-1} L_k`. -/
def S0 : ℚ := ∑ k ∈ minR p Nr Dr R, Lres p Nr Dr R k

/-- `S₁ = ∑_{h=-1} L_k A_k`. -/
def S1 : ℚ := ∑ k ∈ minR p Nr Dr R, Lres p Nr Dr R k * Acoef p Nr Dr R k

/-- `S₂ = ∑_{h=-1} L_k B_k`. -/
def S2 : ℚ := ∑ k ∈ minR p Nr Dr R, Lres p Nr Dr R k * Bcoef p Nr Dr R k

/-- `S₃ = ∑_{h=0} L_k`. -/
def S3 : ℚ := ∑ k ∈ zeroR p Nr Dr R, Lres p Nr Dr R k

/-- `S₄ = ∑_{h=0} σ_k L_k`. -/
def S4 : ℚ := ∑ k ∈ zeroR p Nr Dr R, (sig p Nr Dr k : ℚ) * Lres p Nr Dr R k

/-- The class-`k` term of `D = ∑_{h=-1} L_kA_k + ∑_{h=0} L_k`. -/
def dTerm (k : ℤ) : ℚ :=
  (if hcl p Nr Dr k = -1 then Lres p Nr Dr R k * Acoef p Nr Dr R k else 0) +
    (if hcl p Nr Dr k = 0 then Lres p Nr Dr R k else 0)

/-- The predicted class-`k` contribution to `A_ℓ/p` modulo `p²` (glue helper):
`α_ℓ L_k (1 + p(ℓA_k - B_k))` on a minimal class, `p α_ℓ (ℓ - a_k) L_k` on a class with
`h_k = 0` (`a_k = σ_k - σ_*`), `0` otherwise. -/
def mainA (NU DU : Multiset ℤ) (α : ℤ → ℚ) (ℓ k : ℤ) : ℚ :=
  (if hcl p Nr Dr k = -1 then
      α ℓ * Lres p Nr Dr R k * (1 + p * (ℓ * Acoef p Nr Dr R k - Bcoef p Nr Dr R k))
    else 0) +
  (if hcl p Nr Dr k = 0 then
      p * α ℓ * (ℓ - ((sig p Nr Dr k : ℚ) - sigU NU DU)) * Lres p Nr Dr R k
    else 0)

/-- The predicted class-`k` contribution to `B_ℓ` modulo `p²` (glue helper):
`β_ℓ L_k (1 + p(ℓA_k - B_k)) + p α_ℓ L_k A_k` on a minimal class,
`p L_k (α_ℓ + (ℓ - a_k) β_ℓ)` on a class with `h_k = 0`, `0` otherwise. -/
def mainB (NU DU : Multiset ℤ) (α β : ℤ → ℚ) (ℓ k : ℤ) : ℚ :=
  (if hcl p Nr Dr k = -1 then
      β ℓ * Lres p Nr Dr R k * (1 + p * (ℓ * Acoef p Nr Dr R k - Bcoef p Nr Dr R k)) +
        p * α ℓ * Lres p Nr Dr R k * Acoef p Nr Dr R k
    else 0) +
  (if hcl p Nr Dr k = 0 then
      p * Lres p Nr Dr R k * (α ℓ + (ℓ - ((sig p Nr Dr k : ℚ) - sigU NU DU)) * β ℓ)
    else 0)

end Defs

/-! ### Glue helpers (fully proved; the `ValGE` calculus, as in zeta34 `ZetasAux.lean`) -/

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

omit [Fact p.Prime] in
theorem valGE_neg {a : ℤ} {x : ℚ} (hx : ValGE p a x) : ValGE p a (-x) := by
  rcases hx with rfl | hx
  · left; simp
  · right; rwa [padicValRat.neg]

theorem valGE_add {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x + y) := by
  rcases hx with rfl | hx
  · rwa [zero_add]
  rcases hy with rfl | hy
  · rw [add_zero]; exact Or.inr hx
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  exact Or.inr ((le_min hx hy).trans (padicValRat.min_le_padicValRat_add hxy))

theorem valGE_sub {a : ℤ} {x y : ℚ} (hx : ValGE p a x) (hy : ValGE p a y) :
    ValGE p a (x - y) := by
  rw [sub_eq_add_neg]; exact valGE_add hx (valGE_neg hy)

theorem valGE_sum {ι : Type*} (s : Finset ι) (a : ℤ) (f : ι → ℚ)
    (h : ∀ i ∈ s, ValGE p a (f i)) : ValGE p a (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl (by simp)
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact valGE_add (h x (Finset.mem_insert_self x s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

omit [Fact p.Prime] in
theorem valGE_int (z : ℤ) : ValGE p 0 (z : ℚ) := by
  rcases eq_or_ne z 0 with h | h
  · left; simp [h]
  · right; rw [padicValRat.of_int]; positivity

theorem valGE_p : ValGE p 1 (p : ℚ) :=
  Or.inr (le_of_eq (padicValRat.self (Fact.out : p.Prime).one_lt).symm)

end ValGEcalc

/-! ### Auxiliary facts from `TraceHyp` (class bookkeeping) -/

section HypFacts

open TraceAux

variable {p : ℕ} [Fact p.Prime] {Nr Dr : Multiset ℤ} {R : Finset ℤ} {NU DU : Multiset ℤ}

theorem hyp_sum_hcl (h : TraceHyp p Nr Dr R NU DU) : ∑ s ∈ R, hcl p Nr Dr s = -2 := by
  have h1 := card_hiRoots_sum (p := p) h.complete Nr
  have h2 := card_hiRoots_sum (p := p) h.complete Dr
  simp only [hcl, Finset.sum_sub_distrib, h1, h2, h.deg]
  push_cast; ring

omit [Fact p.Prime] in
theorem hyp_hge (h : TraceHyp p Nr Dr R NU DU) {s : ℤ} (hs : s ∈ R) : -1 ≤ hcl p Nr Dr s := by
  have := h.h_ge s hs; unfold hcl; omega

omit [Fact p.Prime] in
theorem hyp_sig_min (h : TraceHyp p Nr Dr R NU DU) {k : ℤ} (hk : k ∈ R)
    (hm : hcl p Nr Dr k = -1) : sig p Nr Dr k = sigU NU DU := by
  have hc : (hiRoots p k Dr).card = (hiRoots p k Nr).card + 1 := by unfold hcl at hm; omega
  have := congrArg Multiset.sum (h.minimal k hk hc)
  simp only [Multiset.sum_add] at this
  unfold sig sigU; linarith

theorem hyp_ndvd (h : TraceHyp p Nr Dr R NU DU) {k s : ℤ} (hk : k ∈ R) (hs : s ∈ R)
    (hne : k ≠ s) : ¬ (p : ℤ) ∣ k - s := cl_ndvd h.complete hk hs hne

theorem hyp_sub_ne (h : TraceHyp p Nr Dr R NU DU) {k s : ℤ} (hk : k ∈ R) (hs : s ∈ R)
    (hne : k ≠ s) : (((k - s : ℤ)) : ℚ) ≠ 0 := (isPU_int (hyp_ndvd h hk hs hne)).1

theorem hyp_L_unit (h : TraceHyp p Nr Dr R NU DU) {k : ℤ} (hk : k ∈ R) :
    IsPU p (Lres p Nr Dr R k) :=
  isPU_prod _ _ fun _ hs =>
    (isPU_int (hyp_ndvd h hk (mem_of_mem_erase hs) (ne_of_mem_erase hs).symm)).zpow _

theorem hyp_A_int (h : TraceHyp p Nr Dr R NU DU) {k : ℤ} (hk : k ∈ R) :
    ValGE p 0 (Acoef p Nr Dr R k) :=
  vge_sum _ _ _ fun _ hs => vge_div_unit (vge_int _)
    (isPU_int (hyp_ndvd h hk (mem_of_mem_erase hs) (ne_of_mem_erase hs).symm))

theorem hyp_B_int (h : TraceHyp p Nr Dr R NU DU) {k : ℤ} (hk : k ∈ R) :
    ValGE p 0 (Bcoef p Nr Dr R k) :=
  vge_sum _ _ _ fun _ hs => vge_div_unit (vge_int _)
    (isPU_int (hyp_ndvd h hk (mem_of_mem_erase hs) (ne_of_mem_erase hs).symm))

/-- `Q̃` over `ℚ` is `rp R (h + 1)`. -/
theorem Qt_map (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ) :
    (Qt p Nr Dr R).map (Int.castRingHom ℚ) = rp R (fun t => (hcl p Nr Dr t + 1).toNat) := by
  simp [Qt, rp, Polynomial.map_prod]

/-- `∏_{t ≠ k} (k - t)^{h_t + 1} = L_k W_k`. -/
theorem hyp_Qk_eval (h : TraceHyp p Nr Dr R NU DU) {k : ℤ} (hk : k ∈ R) :
    (rp (R.erase k) (fun t => (hcl p Nr Dr t + 1).toNat)).eval (k : ℚ) =
      Lres p Nr Dr R k * Wk R k := by
  rw [rp_eval, Lres, Wk, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t ht => ?_
  have hne := hyp_sub_ne h hk (mem_of_mem_erase ht) (ne_of_mem_erase ht).symm
  push_cast at hne ⊢
  rw [← zpow_add_one₀ hne, ← zpow_natCast]
  congr 1
  have := hyp_hge h (mem_of_mem_erase ht)
  omega

end HypFacts

/-- The residue sum of `F₀(z)/(z - s)` (glue for [1]): simple poles at the minimal classes
`k ≠ s` with residues `L_k/(k - s)`, and at `s` the residue `L_s A_s` (`h_s = -1`, double pole) or
`L_s` (`h_s = 0`). (The term `k = s` of the first sum is `L_s/0 = 0`.) -/
def Cres (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ) (s : ℤ) : ℚ :=
  ∑ k ∈ minR p Nr Dr R, Lres p Nr Dr R k / ((k : ℚ) - s) +
    (if hcl p Nr Dr s = -1 then Lres p Nr Dr R s * Acoef p Nr Dr R s else 0) +
    (if hcl p Nr Dr s = 0 then Lres p Nr Dr R s else 0)

section ResidueFacts

open TraceAux

variable {p : ℕ} [Fact p.Prime] {Nr Dr : Multiset ℤ} {R : Finset ℤ} {NU DU : Multiset ℤ}

theorem hyp_sum_toNat (h : TraceHyp p Nr Dr R NU DU) :
    ((∑ s ∈ R, (hcl p Nr Dr s + 1).toNat : ℕ) : ℤ) = p - 2 := by
  have hcard := card_R h.complete
  push_cast
  rw [Finset.sum_congr rfl (fun s hs => Int.toNat_of_nonneg (by have := hyp_hge h hs; omega)),
    Finset.sum_add_distrib, hyp_sum_hcl h]
  simp [hcard]; ring

/-- `L_k (k - s)^{-1}` as a product with the exponent of `s` lowered by one. -/
theorem Lres_div (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ) {k s : ℤ} (hs : s ∈ R.erase k) :
    ∏ t ∈ R.erase k, ((k : ℚ) - t) ^ (hcl p Nr Dr t - if t = s then 1 else 0) =
      Lres p Nr Dr R k / ((k : ℚ) - s) := by
  have hne : ∀ t ∈ R.erase k, (k : ℚ) - t ≠ 0 := fun t ht =>
    sub_ne_zero.2 (by exact_mod_cast (Finset.ne_of_mem_erase ht).symm)
  have e : ∀ t ∈ R.erase k, ((k : ℚ) - t) ^ (hcl p Nr Dr t - if t = s then 1 else 0) =
      ((k : ℚ) - t) ^ hcl p Nr Dr t * (if t = s then ((k : ℚ) - t)⁻¹ else 1) := by
    intro t ht
    split_ifs
    · rw [zpow_sub₀ (hne t ht), zpow_one, div_eq_mul_inv]
    · rw [sub_zero, mul_one]
  rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, Finset.prod_ite_eq' _ _ _, ite_eq_left hs,
    Lres, div_eq_mul_inv]
  push_cast; rfl

/-- **(RI), first identity.** `∑_{h=-1} L_k = 0`. -/
theorem hyp_S0 (h : TraceHyp p Nr Dr R NU DU) : S0 p Nr Dr R = 0 := by
  classical
  set n : ℤ → ℕ := fun t => (hcl p Nr Dr t + 1).toNat with hn
  have hncast : ∀ t ∈ R, ((n t : ℕ) : ℤ) = hcl p Nr Dr t + 1 := fun t ht =>
    Int.toNat_of_nonneg (by have := hyp_hge h ht; omega)
  have hdeg : (rp R n).natDegree + 2 ≤ R.card := by
    rw [rp_natDegree, card_R h.complete]
    have : ((∑ s ∈ R, n s : ℕ) : ℤ) = p - 2 := hyp_sum_toNat h
    have hp := (Fact.out : p.Prime).two_le
    omega
  have hres := res_sum_simple R (rp R n) hdeg
  rw [S0, minR, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun k hk => ?_).trans hres
  rw [rp_eval_div_Wk R n hk]
  have hiff : n k = 0 ↔ hcl p Nr Dr k = -1 := by
    have := hncast k hk; omega
  by_cases e : hcl p Nr Dr k = -1
  · rw [ite_eq_left e, ite_eq_left (hiff.2 e), Lres]
    push_cast
    refine Finset.prod_congr rfl fun t ht => ?_
    rw [hncast t (Finset.mem_of_mem_erase ht)]; ring_nf
  · rw [ite_eq_right e, ite_eq_right (mt hiff.1 e)]

/-- `C_s = 0` at a class with `h_s ≥ 0` (simple poles only). -/
theorem hyp_Cres_nonneg (h : TraceHyp p Nr Dr R NU DU) {s : ℤ} (hs : s ∈ R)
    (hs0 : 0 ≤ hcl p Nr Dr s) : Cres p Nr Dr R s = 0 := by
  classical
  set n : ℤ → ℕ := fun t => (hcl p Nr Dr t + 1 - if t = s then 1 else 0).toNat with hn
  have hncast : ∀ t ∈ R, ((n t : ℕ) : ℤ) = hcl p Nr Dr t + 1 - if t = s then 1 else 0 :=
    fun t ht => Int.toNat_of_nonneg (by
      have := hyp_hge h ht; split_ifs with e
      · subst e; omega
      · omega)
  have hdeg : (rp R n).natDegree + 2 ≤ R.card := by
    rw [rp_natDegree, card_R h.complete]
    have h1 : ((∑ t ∈ R, (hcl p Nr Dr t + 1).toNat : ℕ) : ℤ) = p - 2 := hyp_sum_toNat h
    have h2 : ((∑ t ∈ R, n t : ℕ) : ℤ) = ((∑ t ∈ R, (hcl p Nr Dr t + 1).toNat : ℕ) : ℤ) - 1 := by
      push_cast
      rw [Finset.sum_congr rfl hncast, Finset.sum_sub_distrib, Finset.sum_ite_eq' R s, ite_eq_left hs,
        Finset.sum_congr rfl (fun t ht => Int.toNat_of_nonneg (by have := hyp_hge h ht; omega))]
    have hp := (Fact.out : p.Prime).two_le
    omega
  have hres := res_sum_simple R (rp R n) hdeg
  rw [← Finset.add_sum_erase R _ hs] at hres
  rw [rp_eval_div_Wk R n hs] at hres
  have hns : n s = 0 ↔ hcl p Nr Dr s = 0 := by have := hncast s hs; simp at this; omega
  -- the term at `s`
  have hts : (if n s = 0 then ∏ t ∈ R.erase s, ((s : ℚ) - t) ^ ((n t : ℤ) - 1) else 0) =
      if hcl p Nr Dr s = 0 then Lres p Nr Dr R s else 0 := by
    by_cases e : hcl p Nr Dr s = 0
    · rw [ite_eq_left (hns.2 e), ite_eq_left e, Lres]; push_cast
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [hncast t (Finset.mem_of_mem_erase ht), ite_eq_right (Finset.ne_of_mem_erase ht)]; ring_nf
    · rw [ite_eq_right (mt hns.1 e), ite_eq_right e]
  -- the other terms
  have htk : ∀ k ∈ R.erase s, (rp R n).eval (k : ℚ) / Wk R k =
      if hcl p Nr Dr k = -1 then Lres p Nr Dr R k / ((k : ℚ) - s) else 0 := by
    intro k hk
    have hkR := Finset.mem_of_mem_erase hk
    have hks := Finset.ne_of_mem_erase hk
    rw [rp_eval_div_Wk R n hkR]
    have hnk : n k = 0 ↔ hcl p Nr Dr k = -1 := by
      have := hncast k hkR; rw [ite_eq_right hks] at this; omega
    by_cases e : hcl p Nr Dr k = -1
    · rw [ite_eq_left (hnk.2 e), ite_eq_left e, ← Lres_div p Nr Dr R
        (Finset.mem_erase.2 ⟨Ne.symm hks, hs⟩)]
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [hncast t (Finset.mem_of_mem_erase ht)]; ring_nf
    · rw [ite_eq_right (mt hnk.1 e), ite_eq_right e]
  rw [hts, Finset.sum_congr rfl htk] at hres
  rw [Cres, ite_eq_right (by omega), add_zero, minR, Finset.sum_filter, ← Finset.sum_erase R
    (a := s) (by rw [ite_eq_right (by omega)])]
  linarith

/-- `C_s = 0` at a minimal class (one double pole). -/
theorem hyp_Cres_min (h : TraceHyp p Nr Dr R NU DU) {s : ℤ} (hs : s ∈ R)
    (hsm : hcl p Nr Dr s = -1) : Cres p Nr Dr R s = 0 := by
  classical
  set n : ℤ → ℕ := fun t => (hcl p Nr Dr t + 1).toNat with hn
  have hncast : ∀ t ∈ R, ((n t : ℕ) : ℤ) = hcl p Nr Dr t + 1 := fun t ht =>
    Int.toNat_of_nonneg (by have := hyp_hge h ht; omega)
  set S := R.erase s with hS
  have hcardS : S.card = p - 1 := by rw [hS, Finset.card_erase_of_mem hs, card_R h.complete]
  have hQ : (rp S n).degree < S.card := by
    refine (degree_le_natDegree).trans_lt ?_
    rw [rp_natDegree, hcardS]
    have h1 : ((∑ t ∈ R, n t : ℕ) : ℤ) = p - 2 := hyp_sum_toNat h
    have h2 : ∑ t ∈ R, n t = n s + ∑ t ∈ S, n t := (Finset.add_sum_erase R _ hs).symm
    have h3 : n s = 0 := by have := hncast s hs; omega
    have hp := (Fact.out : p.Prime).two_le
    have : ∑ t ∈ S, n t < p - 1 := by omega
    exact_mod_cast this
  have hd := res_sum_double S s (Finset.notMem_erase s R) (rp S n) hQ
  -- left side: the minimal classes `k ≠ s`
  have hL : ∀ k ∈ S, (rp S n).eval (k : ℚ) / (Wk S k * ((k : ℚ) - s) ^ 2) =
      if hcl p Nr Dr k = -1 then Lres p Nr Dr R k / ((k : ℚ) - s) else 0 := by
    intro k hk
    have hkR := Finset.mem_of_mem_erase hk
    have hks := Finset.ne_of_mem_erase hk
    have hne : (k : ℚ) - s ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hks)
    rw [← div_div, rp_eval_div_Wk S n hk]
    have hnk : n k = 0 ↔ hcl p Nr Dr k = -1 := by have := hncast k hkR; omega
    by_cases e : hcl p Nr Dr k = -1
    · rw [ite_eq_left (hnk.2 e), ite_eq_left e, Lres, ← Finset.mul_prod_erase (R.erase k) _
        (Finset.mem_erase.2 ⟨Ne.symm hks, hs⟩), Finset.erase_right_comm, hsm]
      push_cast
      rw [zpow_neg_one]
      field_simp
      refine Finset.prod_congr rfl fun t ht => ?_
      rw [hncast t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))]; ring_nf
    · rw [ite_eq_right (mt hnk.1 e), ite_eq_right e, zero_div]
  rw [Finset.sum_congr rfl hL] at hd
  -- right side: `-L_s A_s`
  have hsS : ∀ t ∈ S, (s : ℚ) ≠ t := fun t ht =>
    by exact_mod_cast (Finset.ne_of_mem_erase ht).symm
  have hH : (∏ j ∈ S, (X - C (j : ℚ))) = rp S (fun _ => 1) := by simp [rp]
  have hW : ∏ j ∈ S, ((s : ℚ) - j) = Wk R s := rfl
  have hW0 : Wk R s ≠ 0 := Wk_ne_zero R s
  have hQs : (rp S n).eval (s : ℚ) = Lres p Nr Dr R s * Wk R s := hyp_Qk_eval h hs
  have hHs : (rp S (fun _ => 1)).eval (s : ℚ) = Wk R s := by rw [rp_eval]; simp [Wk, hS]
  rw [hH, rp_deriv_eval S _ _ hsS, rp_deriv_eval S _ _ hsS, hW, hQs, hHs] at hd
  have hA : ∑ t ∈ S, (n t : ℚ) / ((s : ℚ) - t) - ∑ t ∈ S, ((1 : ℕ) : ℚ) / ((s : ℚ) - t) =
      Acoef p Nr Dr R s := by
    rw [Acoef, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    have e1 : ((n t : ℕ) : ℚ) = (hcl p Nr Dr t : ℚ) + 1 := by
      exact_mod_cast hncast t (Finset.mem_of_mem_erase ht)
    rw [e1]; push_cast; ring
  rw [Cres, ite_eq_left hsm, ite_eq_right (by omega), add_zero, minR, Finset.sum_filter,
    ← Finset.sum_erase R (a := s) (by rw [sub_self, div_zero, ite_self]), ← hS, hd, ← hA]
  field_simp
  ring

theorem hyp_Cres (h : TraceHyp p Nr Dr R NU DU) {s : ℤ} (hs : s ∈ R) : Cres p Nr Dr R s = 0 := by
  rcases (show hcl p Nr Dr s = -1 ∨ 0 ≤ hcl p Nr Dr s by have := hyp_hge h hs; omega) with e | e
  · exact hyp_Cres_min h hs e
  · exact hyp_Cres_nonneg h hs e

omit [Fact p.Prime] in
/-- **(RI), second identity**, as `∑_s σ_s C_s`. -/
theorem hyp_RI2 (h : TraceHyp p Nr Dr R NU DU) :
    S2 p Nr Dr R + (sigU NU DU : ℚ) * S1 p Nr Dr R + S4 p Nr Dr R =
      ∑ s ∈ R, (sig p Nr Dr s : ℚ) * Cres p Nr Dr R s := by
  classical
  simp only [Cres, mul_add, Finset.sum_add_distrib]
  have h1 : S2 p Nr Dr R = ∑ s ∈ R, (sig p Nr Dr s : ℚ) *
      ∑ k ∈ minR p Nr Dr R, Lres p Nr Dr R k / ((k : ℚ) - s) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm, S2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Bcoef, Finset.mul_sum, ← Finset.sum_erase R (a := k) (by simp)]
    refine Finset.sum_congr rfl fun s _ => ?_
    push_cast; ring
  have h2 : (sigU NU DU : ℚ) * S1 p Nr Dr R = ∑ s ∈ R, (sig p Nr Dr s : ℚ) *
      (if hcl p Nr Dr s = -1 then Lres p Nr Dr R s * Acoef p Nr Dr R s else 0) := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter, S1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    obtain ⟨hsR, hsm⟩ := Finset.mem_filter.1 hs
    rw [hyp_sig_min h hsR hsm]
  have h3 : S4 p Nr Dr R = ∑ s ∈ R, (sig p Nr Dr s : ℚ) *
      (if hcl p Nr Dr s = 0 then Lres p Nr Dr R s else 0) := by
    simp only [mul_ite, mul_zero]
    rw [← Finset.sum_filter, S4]; rfl
  rw [h1, h2, h3]

end ResidueFacts

section LocalFacts

open TraceAux

variable {p : ℕ} [Fact p.Prime] {Nr Dr : Multiset ℤ} {R : Finset ℤ} {NU DU : Multiset ℤ}

omit [Fact p.Prime] in
theorem hiRoots_add' (k : ℤ) (a b : Multiset ℤ) :
    hiRoots p k (a + b) = hiRoots p k a + hiRoots p k b := by
  simp [hiRoots, Multiset.filter_add, Multiset.map_add]

theorem hyp_disj (h : TraceHyp p Nr Dr R NU DU) (k v : ℤ) :
    (hiRoots p k Nr).count v = 0 ∨ (hiRoots p k Dr).count v = 0 := by
  rw [count_hiRoots, count_hiRoots]
  by_cases hv : k + p * v ∈ Dr
  · left; exact Multiset.count_eq_zero.2 (h.coprime _ hv)
  · right; exact Multiset.count_eq_zero.2 hv

theorem hyp_le_two (h : TraceHyp p Nr Dr R NU DU) (k v : ℤ) : (hiRoots p k Dr).count v ≤ 2 := by
  rw [count_hiRoots]; exact h.pole_le_two _

/-- The Laurent data of one class are `p`-integral (`separated`, `coprime`). -/
theorem hyp_class_int (h : TraceHyp p Nr Dr R NU DU) {k : ℤ} (hk : k ∈ R) (ℓ : ℤ) :
    ValGE p 0 (alC (hiRoots p k Nr) (hiRoots p k Dr) ℓ) ∧
      ValGE p 0 (beC (hiRoots p k Nr) (hiRoots p k Dr) ℓ) := by
  apply alC_int
  · intro hl y hy
    have hne : ℓ ≠ y := by
      rintro rfl
      rw [mem_hiRoots] at hl hy
      exact h.coprime _ hl hy
    exact h.separated k hk ℓ (by rw [hiRoots_add']; exact Multiset.mem_add.2 (Or.inr hl)) y
      (by rw [hiRoots_add']; exact Multiset.mem_add.2 (Or.inl hy)) hne
  · intro hl y hy hyl
    exact h.separated k hk ℓ (by rw [hiRoots_add']; exact Multiset.mem_add.2 (Or.inr hl)) y
      (by rw [hiRoots_add']; exact Multiset.mem_add.2 (Or.inr hy)) (Ne.symm hyl)

/-- There is a minimal class (`∑ h_k = -2`, `h_k ≥ -1`). -/
theorem hyp_exists_min (h : TraceHyp p Nr Dr R NU DU) : ∃ k₀ ∈ R, hcl p Nr Dr k₀ = -1 := by
  by_contra hcon
  push Not at hcon
  have hs := hyp_sum_hcl h
  have : ∀ s ∈ R, 0 ≤ hcl p Nr Dr s := fun s hs' => by
    have := hyp_hge h hs'; have := hcon s hs'; omega
  have := Finset.sum_nonneg this
  omega

theorem vge_p_zpow (n : ℤ) (hn : 0 ≤ n) : ValGE p n ((p : ℚ) ^ n) := by
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  rw [zpow_natCast]; exact vge_p_pow m

end LocalFacts


/-! ### Supporting lemmas -/

/-- **[1] The residue identities (RI).** `∑_{h=-1} L_k = 0` and
`∑_{h=-1} L_k (B_k + σ_* A_k) + ∑_{h=0} σ_k L_k = 0`.
Proof: `F₀ = ∏_{s∈R} (z - s)^{h_s}` is a proper rational function of degree `∑ h_s = |Nr| - |Dr|
= -2` (every root lies in exactly one class), with simple poles exactly at the minimal classes
(`h ≥ -1`), residues `L_k`; and `G = -F₀ ∑_s σ_s/(z - s)` has degree `≤ -3`, residue
`-L_k(B_k + σ_k A_k)` at a minimal class (`σ_k = σ_*` by `minimal`), `-σ_k L_k` at a class with
`h_k = 0`, none elsewhere. The sum of the residues of a rational function of degree `≤ -2`
vanishes (partial fractions + comparison of the `z⁻¹` coefficient at infinity).
* Proved (≈ 230 lines: `hyp_S0`, `Cres`, `hyp_Cres_nonneg`, `hyp_Cres_min`, `hyp_RI2` below; the
  residue sums via Lagrange interpolation, `res_sum_simple` / `res_sum_double` in
  `TraceLemma_Res.lean`). The second identity is proved as `∑_s σ_s C_s = 0`, `C_s` the residue
  sum of `F₀/(z - s)`.
* Directly from the PDF: yes ((RI) of §8, "ordinary residue theorem applied to the proper
  rational functions `F₀` and `∂_P F_P|_{P=0}`"). -/
theorem residue_identities (p : ℕ) [Fact p.Prime] (Nr Dr : Multiset ℤ) (R : Finset ℤ)
    (NU DU : Multiset ℤ) (h : TraceHyp p Nr Dr R NU DU) :
    S0 p Nr Dr R = 0 ∧
      S2 p Nr Dr R + (sigU NU DU : ℚ) * S1 p Nr Dr R + S4 p Nr Dr R = 0 := by
  refine ⟨hyp_S0 h, ?_⟩
  rw [hyp_RI2 h]
  exact Finset.sum_eq_zero fun s hs => by rw [hyp_Cres h hs, mul_zero]

/-- **[2] Unit expansion modulo `p²`.** For an integer `u` prime to `p` and a `p`-integral `v`:
`(u + pv)⁻¹ ≡ u⁻¹(1 - pv/u) (mod p²)`.
Proof: the difference is `p² v² / (u² (u + pv))` and `u + pv` is a `p`-adic unit.
* Proved (≈ 15 lines, in `TraceLemma_Val.lean`: `unit_expansion_gen`).
* Directly from the PDF: partially (the PDF expands in the deformation parameter `P`; this is
  the handoff's direct form at `P = p`). -/
theorem unit_expansion (p : ℕ) [Fact p.Prime] (u : ℤ) (hu : ¬ (p : ℤ) ∣ u) (v : ℚ)
    (hv : ValGE p 0 v) :
    ValGE p 2 (((u : ℚ) + p * v)⁻¹ - (u : ℚ)⁻¹ * (1 - p * v / u)) :=
  TraceAux.unit_expansion_gen (TraceAux.isPU_int hu) hv

/-- **[3] Local expansion of one residue class at the high pole `ℓ`.** There are `p`-integral
`α, β : ℤ → ℚ` (the double- and simple-pole coefficients of the common minimal kernel
`U = ∏_{N_k}(V - ℓ')/∏_{D_k}(V - ℓ')` at `V = ℓ`, zero off its poles) such that for every class
`k ∈ R`, with `a = (pfCoeff Nr Dr (k + pℓ)).1`, `b = (pfCoeff Nr Dr (k + pℓ)).2`, modulo `p²`:
* `h_k = -1`: `a/p ≡ α_ℓ L_k (1 + p(ℓA_k - B_k))`, `b ≡ β_ℓ L_k (1 + p(ℓA_k - B_k)) + p α_ℓ L_k A_k`;
* `h_k = 0`: `a/p ≡ p α_ℓ (ℓ - a_k) L_k`, `b ≡ p L_k (α_ℓ + (ℓ - a_k) β_ℓ)`, `a_k = σ_k - σ_*`;
* `h_k ≥ 1`: `a/p ≡ b ≡ 0`.
Proof: `p F(k + pV) = p^{h_k+1} U_k(V) G_k(V)` with `G_k = ∏_{x' ∉ k}(k - x' + pV)^{±1}`;
`U_k = U` (`minimal`), `U_k = (V - a_k) U` (`affine`, `a_k = σ_k - σ_*` by summing the multiset
identity); `G_k(ℓ) ≡ L_k (1 + p(ℓA_k - B_k))` and `G_k'(ℓ) ≡ p L_k A_k` by [2] (`k - k'` are units
by `complete`); the pole coefficients of `U_k G_k` at `ℓ` are `p`-integral since distinct high
roots of one class differ by units (`separated`), and poles have order `≤ 2` (`pole_le_two`).
* Uses: [2].
* Proved (≈ 600 lines: the proof below and `LocalFacts`, plus `TraceLemma_Loc.lean`
  (`pfCoeff_eq`, `pf_split`, `eq_of_rel`, `alC_aff`, `rest_FO`, `rest_lsum`) and the first-order
  calculus `FO` of `TraceLemma_Val.lean`). `α, β` are the Laurent data `alC, beC` of a fixed
  minimal class `k₀` (one exists since `∑ h_k = -2`).
* Directly from the PDF: partially (§8: "`P F_P(k + PV) = L_k U(V){1 + P(VA_k - B_k)} + O(P²)`";
  the PDF works with the deformation parameter, here at `P = p` with `p`-adic remainders). -/
theorem local_expansion (p : ℕ) [Fact p.Prime] (Nr Dr : Multiset ℤ) (R : Finset ℤ)
    (NU DU : Multiset ℤ) (h : TraceHyp p Nr Dr R NU DU) :
    ∃ α β : ℤ → ℚ, (∀ ℓ, ValGE p 0 (α ℓ) ∧ ValGE p 0 (β ℓ)) ∧ ∀ k ∈ R, ∀ ℓ : ℤ,
      (hcl p Nr Dr k = -1 →
        ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).1 / p -
          α ℓ * Lres p Nr Dr R k * (1 + p * (ℓ * Acoef p Nr Dr R k - Bcoef p Nr Dr R k))) ∧
        ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).2 -
          (β ℓ * Lres p Nr Dr R k * (1 + p * (ℓ * Acoef p Nr Dr R k - Bcoef p Nr Dr R k)) +
            p * α ℓ * Lres p Nr Dr R k * Acoef p Nr Dr R k))) ∧
      (hcl p Nr Dr k = 0 →
        ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).1 / p -
          p * α ℓ * (ℓ - ((sig p Nr Dr k : ℚ) - sigU NU DU)) * Lres p Nr Dr R k) ∧
        ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).2 -
          p * Lres p Nr Dr R k * (α ℓ + (ℓ - ((sig p Nr Dr k : ℚ) - sigU NU DU)) * β ℓ))) ∧
      (1 ≤ hcl p Nr Dr k →
        ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).1 / p) ∧
        ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).2)) := by
  classical
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨k₀, hk₀, hk₀m⟩ := hyp_exists_min h
  have hc₀ : (hiRoots p k₀ Dr).card = (hiRoots p k₀ Nr).card + 1 := by unfold hcl at hk₀m; omega
  have hmin₀ := h.minimal k₀ hk₀ hc₀
  refine ⟨fun ℓ => TraceAux.alC (hiRoots p k₀ Nr) (hiRoots p k₀ Dr) ℓ,
    fun ℓ => TraceAux.beC (hiRoots p k₀ Nr) (hiRoots p k₀ Dr) ℓ,
    fun ℓ => hyp_class_int h hk₀ ℓ, ?_⟩
  intro k hk ℓ
  have hpf := TraceAux.pfCoeff_eq Nr Dr (k + p * ℓ) (h.coprime _)
  obtain ⟨hs1, hs2⟩ := TraceAux.pf_split p hp0 k ℓ (hiRoots p k Nr) (hiRoots p k Dr)
    (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k)
    (TraceAux.not_mem_rest p k ℓ Dr)
  rw [← TraceAux.decomp_class p k Nr, ← TraceAux.decomp_class p k Dr] at hs1 hs2
  have hh : ((Multiset.card (hiRoots p k Nr) : ℤ) - Multiset.card (hiRoots p k Dr)) =
      hcl p Nr Dr k := rfl
  rw [hh] at hs1 hs2
  rw [hpf]
  dsimp only
  rw [hs1, hs2]
  -- the other classes
  set g := TraceAux.vprod (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) ((k + p * ℓ : ℤ) : ℚ) /
    TraceAux.vprod (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) ((k + p * ℓ : ℤ) : ℚ) with hg_def
  set μ := TraceAux.lsum (Nr.filter fun y => ¬ (p : ℤ) ∣ y - k) ((k + p * ℓ : ℤ) : ℚ) -
    TraceAux.lsum (Dr.filter fun y => ¬ (p : ℤ) ∣ y - k) ((k + p * ℓ : ℤ) : ℚ) with hμ_def
  set L := Lres p Nr Dr R k with hL_def
  set A := Acoef p Nr Dr R k with hA_def
  set t := (ℓ : ℚ) * A - Bcoef p Nr Dr R k with ht_def
  have hg : TraceAux.FO p g L t := by
    refine (TraceAux.rest_FO h.complete hk ℓ Nr Dr).congr rfl ?_
    rw [ht_def, hA_def, Acoef, Bcoef, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hcl, sig]; push_cast; ring
  have hμ : ValGE p 1 (μ - A) := by
    have := TraceAux.rest_lsum h.complete hk ℓ Nr Dr
    convert this using 2
    rw [hA_def, Acoef]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hcl]; push_cast; ring
  have hLu : TraceAux.IsPU p L := hyp_L_unit h hk
  have hAI : ValGE p 0 A := hyp_A_int h hk
  have hgI := hg.int
  have hg1 : ValGE p 1 (g - L) := hg.cong1
  have hgt : ValGE p 2 (g - L * (1 + p * t)) := hg.2.2
  have hμI : ValGE p 0 μ := by
    have := TraceAux.vge_add (TraceAux.vge_mono hμ (by norm_num)) hAI
    rwa [sub_add_cancel] at this
  have hpμ : ValGE p 1 (p * μ) := by simpa using TraceAux.vge_p_mul hμI
  have hgpμ : ValGE p 2 (g * (p * μ) - p * L * A) := by
    have e : g * (p * μ) - p * L * A = (g - L) * (p * μ) + L * (p * (μ - A)) := by ring
    rw [e]
    exact TraceAux.vge_add (TraceAux.vge_mul' hg1 hpμ (by norm_num))
      (TraceAux.vge_mul' hLu.vge (TraceAux.vge_p_mul hμ) (by norm_num))
  obtain ⟨hαk, hβk⟩ := hyp_class_int h hk ℓ
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · -- a minimal class: the same kernel `U`
    rw [e]
    have hc : (hiRoots p k Dr).card = (hiRoots p k Nr).card + 1 := by unfold hcl at e; omega
    have hmin := h.minimal k hk hc
    have hrel : hiRoots p k Nr + hiRoots p k₀ Dr = hiRoots p k₀ Nr + hiRoots p k Dr := by
      ext v
      have h1 := congrArg (Multiset.count v) hmin
      have h2 := congrArg (Multiset.count v) hmin₀
      simp only [Multiset.count_add] at h1 h2 ⊢; omega
    obtain ⟨eN, eD⟩ := TraceAux.eq_of_rel hrel (hyp_disj h k) (hyp_disj h k₀)
    rw [eN, eD]
    obtain ⟨hαI, hβI⟩ := hyp_class_int h hk₀ ℓ
    set α := TraceAux.alC (hiRoots p k₀ Nr) (hiRoots p k₀ Dr) ℓ
    set β := TraceAux.beC (hiRoots p k₀ Nr) (hiRoots p k₀ Dr) ℓ
    constructor
    · have e1 : (p : ℚ) ^ ((-1 : ℤ) + 2) * α * g / p - α * L * (1 + p * t) =
          α * (g - L * (1 + p * t)) := by
        rw [show ((-1 : ℤ) + 2) = 1 by norm_num, zpow_one]; field_simp
      rw [e1]; exact TraceAux.vge_mul' hαI hgt (by norm_num)
    · have e2 : (p : ℚ) ^ ((-1 : ℤ) + 1) * (β * g + α * g * (p * μ)) -
          (β * L * (1 + p * t) + p * α * L * A) =
          β * (g - L * (1 + p * t)) + α * (g * (p * μ) - p * L * A) := by
        rw [show ((-1 : ℤ) + 1) = 0 by norm_num, zpow_zero]; ring
      rw [e2]
      exact TraceAux.vge_add (TraceAux.vge_mul' hβI hgt (by norm_num))
        (TraceAux.vge_mul' hαI hgpμ (by norm_num))
  · -- a class with `h_k = 0`: `U_k = (V - a) U`
    rw [e]
    have hc : (hiRoots p k Dr).card = (hiRoots p k Nr).card := by unfold hcl at e; omega
    obtain ⟨a, haff⟩ := h.affine k hk hc
    have hrel : hiRoots p k Nr + hiRoots p k₀ Dr = (a ::ₘ hiRoots p k₀ Nr) + hiRoots p k Dr := by
      ext v
      have h1 := congrArg (Multiset.count v) haff
      have h2 := congrArg (Multiset.count v) hmin₀
      simp only [Multiset.count_add, Multiset.count_cons] at h1 h2 ⊢; omega
    obtain ⟨hal, hbe⟩ := TraceAux.alC_aff hrel (hyp_disj h k) (hyp_disj h k₀) (hyp_le_two h k₀) ℓ
    have ha : (a : ℚ) = (sig p Nr Dr k : ℚ) - sigU NU DU := by
      have := congrArg Multiset.sum haff
      simp only [Multiset.sum_add, Multiset.sum_cons] at this
      have : a = sig p Nr Dr k - sigU NU DU := by unfold sig sigU; linarith
      rw [this]; push_cast; ring
    rw [hal, hbe, ← ha]
    obtain ⟨hαI, hβI⟩ := hyp_class_int h hk₀ ℓ
    set α := TraceAux.alC (hiRoots p k₀ Nr) (hiRoots p k₀ Dr) ℓ
    set β := TraceAux.beC (hiRoots p k₀ Nr) (hiRoots p k₀ Dr) ℓ
    have hla : ValGE p 0 ((ℓ : ℚ) - a) := by exact_mod_cast TraceAux.vge_int (p := p) (ℓ - a)
    constructor
    · have e1 : (p : ℚ) ^ ((0 : ℤ) + 2) * (((ℓ : ℚ) - a) * α) * g / p -
          p * α * ((ℓ : ℚ) - a) * L = p * ((((ℓ : ℚ) - a) * α) * (g - L)) := by
        rw [show ((0 : ℤ) + 2) = 2 by norm_num, zpow_two]; field_simp
      rw [e1]
      simpa using TraceAux.vge_p_mul (TraceAux.vge_mul (TraceAux.vge_mul hla hαI) hg1)
    · have e2 : (p : ℚ) ^ ((0 : ℤ) + 1) * ((α + ((ℓ : ℚ) - a) * β) * g +
          ((ℓ : ℚ) - a) * α * g * (p * μ)) - p * L * (α + ((ℓ : ℚ) - a) * β) =
          p * ((α + ((ℓ : ℚ) - a) * β) * (g - L)) + p * ((((ℓ : ℚ) - a) * α * g) * (p * μ)) := by
        rw [show ((0 : ℤ) + 1) = 1 by norm_num, zpow_one]; ring
      rw [e2]
      have hb : ValGE p 0 (α + ((ℓ : ℚ) - a) * β) :=
        TraceAux.vge_add hαI (by simpa using TraceAux.vge_mul hla hβI)
      refine TraceAux.vge_add ?_ ?_
      · simpa using TraceAux.vge_p_mul (TraceAux.vge_mul hb hg1)
      · simpa using TraceAux.vge_p_mul
          (TraceAux.vge_mul (TraceAux.vge_mul (TraceAux.vge_mul hla hαI) hgI) hpμ)
  · -- a class with `h_k ≥ 1`: already divisible by `p²`
    have e1 : (p : ℚ) ^ (hcl p Nr Dr k + 2) *
        TraceAux.alC (hiRoots p k Nr) (hiRoots p k Dr) ℓ * g / p =
        (p : ℚ) ^ (hcl p Nr Dr k + 1) * (TraceAux.alC (hiRoots p k Nr) (hiRoots p k Dr) ℓ * g) := by
      rw [show hcl p Nr Dr k + 2 = (hcl p Nr Dr k + 1) + 1 by ring, zpow_add_one₀ hp0]
      field_simp
    have hpz := vge_p_zpow (p := p) (hcl p Nr Dr k + 1) (by omega)
    constructor
    · rw [e1]
      exact TraceAux.vge_mul' hpz (by simpa using TraceAux.vge_mul hαk hgI) (by omega)
    · refine TraceAux.vge_mul' hpz (TraceAux.vge_add (by simpa using TraceAux.vge_mul hβk hgI)
        (TraceAux.vge_mono (by simpa using TraceAux.vge_mul (TraceAux.vge_mul hαk hgI) hpμ)
          (by norm_num))) (by omega)

/-- **[4] The degree of `Q̃`.** `deg Q̃ = ∑_{s∈R} (h_s + 1) = p + |Nr| - |Dr| = p - 2`.
Proof: `h_s ≥ -1` (`h_ge`) makes the `toNat` exact; `|R| = p` and every root lies in exactly one
class (`complete`), so `∑_s h_s = |Nr| - |Dr| = -2` (`deg`).
* Proved (≈ 25 lines, with `card_hiRoots_sum`, `card_R` of `TraceLemma_Cls.lean`).
* Directly from the PDF: yes ("`deg Q̃ = p - 2`"). -/
theorem Qt_natDegree (p : ℕ) [Fact p.Prime] (Nr Dr : Multiset ℤ) (R : Finset ℤ)
    (NU DU : Multiset ℤ) (h : TraceHyp p Nr Dr R NU DU) :
    (Qt p Nr Dr R).natDegree ≤ p - 2 := by
  have hcard := TraceAux.card_R h.complete
  have hsum := hyp_sum_hcl h
  rw [Qt, natDegree_prod_of_monic _ _ (fun s _ => (monic_X_sub_C _).pow _)]
  simp only [natDegree_pow, natDegree_X_sub_C, mul_one]
  have : ((∑ s ∈ R, (hcl p Nr Dr s + 1).toNat : ℕ) : ℤ) = p - 2 := by
    push_cast
    rw [Finset.sum_congr rfl (fun s hs => Int.toNat_of_nonneg (by have := hyp_hge h hs; omega)),
      Finset.sum_add_distrib, hsum]
    simp [hcard]; ring
  omega

/-- **[5] The class terms of `D` modulo `p`.** For every `k ∈ R`: `D_k ≡ -Q̃'(k) (mod p)`, where
`D_k = L_kA_k` on a minimal class, `L_k` on a class with `h_k = 0`, `0` otherwise.
Proof: `F₀ = Q̃/H`, `H = (z - k) H_k`; at a minimal class the constant Laurent term is
`L_kA_k = (Q̃/H_k)'(k) = Q̃'(k)/H_k(k) - Q̃(k) H_k'(k)/H_k(k)²`; at `h_k = 0`,
`L_k = Q̃'(k)/H_k(k)`; for `h_k ≥ 1`, `Q̃'(k) = 0`. Since `R` is complete,
`H ≡ z^p - z (mod p)`, so `H_k(k) = H'(k) ≡ -1` and `H_k'(k) = H''(k)/2 ≡ 0` (`p` odd).
* Proved (≈ 55 lines; Wilson `wilson_R` and `∑_{s≠k} 1/(k-s) ≡ 0` (`inv_sum_R`, via Fermat and
  [6]) in `TraceLemma_Cls.lean`, the logarithmic derivative `rp_deriv_eval` in `TraceLemma_Res`).
* Directly from the PDF: yes (§8, "At a minimal class, `L_kA_k ≡ -Q̃'(k)`; at a class with
  `h_k = 0`, `L_k ≡ -Q̃'(k)`; and at every other class this polynomial derivative vanishes"). -/
theorem D_terms_congr (p : ℕ) [Fact p.Prime] (Nr Dr : Multiset ℤ) (R : Finset ℤ)
    (NU DU : Multiset ℤ) (h : TraceHyp p Nr Dr R NU DU) :
    ∀ k ∈ R, ValGE p 1 (dTerm p Nr Dr R k + (((derivative (Qt p Nr Dr R)).eval k : ℤ) : ℚ)) := by
  intro k hk
  classical
  set n : ℤ → ℕ := fun t => (hcl p Nr Dr t + 1).toNat with hn
  have hQ : (((derivative (Qt p Nr Dr R)).eval k : ℤ) : ℚ) =
      (derivative (TraceAux.rp R n)).eval (k : ℚ) := by
    rw [hn, ← Qt_map, derivative_map, eval_intCast_map]; rfl
  rw [hQ]
  have hsplit : TraceAux.rp R n = (X - C (k : ℚ)) ^ (n k) * TraceAux.rp (R.erase k) n := by
    rw [TraceAux.rp, TraceAux.rp]
    exact (Finset.mul_prod_erase R (fun s => (X - C (s : ℚ)) ^ (n s)) hk).symm
  have hnot : ∀ t ∈ R.erase k, (k : ℚ) ≠ t := fun t ht => by
    have := hyp_sub_ne h hk (mem_of_mem_erase ht) (ne_of_mem_erase ht).symm
    push_cast at this; exact sub_ne_zero.1 this
  have hQk := hyp_Qk_eval h hk
  have hder : (derivative (TraceAux.rp R n)).eval (k : ℚ) =
      (n k : ℚ) * (0 : ℚ) ^ (n k - 1) * (TraceAux.rp (R.erase k) n).eval (k : ℚ) +
        (0 : ℚ) ^ (n k) * (derivative (TraceAux.rp (R.erase k) n)).eval (k : ℚ) := by
    rw [hsplit, derivative_mul, derivative_X_sub_C_pow]
    simp
  have hL := hyp_L_unit h hk
  have hA := hyp_A_int h hk
  have hW : (p : ℤ) ∣ (∏ s ∈ R.erase k, (k - s)) + 1 := TraceAux.wilson_R h.complete hk
  obtain ⟨w, hw⟩ := hW
  have hWq : TraceAux.Wk R k + 1 = (p : ℚ) * w := by
    rw [TraceAux.Wk]; exact_mod_cast hw
  have hWint : ValGE p 0 (TraceAux.Wk R k) := by
    rw [TraceAux.Wk]; exact_mod_cast TraceAux.vge_int (p := p) (∏ s ∈ R.erase k, (k - s))
  have hW1 : ValGE p 1 (TraceAux.Wk R k + 1) := by
    rw [hWq]; simpa using TraceAux.vge_p_mul (TraceAux.vge_int (p := p) w)
  have hge := hyp_hge h hk
  rcases (show hcl p Nr Dr k = -1 ∨ hcl p Nr Dr k = 0 ∨ 1 ≤ hcl p Nr Dr k by omega) with e | e | e
  · -- minimal class: `L A + L W (A + E) = L A (W + 1) + L W E`
    have hnk : n k = 0 := by simp [hn, e]
    have hdk : dTerm p Nr Dr R k = Lres p Nr Dr R k * Acoef p Nr Dr R k := by
      simp [dTerm, e]
    have hsumn : ∑ t ∈ R.erase k, (n t : ℚ) / ((k : ℚ) - t) =
        Acoef p Nr Dr R k + ∑ t ∈ R.erase k, (((k - t : ℤ)) : ℚ)⁻¹ := by
      rw [Acoef, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t ht => ?_
      have e1 : ((n t : ℕ) : ℤ) = hcl p Nr Dr t + 1 :=
        Int.toNat_of_nonneg (by have := hyp_hge h (mem_of_mem_erase ht); omega)
      have e2 : ((n t : ℕ) : ℚ) = (hcl p Nr Dr t : ℚ) + 1 := by exact_mod_cast e1
      rw [e2]; push_cast; rw [add_div, one_div]
    rw [hder, hnk, hdk, TraceAux.rp_deriv_eval _ _ _ hnot, hQk, hsumn]
    simp only [CharP.cast_eq_zero, zero_mul, pow_zero, one_mul, zero_add]
    have hE := TraceAux.inv_sum_R h.complete h.odd hk
    have e3 : Lres p Nr Dr R k * Acoef p Nr Dr R k + Lres p Nr Dr R k * TraceAux.Wk R k *
        (Acoef p Nr Dr R k + ∑ t ∈ R.erase k, (((k - t : ℤ)) : ℚ)⁻¹) =
        (Lres p Nr Dr R k * Acoef p Nr Dr R k) * (TraceAux.Wk R k + 1) +
          (Lres p Nr Dr R k * TraceAux.Wk R k) * ∑ t ∈ R.erase k, (((k - t : ℤ)) : ℚ)⁻¹ := by
      ring
    rw [e3]
    exact TraceAux.vge_add (by simpa using TraceAux.vge_mul (TraceAux.vge_mul hL.vge hA) hW1)
      (by simpa using TraceAux.vge_mul (TraceAux.vge_mul hL.vge hWint) hE)
  · have hnk : n k = 1 := by simp [hn, e]
    have hdk : dTerm p Nr Dr R k = Lres p Nr Dr R k := by simp [dTerm, e]
    rw [hder, hnk, hdk, hQk]
    simp only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero, pow_one, zero_mul, add_zero]
    have e3 : Lres p Nr Dr R k + Lres p Nr Dr R k * TraceAux.Wk R k =
        Lres p Nr Dr R k * (TraceAux.Wk R k + 1) := by ring
    rw [e3]
    simpa using TraceAux.vge_mul hL.vge hW1
  · have hnk : 2 ≤ n k := by simp only [hn]; omega
    have hdk : dTerm p Nr Dr R k = 0 := by
      simp [dTerm, show hcl p Nr Dr k ≠ -1 by omega, show hcl p Nr Dr k ≠ 0 by omega]
    rw [hder, hdk, zero_pow (by omega), zero_pow (by omega)]
    simp [TraceAux.vge_zero]

/-- **[6] Complete residue sums vanish.** If `R` is a complete system of representatives modulo
`p` and `deg T ≤ p - 2`, then `p ∣ ∑_{k∈R} T(k)` (`∑_{x ∈ 𝔽_p} x^i = 0` for `i < p - 1`).
* Proved (≈ 40 lines, in `TraceLemma_Cls.lean`: `sum_R_zmod`, `complete_sum_dvd_gen`).
* Directly from the PDF: yes ("since `deg Q̃' = p - 3 < p - 1`"). -/
theorem complete_sum_dvd (p : ℕ) [Fact p.Prime] (R : Finset ℤ)
    (hR : ∀ x : ℤ, ∃! k, k ∈ R ∧ (p : ℤ) ∣ x - k) (T : ℤ[X]) (hT : T.natDegree ≤ p - 2) :
    (p : ℤ) ∣ ∑ k ∈ R, T.eval k :=
  TraceAux.complete_sum_dvd_gen hR T hT

/-! ### The node -/

/-- **Second-order trace lemma** (T2) (statement verbatim from `Blueprint_5255.lean`), proved
from [1], [3], [4], [5], [6]. -/
theorem trace_lemma (p : ℕ) [Fact p.Prime] (Nr Dr : Multiset ℤ) (R : Finset ℤ)
    (NU DU : Multiset ℤ) (h : TraceHyp p Nr Dr R NU DU) (ℓ : ℤ) :
    ValGE p 3 (highPoleA p Nr Dr R ℓ) ∧ ValGE p 2 (highPoleB p Nr Dr R ℓ) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  obtain ⟨hS0, hRI⟩ := residue_identities p Nr Dr R NU DU h
  obtain ⟨α, β, hαβ, hloc⟩ := local_expansion p Nr Dr R NU DU h
  -- `D = S₁ + S₃ ≡ 0 (mod p)`
  have hD : ValGE p 1 (S1 p Nr Dr R + S3 p Nr Dr R) := by
    have hdeg : (derivative (Qt p Nr Dr R)).natDegree ≤ p - 2 :=
      (natDegree_derivative_le _).trans (by have := Qt_natDegree p Nr Dr R NU DU h; omega)
    obtain ⟨w, hw⟩ := complete_sum_dvd p R h.complete _ hdeg
    have hw' : ∑ k ∈ R, (((derivative (Qt p Nr Dr R)).eval k : ℤ) : ℚ) = (p : ℚ) * w := by
      exact_mod_cast hw
    have hsum := valGE_sum R 1 _ (D_terms_congr p Nr Dr R NU DU h)
    rw [Finset.sum_add_distrib, hw'] at hsum
    have e : ∑ k ∈ R, dTerm p Nr Dr R k = S1 p Nr Dr R + S3 p Nr Dr R := by
      simp only [dTerm]
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      rfl
    rw [e] at hsum
    have hpw : ValGE p 1 ((p : ℚ) * w) := by
      have := valGE_mul (valGE_p (p := p)) (valGE_int (p := p) w); simpa using this
    have := valGE_sub hsum hpw
    rwa [add_sub_cancel_right] at this
  -- reindex the high-pole sums over the representatives
  have hre : ∀ g : ℤ → ℚ, (∀ x, x ∉ Dr → g x = 0) →
      ∑ x ∈ Dr.toFinset.filter (fun x => x - p * ℓ ∈ R), g x = ∑ k ∈ R, g (k + p * ℓ) := by
    intro g hg
    rw [← Finset.sum_image (s := R) (g := fun k => k + p * ℓ) (f := g)
      (fun x _ y _ hxy => by simpa using hxy)]
    refine Finset.sum_subset (fun x hx => ?_) (fun x hx hx' => hg x ?_)
    · simp only [Finset.mem_filter] at hx
      exact Finset.mem_image.2 ⟨x - p * ℓ, hx.2, by ring⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      intro hmem
      exact hx' (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hmem, by simpa using hk⟩)
  have hzero : ∀ x, x ∉ Dr → pfCoeff Nr Dr x = (0, 0) := by
    intro x hx
    have hc : Dr.count x = 0 := Multiset.count_eq_zero.2 hx
    simp [pfCoeff, hc]
  have hA : highPoleA p Nr Dr R ℓ = ∑ k ∈ R, (pfCoeff Nr Dr (k + p * ℓ)).1 :=
    hre (fun x => (pfCoeff Nr Dr x).1) fun x hx => by simp [hzero x hx]
  have hB : highPoleB p Nr Dr R ℓ = ∑ k ∈ R, (pfCoeff Nr Dr (k + p * ℓ)).2 :=
    hre (fun x => (pfCoeff Nr Dr x).2) fun x hx => by simp [hzero x hx]
  -- every class has `h_k ≥ -1`
  have hge : ∀ k ∈ R, hcl p Nr Dr k = -1 ∨ hcl p Nr Dr k = 0 ∨ 1 ≤ hcl p Nr Dr k := by
    intro k hk
    have := h.h_ge k hk
    unfold hcl
    omega
  -- class by class, modulo `p²`
  have hclA : ∀ k ∈ R, ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).1 / p -
      mainA p Nr Dr R NU DU α ℓ k) := by
    intro k hk
    obtain ⟨hm, hz, hh⟩ := hloc k hk ℓ
    rcases hge k hk with e | e | e
    · rw [mainA, ite_eq_left e, ite_eq_right (by rw [e]; norm_num), add_zero]; exact (hm e).1
    · rw [mainA, ite_eq_right (by rw [e]; norm_num), ite_eq_left e, zero_add]; exact (hz e).1
    · rw [mainA, ite_eq_right (by omega), ite_eq_right (by omega), add_zero, sub_zero]; exact (hh e).1
  have hclB : ∀ k ∈ R, ValGE p 2 ((pfCoeff Nr Dr (k + p * ℓ)).2 -
      mainB p Nr Dr R NU DU α β ℓ k) := by
    intro k hk
    obtain ⟨hm, hz, hh⟩ := hloc k hk ℓ
    rcases hge k hk with e | e | e
    · rw [mainB, ite_eq_left e, ite_eq_right (by rw [e]; norm_num), add_zero]; exact (hm e).2
    · rw [mainB, ite_eq_right (by rw [e]; norm_num), ite_eq_left e, zero_add]; exact (hz e).2
    · rw [mainB, ite_eq_right (by omega), ite_eq_right (by omega), add_zero, sub_zero]; exact (hh e).2
  -- the summed predictions, in terms of `S₀, …, S₄`
  set σ : ℚ := (sigU NU DU : ℚ) with hσ
  have hMA : ∑ k ∈ R, mainA p Nr Dr R NU DU α ℓ k =
      α ℓ * S0 p Nr Dr R + (p * α ℓ * ℓ) * S1 p Nr Dr R - (p * α ℓ) * S2 p Nr Dr R +
        ((p * α ℓ * ℓ + p * α ℓ * σ) * S3 p Nr Dr R - (p * α ℓ) * S4 p Nr Dr R) := by
    simp only [mainA]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    · simp only [S0, S1, S2, minR]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [S3, S4, zeroR]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hσ]; ring
  have hMB : ∑ k ∈ R, mainB p Nr Dr R NU DU α β ℓ k =
      β ℓ * S0 p Nr Dr R + (p * β ℓ * ℓ) * S1 p Nr Dr R - (p * β ℓ) * S2 p Nr Dr R +
        (p * α ℓ) * S1 p Nr Dr R +
        ((p * α ℓ + p * β ℓ * ℓ + p * β ℓ * σ) * S3 p Nr Dr R - (p * β ℓ) * S4 p Nr Dr R) := by
    simp only [mainB]
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    · simp only [S0, S1, S2, minR]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [S3, S4, zeroR]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hσ]; ring
  -- (RI) collapses the predictions to multiples of `p D`
  have hMA' : ∑ k ∈ R, mainA p Nr Dr R NU DU α ℓ k =
      (p : ℚ) * (α ℓ * (((ℓ + sigU NU DU : ℤ) : ℚ) * (S1 p Nr Dr R + S3 p Nr Dr R))) := by
    rw [hMA]; push_cast
    linear_combination α ℓ * hS0 - (p * α ℓ) * hRI
  have hMB' : ∑ k ∈ R, mainB p Nr Dr R NU DU α β ℓ k =
      (p : ℚ) * ((α ℓ + β ℓ * ((ℓ + sigU NU DU : ℤ) : ℚ)) * (S1 p Nr Dr R + S3 p Nr Dr R)) := by
    rw [hMB]; push_cast
    linear_combination β ℓ * hS0 - (p * β ℓ) * hRI
  -- `p`-adic bookkeeping
  have hαv := fun ℓ => (hαβ ℓ).1
  have hβv := fun ℓ => (hαβ ℓ).2
  have hMAv : ValGE p 2 (∑ k ∈ R, mainA p Nr Dr R NU DU α ℓ k) := by
    rw [hMA']
    have := valGE_mul (valGE_p (p := p))
      (valGE_mul (hαv ℓ) (valGE_mul (valGE_int (p := p) (ℓ + sigU NU DU)) hD))
    simpa using this
  have hMBv : ValGE p 2 (∑ k ∈ R, mainB p Nr Dr R NU DU α β ℓ k) := by
    rw [hMB']
    have := valGE_mul (valGE_p (p := p))
      (valGE_mul (valGE_add (hαv ℓ)
        (by simpa using valGE_mul (hβv ℓ) (valGE_int (p := p) (ℓ + sigU NU DU)))) hD)
    simpa using this
  constructor
  · -- `A_ℓ/p ≡ ∑ mainA ≡ 0 (mod p²)`, hence `A_ℓ ∈ p³ ℤ_(p)`
    have h1 : ValGE p 2 (highPoleA p Nr Dr R ℓ / p - ∑ k ∈ R, mainA p Nr Dr R NU DU α ℓ k) := by
      rw [hA, Finset.sum_div, ← Finset.sum_sub_distrib]
      exact valGE_sum _ _ _ hclA
    have h2 := valGE_add h1 hMAv
    rw [sub_add_cancel] at h2
    have e : highPoleA p Nr Dr R ℓ = highPoleA p Nr Dr R ℓ / p * p := by field_simp
    rw [e]
    have := valGE_mul h2 (valGE_p (p := p))
    simpa using this
  · have h1 : ValGE p 2 (highPoleB p Nr Dr R ℓ - ∑ k ∈ R, mainB p Nr Dr R NU DU α β ℓ k) := by
      rw [hB, ← Finset.sum_sub_distrib]
      exact valGE_sum _ _ _ hclB
    have h2 := valGE_add h1 hMBv
    rwa [sub_add_cancel] at h2

end Meijer5255.TraceLemma
