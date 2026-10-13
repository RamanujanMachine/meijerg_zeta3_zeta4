/-
# Auxiliary lemmas for `Meijer5255.CmfReadout`: kernels, the polynomial `D_w`, one CMF step

Generic facts used by the node file `CmfReadout.lean` (imported only there):

* `gker a b = ∏ᵢ Γ(t + bᵢ)/Γ(t + aᵢ)` with the identity pairing `(bᵢ, aᵢ)`, as a product of the
  zeta34 `pairKer`s, its zeros/poles `kZ`, `kP` (`gker_eq_lin`), the boundary factor
  `Bp b = ∏ⱼ (t + bⱼ)` (`Bp_mul_lin`), and the functional equation
  `Ap a · gker = (Bp b · gker)(t - 1)` (`Ap_mul_gker`);
* the one-step relations of `gker` along the four kinds of moves;
* `Vertex.D`: degree `< 5`, `D(-t) = ∏ⱼ (t + bⱼ) - ∏ᵢ (t + aᵢ - 1)`, `d₄ = 5 - ∑a + ∑b`, the
  value `D(c)`, and `det (c I - θ) = D(c)/d₄`;
* `mm_step`: one forward CMF step for a moment matrix (zeta34 `step_fwd`, `CMF_transport.lean`,
  restated for `Fin 3 → ℚ`-valued functionals and the native companion matrix `Vertex.theta`).

Provenance: `pairKer`, `lin`, `ival` and their lemmas are the zeta34 ones
(`QGrowth_CMF_basic.lean`, a copy of `../zetas_irr/blueprints/CMF_basic.lean`); the proofs
of `Bp_mul_lin`, `gker` relations and `mm_step` adapt `lin_bro`, `ker_lower_a`, `ker_raise_b`,
`ker_laurent`, `step_fwd`, `det_Amat` of `../zetas_irr/blueprints/CMF_transport.lean` /
`CMF_basic.lean`.
-/
import Meijer5255.definitions
import Meijer5255.QGrowth_CMF_basic

open Polynomial Finset
open scoped RatFunc Matrix

noncomputable section

namespace Meijer5255.CmfReadout

open Meijer5255
open Meijer5255.QGA.ZetasIrr.CMF (lin lp ival pairKer pairKer_lower pairKer_raise pairKer_laurent lin_add
  lin_cons_left)

/-! ### The kernel with the identity pairing -/

/-- `∏ᵢ Γ(t + bᵢ)/Γ(t + aᵢ)` (pairs `(bᵢ, aᵢ)`). -/
def gker (a b : Fin 5 → ℤ) : RatFunc ℚ :=
  pairKer (b 0) (a 0) * pairKer (b 1) (a 1) * pairKer (b 2) (a 2) * pairKer (b 3) (a 3) *
    pairKer (b 4) (a 4)

/-- The zeros of `gker a b` (before cancellation): `{1 - bᵢ, …, -aᵢ}` for `aᵢ < bᵢ`. -/
def kZ (a b : Fin 5 → ℤ) : Multiset ℤ :=
  ival (1 - b 0) (b 0 - a 0).toNat + ival (1 - b 1) (b 1 - a 1).toNat +
    ival (1 - b 2) (b 2 - a 2).toNat + ival (1 - b 3) (b 3 - a 3).toNat +
    ival (1 - b 4) (b 4 - a 4).toNat

/-- The poles of `gker a b` (before cancellation): `{1 - aᵢ, …, -bᵢ}` for `bᵢ < aᵢ`. -/
def kP (a b : Fin 5 → ℤ) : Multiset ℤ :=
  ival (1 - a 0) (a 0 - b 0).toNat + ival (1 - a 1) (a 1 - b 1).toNat +
    ival (1 - a 2) (a 2 - b 2).toNat + ival (1 - a 3) (a 3 - b 3).toNat +
    ival (1 - a 4) (a 4 - b 4).toNat

theorem gker_eq_lin (a b : Fin 5 → ℤ) : gker a b = lin (kZ a b) (kP a b) := by
  simp only [gker, pairKer, kZ, kP, lin_add]

/-- The roots `-bⱼ` of `∏ⱼ (t + bⱼ)`. -/
def bro (b : Fin 5 → ℤ) : Multiset ℤ := {-b 0, -b 1, -b 2, -b 3, -b 4}

/-- `X - z` in `ℚ(X)` for an integer `z`. -/
def lf (z : ℤ) : RatFunc ℚ := RatFunc.X - RatFunc.C (z : ℚ)

/-- `∏ⱼ (t + bⱼ)`. -/
def Bp (b : Fin 5 → ℤ) : RatFunc ℚ := lf (-b 0) * lf (-b 1) * lf (-b 2) * lf (-b 3) * lf (-b 4)

/-- `∏ᵢ (t + aᵢ - 1)`. -/
def Ap (a : Fin 5 → ℤ) : RatFunc ℚ :=
  lf (1 - a 0) * lf (1 - a 1) * lf (1 - a 2) * lf (1 - a 3) * lf (1 - a 4)

theorem Bp_mul_lin (b : Fin 5 → ℤ) (Z P : Multiset ℤ) : Bp b * lin Z P = lin (bro b + Z) P := by
  simp only [bro, Bp, lf, Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
    lin_cons_left]
  ring

theorem lf_laurent (c : ℤ) : RatFunc.laurent (-1 : ℚ) (lf (-c)) = lf (1 - c) := by
  simp only [lf, map_sub, RatFunc.laurent_X, RatFunc.laurent_C, Int.cast_neg, Int.cast_sub,
    Int.cast_one, map_neg, map_one]
  ring

/-- The functional equation `∏ᵢ (t + aᵢ - 1) · r(t) = (∏ⱼ (t + bⱼ) r)(t - 1)`. -/
theorem Ap_mul_gker (a b : Fin 5 → ℤ) :
    Ap a * gker a b = RatFunc.laurent (-1 : ℚ) (Bp b * gker a b) := by
  have h0 := pairKer_laurent (b 0) (a 0)
  have h1 := pairKer_laurent (b 1) (a 1)
  have h2 := pairKer_laurent (b 2) (a 2)
  have h3 := pairKer_laurent (b 3) (a 3)
  have h4 := pairKer_laurent (b 4) (a 4)
  simp only [Bp, gker, map_mul, lf_laurent, Ap]
  simp only [lf]
  calc _ = (pairKer (b 0) (a 0) * (RatFunc.X - RatFunc.C ((1 - a 0 : ℤ) : ℚ))) *
          (pairKer (b 1) (a 1) * (RatFunc.X - RatFunc.C ((1 - a 1 : ℤ) : ℚ))) *
          (pairKer (b 2) (a 2) * (RatFunc.X - RatFunc.C ((1 - a 2 : ℤ) : ℚ))) *
          (pairKer (b 3) (a 3) * (RatFunc.X - RatFunc.C ((1 - a 3 : ℤ) : ℚ))) *
          (pairKer (b 4) (a 4) * (RatFunc.X - RatFunc.C ((1 - a 4 : ℤ) : ℚ))) := by ring
    _ = _ := by rw [← h0, ← h1, ← h2, ← h3, ← h4]; ring

/-! ### One-step relations of `gker` -/

theorem gker_lower_a (a b : Fin 5 → ℤ) (i : Fin 5) :
    gker (Function.update a i (a i - 1)) b = lf (1 - a i) * gker a b := by
  fin_cases i <;>
    simp only [gker, Function.update_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.reduceEq, ite_true, ite_false, lf] <;>
    rw [pairKer_lower] <;> ring

theorem gker_raise_b (a b : Fin 5 → ℤ) (j : Fin 5) :
    gker a (Function.update b j (b j + 1)) = lf (-b j) * gker a b := by
  fin_cases j <;>
    simp only [gker, Function.update_apply, Fin.isValue, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, Fin.reduceEq, ite_true, ite_false, lf] <;>
    rw [pairKer_raise] <;> ring

theorem gker_raise_a (a b : Fin 5 → ℤ) (i : Fin 5) :
    gker a b = lf (-a i) * gker (Function.update a i (a i + 1)) b := by
  have h := gker_lower_a (Function.update a i (a i + 1)) b i
  rw [Function.update_self, add_sub_cancel_right, Function.update_idem,
    Function.update_eq_self] at h
  rw [h]
  congr 2
  ring

theorem gker_lower_b (a b : Fin 5 → ℤ) (j : Fin 5) :
    gker a b = lf (-(b j - 1)) * gker a (Function.update b j (b j - 1)) := by
  have h := gker_raise_b a (Function.update b j (b j - 1)) j
  rw [Function.update_self, sub_add_cancel, Function.update_idem, Function.update_eq_self] at h
  exact h

/-! ### The polynomial `D_w` -/

theorem prod_X_sub_C_monic (f : Fin 5 → ℚ) : (∏ i, (X - C (f i))).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

theorem prod_X_sub_C_natDegree (f : Fin 5 → ℚ) : (∏ i, (X - C (f i))).natDegree = 5 := by
  simp

theorem D_natDegree_lt (w : Vertex) : w.D.natDegree < 5 := by
  unfold Vertex.D
  set P := ∏ i, (X - C ((w.a i : ℚ) - 1)) with hP
  set Q := ∏ j, (X - C (w.b j : ℚ)) with hQ
  by_cases h : P - Q = 0
  · rw [h]; simp
  have hPm : P.Monic := prod_X_sub_C_monic _
  have hQm : Q.Monic := prod_X_sub_C_monic _
  have hdP : P.natDegree = 5 := prod_X_sub_C_natDegree _
  have hdQ : Q.natDegree = 5 := prod_X_sub_C_natDegree _
  have hlt := degree_sub_lt_left (p := P) (q := Q)
    (by rw [degree_eq_natDegree hPm.ne_zero, degree_eq_natDegree hQm.ne_zero, hdP, hdQ])
    hPm.ne_zero (by rw [hPm.leadingCoeff, hQm.leadingCoeff])
  rw [degree_eq_natDegree h, degree_eq_natDegree hPm.ne_zero, hdP] at hlt
  exact_mod_cast hlt

theorem D_eq_sum (w : Vertex) : w.D = ∑ k ∈ range 5, C (w.D.coeff k) * X ^ k :=
  w.D.as_sum_range_C_mul_X_pow' (D_natDegree_lt w)

/-- `D_w(-t) = ∏ⱼ (t + bⱼ) - ∏ᵢ (t + aᵢ - 1)` in `ℚ(t)`. -/
theorem D_neg (w : Vertex) :
    ∑ k ∈ range 5, RatFunc.C (w.D.coeff k) * (-RatFunc.X) ^ k = Bp w.b - Ap w.a := by
  have hC : ∀ q : ℚ, algebraMap ℚ (RatFunc ℚ) q = RatFunc.C q := fun q => by simp
  have h := congrArg (Polynomial.aeval (-RatFunc.X : RatFunc ℚ)) (D_eq_sum w)
  simp only [map_sum, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hC] at h
  rw [← h, Vertex.D, map_sub, map_prod, map_prod]
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hC, Fin.prod_univ_five, Bp, Ap, lf,
    Int.cast_neg, Int.cast_sub, Int.cast_one, map_neg, map_one]
  ring

theorem D_coeff_four (w : Vertex) :
    w.D.coeff 4 = 5 - ∑ i, (w.a i : ℚ) + ∑ j, (w.b j : ℚ) := by
  have h1 := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin 5))
    (fun i => (w.a i : ℚ) - 1) (by simp)
  have h2 := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin 5))
    (fun j => (w.b j : ℚ)) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin, Nat.reduceSub] at h1 h2
  rw [Vertex.D, coeff_sub, h1, h2, Finset.sum_sub_distrib]
  simp

/-- `D_w(c) = ∏ᵢ (c - aᵢ + 1) - ∏ⱼ (c - bⱼ)`. -/
theorem D_eval_sum (w : Vertex) (c : ℚ) :
    ∑ k ∈ range 5, w.D.coeff k * c ^ k =
      ∏ i, (c - ((w.a i : ℚ) - 1)) - ∏ j, (c - (w.b j : ℚ)) := by
  have h := congrArg (Polynomial.eval c) (D_eq_sum w)
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X] at h
  rw [← h, Vertex.D, eval_sub, eval_prod, eval_prod]
  simp

/-- `det (c I - θ_w) = D_w(c)/d₄` (zeta34 `det_Amat`). -/
theorem det_theta (w : Vertex) (c : ℚ) (hd : w.D.coeff 4 ≠ 0) :
    (c • (1 : Matrix (Fin 4) (Fin 4) ℚ) - w.theta).det =
      (∑ k ∈ range 5, w.D.coeff k * c ^ k) / w.D.coeff 4 := by
  have hM : c • (1 : Matrix (Fin 4) (Fin 4) ℚ) - w.theta =
      !![c, 0, 0, w.D.coeff 0 / w.D.coeff 4; -1, c, 0, w.D.coeff 1 / w.D.coeff 4;
        0, -1, c, w.D.coeff 2 / w.D.coeff 4; 0, 0, -1, c + w.D.coeff 3 / w.D.coeff 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Vertex.theta] <;> ring
  have h32 : (3 : Fin 4).succAbove 2 = 2 := by decide
  rw [hM]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, h32, Finset.sum_range_succ]
  field_simp
  ring

/-! ### One forward step for a moment matrix -/

/-- The `3 × 4` matrix `Φ_K[(-t)^j r]`. -/
def mm (Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ) (K : ℤ) (r : RatFunc ℚ) : Matrix (Fin 3) (Fin 4) ℚ :=
  Matrix.of fun i j => Φ K ((-RatFunc.X) ^ (j : ℕ) * r) i

/-- **One CMF step** (zeta34 `step_fwd`): if `r' = s (t - c) r` and the companion relation
`∑ₖ dₖ Φ_K[(-t)^k r] = 0` holds with `d = D_u`, `d₄ ≠ 0`, then
`Φ_K[(-t)^j r'] = Φ_K[(-t)^j r] · s(-c I - θ_u)`. -/
theorem mm_step (Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ)
    (hadd : ∀ K f g, Φ K (f + g) = Φ K f + Φ K g)
    (hsmul : ∀ K (c : ℚ) f, Φ K (RatFunc.C c * f) = c • Φ K f) (K : ℤ) (u : Vertex)
    (r : RatFunc ℚ) (s c : ℚ) (hd : u.D.coeff 4 ≠ 0)
    (hcomp : ∑ k ∈ range 5, u.D.coeff k • Φ K ((-RatFunc.X) ^ k * r) = 0) :
    mm Φ K (RatFunc.C s * ((RatFunc.X - RatFunc.C c) * r)) =
      mm Φ K r * (s • ((-c) • (1 : Matrix (Fin 4) (Fin 4) ℚ) - u.theta)) := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ → Fin 3 → ℚ, ∀ k, Φ K ((-RatFunc.X) ^ k * r) = m k :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ j : ℕ, Φ K ((-RatFunc.X) ^ j * (RatFunc.C s * ((RatFunc.X - RatFunc.C c) * r))) =
      (-s * c) • m j + (-s) • m (j + 1) := by
    intro j
    have e : (-RatFunc.X) ^ j * (RatFunc.C s * ((RatFunc.X - RatFunc.C c) * r)) =
        RatFunc.C (-s * c) * ((-RatFunc.X) ^ j * r) +
          RatFunc.C (-s) * ((-RatFunc.X) ^ (j + 1) * r) := by
      simp only [map_neg, map_mul, pow_succ]; ring
    rw [e, hadd, hsmul, hsmul, hm, hm]
  ext i j
  have hc := congrFun hcomp i
  simp only [hm, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ,
    Finset.sum_range_zero, Pi.zero_apply, zero_add] at hc
  simp only [mm, Matrix.of_apply, Matrix.mul_apply, hstep, hm, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Fin.sum_univ_four]
  fin_cases j <;> simp [Vertex.theta] <;> [ring; ring; ring; skip]
  field_simp
  linear_combination (-s) * hc
