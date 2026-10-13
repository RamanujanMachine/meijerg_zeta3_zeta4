/-
# Node blueprint: `cmf_readout` (paper §3, "Proof by the CMF mechanism")

Target (restated verbatim from `Blueprint_5255.lean`):
  `Q n = (-1)^n * W n 0 0 ∧ W n 1 0 = 0 ∧ P3 n = (-1)^n * (-(W n 2 0)/2 + W n 3 0/4) ∧
   P4 n = (-1)^n * (-(W n 3 0)/6)`.

Strategy (paper §3, handoff §5.2). Attach to every vertex `w` the signed rational kernel
`R_w(t) = (-1)^{a₀+a₁} ∏ Γ(t+bⱼ)/Γ(t+aᵢ)` (`kerR`, a product of zeta34 `pairKer`s with the
identity pairing, i.e. `lin (kZ w) (kP w)` with explicit zero/pole multisets), and to every
rational function the two zeta34 *formal moment functionals* `𝓛_K` (`Lfun`, `∫ K₂ f/(2πi)`) and
`𝓜_K = -𝓛_K[f']` (`Mfun`, `∫ K₃ f/(2πi) = -½ 𝓜_K`), read in the coordinates `(Z₃, Z₂, 1)`
(`Lmom`) and `(Z₄, Z₃, 1)` (`Mmom`). Both satisfy the abstract axioms `IsMom` (zeta34 `IsMom`:
linearity, invariance under `t ↦ t-1` of `lin Z P` with a zero of order `≥ ord` at the cutoff
`K` after cancellation, and the cutoff move `K ↦ K+1`). The axioms give the companion relation
`∑ d_k Φ[(-t)^k R_w] = 0` at every vertex satisfying the boundary condition `VC` at `K`, hence the
native transport `momMat(v) = momMat(w) · E` along every move, hence
`momMat_{2n}(w_n) = momMat_0(w_0) · W_n` (cutoff `0` on blocks 1–3, moved to `2n` across the
triple zeros `1..2n` before block 4). Reading off column `0` against the initial rows
`(2Z₃, -Z₂, 1, -1/2)`, `(6Z₄, -2Z₃, 0, 1)` and the endpoint values
`𝓛_{2n}[(-1)^n F_n] = (-1)^n (2Q_n Z₃ + 0·Z₂ - 2P_{3,n})`,
`𝓜_{2n}[(-1)^n F_n] = (-1)^n (6Q_n Z₄ + 0·Z₃ - 6P_{4,n})` proves the four identities.

Supporting lemmas (10):

| # | lemma | directly from the PDF |
|---|---|---|
| 1 | `walkEnd_blockPath` | yes (path description, §2–3) |
| 2 | `kerR_endpoints` | yes ("initially `t⁻²`, at the endpoint `(-1)^n F_n`") |
| 3 | `Lmom_isMom` | partially (contour argument; formal version is zeta34's) |
| 4 | `Mmom_isMom` | partially (as 3; `K₃ = -K₂'/2`) |
| 5 | `companion` | yes (`R_w ∏(t+aᵢ-1) = H_w(t-1)`) |
| 6 | `edge_transport` | yes ("gamma functional equation gives the native multipliers") |
| 7 | `path_conditions` | partially (zero orders asserted; invertibility implicit) |
| 8 | `path_transport` | yes (induction along the four blocks, cutoff move) |
| 9 | `init_rows` | yes (the two initial rows, §3) |
| 10 | `end_rows` | yes ("closing the endpoint contour to the right") |

Helper modules (imported only here): `CmfReadout_Aux` (kernels `gker`/`kZ`/`kP`/`bro`, the
polynomial `D_w`, one CMF step `mm_step`), `CmfReadout_Path` (`walkEnd`, `moveSrc`,
`moveIsInv`, `VC`, `StepOK`, `WalkOK`, the vertex families of the nine blocks and all boundary
conditions), `CmfReadout_PF` (partial fractions of `F_n`, `𝓛_{2n}[F_n]`, `𝓜_{2n}[F_n]`). The
zeta34 functionals and their `IsMom` instances come from the shared copies `QGrowth_CMF_basic`
etc. (namespace `Meijer5255.QGA.ZetasIrr`).
-/
import Meijer5255.definitions
import Meijer5255.CmfReadout_Aux
import Meijer5255.CmfReadout_PF
import Meijer5255.CmfReadout_Path

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.CmfReadout

open Meijer5255
open Meijer5255.QGA.ZetasIrr.CMF (lin ival lin_cons_left count_ival)

/-! ### Objects

`walkEnd`, `moveSrc`, `moveIsInv`, `VC`, `StepOK`, `WalkOK`, `path123`, `path4`, `junction` are
defined in `CmfReadout_Path`; `gker`, `kZ`, `kP`, `bro`, `mm` in `CmfReadout_Aux`. -/

/-- The endpoint vertex `(1+16n, 1+17n, -11n, -12n, -10n; 2n, n, 0, -n, -2n)`. -/
def endVertex (n : ℕ) : Vertex :=
  ⟨![1 + 16 * n, 1 + 17 * n, -11 * n, -12 * n, -10 * n], ![2 * n, n, 0, -n, -2 * n]⟩

/-- The sign `(-1)^{a₀+a₁}`. -/
def kSign (w : Vertex) : ℚ := (-1 : ℚ) ^ (w.a 0 + w.a 1)

/-- The signed kernel `R_w(t) = (-1)^{a₀+a₁} ∏ᵢ Γ(t+bᵢ)/Γ(t+aᵢ)` of the paper. -/
def kerR (w : Vertex) : RatFunc ℚ := RatFunc.C (kSign w) * gker w.a w.b

/-- The kernel `F_n = ∏(X - x)_{x ∈ numRoots} / ∏(X - x)_{x ∈ denRoots}`. -/
def Fn (n : ℕ) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (rootPoly (numRoots n)) /
    algebraMap ℚ[X] (RatFunc ℚ) (rootPoly (denRoots n))

/-- The first functional `𝓛_K[f] = ∫ K₂ f/(2πi)` (zeta34 `Lfun`, the regularised
`-∑_{t>K} f'(t)`) in the coordinates `(Z₃, Z₂, 1)`. -/
def Lmom (K : ℤ) (f : RatFunc ℚ) : Fin 3 → ℚ :=
  ![QGA.ZetasIrr.Lfun K f 3, QGA.ZetasIrr.Lfun K f 2, QGA.ZetasIrr.Lfun K f 0]

/-- The second functional `𝓜_K[f] = -𝓛_K[f']` (zeta34 `Mfun`, the regularised
`∑_{t>K} f''(t)`) in the coordinates `(Z₄, Z₃, 1)`. (The paper's `∫ K₃ f/(2πi)` is `-½ 𝓜_K[f]`.) -/
def Mmom (K : ℤ) (f : RatFunc ℚ) : Fin 3 → ℚ :=
  ![QGA.ZetasIrr.Mfun K f 4, QGA.ZetasIrr.Mfun K f 3, QGA.ZetasIrr.Mfun K f 0]

/-- The abstract axioms of a moment functional of order `ord` (zeta34 `IsMom`): additivity,
homogeneity, invariance of `lin Z P` under `t ↦ t - 1` when all poles are `≤ K` and the zero at
`K` has order `≥ ord` after cancellation, and the cutoff move `K ↦ K+1` when the poles are `≤ K`
and `f` vanishes to order `≥ ord` at `K+1`. -/
structure IsMom (Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ) (ord : ℕ) : Prop where
  add : ∀ K f g, Φ K (f + g) = Φ K f + Φ K g
  smul : ∀ K (c : ℚ) f, Φ K (RatFunc.C c * f) = c • Φ K f
  shift : ∀ K (Z P : Multiset ℤ), (∀ p ∈ P, p ≤ K) → P.count K + ord ≤ Z.count K →
    Φ K (RatFunc.laurent (-1 : ℚ) (lin Z P)) = Φ K (lin Z P)
  cut : ∀ K (Z P : Multiset ℤ), (∀ p ∈ P, p ≤ K) → ord ≤ Z.count (K + 1) →
    Φ (K + 1) (lin Z P) = Φ K (lin Z P)

/-- The `3 × 4` moment matrix `Φ_K[(-t)^r R_w]`, columns indexed by the basis exponent `r`. -/
def momMat (Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ) (K : ℤ) (w : Vertex) : Matrix (Fin 3) (Fin 4) ℚ :=
  Matrix.of fun i r => Φ K ((-RatFunc.X) ^ (r : ℕ) * kerR w) i

/-! ### Auxiliary lemmas -/

theorem IsMom.zero {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ) :
    Φ K 0 = 0 := by
  have := hΦ.add K 0 0
  rw [add_zero] at this
  exact left_eq_add.mp this

theorem IsMom.sum {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ)
    (s : Finset ℕ) (c : ℕ → ℚ) (f : ℕ → RatFunc ℚ) :
    Φ K (∑ i ∈ s, RatFunc.C (c i) * f i) = ∑ i ∈ s, c i • Φ K (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [hΦ.zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hΦ.add, hΦ.smul, ih]

theorem IsMom.sub {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ)
    (f g : RatFunc ℚ) : Φ K (f - g) = Φ K f - Φ K g := by
  rw [sub_eq_add_neg, hΦ.add, show -g = RatFunc.C (-1) * g by simp, hΦ.smul, neg_one_smul,
    sub_eq_add_neg]

theorem VC.mono {ord ord' : ℕ} {K : ℤ} {w : Vertex} (h : VC ord' K w) (hle : ord ≤ ord') :
    VC ord K w := ⟨h.1, by have := h.2; omega⟩

theorem kSign_aDown (i : Fin 5) (w : Vertex) :
    kSign ((Move.aDown i).next w) = -aSign i * kSign w := by
  have hm : (-1 : ℚ) ^ (w.a 0 + w.a 1 - 1) = -(-1 : ℚ) ^ (w.a 0 + w.a 1) := by
    rw [zpow_sub_one₀ (by norm_num)]; norm_num
  fin_cases i <;> simp [kSign, Move.next, aSign]
  · rw [show w.a 0 - 1 + w.a 1 = w.a 0 + w.a 1 - 1 by ring, hm]
  · rw [show w.a 0 + (w.a 1 - 1) = w.a 0 + w.a 1 - 1 by ring, hm]

theorem kerR_aDown (i : Fin 5) (w : Vertex) :
    kerR ((Move.aDown i).next w) = RatFunc.C (-aSign i) *
      ((RatFunc.X - RatFunc.C (((1 - w.a i : ℤ)) : ℚ)) * kerR w) := by
  rw [kerR, kSign_aDown, kerR]
  simp only [Move.next, gker_lower_a, lf, map_mul, map_neg]
  ring

theorem kerR_bUp (j : Fin 5) (w : Vertex) :
    kerR ((Move.bUp j).next w) = RatFunc.C 1 *
      ((RatFunc.X - RatFunc.C (((-w.b j : ℤ)) : ℚ)) * kerR w) := by
  simp only [kerR, kSign, Move.next, gker_raise_b, lf, map_one]
  ring

theorem kerR_aUp (i : Fin 5) (w : Vertex) :
    kerR w = RatFunc.C (-aSign i) *
      ((RatFunc.X - RatFunc.C (((-w.a i : ℤ)) : ℚ)) * kerR ((Move.aUp i).next w)) := by
  have h := kerR_aDown i ((Move.aUp i).next w)
  have hv : (Move.aDown i).next ((Move.aUp i).next w) = w := by
    simp only [Move.next, Function.update_self, add_sub_cancel_right, Function.update_idem,
      Function.update_eq_self]
  have ha : ((Move.aUp i).next w).a i = w.a i + 1 := by simp [Move.next]
  rw [hv, ha] at h
  rw [h, show ((1 - (w.a i + 1) : ℤ) : ℚ) = ((-w.a i : ℤ) : ℚ) by push_cast; ring]

theorem kerR_bDown (j : Fin 5) (w : Vertex) :
    kerR w = RatFunc.C 1 *
      ((RatFunc.X - RatFunc.C (((-(w.b j - 1) : ℤ)) : ℚ)) * kerR ((Move.bDown j).next w)) := by
  simp only [kerR, kSign, Move.next, map_one, one_mul]
  rw [gker_lower_b w.a w.b j, lf]
  ring

theorem det_ne_zero_of_inv {A : Matrix (Fin 4) (Fin 4) ℚ} (h : A⁻¹.det ≠ 0) : A.det ≠ 0 := by
  intro h0
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, h0, inv_zero] at h
  exact h rfl

/-- `(-t)^r · lin Z P = (-1)^r · lin (0^r + Z) P`. -/
theorem negX_pow_mul_lin (r : ℕ) (Z P : Multiset ℤ) :
    (-RatFunc.X) ^ r * lin Z P =
      RatFunc.C ((-1 : ℚ) ^ r) * lin (Multiset.replicate r 0 + Z) P := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Multiset.replicate_succ, Multiset.cons_add, lin_cons_left, pow_succ,
      mul_comm _ (-RatFunc.X), mul_assoc, ih]
    simp only [Int.cast_zero, map_zero, sub_zero, map_pow, map_neg, map_one]
    ring

/-! ### Supporting lemmas -/

/-- **[1] Endpoint of the block path.**
* Proved (≈ 5 lines; the vertex families `V1 … V9` and `walkEnd_replicate` are in
  `CmfReadout_Path`).
* Directly from the PDF: yes (the path and its endpoint are stated in §2–3). -/
theorem walkEnd_blockPath (n : ℕ) : walkEnd startVertex (blockPath n) = endVertex n := by
  rw [blockPath_eq, walkEnd_append]
  exact (walkEnd_path4 n).trans (V9_end n)

/-- **[2] The kernel at the endpoints.** `R_{w₀} = t⁻²` and `R_{w_n} = (-1)^n F_n`.
* Proved (≈ 30 lines).
* Directly from the PDF: yes ("Initially it is `t⁻²`, and at the endpoint it is `(-1)^n F_n`"). -/
theorem kerR_endpoints (n : ℕ) :
    kerR startVertex = (RatFunc.X ^ 2)⁻¹ ∧
      kerR (endVertex n) = RatFunc.C ((-1 : ℚ) ^ n) * Fn n := by
  constructor
  · have hs : kSign startVertex = 1 := by simp [kSign, startVertex]
    rw [kerR, hs, map_one, one_mul, gker_eq_lin]
    have hZ : kZ startVertex.a startVertex.b = 0 := by simp [kZ, startVertex, ival]
    have hP : kP startVertex.a startVertex.b = {0, 0} := by simp [kP, startVertex, ival]
    rw [hZ, hP]
    simp [lin, QGA.ZetasIrr.CMF.lp]
    ring
  · have hs : kSign (endVertex n) = (-1 : ℚ) ^ n := by
      rw [kSign, show (endVertex n).a 0 + (endVertex n).a 1 = ((2 + 33 * n : ℕ) : ℤ) by
        simp [endVertex]; ring, zpow_natCast, pow_add, pow_mul]
      norm_num
    have hZ : kZ (endVertex n).a (endVertex n).b = numRoots n := by
      refine Multiset.ext.mpr fun k => ?_
      simp only [kZ, endVertex, numRoots, Multiset.count_add, count_ival, count_Icc,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      split_ifs <;> omega
    have hP : kP (endVertex n).a (endVertex n).b = denRoots n := by
      refine Multiset.ext.mpr fun k => ?_
      simp only [kP, endVertex, denRoots, Multiset.count_add, count_ival, count_Icc,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
      split_ifs <;> omega
    rw [kerR, hs, gker_eq_lin, hZ, hP, Fn, rootPoly_eq_lp, rootPoly_eq_lp]
    rfl

/-- **[3] `Lmom` is a moment functional of order `2`.** The coordinates of zeta34 `isMom_Lfun`
(`Lfun_add`, `Lfun_C_mul`, `Lfun_shift`, `Lfun_cut`, from `Lfun_sub_Lfun_pred`).
* Proved (≈ 10 lines).
* Directly from the PDF: partially (the PDF argues with contour integrals of `K₂`; the formal
  partial-fraction model and its axioms are the zeta34 formalisation). -/
theorem Lmom_isMom : IsMom Lmom 2 := by
  refine ⟨fun K f g => ?_, fun K c f => ?_, fun K Z P hP h => ?_, fun K Z P hP h => ?_⟩
  · funext i; fin_cases i <;> simp [Lmom, QGA.ZetasIrr.Aux.Lfun_add]
  · funext i; rw [Lmom, Lmom, QGA.ZetasIrr.Aux.Lfun_C_mul]; fin_cases i <;> simp
  · rw [Lmom, Lmom, QGA.ZetasIrr.CMF.Lfun_shift K Z P hP h]
  · rw [Lmom, Lmom, QGA.ZetasIrr.CMF.Lfun_cut K Z P hP h]

/-- **[4] `Mmom` is a moment functional of order `3`.** The coordinates of zeta34
`isMom_Mfun`; the translate difference contributes `-g''(K)`, which vanishes for a zero of order
`≥ 3`.
* Proved (≈ 10 lines).
* Directly from the PDF: partially (as [3]). -/
theorem Mmom_isMom : IsMom Mmom 3 := by
  refine ⟨fun K f g => ?_, fun K c f => ?_, fun K Z P hP h => ?_, fun K Z P hP h => ?_⟩
  · funext i; fin_cases i <;> simp [Mmom, QGA.ZetasIrr.Aux.Mfun_add]
  · funext i; rw [Mmom, Mmom, QGA.ZetasIrr.CMF.Mfun_C_mul]; fin_cases i <;> simp
  · rw [Mmom, Mmom, QGA.ZetasIrr.CMF.Mfun_shift K Z P hP h]
  · rw [Mmom, Mmom, QGA.ZetasIrr.CMF.Mfun_cut K Z P hP h]

/-- **[5] Companion relation.** If `w` satisfies the boundary condition `VC ord K` then
`∑_k d_k Φ_K[(-t)^k R_w] = 0`, because
`∑_k d_k (-t)^k R_w = D_w(-t) R_w = H_w(t) - H_w(t-1)` with `H_w = ∏ⱼ (t + bⱼ) R_w`.
* Proved (≈ 15 lines).
* Directly from the PDF: yes (`R_w(t)∏(t+aᵢ-1) = H_w(t-1)`, §3). -/
theorem companion {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ)
    (w : Vertex) (hvc : VC ord K w) :
    ∑ k ∈ range 5, w.D.coeff k • Φ K ((-RatFunc.X) ^ k * kerR w) = 0 := by
  rw [← hΦ.sum]
  have e : ∑ k ∈ range 5, RatFunc.C (w.D.coeff k) * ((-RatFunc.X) ^ k * kerR w) =
      RatFunc.C (kSign w) * (Bp w.b * gker w.a w.b) -
        RatFunc.C (kSign w) * (Ap w.a * gker w.a w.b) := by
    rw [show ∑ k ∈ range 5, RatFunc.C (w.D.coeff k) * ((-RatFunc.X) ^ k * kerR w) =
        (∑ k ∈ range 5, RatFunc.C (w.D.coeff k) * (-RatFunc.X) ^ k) * kerR w by
      rw [Finset.sum_mul]; simp_rw [mul_assoc], D_neg, kerR]
    ring
  rw [e, Ap_mul_gker, gker_eq_lin, Bp_mul_lin, hΦ.sub, hΦ.smul, hΦ.smul,
    hΦ.shift K _ _ hvc.1 hvc.2, sub_self]

/-- **[6] Edge transport.** For a move `m` at `w` with `v = m.next w`: if the companion relation
holds at `m.src w` with `d₄ ≠ 0` there, the step matrix is invertible when `m` divides, and
`m = aᵢ↑` only for `i ∈ {0, 1}`, then `momMat Φ K v = momMat Φ K w * m.mat w`.
Proof: `R_v = -sᵢ (t + aᵢ - 1) R_w` (`a↓`), `R_w = -sᵢ (t + aᵢ) R_v` (`a↑`), `R_v = (t + bⱼ) R_w`
(`b↑`), `R_w = (t + bⱼ - 1) R_v` (`b↓`) and `mm_step`; invert for the dividing moves.
* Proved (≈ 40 lines).
* Directly from the PDF: yes ("the elementary gamma relations prove the edge relations"). -/
theorem edge_transport {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord) (K : ℤ)
    (m : Move) (w : Vertex)
    (hcomp : ∑ k ∈ range 5,
      (moveSrc m w).D.coeff k • Φ K ((-RatFunc.X) ^ k * kerR (moveSrc m w)) = 0)
    (hd4 : (moveSrc m w).D.coeff 4 ≠ 0)
    (hdet : moveIsInv m → (m.mat w).det ≠ 0)
    (hA : ∀ i, m = .aUp i → (i : ℕ) < 2) :
    momMat Φ K (m.next w) = momMat Φ K w * m.mat w := by
  have hm : ∀ u, momMat Φ K u = mm Φ K (kerR u) := fun _ => rfl
  cases m with
  | aDown i =>
    simp only [moveSrc] at hcomp hd4
    rw [hm, hm, kerR_aDown, mm_step Φ hΦ.add hΦ.smul K w _ _ _ hd4 hcomp, Move.mat]
    congr 1
    ext a b; simp [Matrix.sub_apply, Matrix.smul_apply]; ring
  | bUp j =>
    simp only [moveSrc] at hcomp hd4
    rw [hm, hm, kerR_bUp, mm_step Φ hΦ.add hΦ.smul K w _ _ _ hd4 hcomp, Move.mat]
    congr 1
    ext a b; simp [Matrix.sub_apply, Matrix.smul_apply]
  | aUp i =>
    have hi : aSign i = 1 := by
      have := hA i rfl; simp [aSign, this]
    simp only [moveSrc] at hcomp hd4
    set v := (Move.aUp i).next w with hv
    have key := mm_step Φ hΦ.add hΦ.smul K v (kerR v) (-aSign i) ((-w.a i : ℤ) : ℚ) hd4 hcomp
    rw [← kerR_aUp] at key
    set B := -aSign i • (-(((-w.a i : ℤ)) : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) - v.theta)
      with hB
    have hBm : (Move.aUp i).mat w = B⁻¹ := by
      rw [Move.mat, hB, hi]
      congr 1
      ext a b; simp [Matrix.sub_apply, Matrix.smul_apply, hv]
    have hdB : IsUnit B.det := by
      rw [isUnit_iff_ne_zero]; exact det_ne_zero_of_inv (hBm ▸ hdet trivial)
    rw [hm, hm, key, hBm, Matrix.mul_nonsing_inv_cancel_right _ _ hdB]
  | bDown j =>
    simp only [moveSrc] at hcomp hd4
    set v := (Move.bDown j).next w with hv
    have key := mm_step Φ hΦ.add hΦ.smul K v (kerR v) 1 ((-(w.b j - 1) : ℤ) : ℚ) hd4 hcomp
    rw [← kerR_bDown] at key
    set B := (1 : ℚ) • (-(((-(w.b j - 1) : ℤ)) : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) - v.theta)
      with hB
    have hBm : (Move.bDown j).mat w = B⁻¹ := by
      rw [Move.mat, hB]
      congr 1
      ext a b; simp [Matrix.sub_apply, Matrix.smul_apply, hv]
    have hdB : IsUnit B.det := by
      rw [isUnit_iff_ne_zero]; exact det_ne_zero_of_inv (hBm ▸ hdet trivial)
    rw [hm, hm, key, hBm, Matrix.mul_nonsing_inv_cancel_right _ _ hdB]

/-- **[7] The block path satisfies all hypotheses.** Blocks 1–3 (`path123`) at cutoff `0` and
block 4 (`path4`) at cutoff `2n` satisfy `WalkOK` (boundary condition of order `3` at every
companion vertex, `d₄ ≠ 0`, invertible dividing steps, `a↑` only for `a₀, a₁`); at the junction
all poles are `≤ 0` and the kernel has zeros of order `≥ 3` at `1, …, 2n` (so the cutoff can be
moved from `0` to `2n`).
* Proved (≈ 10 lines here; ≈ 250 lines in `CmfReadout_Path`: the nine vertex families, the
  per-pair order count `VC_of`, `d₄ = 5 - ∑a + ∑b`, `det (cI - θ) = D(c)/d₄`).
* Directly from the PDF: partially (the zero orders are asserted in one paragraph of §3; the
  invertibility of the dividing steps is implicit). -/
theorem path_conditions (n : ℕ) :
    WalkOK 0 startVertex (path123 n) ∧ WalkOK (2 * n) (junction n) (path4 n) ∧
      (∀ p ∈ kP (junction n).a (junction n).b, p ≤ 0) ∧
      ∀ k : ℤ, 1 ≤ k → k ≤ 2 * n → 3 ≤ (kZ (junction n).a (junction n).b).count k :=
  ⟨walk123_ok n, walk4_ok n, junction_poles n, junction_zeros n⟩

/-- Transport along a walk all of whose steps satisfy `StepOK` (zeta34 `walk_transport`). -/
theorem walk_transport {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord)
    (hord : ord ≤ 3) (K : ℤ) :
    ∀ (L : List Move) (w : Vertex), WalkOK K w L →
      momMat Φ K (walkEnd w L) = momMat Φ K w * walkFrom w L := by
  intro L
  induction L with
  | nil => intro w _; simp [walkEnd, walkFrom]
  | cons m ms ih =>
    intro w h
    obtain ⟨⟨hvc, hd4, hdet, hA⟩, hrest⟩ := h
    rw [walkEnd, ih _ hrest,
      edge_transport hΦ K m w (companion hΦ K _ (hvc.mono hord)) hd4 hdet hA, walkFrom,
      Matrix.mul_assoc]

/-- The cutoff move `0 → 2n` at the junction. -/
theorem momMat_junction_cut {Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ} {ord : ℕ} (hΦ : IsMom Φ ord)
    (hord : ord ≤ 3) (n : ℕ) : momMat Φ (2 * n) (junction n) = momMat Φ 0 (junction n) := by
  obtain ⟨-, -, hP, hZ⟩ := path_conditions n
  have hcut : ∀ (r m : ℕ), m ≤ 2 * n →
      Φ m (lin (Multiset.replicate r 0 + kZ (junction n).a (junction n).b)
        (kP (junction n).a (junction n).b)) =
      Φ 0 (lin (Multiset.replicate r 0 + kZ (junction n).a (junction n).b)
        (kP (junction n).a (junction n).b)) := by
    intro r m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      have h3 := hZ (m + 1) (by omega) (by omega)
      push_cast
      rw [hΦ.cut _ _ _ (fun p hp => (hP p hp).trans (by positivity)) (by
        rw [Multiset.count_add]; omega), ih (by omega)]
  ext i r
  simp only [momMat, Matrix.of_apply]
  rw [kerR, gker_eq_lin, mul_left_comm ((-RatFunc.X) ^ (r : ℕ)), negX_pow_mul_lin, ← mul_assoc,
    ← map_mul, hΦ.smul, hΦ.smul, Pi.smul_apply, Pi.smul_apply]
  have := hcut r (2 * n) le_rfl
  push_cast at this
  rw [this]

/-- **[8] Transport along the whole path.** For every moment functional of order `ord ≤ 3`:
`momMat Φ (2n) (w_n) = momMat Φ 0 (w₀) * W n`.
Proof: `walk_transport` over blocks 1–3 at cutoff `0` and block 4 at cutoff `2n` ([5], [6],
[7]), the cutoff move at the junction (`IsMom.cut` `2n` times), and [1].
* Proved (≈ 10 lines).
* Directly from the PDF: yes ("Hence these integrals propagate by the actual native CMF
  matrices", §3). -/
theorem path_transport (n : ℕ) (Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ) (ord : ℕ) (hΦ : IsMom Φ ord)
    (hord : ord ≤ 3) :
    momMat Φ (2 * n) (endVertex n) = momMat Φ 0 startVertex * W n := by
  obtain ⟨h123, h4, -, -⟩ := path_conditions n
  rw [← walkEnd_blockPath, W, blockPath_eq, walkEnd_append, walkFrom_append]
  change momMat Φ (2 * n) (walkEnd (junction n) (path4 n)) =
    momMat Φ 0 startVertex * (walkFrom startVertex (path123 n) * walkFrom (junction n) (path4 n))
  rw [walk_transport hΦ hord _ _ _ h4, momMat_junction_cut hΦ hord, junction,
    walk_transport hΦ hord _ _ _ h123, Matrix.mul_assoc]

/-- **[9] The initial rows.** At `w₀` (`R = t⁻²`, `K = 0`):
`Lmom` on `((-t)^r/t²)_{r<4}` is `(2Z₃, -Z₂, 1, -1/2)` and `Mmom` is `(6Z₄, -2Z₃, 0, 1)`.
(The paper's second row `(-3ζ4, ζ3, 0, -1/2)` is `-½` of the `Mmom` row.)
* Proved (≈ 25 lines here; `Lfun0_simple`, `Mfun0_simple`, `col0..3` in `CmfReadout_PF`:
  zeta34 `Lfun_zero_of_decomp`, `B₀ = 1`, `B₁(1) = 1/2`).
* Directly from the PDF: yes (§3, "the two initial rows … are"). -/
theorem init_rows :
    momMat Lmom 0 startVertex = !![2, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, -1 / 2] ∧
      momMat Mmom 0 startVertex = !![6, 0, 0, 0; 0, -2, 0, 0; 0, 0, 0, 1] := by
  have hk := (kerR_endpoints 0).1
  have key : ∀ (Φ : ℤ → RatFunc ℚ → Fin 3 → ℚ) (i : Fin 3) (r : Fin 4),
      momMat Φ 0 startVertex i r = Φ 0 ((-RatFunc.X) ^ (r : ℕ) * (RatFunc.X ^ 2)⁻¹) i := by
    intro Φ i r; simp only [momMat, Matrix.of_apply, hk]
  refine ⟨?_, ?_⟩ <;> ext i r <;> rw [key] <;> fin_cases r
  · rw [col0, Lmom, Lfun0_simple _ _ (by norm_num) (by norm_num)]
    fin_cases i <;> simp [QGA.ZetasIrr.Zsym, bsum_zero]
  · rw [col1, Lmom, Lfun0_simple _ _ (by norm_num) (by norm_num)]
    fin_cases i <;> simp [QGA.ZetasIrr.Zsym, bsum_zero]
  · rw [col2, Lmom, Lfun0_simple _ _ (by norm_num) (by norm_num)]
    fin_cases i <;> simp [QGA.ZetasIrr.Zsym, bsum_one]
  · rw [col3, Lmom, Lfun0_simple _ _ (by norm_num) (by norm_num)]
    fin_cases i <;> simp [QGA.ZetasIrr.Zsym, bsum_negX]
  · rw [col0, Mmom, Mfun0_simple _ _ (by norm_num)]
    fin_cases i <;> norm_num [QGA.ZetasIrr.Zsym, bsum_zero]
  · rw [col1, Mmom, Mfun0_simple _ _ (by norm_num)]
    fin_cases i <;> norm_num [QGA.ZetasIrr.Zsym, bsum_zero]
  · rw [col2, Mmom, Mfun0_simple _ _ (by norm_num)]
    fin_cases i <;> norm_num [QGA.ZetasIrr.Zsym, bsum_zero]
  · rw [col3, Mmom, Mfun0_simple _ _ (by norm_num)]
    fin_cases i <;> norm_num [QGA.ZetasIrr.Zsym, bsum_negone]


/-- **[10] The endpoint values.** `Lmom_{2n}[F_n] = (2Q_n, ∑ⱼ bⱼ, -2P_{3,n})` and
`Mmom_{2n}[F_n] = (6Q_n, 2∑ⱼ bⱼ, -6P_{4,n})`, with `∑ⱼ bⱼ = 0` since `F_n = O(t⁻²)`.
Proof: `F_n = lin (numRoots n) (denRoots n)`; its Laurent coefficients at `-j` are `aCoef n j`,
`bCoef n j` (`pfCoeff_FL_two`, `pfCoeff_FL_one`), the harmonic index is `⌊2n + j⌋ = j + 2n`, the
polynomial part is `0`, and `∑ bⱼ = 0` by zeta34 `residue_sum_eq_zero` (all in `CmfReadout_PF`).
* Proved (≈ 5 lines here; ≈ 300 lines in `CmfReadout_PF`, adapted from pfq54 `pf_aux.lean`).
* Directly from the PDF: yes (§3, the two endpoint contour integrals and `∑ bⱼ = 0`). -/
theorem end_rows (n : ℕ) :
    Lmom (2 * n) (Fn n) = ![2 * Q n, 0, -2 * P3 n] ∧
      Mmom (2 * n) (Fn n) = ![6 * Q n, 0, -6 * P4 n] := by
  have hF : Fn n = FL n := by rw [Fn, rootPoly_eq_lp, rootPoly_eq_lp]; rfl
  have h2 : ((2 * n : ℕ) : ℤ) = 2 * (n : ℤ) := by push_cast; ring
  have hL3 := Lfun_FL_three n; have hL2 := Lfun_FL_two n; have hL0 := Lfun_FL_zero n
  have hM4 := Mfun_FL_four n; have hM3 := Mfun_FL_three n; have hM0 := Mfun_FL_zero n
  refine ⟨?_, ?_⟩
  · rw [Lmom, hF, hL3, hL2, hL0]
  · rw [Mmom, hF, hM4, hM3, hM0]

/-! ### The node -/

/-- **CMF readout** (statement verbatim from `Blueprint_5255.lean`), proved from [3], [4], [8],
[9], [10] and the second half of [2]. -/
theorem cmf_readout (n : ℕ) :
    Q n = (-1) ^ n * W n 0 0 ∧ W n 1 0 = 0 ∧
      P3 n = (-1) ^ n * (-(W n 2 0) / 2 + W n 3 0 / 4) ∧
      P4 n = (-1) ^ n * (-(W n 3 0) / 6) := by
  have hL := path_transport n Lmom 2 Lmom_isMom (by norm_num)
  have hM := path_transport n Mmom 3 Mmom_isMom (by norm_num)
  obtain ⟨hL0, hM0⟩ := init_rows
  obtain ⟨hLn, hMn⟩ := end_rows n
  have hker := (kerR_endpoints n).2
  -- the endpoint column `0` of both moment matrices
  have eL : ∀ i, momMat Lmom (2 * n) (endVertex n) i 0 = (-1) ^ n * Lmom (2 * n) (Fn n) i := by
    intro i
    simp only [momMat, Matrix.of_apply, Fin.val_zero, pow_zero, one_mul, hker]
    rw [Lmom_isMom.smul]; rfl
  have eM : ∀ i, momMat Mmom (2 * n) (endVertex n) i 0 = (-1) ^ n * Mmom (2 * n) (Fn n) i := by
    intro i
    simp only [momMat, Matrix.of_apply, Fin.val_zero, pow_zero, one_mul, hker]
    rw [Mmom_isMom.smul]; rfl
  -- the transported column `0`
  have tL : ∀ i, momMat Lmom (2 * n) (endVertex n) i 0 =
      ∑ r, (!![2, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, -1 / 2] : Matrix (Fin 3) (Fin 4) ℚ) i r *
        W n r 0 := by
    intro i; rw [hL, hL0, Matrix.mul_apply]
  have tM : ∀ i, momMat Mmom (2 * n) (endVertex n) i 0 =
      ∑ r, (!![6, 0, 0, 0; 0, -2, 0, 0; 0, 0, 0, 1] : Matrix (Fin 3) (Fin 4) ℚ) i r *
        W n r 0 := by
    intro i; rw [hM, hM0, Matrix.mul_apply]
  have hs : ((-1 : ℚ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  have h0 := (eL 0).symm.trans (tL 0)
  have h1 := (eL 1).symm.trans (tL 1)
  have h2 := (eL 2).symm.trans (tL 2)
  have h3 := (eM 2).symm.trans (tM 2)
  simp only [hLn, hMn, Fin.sum_univ_four] at h0 h1 h2 h3
  norm_num [Matrix.vecHead, Matrix.vecTail] at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination ((-1 : ℚ) ^ n / 2) * h0 - Q n * hs
  · linear_combination h1
  · linear_combination (-(-1 : ℚ) ^ n / 2) * h2 - P3 n * hs
  · linear_combination (-(-1 : ℚ) ^ n / 6) * h3 - P4 n * hs

end Meijer5255.CmfReadout
