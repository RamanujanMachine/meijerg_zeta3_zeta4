/-
# The block path of `Meijer5255.CmfReadout`: vertices and boundary conditions

Walks along lists of moves (`walkEnd`), the vertex whose companion relation a move uses
(`moveSrc`), the boundary condition `VC` (zeta34 `VC`, `CMF_path.lean`), the per-step conditions
`StepOK` and their conjunction `WalkOK` along a walk. The paper's block path is described by nine
explicit vertex families `V1 … V9` (one per block, `j` = number of moves done in the block), and
`path_ok` checks every condition along it (cutoff `0` on blocks 1–3, `2n` on block 4, triple zeros
`1..2n` at the junction).

Provenance: the pattern (generic vertex of a block + `count_ival` + `omega`) follows zeta34
`CMF_path.lean` (`AShape`, `BShape`, `VC_*`) and pfq54 `star_aux.lean` (`VC_wpt`, `Zk_wpt`).
-/
import Meijer5255.CmfReadout_Aux

open Polynomial Finset
open scoped RatFunc Matrix

set_option linter.unusedSimpArgs false

noncomputable section

namespace Meijer5255.CmfReadout

open Meijer5255
open Meijer5255.QGA.ZetasIrr.CMF (ival mem_ival count_ival)

/-! ### Walks -/

/-- The vertex reached after a list of moves. -/
def walkEnd : Vertex → List Move → Vertex
  | w, [] => w
  | w, m :: ms => walkEnd (m.next w) ms

/-- The vertex whose companion matrix a move uses: the source for `a↓, b↑`, the target for
`a↑, b↓`. -/
def moveSrc (m : Move) (w : Vertex) : Vertex :=
  match m with
  | .aDown _ => w
  | .bUp _ => w
  | .aUp _ => m.next w
  | .bDown _ => m.next w

/-- Whether a move is a dividing (inverse-matrix) step. -/
def moveIsInv : Move → Prop
  | .aDown _ => False
  | .bUp _ => False
  | .aUp _ => True
  | .bDown _ => True

/-- The boundary condition at cutoff `K` (zeta34 `VC`): all poles of `R_w` are `≤ K`, and
`H_w = ∏ⱼ (t + bⱼ) R_w` has a zero of order `≥ ord` at `K` after cancellation. -/
def VC (ord : ℕ) (K : ℤ) (w : Vertex) : Prop :=
  (∀ p ∈ kP w.a w.b, p ≤ K) ∧ (kP w.a w.b).count K + ord ≤ (bro w.b + kZ w.a w.b).count K

/-- The hypotheses of one transport step: boundary condition (order `3`) at the companion vertex,
`d₄ ≠ 0` there, invertibility of a dividing step, and `a↑` only for `i ∈ {0, 1}` (for which the
native matrix `(sᵢ θ(v) - aᵢ I)⁻¹` of `definitions.lean` is the transport matrix). -/
def StepOK (K : ℤ) (m : Move) (w : Vertex) : Prop :=
  VC 3 K (moveSrc m w) ∧ (moveSrc m w).D.coeff 4 ≠ 0 ∧ (moveIsInv m → (m.mat w).det ≠ 0) ∧
    ∀ i, m = .aUp i → (i : ℕ) < 2

/-- `StepOK` at every step of a walk. -/
def WalkOK (K : ℤ) : Vertex → List Move → Prop
  | _, [] => True
  | w, m :: ms => StepOK K m w ∧ WalkOK K (m.next w) ms

theorem walkEnd_append (w : Vertex) (L₁ L₂ : List Move) :
    walkEnd w (L₁ ++ L₂) = walkEnd (walkEnd w L₁) L₂ := by
  induction L₁ generalizing w with
  | nil => rfl
  | cons m ms ih => exact ih _

theorem walkFrom_append (w : Vertex) (L₁ L₂ : List Move) :
    walkFrom w (L₁ ++ L₂) = walkFrom w L₁ * walkFrom (walkEnd w L₁) L₂ := by
  induction L₁ generalizing w with
  | nil => simp [walkFrom, walkEnd]
  | cons m ms ih => simp only [List.cons_append, walkFrom, walkEnd, ih, Matrix.mul_assoc]

theorem walkOK_append (K : ℤ) (w : Vertex) (L₁ L₂ : List Move) (h₁ : WalkOK K w L₁)
    (h₂ : WalkOK K (walkEnd w L₁) L₂) : WalkOK K w (L₁ ++ L₂) := by
  induction L₁ generalizing w with
  | nil => exact h₂
  | cons m ms ih => exact ⟨h₁.1, ih _ h₁.2 h₂⟩

/-- A block `m^k` along a vertex family `f` with `m.next (f j) = f (j+1)`. -/
theorem walkEnd_replicate (f : ℕ → Vertex) (m : Move) (hf : ∀ j, m.next (f j) = f (j + 1))
    (k : ℕ) : walkEnd (f 0) (List.replicate k m) = f k := by
  suffices h : ∀ k i, walkEnd (f i) (List.replicate k m) = f (i + k) by simpa using h k 0
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih => intro i; rw [List.replicate_succ, walkEnd, hf, ih]; congr 1; omega

theorem walkOK_replicate (K : ℤ) (f : ℕ → Vertex) (m : Move)
    (hf : ∀ j, m.next (f j) = f (j + 1)) (k : ℕ) (h : ∀ j < k, StepOK K m (f j)) :
    WalkOK K (f 0) (List.replicate k m) := by
  suffices H : ∀ k i, (∀ j, i ≤ j → j < i + k → StepOK K m (f j)) →
      WalkOK K (f i) (List.replicate k m) from H k 0 fun j _ hj => h j (by omega)
  intro k
  induction k with
  | zero => intro i _; trivial
  | succ k ih =>
    intro i hi
    rw [List.replicate_succ]
    exact ⟨hi i le_rfl (by omega), hf i ▸ ih (i + 1) fun j h1 h2 => hi j (by omega) (by omega)⟩

/-! ### The block path -/

/-- Blocks 1–3 of the path (`a₂,a₃,a₄` down, `a₀,a₁` up, `b₀,b₁` up). -/
def path123 (n : ℕ) : List Move :=
  List.replicate (11 * n) (.aDown 2) ++ List.replicate (12 * n) (.aDown 3) ++
    List.replicate (10 * n) (.aDown 4) ++ List.replicate (16 * n) (.aUp 0) ++
    List.replicate (17 * n) (.aUp 1) ++ List.replicate (2 * n) (.bUp 0) ++
    List.replicate n (.bUp 1)

/-- Block 4 of the path (`b₃,b₄` down). -/
def path4 (n : ℕ) : List Move := List.replicate n (.bDown 3) ++ List.replicate (2 * n) (.bDown 4)

theorem blockPath_eq (n : ℕ) : blockPath n = path123 n ++ path4 n := by
  simp only [blockPath, path123, path4, List.append_assoc]

/-- The upper parameters after block 2. -/
def aE (n : ℕ) : Fin 5 → ℤ := ![1 + 16 * n, 1 + 17 * n, -11 * n, -12 * n, -10 * n]

/-- The vertex after `j` moves of block `a₂↓`. -/
def V1 (j : ℕ) : Vertex := ⟨![1, 1, -(j : ℤ), 0, 0], ![0, 0, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `a₃↓`. -/
def V2 (n j : ℕ) : Vertex := ⟨![1, 1, -11 * n, -(j : ℤ), 0], ![0, 0, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `a₄↓`. -/
def V3 (n j : ℕ) : Vertex := ⟨![1, 1, -11 * n, -12 * n, -(j : ℤ)], ![0, 0, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `a₀↑`. -/
def V4 (n j : ℕ) : Vertex := ⟨![1 + j, 1, -11 * n, -12 * n, -10 * n], ![0, 0, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `a₁↑`. -/
def V5 (n j : ℕ) : Vertex := ⟨![1 + 16 * n, 1 + j, -11 * n, -12 * n, -10 * n], ![0, 0, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `b₀↑`. -/
def V6 (n j : ℕ) : Vertex := ⟨aE n, ![j, 0, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `b₁↑`. -/
def V7 (n j : ℕ) : Vertex := ⟨aE n, ![2 * n, j, 0, 0, 0]⟩
/-- The vertex after `j` moves of block `b₃↓`. -/
def V8 (n j : ℕ) : Vertex := ⟨aE n, ![2 * n, n, 0, -(j : ℤ), 0]⟩
/-- The vertex after `j` moves of block `b₄↓`. -/
def V9 (n j : ℕ) : Vertex := ⟨aE n, ![2 * n, n, 0, -n, -(j : ℤ)]⟩

/-- The junction vertex between blocks 3 and 4, where the cutoff moves from `0` to `2n`. -/
def junction (n : ℕ) : Vertex := walkEnd startVertex (path123 n)

theorem vertex_ext {a a' b b' : Fin 5 → ℤ} (ha : ∀ i, a i = a' i) (hb : ∀ i, b i = b' i) :
    (⟨a, b⟩ : Vertex) = ⟨a', b'⟩ := by
  rw [funext ha, funext hb]

/-! ### Boundary conditions from the coordinates -/

/-- The net order contributed at `K` by the pair `(b, a)` (when no pole exceeds `K`). -/
def pairOrd (a b K : ℤ) : ℕ := if (-b = K ∧ a ≤ b) ∨ (1 - b ≤ K ∧ K ≤ -a) then 1 else 0

theorem pair_ineq (a b K : ℤ) (h : b < a → -b ≤ K) :
    (ival (1 - a) (a - b).toNat).count K + pairOrd a b K ≤
      (ival (1 - b) (b - a).toNat).count K + (if K = -b then 1 else 0) := by
  rw [count_ival, count_ival, pairOrd]; split_ifs <;> omega

theorem VC_of (ord : ℕ) (K : ℤ) (w : Vertex) (hP : ∀ i, w.b i < w.a i → -w.b i ≤ K)
    (hc : ord ≤ ∑ i, pairOrd (w.a i) (w.b i) K) : VC ord K w := by
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [kP, Multiset.mem_add, mem_ival] at hp
    have h0 := hP 0; have h1 := hP 1; have h2 := hP 2; have h3 := hP 3; have h4 := hP 4
    omega
  · have h0 := pair_ineq _ _ K (hP 0); have h1 := pair_ineq _ _ K (hP 1)
    have h2 := pair_ineq _ _ K (hP 2); have h3 := pair_ineq _ _ K (hP 3)
    have h4 := pair_ineq _ _ K (hP 4)
    rw [Fin.sum_univ_five] at hc
    simp only [kP, kZ, bro, Multiset.insert_eq_cons, Multiset.count_cons, Multiset.count_singleton,
      Multiset.count_add]
    omega

/-! ### Determinants of the dividing steps -/

theorem det_aUp (i : Fin 5) (hi : aSign i = 1) (w : Vertex)
    (hd : ((Move.aUp i).next w).D.coeff 4 ≠ 0)
    (hD : ∑ k ∈ range 5, ((Move.aUp i).next w).D.coeff k * (w.a i : ℚ) ^ k ≠ 0) :
    ((Move.aUp i).mat w).det ≠ 0 := by
  rw [Move.mat, hi, one_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  refine inv_ne_zero ?_
  rw [show ((Move.aUp i).next w).theta - (w.a i : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) =
      -((w.a i : ℚ) • 1 - ((Move.aUp i).next w).theta) by abel, Matrix.det_neg, det_theta _ _ hd]
  simp only [Fintype.card_fin]
  exact mul_ne_zero (by norm_num) (div_ne_zero hD hd)

theorem det_bDown (j : Fin 5) (w : Vertex)
    (hd : ((Move.bDown j).next w).D.coeff 4 ≠ 0)
    (hD : ∑ k ∈ range 5, ((Move.bDown j).next w).D.coeff k * ((w.b j : ℚ) - 1) ^ k ≠ 0) :
    ((Move.bDown j).mat w).det ≠ 0 := by
  rw [Move.mat, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, det_theta _ _ hd]
  exact inv_ne_zero (div_ne_zero hD hd)

theorem V1_next (j : ℕ) : (Move.aDown 2).next (V1 j) = V1 (j + 1) := by
  refine vertex_ext (fun i => ?_) (fun i => rfl)
  fin_cases i <;> simp [V1, Move.next] ; ring
theorem V2_next (n j : ℕ) : (Move.aDown 3).next (V2 n j) = V2 n (j + 1) := by
  refine vertex_ext (fun i => ?_) (fun i => rfl)
  fin_cases i <;> simp [V2, Move.next] ; ring
theorem V3_next (n j : ℕ) : (Move.aDown 4).next (V3 n j) = V3 n (j + 1) := by
  refine vertex_ext (fun i => ?_) (fun i => rfl)
  fin_cases i <;> simp [V3, Move.next] ; ring
theorem V4_next (n j : ℕ) : (Move.aUp 0).next (V4 n j) = V4 n (j + 1) := by
  refine vertex_ext (fun i => ?_) (fun i => rfl)
  fin_cases i <;> simp [V4, Move.next] ; ring
theorem V5_next (n j : ℕ) : (Move.aUp 1).next (V5 n j) = V5 n (j + 1) := by
  refine vertex_ext (fun i => ?_) (fun i => rfl)
  fin_cases i <;> simp [V5, Move.next] ; ring
theorem V6_next (n j : ℕ) : (Move.bUp 0).next (V6 n j) = V6 n (j + 1) := by
  refine vertex_ext (fun i => rfl) (fun i => ?_)
  fin_cases i <;> simp [V6, Move.next]
theorem V7_next (n j : ℕ) : (Move.bUp 1).next (V7 n j) = V7 n (j + 1) := by
  refine vertex_ext (fun i => rfl) (fun i => ?_)
  fin_cases i <;> simp [V7, Move.next]
theorem V8_next (n j : ℕ) : (Move.bDown 3).next (V8 n j) = V8 n (j + 1) := by
  refine vertex_ext (fun i => rfl) (fun i => ?_)
  fin_cases i <;> simp [V8, Move.next] ; ring
theorem V9_next (n j : ℕ) : (Move.bDown 4).next (V9 n j) = V9 n (j + 1) := by
  refine vertex_ext (fun i => rfl) (fun i => ?_)
  fin_cases i <;> simp [V9, Move.next] ; ring

theorem start_eq : startVertex = V1 0 := by
  refine vertex_ext (fun i => ?_) (fun i => rfl); fin_cases i <;> simp [V1, startVertex]
theorem V1_V2 (n : ℕ) : V1 (11 * n) = V2 n 0 := by
  refine vertex_ext (fun i => ?_) (fun i => rfl); fin_cases i <;> simp [V1, V2]
theorem V2_V3 (n : ℕ) : V2 n (12 * n) = V3 n 0 := by
  refine vertex_ext (fun i => ?_) (fun i => rfl); fin_cases i <;> simp [V2, V3]
theorem V3_V4 (n : ℕ) : V3 n (10 * n) = V4 n 0 := by
  refine vertex_ext (fun i => ?_) (fun i => rfl); fin_cases i <;> simp [V3, V4]
theorem V4_V5 (n : ℕ) : V4 n (16 * n) = V5 n 0 := by
  refine vertex_ext (fun i => ?_) (fun i => rfl); fin_cases i <;> simp [V4, V5]
theorem V5_V6 (n : ℕ) : V5 n (17 * n) = V6 n 0 := by
  refine vertex_ext (fun i => ?_) (fun i => ?_) <;> fin_cases i <;> simp [V5, V6, aE]
theorem V6_V7 (n : ℕ) : V6 n (2 * n) = V7 n 0 := by
  refine vertex_ext (fun i => rfl) (fun i => ?_); fin_cases i <;> simp [V6, V7]
theorem V7_V8 (n : ℕ) : V7 n n = V8 n 0 := by
  refine vertex_ext (fun i => rfl) (fun i => ?_); fin_cases i <;> simp [V7, V8]
theorem V8_V9 (n : ℕ) : V8 n n = V9 n 0 := by
  refine vertex_ext (fun i => rfl) (fun i => ?_); fin_cases i <;> simp [V8, V9]
theorem V9_end (n : ℕ) : V9 n (2 * n) = ⟨![1 + 16 * n, 1 + 17 * n, -11 * n, -12 * n, -10 * n],
    ![2 * n, n, 0, -n, -2 * n]⟩ := by
  refine vertex_ext (fun i => ?_) (fun i => ?_) <;> fin_cases i <;> simp [V9, aE]

theorem ok1 (j : ℕ) : StepOK 0 (.aDown 2) (V1 j) := by
  refine ⟨?_, ?_, fun h => h.elim, fun i h => by cases h⟩
  · exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V1, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V1, aE, pairOrd]; try (split_ifs <;> omega))
  · rw [moveSrc, D_coeff_four]; simp [V1, Fin.sum_univ_five]; intro h; linarith [(j.cast_nonneg : (0:ℚ) ≤ j)]

theorem ok2 (n j : ℕ) (hj : j < 12 * n) : StepOK 0 (.aDown 3) (V2 n j) := by
  refine ⟨?_, ?_, fun h => h.elim, fun i h => by cases h⟩
  · exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V2, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V2, aE, pairOrd]; try (split_ifs <;> omega))
  · rw [moveSrc, D_coeff_four]; simp [V2, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]

theorem ok3 (n j : ℕ) (hj : j < 10 * n) : StepOK 0 (.aDown 4) (V3 n j) := by
  refine ⟨?_, ?_, fun h => h.elim, fun i h => by cases h⟩
  · exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V3, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V3, aE, pairOrd]; try (split_ifs <;> omega))
  · rw [moveSrc, D_coeff_four]; simp [V3, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]

theorem ok4 (n j : ℕ) (hj : j < 16 * n) : StepOK 0 (.aUp 0) (V4 n j) := by
  have hj' : (j : ℚ) + 1 ≤ 16 * n := by exact_mod_cast hj
  have hs : moveSrc (.aUp 0) (V4 n j) = V4 n (j + 1) := V4_next n j
  have hd : (V4 n (j + 1)).D.coeff 4 ≠ 0 := by
    rw [D_coeff_four]; simp [V4, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]
  refine ⟨?_, hs ▸ hd, fun _ => ?_, fun i h => by cases h; decide⟩
  · rw [hs]; exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V4, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V4, aE, pairOrd]; try (split_ifs <;> omega))
  · refine det_aUp 0 (by simp [aSign]) _ (by rwa [V4_next]) ?_
    rw [V4_next, D_eval_sum]
    simp [V4, Fin.prod_univ_five]
    intro h
    have : (1 + (j : ℚ)) ^ 5 = 0 := by linear_combination -h
    exact absurd this (by positivity)

theorem ok5 (n j : ℕ) (hj : j < 17 * n) : StepOK 0 (.aUp 1) (V5 n j) := by
  have hj' : (j : ℚ) + 1 ≤ 17 * n := by exact_mod_cast hj
  have hs : moveSrc (.aUp 1) (V5 n j) = V5 n (j + 1) := V5_next n j
  have hd : (V5 n (j + 1)).D.coeff 4 ≠ 0 := by
    rw [D_coeff_four]; simp [V5, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]
  refine ⟨?_, hs ▸ hd, fun _ => ?_, fun i h => by cases h; decide⟩
  · rw [hs]; exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V5, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V5, aE, pairOrd]; try (split_ifs <;> omega))
  · refine det_aUp 1 (by simp [aSign]) _ (by rwa [V5_next]) ?_
    rw [V5_next, D_eval_sum]
    simp [V5, Fin.prod_univ_five]
    intro h
    have : (1 + (j : ℚ)) ^ 5 = 0 := by linear_combination -h
    exact absurd this (by positivity)

theorem ok6 (n j : ℕ) (hj : j < 2 * n) : StepOK 0 (.bUp 0) (V6 n j) := by
  refine ⟨?_, ?_, fun h => h.elim, fun i h => by cases h⟩
  · exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V6, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V6, aE, pairOrd]; try (split_ifs <;> omega))
  · rw [moveSrc, D_coeff_four]; simp [V6, aE, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]

theorem ok7 (n j : ℕ) (hj : j < n) : StepOK 0 (.bUp 1) (V7 n j) := by
  refine ⟨?_, ?_, fun h => h.elim, fun i h => by cases h⟩
  · exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V7, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V7, aE, pairOrd]; try (split_ifs <;> omega))
  · rw [moveSrc, D_coeff_four]; simp [V7, aE, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]

theorem ok8 (n j : ℕ) (hj : j < n) : StepOK (2 * n) (.bDown 3) (V8 n j) := by
  have hj' : (j : ℚ) + 1 ≤ n := by exact_mod_cast hj
  have hs : moveSrc (.bDown 3) (V8 n j) = V8 n (j + 1) := V8_next n j
  have hd : (V8 n (j + 1)).D.coeff 4 ≠ 0 := by
    rw [D_coeff_four]; simp [V8, aE, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]
  refine ⟨?_, hs ▸ hd, fun _ => ?_, fun i h => by cases h⟩
  · rw [hs]; exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V8, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V8, aE, pairOrd]; try (split_ifs <;> omega))
  · refine det_bDown 3 _ (by rwa [V8_next]) ?_
    rw [V8_next, D_eval_sum]
    simp [V8, aE, Fin.prod_univ_five]
    intro h
    have : ((j : ℚ) + 1 + 16 * n) * (j + 1 + 17 * n) * (11 * n - j) * (12 * n - j) *
        (10 * n - j) = 0 := by linear_combination h
    have := mul_pos (mul_pos (mul_pos (mul_pos (by positivity : (0 : ℚ) < j + 1 + 16 * n)
      (by positivity : (0 : ℚ) < j + 1 + 17 * n)) (by linarith : (0 : ℚ) < 11 * n - j))
      (by linarith : (0 : ℚ) < 12 * n - j)) (by linarith : (0 : ℚ) < 10 * n - j)
    linarith

theorem ok9 (n j : ℕ) (hj : j < 2 * n) : StepOK (2 * n) (.bDown 4) (V9 n j) := by
  have hj' : (j : ℚ) + 1 ≤ 2 * n := by exact_mod_cast hj
  have hs : moveSrc (.bDown 4) (V9 n j) = V9 n (j + 1) := V9_next n j
  have hd : (V9 n (j + 1)).D.coeff 4 ≠ 0 := by
    rw [D_coeff_four]; simp [V9, aE, Fin.sum_univ_five]; intro h
    linarith [(j.cast_nonneg : (0:ℚ) ≤ j), (n.cast_nonneg : (0:ℚ) ≤ n)]
  refine ⟨?_, hs ▸ hd, fun _ => ?_, fun i h => by cases h⟩
  · rw [hs]; exact VC_of _ _ _ (fun i => by fin_cases i <;> simp [moveSrc, V9, aE] <;> omega)
      (by rw [Fin.sum_univ_five]; simp [moveSrc, V9, aE, pairOrd]; try (split_ifs <;> omega))
  · refine det_bDown 4 _ (by rwa [V9_next]) ?_
    rw [V9_next, D_eval_sum]
    simp [V9, aE, Fin.prod_univ_five]
    intro h
    have : ((j : ℚ) + 1 + 16 * n) * (j + 1 + 17 * n) * (11 * n - j) * (12 * n - j) *
        (10 * n - j) = 0 := by linear_combination h
    have := mul_pos (mul_pos (mul_pos (mul_pos (by positivity : (0 : ℚ) < j + 1 + 16 * n)
      (by positivity : (0 : ℚ) < j + 1 + 17 * n)) (by linarith : (0 : ℚ) < 11 * n - j))
      (by linarith : (0 : ℚ) < 12 * n - j)) (by linarith : (0 : ℚ) < 10 * n - j)
    linarith

theorem junction_eq (n : ℕ) : junction n = V8 n 0 := by
  simp only [junction, path123, walkEnd_append]
  rw [start_eq, walkEnd_replicate V1 _ V1_next, V1_V2, walkEnd_replicate (V2 n) _ (V2_next n),
    V2_V3, walkEnd_replicate (V3 n) _ (V3_next n), V3_V4, walkEnd_replicate (V4 n) _ (V4_next n),
    V4_V5, walkEnd_replicate (V5 n) _ (V5_next n), V5_V6, walkEnd_replicate (V6 n) _ (V6_next n),
    V6_V7, walkEnd_replicate (V7 n) _ (V7_next n), V7_V8]

theorem walkEnd_path4 (n : ℕ) : walkEnd (junction n) (path4 n) = V9 n (2 * n) := by
  rw [junction_eq, path4, walkEnd_append, walkEnd_replicate (V8 n) _ (V8_next n), V8_V9,
    walkEnd_replicate (V9 n) _ (V9_next n)]

theorem walk123_ok (n : ℕ) : WalkOK 0 startVertex (path123 n) := by
  simp only [path123, List.append_assoc]
  rw [start_eq]
  refine walkOK_append _ _ _ _ (walkOK_replicate 0 V1 _ V1_next _ fun j _ => ok1 j) ?_
  rw [walkEnd_replicate V1 _ V1_next, V1_V2]
  refine walkOK_append _ _ _ _ (walkOK_replicate 0 (V2 n) _ (V2_next n) _ fun j hj => ok2 n j hj) ?_
  rw [walkEnd_replicate (V2 n) _ (V2_next n), V2_V3]
  refine walkOK_append _ _ _ _ (walkOK_replicate 0 (V3 n) _ (V3_next n) _ fun j hj => ok3 n j hj) ?_
  rw [walkEnd_replicate (V3 n) _ (V3_next n), V3_V4]
  refine walkOK_append _ _ _ _ (walkOK_replicate 0 (V4 n) _ (V4_next n) _ fun j hj => ok4 n j hj) ?_
  rw [walkEnd_replicate (V4 n) _ (V4_next n), V4_V5]
  refine walkOK_append _ _ _ _ (walkOK_replicate 0 (V5 n) _ (V5_next n) _ fun j hj => ok5 n j hj) ?_
  rw [walkEnd_replicate (V5 n) _ (V5_next n), V5_V6]
  refine walkOK_append _ _ _ _ (walkOK_replicate 0 (V6 n) _ (V6_next n) _ fun j hj => ok6 n j hj) ?_
  rw [walkEnd_replicate (V6 n) _ (V6_next n), V6_V7]
  exact walkOK_replicate 0 (V7 n) _ (V7_next n) _ fun j hj => ok7 n j hj

theorem walk4_ok (n : ℕ) : WalkOK (2 * n) (junction n) (path4 n) := by
  rw [junction_eq, path4]
  refine walkOK_append _ _ _ _ (walkOK_replicate _ (V8 n) _ (V8_next n) _ fun j hj => ok8 n j hj) ?_
  rw [walkEnd_replicate (V8 n) _ (V8_next n), V8_V9]
  exact walkOK_replicate _ (V9 n) _ (V9_next n) _ fun j hj => ok9 n j hj

theorem junction_poles (n : ℕ) : ∀ p ∈ kP (junction n).a (junction n).b, p ≤ 0 := by
  intro p hp
  rw [junction_eq] at hp
  simp [V8, aE, kP, mem_ival] at hp
  omega

theorem junction_zeros (n : ℕ) (k : ℤ) (h1 : 1 ≤ k) (h2 : k ≤ 2 * n) :
    3 ≤ (kZ (junction n).a (junction n).b).count k := by
  rw [junction_eq]
  simp [V8, aE, kZ, count_ival]
  split_ifs <;> omega

end Meijer5255.CmfReadout
