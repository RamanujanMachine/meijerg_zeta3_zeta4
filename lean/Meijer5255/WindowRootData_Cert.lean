/-
# Helper for `WindowRootData.lean`: the Farey-29 chamber certificate at `t = 0`

For `f` in a window and `y ∈ (0, 1]`, the five `t = 0` high-root intervals
`endsQ f y` (the body of `WindowRootData.ends0`) are determined by the integers
`c_i = ⌊s_i f⌋` (slopes `s = 1, 2, 10, 11, 12, -1, -2, -17, -16`) and the bits
`b_i = [τ_i < y]` (floors) resp. `[τ_i ≤ y]` (ceilings), `τ_i = s_i f - c_i ∈ (0, 1)`.

On each of the 9 Farey-29 cells of the two windows the `c_i` are constant and the `τ_i` are
totally ordered (`geomB`, integer inequalities at the cell ends); the bits are then monotone along
that order (`chainB`). A kernel check (`decide +kernel`) over all `2⁹` bit vectors shows that every
monotone one gives `h ≥ -1`, the table's minimal intervals for `h = -1`, and one of the listed
`h = 0` intervals (`Zs`).

The cell data were generated from the paper's certificate (`second_order_certificate.json`,
recomputed by a short script); the Lean check does not depend on it.
-/
import Meijer5255.definitions

open Finset

noncomputable section

namespace Meijer5255.WindowRootData.Cert

/-! ### Integer data -/

/-- The slopes `s_i`: floor-type `0..6`, ceiling-type `7, 8`. -/
def slope : Fin 9 → ℤ := ![1, 2, 10, 11, 12, -1, -2, -17, -16]

/-- `[b]` as an integer. -/
def bitv (b : Bool) : ℤ := if b then 1 else 0

/-- The endpoint data from the integers `c` and the bits `b`. -/
def Eint (c : Fin 9 → ℤ) (b : Fin 9 → Bool) : Fin 5 → ℤ × ℤ :=
  ![(0, c 2 - bitv (b 2)), (c 0 - bitv (b 0) + 1, c 3 - bitv (b 3)),
    (c 1 - bitv (b 1) + 1, c 4 - bitv (b 4)), (c 7 + 1 - bitv (b 7), c 5 - bitv (b 5)),
    (c 8 + 1 - bitv (b 8), c 6 - bitv (b 6))]

/-- The `t = 0` endpoints (the body of `WindowRootData.ends0`). -/
def endsQ (f y : ℚ) : Fin 5 → ℤ × ℤ :=
  ![(⌊-y⌋ + 1, ⌊10 * f - y⌋), (⌊f - y⌋ + 1, ⌊11 * f - y⌋), (⌊2 * f - y⌋ + 1, ⌊12 * f - y⌋),
    (⌈-17 * f - y⌉, ⌊-f - y⌋), (⌈-16 * f - y⌉, ⌊-2 * f - y⌋)]

/-- Number of integers in `[L, U]`. -/
def icountC (L U : ℤ) : ℤ := max 0 (U - L + 1)

/-- `h = #N₀ + #N₁ + #N₂ - #D₀ - #D₁`. -/
def hcE (E : Fin 5 → ℤ × ℤ) : ℤ :=
  icountC (E 0).1 (E 0).2 + icountC (E 1).1 (E 1).2 + icountC (E 2).1 (E 2).2 -
    icountC (E 3).1 (E 3).2 - icountC (E 4).1 (E 4).2

/-- Boolean equality of endpoint data. -/
def eqE (E E' : Fin 5 → ℤ × ℤ) : Bool := (List.finRange 5).all fun i => E i == E' i

theorem eqE_spec {E E' : Fin 5 → ℤ × ℤ} (h : eqE E E' = true) : E = E' := by
  funext i
  have := List.all_eq_true.1 h i (List.mem_finRange i)
  simpa using this

/-- The minimal-class endpoints (table (S2)). -/
def Emin : Fin 2 → Fin 5 → ℤ × ℤ :=
  ![![(0, 0), (0, 0), (0, 0), (-2, -1), (-2, -1)],
    ![(0, 8), (1, 9), (2, 10), (-16, -2), (-15, -3)]]

/-- The `h = 0` endpoint data occurring on the windows. -/
def Zs : Fin 2 → List (Fin 5 → ℤ × ℤ) :=
  ![[![(0, 0), (0, 0), (0, 0), (-2, -1), (-1, -1)],
      ![(0, 0), (0, 0), (0, 0), (-2, -1), (-2, -2)]],
    [![(0, 8), (1, 9), (2, 10), (-15, -2), (-15, -3)],
      ![(0, 8), (1, 9), (1, 10), (-16, -2), (-15, -3)],
      ![(0, 9), (1, 9), (2, 10), (-16, -2), (-15, -3)]]]

/-- The certified properties of endpoint data. -/
def goodB (w : Fin 2) (E : Fin 5 → ℤ × ℤ) : Bool :=
  decide (-1 ≤ hcE E) && (!(hcE E == -1) || eqE E (Emin w)) &&
    (!(hcE E == 0) || (Zs w).any (eqE E))

theorem goodB_spec {w : Fin 2} {E : Fin 5 → ℤ × ℤ} (h : goodB w E = true) :
    -1 ≤ hcE E ∧ (hcE E = -1 → E = Emin w) ∧ (hcE E = 0 → E ∈ Zs w) := by
  simp only [goodB, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, fun e => ?_, fun e => ?_⟩
  · rcases h2 with h2 | h2
    · exact absurd e h2
    · exact eqE_spec h2
  · rcases h3 with h3 | h3
    · exact absurd e h3
    · obtain ⟨E', hE', h⟩ := List.any_eq_true.1 h3
      rwa [eqE_spec h]

/-- Monotonicity of the bits along the order `ord` of the `τ`'s. -/
def chainB (ord : Fin 9 → Fin 9) (b : Fin 9 → Bool) : Bool :=
  (List.finRange 8).all fun m => !(b (ord m.succ)) || b (ord m.castSucc)

/-- The kernel-checked statement for one cell: every monotone bit vector is good. -/
def CellOK (w : Fin 2) (c : Fin 9 → ℤ) (ord : Fin 9 → Fin 9) : Prop :=
  ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 : Bool,
    chainB ord ![b0, b1, b2, b3, b4, b5, b6, b7, b8] = true →
      goodB w (Eint c ![b0, b1, b2, b3, b4, b5, b6, b7, b8]) = true

instance (w : Fin 2) (c : Fin 9 → ℤ) (ord : Fin 9 → Fin 9) : Decidable (CellOK w c ord) := by
  unfold CellOK; infer_instance

/-- The geometry of a cell `(a₁/q₁, a₂/q₂)`: the integers `c_i` and the order `ord` of the `τ_i`
are valid at both ends (integer inequalities). -/
def geomB (a1 q1 a2 q2 : ℤ) (c : Fin 9 → ℤ) (ord : Fin 9 → Fin 9) : Bool :=
  decide (0 < q1) && decide (0 < q2) &&
    (List.finRange 9).all (fun i => decide (c i * q1 ≤ slope i * a1) &&
      decide (slope i * a1 ≤ (c i + 1) * q1) && decide (c i * q2 ≤ slope i * a2) &&
      decide (slope i * a2 ≤ (c i + 1) * q2)) &&
    (List.finRange 8).all (fun m => decide (slope (ord m.castSucc) ≠ slope (ord m.succ)) &&
      decide ((slope (ord m.castSucc) - slope (ord m.succ)) * a1 ≤
        (c (ord m.castSucc) - c (ord m.succ)) * q1) &&
      decide ((slope (ord m.castSucc) - slope (ord m.succ)) * a2 ≤
        (c (ord m.castSucc) - c (ord m.succ)) * q2))

/-! ### From the cell data to the endpoints -/

theorem slope_ne_zero (i : Fin 9) : slope i ≠ 0 := by
  fin_cases i <;> decide

/-- An affine function `s x - d` (`s ≠ 0`) that is `≤ 0` at both ends is `< 0` inside. -/
theorem lin_strict (s : ℤ) (hs : s ≠ 0) (d α β f : ℚ) (hα : (s : ℚ) * α ≤ d)
    (hβ : (s : ℚ) * β ≤ d) (h1 : α < f) (h2 : f < β) : (s : ℚ) * f < d := by
  rcases lt_or_gt_of_ne hs with h | h
  · have : (s : ℚ) < 0 := by exact_mod_cast h
    nlinarith
  · have : (0 : ℚ) < s := by exact_mod_cast h
    nlinarith

theorem geom_spec {a1 q1 a2 q2 : ℤ} {c : Fin 9 → ℤ} {ord : Fin 9 → Fin 9}
    (h : geomB a1 q1 a2 q2 c ord = true) (f : ℚ)
    (hf : (a1 : ℚ) / q1 < f ∧ f < (a2 : ℚ) / q2) :
    (∀ i, (c i : ℚ) < slope i * f ∧ (slope i : ℚ) * f < c i + 1) ∧
      ∀ m : Fin 8, (slope (ord m.castSucc) : ℚ) * f - c (ord m.castSucc) <
        slope (ord m.succ) * f - c (ord m.succ) := by
  simp only [geomB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange,
    true_implies] at h
  obtain ⟨⟨⟨hq1, hq2⟩, hc⟩, ho⟩ := h
  have hq1' : (0 : ℚ) < q1 := by exact_mod_cast hq1
  have hq2' : (0 : ℚ) < q2 := by exact_mod_cast hq2
  -- the ends as rationals
  have key : ∀ (s : ℤ) (d : ℤ), s * a1 ≤ d * q1 → s * a2 ≤ d * q2 → s ≠ 0 →
      (s : ℚ) * f < d := by
    intro s d h1 h2 hs
    refine lin_strict s hs d _ _ f ?_ ?_ hf.1 hf.2
    · rw [mul_div_assoc', div_le_iff₀ hq1']; exact_mod_cast h1
    · rw [mul_div_assoc', div_le_iff₀ hq2']; exact_mod_cast h2
  refine ⟨fun i => ⟨?_, ?_⟩, fun m => ?_⟩
  · obtain ⟨⟨⟨h1, -⟩, h2⟩, -⟩ := hc i
    have := key (-slope i) (-c i) (by linarith) (by linarith) (neg_ne_zero.2 (slope_ne_zero i))
    push_cast at this; linarith
  · obtain ⟨⟨⟨-, h1⟩, -⟩, h2⟩ := hc i
    have := key (slope i) (c i + 1) (by linarith) (by linarith) (slope_ne_zero i)
    push_cast at this; linarith
  · obtain ⟨⟨hne, h1⟩, h2⟩ := ho m
    have := key _ _ h1 h2 (sub_ne_zero.2 hne)
    push_cast at this; linarith

theorem floor_bit (x y : ℚ) (c : ℤ) (h1 : (c : ℚ) < x) (h2 : x < c + 1) (hy0 : 0 < y)
    (hy1 : y ≤ 1) : ⌊x - y⌋ = c - bitv (decide (x - c < y)) := by
  rw [Int.floor_eq_iff]
  by_cases h : x - c < y
  · simp only [h, decide_true, bitv, ite_true]; push_cast; constructor <;> linarith
  · simp only [h, decide_false, bitv]; push_cast; constructor <;> linarith

theorem ceil_bit (x y : ℚ) (c : ℤ) (h1 : (c : ℚ) < x) (h2 : x < c + 1) (hy0 : 0 < y)
    (hy1 : y ≤ 1) : ⌈x - y⌉ = c + 1 - bitv (decide (x - c ≤ y)) := by
  rw [Int.ceil_eq_iff]
  by_cases h : x - c ≤ y
  · simp only [h, decide_true, bitv, ite_true]; push_cast; constructor <;> linarith
  · simp only [h, decide_false, bitv]; push_cast; constructor <;> linarith

/-- The bits at `(f, y)`. -/
def bits (c : Fin 9 → ℤ) (f y : ℚ) : Fin 9 → Bool := fun i =>
  if (i : ℕ) < 7 then decide ((slope i : ℚ) * f - c i < y) else decide ((slope i : ℚ) * f - c i ≤ y)

theorem endsQ_eq (c : Fin 9 → ℤ) (f y : ℚ)
    (hc : ∀ i, (c i : ℚ) < slope i * f ∧ (slope i : ℚ) * f < c i + 1) (hy : 0 < y ∧ y ≤ 1) :
    endsQ f y = Eint c (bits c f y) := by
  have hfl : ⌊-y⌋ = -1 := by rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
  have F : ∀ (i : Fin 9) (u : ℚ), (i : ℕ) < 7 → (slope i : ℚ) = u →
      ⌊u * f - y⌋ = c i - bitv (bits c f y i) := by
    intro i u hi hu
    have h := hc i
    rw [hu] at h
    rw [floor_bit (u * f) y (c i) h.1 h.2 hy.1 hy.2]
    congr 2
    simp [bits, hi, hu]
  have C : ∀ (i : Fin 9) (u : ℚ), ¬ (i : ℕ) < 7 → (slope i : ℚ) = u →
      ⌈u * f - y⌉ = c i + 1 - bitv (bits c f y i) := by
    intro i u hi hu
    have h := hc i
    rw [hu] at h
    rw [ceil_bit (u * f) y (c i) h.1 h.2 hy.1 hy.2]
    congr 2
    simp [bits, hi, hu]
  have e0 := F 0 1 (by decide) (by simp [slope])
  have e1 := F 1 2 (by decide) (by simp [slope])
  have e2 := F 2 10 (by decide) (by simp [slope])
  have e3 := F 3 11 (by decide) (by simp [slope])
  have e4 := F 4 12 (by decide) (by simp [slope])
  have e5 := F 5 (-1) (by decide) (by simp [slope])
  have e6 := F 6 (-2) (by decide) (by simp [slope])
  have e7 := C 7 (-17) (by decide) (by simp [slope])
  have e8 := C 8 (-16) (by decide) (by simp [slope])
  rw [one_mul] at e0
  rw [neg_one_mul] at e5
  rw [neg_mul] at e6 e7 e8
  funext i
  fin_cases i <;> simp only [endsQ, Eint] <;> ext <;> simp [hfl, e0, e1, e2, e3, e4, e5, e6, e7, e8]

theorem chain_bits (c : Fin 9 → ℤ) (ord : Fin 9 → Fin 9) (f y : ℚ)
    (ho : ∀ m : Fin 8, (slope (ord m.castSucc) : ℚ) * f - c (ord m.castSucc) <
        slope (ord m.succ) * f - c (ord m.succ)) :
    chainB ord (bits c f y) = true := by
  simp only [chainB, List.all_eq_true, List.mem_finRange, true_implies, Bool.or_eq_true,
    Bool.not_eq_true']
  intro m
  have hm := ho m
  by_cases hb : bits c f y (ord m.succ) = true
  · right
    have hle : (slope (ord m.succ) : ℚ) * f - c (ord m.succ) ≤ y := by
      unfold bits at hb
      split_ifs at hb with h
      · exact (of_decide_eq_true hb).le
      · exact of_decide_eq_true hb
    unfold bits
    split_ifs with h
    · exact decide_eq_true (by linarith)
    · exact decide_eq_true (by linarith)
  · left; simpa using hb

/-- **One cell.** -/
theorem cell_good (w : Fin 2) (a1 q1 a2 q2 : ℤ) (c : Fin 9 → ℤ) (ord : Fin 9 → Fin 9)
    (hG : geomB a1 q1 a2 q2 c ord = true) (hK : CellOK w c ord) (f y : ℚ)
    (hf : (a1 : ℚ) / q1 < f ∧ f < (a2 : ℚ) / q2) (hy : 0 < y ∧ y ≤ 1) :
    goodB w (endsQ f y) = true := by
  obtain ⟨hc, ho⟩ := geom_spec hG f hf
  have heta : ∀ b : Fin 9 → Bool, ![b 0, b 1, b 2, b 3, b 4, b 5, b 6, b 7, b 8] = b := by
    intro b; funext i; fin_cases i <;> rfl
  have h := hK (bits c f y 0) (bits c f y 1) (bits c f y 2) (bits c f y 3) (bits c f y 4)
    (bits c f y 5) (bits c f y 6) (bits c f y 7) (bits c f y 8)
  rw [heta] at h
  rw [endsQ_eq c f y hc hy]
  exact h (chain_bits c ord f y ho)

/-! ### The cell data -/

/-- `⌊s_i f⌋` on the first window `(1/10, 2/19)`. -/
def c0 : Fin 9 → ℤ := ![0, 0, 1, 1, 1, -1, -1, -2, -2]

/-- `⌊s_i f⌋` on the second window `(11/12, 15/16)`. -/
def c1 : Fin 9 → ℤ := ![0, 1, 9, 10, 11, -1, -2, -16, -15]

theorem ok00 : CellOK 0 c0 ![2, 0, 3, 1, 4, 7, 8, 6, 5] := by decide +kernel
theorem ok01 : CellOK 0 c0 ![2, 0, 3, 1, 7, 4, 8, 6, 5] := by decide +kernel
theorem ok10 : CellOK 1 c1 ![4, 5, 3, 6, 2, 8, 7, 1, 0] := by decide +kernel
theorem ok12 : CellOK 1 c1 ![5, 4, 6, 3, 8, 2, 7, 1, 0] := by decide +kernel
theorem ok13 : CellOK 1 c1 ![5, 4, 6, 8, 3, 7, 2, 1, 0] := by decide +kernel
theorem ok14 : CellOK 1 c1 ![5, 8, 6, 4, 7, 3, 2, 1, 0] := by decide +kernel
theorem ok15 : CellOK 1 c1 ![5, 8, 6, 7, 4, 3, 2, 1, 0] := by decide +kernel
theorem ok16 : CellOK 1 c1 ![8, 5, 7, 6, 4, 3, 2, 1, 0] := by decide +kernel

/-- **The first window** `(1/10, 2/19)`: cells `(1/10, 3/29)`, `(3/29, 2/19)`. -/
theorem cert_w0 (f y : ℚ) (hf : 1 / 10 < f ∧ f < 2 / 19) (h29 : f * 29 ≠ 3)
    (hy : 0 < y ∧ y ≤ 1) : goodB 0 (endsQ f y) = true := by
  rcases lt_or_gt_of_ne (show f ≠ 3 / 29 by intro h; apply h29; rw [h]; norm_num) with h | h
  · exact cell_good 0 1 10 3 29 c0 _ (by decide +kernel) ok00 f y
      ⟨by push_cast; linarith, by push_cast; linarith⟩ hy
  · exact cell_good 0 3 29 2 19 c0 _ (by decide +kernel) ok01 f y
      ⟨by push_cast; linarith, by push_cast; linarith⟩ hy

/-- **The second window** `(11/12, 15/16)`: cells cut at `23/25, 12/13, 25/27, 13/14, 27/29,
14/15`. -/
theorem cert_w1 (f y : ℚ) (hf : 11 / 12 < f ∧ f < 15 / 16)
    (hF : ∀ q : ℕ, 0 < q → q ≤ 29 → ∀ m : ℤ, f * q ≠ m) (hy : 0 < y ∧ y ≤ 1) :
    goodB 1 (endsQ f y) = true := by
  have ne : ∀ (q : ℕ) (m : ℤ), 0 < q → q ≤ 29 → f ≠ (m : ℚ) / q := by
    intro q m hq hq29 h
    apply hF q hq hq29 m
    rw [h]; field_simp
  rcases lt_or_gt_of_ne (ne 25 23 (by norm_num) (by norm_num)) with h1 | h1
  · exact cell_good 1 11 12 23 25 c1 _ (by decide +kernel) ok10 f y
      ⟨by push_cast; linarith, by push_cast at h1 ⊢; linarith⟩ hy
  rcases lt_or_gt_of_ne (ne 13 12 (by norm_num) (by norm_num)) with h2 | h2
  · exact cell_good 1 23 25 12 13 c1 _ (by decide +kernel) ok10 f y
      ⟨by push_cast at h1 ⊢; linarith, by push_cast at h2 ⊢; linarith⟩ hy
  rcases lt_or_gt_of_ne (ne 27 25 (by norm_num) (by norm_num)) with h3 | h3
  · exact cell_good 1 12 13 25 27 c1 _ (by decide +kernel) ok12 f y
      ⟨by push_cast at h2 ⊢; linarith, by push_cast at h3 ⊢; linarith⟩ hy
  rcases lt_or_gt_of_ne (ne 14 13 (by norm_num) (by norm_num)) with h4 | h4
  · exact cell_good 1 25 27 13 14 c1 _ (by decide +kernel) ok13 f y
      ⟨by push_cast at h3 ⊢; linarith, by push_cast at h4 ⊢; linarith⟩ hy
  rcases lt_or_gt_of_ne (ne 29 27 (by norm_num) (by norm_num)) with h5 | h5
  · exact cell_good 1 13 14 27 29 c1 _ (by decide +kernel) ok14 f y
      ⟨by push_cast at h4 ⊢; linarith, by push_cast at h5 ⊢; linarith⟩ hy
  rcases lt_or_gt_of_ne (ne 15 14 (by norm_num) (by norm_num)) with h6 | h6
  · exact cell_good 1 27 29 14 15 c1 _ (by decide +kernel) ok15 f y
      ⟨by push_cast at h5 ⊢; linarith, by push_cast at h6 ⊢; linarith⟩ hy
  · exact cell_good 1 14 15 15 16 c1 _ (by decide +kernel) ok16 f y
      ⟨by push_cast at h6 ⊢; linarith, by push_cast; linarith⟩ hy

end Meijer5255.WindowRootData.Cert
