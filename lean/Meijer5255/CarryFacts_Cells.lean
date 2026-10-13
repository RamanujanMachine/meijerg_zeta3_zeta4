/-
# Helper for `CarryFacts` [5]: the cell certificate for `ψ = c + 1` on the shells and windows

The breakpoints `cellPts` (sorted, `0` and `1` included) are all endpoints of the `psiRows`,
`shellRows` and `windowRows` intervals and all `j/15`, `j/10`; every one has denominator `≤ 19`.
On each open cell between two consecutive breakpoints, `ψ`, `⌊15f⌋`, `⌊10f⌋` and the shell/window
membership are constant, so they can be read off at the cell midpoint; the midpoint values are
checked by `decide +kernel` (`cells_check`).
-/
import Meijer5255.definitions

noncomputable section

namespace Meijer5255.CarryFacts.Cells

open Meijer5255

/-- The breakpoints as numerator/denominator pairs (sorted increasingly). -/
def cellPairs : List (ℕ × ℕ) :=
  [(0, 1), (1, 15), (1, 13), (1, 12), (1, 11), (1, 10), (2, 19), (1, 8), (2, 15), (2, 13),
   (3, 17), (2, 11), (1, 5), (3, 13), (4, 17), (4, 15), (3, 11), (5, 18), (5, 17), (3, 10),
   (4, 13), (5, 16), (1, 3), (4, 11), (7, 19), (5, 13), (7, 18), (2, 5), (5, 12), (8, 19),
   (5, 11), (7, 15), (8, 17), (9, 19), (1, 2), (8, 15), (7, 13), (6, 11), (9, 16), (7, 12),
   (10, 17), (3, 5), (7, 11), (11, 17), (2, 3), (11, 16), (9, 13), (7, 10), (12, 17), (8, 11),
   (11, 15), (14, 19), (3, 4), (4, 5), (13, 16), (9, 11), (16, 19), (13, 15), (7, 8), (15, 17),
   (9, 10), (10, 11), (11, 12), (14, 15), (15, 16), (16, 17), (17, 18), (18, 19), (1, 1)]

/-- The breakpoints as rationals. -/
def cellPts : List ℚ := cellPairs.map fun p => (p.1 : ℚ) / p.2

theorem cellPairs_den : ∀ p ∈ cellPairs, 0 < p.2 ∧ p.2 ≤ 29 := by decide +kernel

theorem cellPts_sorted : cellPts.Pairwise (· < ·) := by decide +kernel

theorem cellPts_zero : (0 : ℚ) ∈ cellPts := by decide +kernel

theorem cellPts_one : (1 : ℚ) ∈ cellPts := by decide +kernel

theorem psiRows_mem : ∀ r ∈ psiRows, r.1 ∈ cellPts ∧ r.2.1 ∈ cellPts := by decide +kernel

theorem shellRows_mem : ∀ r ∈ shellRows, r.1 ∈ cellPts ∧ r.2 ∈ cellPts := by decide +kernel

theorem windowRows_mem : ∀ r ∈ windowRows, r.1 ∈ cellPts ∧ r.2 ∈ cellPts := by decide +kernel

theorem fifteenths_mem : ∀ j ∈ List.range 16, ((j : ℕ) : ℚ) / 15 ∈ cellPts := by decide +kernel

theorem tenths_mem : ∀ j ∈ List.range 11, ((j : ℕ) : ℚ) / 10 ∈ cellPts := by decide +kernel

/-- The certificate: at the midpoint of every cell lying in a shell or a window, `ψ = c + 1`. -/
theorem cells_check : (cellPts.zip cellPts.tail).all (fun p =>
    !(inRows shellRows ((p.1 + p.2) / 2) || inRows windowRows ((p.1 + p.2) / 2)) ||
      decide ((psi ((p.1 + p.2) / 2) : ℤ) = cfun ((p.1 + p.2) / 2) + 1)) = true := by
  decide +kernel

/-! ### Generic cell lemmas -/

/-- A point of `(min L, max L)` off a sorted list lies strictly between two consecutive entries. -/
theorem locate : ∀ (L : List ℚ), L.Pairwise (· < ·) → ∀ f : ℚ, f ∉ L → (∃ q ∈ L, q < f) →
    (∃ q ∈ L, f < q) → ∃ p ∈ L.zip L.tail, p.1 < f ∧ f < p.2
  | [], _, _, _, ⟨_, hq, _⟩, _ => by simp at hq
  | [a], _, f, _, ⟨q, hq, h1⟩, ⟨q', hq', h2⟩ => by
    simp only [List.mem_singleton] at hq hq'
    subst hq hq'
    exact absurd (h1.trans h2) (lt_irrefl _)
  | a :: b :: L, hs, f, hf, ⟨q, hq, h1⟩, ⟨q', hq', h2⟩ => by
    have ha : a < f := by
      rcases List.mem_cons.1 hq with rfl | hq
      · exact h1
      · exact lt_trans (List.rel_of_pairwise_cons hs hq) h1
    have hfb : f ≠ b := fun h => hf (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    rcases lt_or_gt_of_ne hfb with hb | hb
    · exact ⟨(a, b), by simp, ha, hb⟩
    · have hq'' : q' ∈ b :: L := by
        rcases List.mem_cons.1 hq' with rfl | h
        · exact absurd (ha.trans h2) (lt_irrefl _)
        · exact h
      obtain ⟨p, hp, hp1, hp2⟩ := locate (b :: L) hs.of_cons f
        (fun h => hf (List.mem_cons_of_mem _ h)) ⟨b, List.mem_cons_self, hb⟩ ⟨q', hq'', h2⟩
      refine ⟨p, ?_, hp1, hp2⟩
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp ⊢
      exact Or.inr hp

/-- No entry of a sorted list lies strictly between two consecutive entries. -/
theorem consecutive : ∀ (L : List ℚ), L.Pairwise (· < ·) → ∀ p ∈ L.zip L.tail, ∀ q ∈ L,
    q ≤ p.1 ∨ p.2 ≤ q
  | [], _, _, hp, _, _ => by simp at hp
  | [_], _, _, hp, _, _ => by simp at hp
  | a :: b :: L, hs, p, hp, q, hq => by
    simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at hp
    rcases hp with rfl | hp
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact Or.inl le_rfl
      · rcases List.mem_cons.1 hq with rfl | hq
        · exact Or.inr le_rfl
        · exact Or.inr (List.rel_of_pairwise_cons hs.of_cons hq).le
    · rcases List.mem_cons.1 hq with rfl | hq
      · have hp1 : p.1 ∈ b :: L := (List.of_mem_zip hp).1
        exact Or.inl (List.rel_of_pairwise_cons hs hp1).le
      · exact consecutive (b :: L) hs.of_cons p (by simpa using hp) q hq

/-- Two points of `(0,1)` off `cellPts`, with the same position relative to every breakpoint,
have the same `ψ`, the same `c` and the same shell/window membership. -/
theorem transfer (f g : ℚ) (hf0 : 0 < f) (hf1 : f < 1) (hg0 : 0 < g) (hg1 : g < 1)
    (hf : f ∉ cellPts) (hg : g ∉ cellPts) (hT : ∀ q ∈ cellPts, q < f ↔ q < g) :
    psi f = psi g ∧ cfun f = cfun g ∧ inRows shellRows f = inRows shellRows g ∧
      inRows windowRows f = inRows windowRows g := by
  have hff : Int.fract f = f := Int.fract_eq_self.2 ⟨hf0.le, hf1⟩
  have hgg : Int.fract g = g := Int.fract_eq_self.2 ⟨hg0.le, hg1⟩
  have hlt : ∀ q ∈ cellPts, f < q ↔ g < q := fun q hq => by
    have hfq : q ≠ f := fun h => hf (h ▸ hq)
    have hgq : q ≠ g := fun h => hg (h ▸ hq)
    rw [lt_iff_le_and_ne, lt_iff_le_and_ne, ← not_lt, ← not_lt, hT q hq]
    exact ⟨fun h => ⟨h.1, fun e => hgq e.symm⟩, fun h => ⟨h.1, fun e => hfq e.symm⟩⟩
  have hrows : ∀ rows : List (ℚ × ℚ), (∀ r ∈ rows, r.1 ∈ cellPts ∧ r.2 ∈ cellPts) →
      inRows rows f = inRows rows g := by
    intro rows hr
    rw [Bool.eq_iff_iff]
    simp only [inRows, List.any_eq_true, decide_eq_true_eq, hff, hgg]
    exact exists_congr fun r => and_congr_right fun hm =>
      and_congr (hT _ (hr r hm).1) (hlt _ (hr r hm).2)
  -- floors: `⌊k f⌋ ≤ ⌊k g⌋`, by symmetry
  have key : ∀ x y : ℚ, 0 < x → x < 1 → x ∉ cellPts → (∀ q ∈ cellPts, q < x → q < y) →
      ∀ k : ℕ, 0 < k → (∀ j ∈ List.range (k + 1), ((j : ℕ) : ℚ) / k ∈ cellPts) →
      ⌊(k : ℚ) * x⌋ ≤ ⌊(k : ℚ) * y⌋ := by
    intro x y hx0 hx1 hx hxy k hk hB
    have hk' : (0 : ℚ) < k := by exact_mod_cast hk
    have hm0 : 0 ≤ ⌊(k : ℚ) * x⌋ := Int.floor_nonneg.2 (by positivity)
    have hmk : ⌊(k : ℚ) * x⌋ < k := Int.floor_lt.2 (by push_cast; nlinarith)
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = ⌊(k : ℚ) * x⌋ := ⟨_, Int.toNat_of_nonneg hm0⟩
    have hjm : ((j : ℕ) : ℚ) / k ∈ cellPts := hB j (List.mem_range.2 (by omega))
    have h1 : ((j : ℕ) : ℚ) / k ≤ x := by
      rw [div_le_iff₀ hk']
      have := Int.floor_le ((k : ℚ) * x)
      rw [← hj] at this
      push_cast at this
      linarith
    have h2 : ((j : ℕ) : ℚ) / k < x := lt_of_le_of_ne h1 fun h => hx (h ▸ hjm)
    have h3 := hxy _ hjm h2
    rw [div_lt_iff₀ hk'] at h3
    rw [← hj]
    exact Int.le_floor.2 (by push_cast; linarith)
  have hfl : ∀ k : ℕ, 0 < k → (∀ j ∈ List.range (k + 1), ((j : ℕ) : ℚ) / k ∈ cellPts) →
      ⌊(k : ℚ) * f⌋ = ⌊(k : ℚ) * g⌋ := fun k hk hB =>
    le_antisymm (key f g hf0 hf1 hf (fun q hq => (hT q hq).1) k hk hB)
      (key g f hg0 hg1 hg (fun q hq => (hT q hq).2) k hk hB)
  refine ⟨?_, ?_, hrows _ shellRows_mem, hrows _ windowRows_mem⟩
  · unfold psi
    rw [hff, hgg]
    congr 1
    refine List.map_congr_left fun r hr => ?_
    have hc : (r.1 < f ∧ f < r.2.1) ↔ (r.1 < g ∧ g < r.2.1) :=
      and_congr (hT _ (psiRows_mem r hr).1) (hlt _ (psiRows_mem r hr).2)
    simp only [hc]
  · have h15 := hfl 15 (by norm_num) fifteenths_mem
    have h10 := hfl 10 (by norm_num) tenths_mem
    push_cast at h15 h10
    unfold cfun
    rw [h15, h10]

end Meijer5255.CarryFacts.Cells
