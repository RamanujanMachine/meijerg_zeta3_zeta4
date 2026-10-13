/-
# Helper for `BaselineProfile` [6]: the cell certificate for `ψ = φ₁₀`

The breakpoints `cellPts` are the Farey fractions of order `19` in `[0,1]` (sorted).  They
contain all `j/k`, `k ≤ 19`, hence every breakpoint of `⌊k f⌋` (`k ≤ 19`), and all endpoints of
the `psiRows` intervals.  On each open cell between two consecutive breakpoints, `ψ` and `φ₁₀`
(which only depends on `⌊k f⌋`, `8 ≤ k ≤ 19`, and `c(f)`) are constant, so they can be compared
at the cell midpoint; the 120 midpoint values are checked by `decide +kernel` (`cells_check`).
`φ₁₀` is `1`-periodic since `∑ L = ∑ D` in every row.

`rowValC`, `pairsC`, `phiC` are verbatim copies of the node file's `rowVal`, `pairings10`,
`phi10` (the node file identifies them by `rfl`).  The generic cell lemmas `locate`,
`consecutive` and `fract_not_farey` are copied from `CarryFacts_Cells.lean` / `CarryFacts.lean`.
-/
import Meijer5255.definitions

noncomputable section

namespace Meijer5255.BaselineProfile.Cells

open Meijer5255

/-- Copy of the node file's `pairings10`. -/
def pairsC : List (List ℤ × List ℤ) :=
  [([8, 13, 13], [17, 17]), ([11, 11, 11], [14, 19]), ([9, 9, 14], [16, 16]),
   ([12, 12, 12], [18, 18]), ([11, 11, 14], [18, 18]), ([9, 9, 12], [14, 16]),
   ([10, 10, 10], [14, 16]), ([9, 11, 14], [17, 17]), ([9, 9, 14], [15, 17]),
   ([8, 13, 13], [16, 18])]

/-- Copy of the node file's `rowVal`. -/
def rowValC (LD : List ℤ × List ℤ) (x : ℚ) : ℤ :=
  cfun x - (LD.2.map fun d => ⌊(d : ℚ) * x⌋).sum + (LD.1.map fun l => ⌊(l : ℚ) * x⌋).sum

/-- Copy of the node file's `phi10`. -/
def phiC (x : ℚ) : ℤ :=
  pairsC.foldr (fun LD m => max m (rowValC LD x)) 0

/-- The breakpoints: the Farey fractions of order `19`, as numerator/denominator pairs
(sorted increasingly). -/
def cellPairs : List (ℕ × ℕ) :=
  [(0, 1), (1, 19), (1, 18), (1, 17), (1, 16), (1, 15), (1, 14), (1, 13), (1, 12), (1, 11),
   (1, 10), (2, 19), (1, 9), (2, 17), (1, 8), (2, 15), (1, 7), (2, 13), (3, 19), (1, 6),
   (3, 17), (2, 11), (3, 16), (1, 5), (4, 19), (3, 14), (2, 9), (3, 13), (4, 17), (1, 4),
   (5, 19), (4, 15), (3, 11), (5, 18), (2, 7), (5, 17), (3, 10), (4, 13), (5, 16), (6, 19),
   (1, 3), (6, 17), (5, 14), (4, 11), (7, 19), (3, 8), (5, 13), (7, 18), (2, 5), (7, 17),
   (5, 12), (8, 19), (3, 7), (7, 16), (4, 9), (5, 11), (6, 13), (7, 15), (8, 17), (9, 19),
   (1, 2), (10, 19), (9, 17), (8, 15), (7, 13), (6, 11), (5, 9), (9, 16), (4, 7), (11, 19),
   (7, 12), (10, 17), (3, 5), (11, 18), (8, 13), (5, 8), (12, 19), (7, 11), (9, 14), (11, 17),
   (2, 3), (13, 19), (11, 16), (9, 13), (7, 10), (12, 17), (5, 7), (13, 18), (8, 11), (11, 15),
   (14, 19), (3, 4), (13, 17), (10, 13), (7, 9), (11, 14), (15, 19), (4, 5), (13, 16), (9, 11),
   (14, 17), (5, 6), (16, 19), (11, 13), (6, 7), (13, 15), (7, 8), (15, 17), (8, 9), (17, 19),
   (9, 10), (10, 11), (11, 12), (12, 13), (13, 14), (14, 15), (15, 16), (16, 17), (17, 18),
   (18, 19), (1, 1)]

/-- The breakpoints as rationals. -/
def cellPts : List ℚ := cellPairs.map fun p => (p.1 : ℚ) / p.2

theorem cellPairs_den : ∀ p ∈ cellPairs, 0 < p.2 ∧ p.2 ≤ 29 := by decide +kernel

theorem cellPts_chain : cellPts.IsChain (· < ·) := by decide +kernel

theorem cellPts_sorted : cellPts.Pairwise (· < ·) :=
  List.isChain_iff_pairwise.1 cellPts_chain

theorem cellPts_zero : (0 : ℚ) ∈ cellPts := by decide +kernel

theorem cellPts_one : (1 : ℚ) ∈ cellPts := by decide +kernel

theorem psiRows_mem : ∀ r ∈ psiRows, r.1 ∈ cellPts ∧ r.2.1 ∈ cellPts := by decide +kernel

theorem floors_mem : ∀ k ∈ List.range 20, 0 < k →
    ∀ j ∈ List.range (k + 1), ((j : ℕ) : ℚ) / k ∈ cellPts := by decide +kernel

theorem pairsC_range : ∀ LD ∈ pairsC, ∀ d ∈ LD.1 ++ LD.2, 1 ≤ d ∧ d ≤ 19 := by decide +kernel

theorem pairsC_sum : ∀ LD ∈ pairsC, LD.1.sum = LD.2.sum := by decide +kernel

/-- The certificate: at the midpoint of every cell, `ψ = φ₁₀`. -/
theorem cells_check : (cellPts.zip cellPts.tail).all (fun p =>
    decide ((psi ((p.1 + p.2) / 2) : ℤ) = phiC ((p.1 + p.2) / 2))) = true := by
  decide +kernel

/-! ### Generic cell lemmas (copied from `CarryFacts_Cells.lean`) -/

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

/-! ### Transfer between points of the same cell -/

theorem foldr_congr (l : List (List ℤ × List ℤ)) (f g : ℚ)
    (h : ∀ LD ∈ l, rowValC LD f = rowValC LD g) :
    l.foldr (fun LD m => max m (rowValC LD f)) 0 = l.foldr (fun LD m => max m (rowValC LD g)) 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih fun LD hLD => h LD (List.mem_cons_of_mem _ hLD),
      h a List.mem_cons_self]

/-- The list coercion `List ℤ → List ℚ` hidden in `rowValC` (`d : ℚ` ranges over the cast list). -/
theorem map_coe (l : List ℤ) (x : ℚ) :
    (l.map fun d => ⌊(d : ℚ) * x⌋) = l.map (fun d : ℤ => ⌊(d : ℚ) * x⌋) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons] at ih ⊢; simp [List.flatMap_cons, ← ih]

/-- `φ₁₀` only depends on the floors `⌊k x⌋`, `1 ≤ k ≤ 19`. -/
theorem phiC_congr (f g : ℚ) (h : ∀ k : ℕ, 1 ≤ k → k ≤ 19 → ⌊(k : ℚ) * f⌋ = ⌊(k : ℚ) * g⌋) :
    phiC f = phiC g := by
  have hint : ∀ d : ℤ, 1 ≤ d → d ≤ 19 → ⌊(d : ℚ) * f⌋ = ⌊(d : ℚ) * g⌋ := fun d h1 h2 => by
    have e : (d : ℚ) = ((d.toNat : ℕ) : ℚ) := by exact_mod_cast (Int.toNat_of_nonneg (by omega)).symm
    rw [e]; exact h _ (by omega) (by omega)
  have hc : cfun f = cfun g := by
    have h15 := h 15 (by norm_num) (by norm_num)
    have h10 := h 10 (by norm_num) (by norm_num)
    push_cast at h15 h10
    unfold cfun; rw [h15, h10]
  have hrow : ∀ LD ∈ pairsC, rowValC LD f = rowValC LD g := fun LD hLD => by
    have hr := pairsC_range LD hLD
    unfold rowValC
    rw [map_coe, map_coe, map_coe, map_coe, hc, List.map_congr_left fun d hd => hint d (hr d (List.mem_append_right _ hd)).1
        (hr d (List.mem_append_right _ hd)).2,
      List.map_congr_left fun d hd => hint d (hr d (List.mem_append_left _ hd)).1
        (hr d (List.mem_append_left _ hd)).2]
  exact foldr_congr pairsC f g hrow

/-- Two points of `(0,1)` off `cellPts`, with the same position relative to every breakpoint,
have the same `ψ` and the same `φ₁₀`. -/
theorem transfer (f g : ℚ) (hf0 : 0 < f) (hf1 : f < 1) (hg0 : 0 < g) (hg1 : g < 1)
    (hf : f ∉ cellPts) (hg : g ∉ cellPts) (hT : ∀ q ∈ cellPts, q < f ↔ q < g) :
    psi f = psi g ∧ phiC f = phiC g := by
  have hff : Int.fract f = f := Int.fract_eq_self.2 ⟨hf0.le, hf1⟩
  have hgg : Int.fract g = g := Int.fract_eq_self.2 ⟨hg0.le, hg1⟩
  have hlt : ∀ q ∈ cellPts, f < q ↔ g < q := fun q hq => by
    have hfq : q ≠ f := fun h => hf (h ▸ hq)
    have hgq : q ≠ g := fun h => hg (h ▸ hq)
    rw [lt_iff_le_and_ne, lt_iff_le_and_ne, ← not_lt, ← not_lt, hT q hq]
    exact ⟨fun h => ⟨h.1, fun e => hgq e.symm⟩, fun h => ⟨h.1, fun e => hfq e.symm⟩⟩
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
  have hfl : ∀ k : ℕ, 1 ≤ k → k ≤ 19 → ⌊(k : ℚ) * f⌋ = ⌊(k : ℚ) * g⌋ := fun k hk1 hk2 => by
    have hB := floors_mem k (List.mem_range.2 (by omega)) (by omega)
    exact le_antisymm (key f g hf0 hf1 hf (fun q hq => (hT q hq).1) k (by omega) hB)
      (key g f hg0 hg1 hg (fun q hq => (hT q hq).2) k (by omega) hB)
  refine ⟨?_, phiC_congr f g hfl⟩
  unfold psi
  rw [hff, hgg]
  congr 1
  refine List.map_congr_left fun r hr => ?_
  have hc : (r.1 < f ∧ f < r.2.1) ↔ (r.1 < g ∧ g < r.2.1) :=
    and_congr (hT _ (psiRows_mem r hr).1) (hlt _ (psiRows_mem r hr).2)
  simp only [hc]

/-! ### Periodicity of `φ₁₀` -/

theorem floor_sum_fract (x : ℚ) (l : List ℤ) :
    (l.map fun d : ℤ => ⌊(d : ℚ) * x⌋).sum =
      (l.map fun d : ℤ => ⌊(d : ℚ) * Int.fract x⌋).sum + l.sum * ⌊x⌋ := by
  induction l with
  | nil => simp
  | cons d l ih =>
    have e : ⌊(d : ℚ) * x⌋ = ⌊(d : ℚ) * Int.fract x⌋ + d * ⌊x⌋ := by
      rw [← Int.floor_add_intCast]; congr 1; rw [Int.fract]; push_cast; ring
    simp only [List.map_cons, List.sum_cons, e, ih]
    ring

theorem cfun_fract (x : ℚ) : cfun x = cfun (Int.fract x) := by
  -- provenance: `CarryFacts.cfun_fract`
  have h : ∀ k : ℤ, ⌊(k : ℚ) * x⌋ = ⌊(k : ℚ) * Int.fract x⌋ + k * ⌊x⌋ := fun k => by
    rw [← Int.floor_add_intCast]; congr 1; rw [Int.fract]; push_cast; ring
  have h15 := h 15
  have h10 := h 10
  push_cast at h15 h10
  unfold cfun; rw [h15, h10]; ring

theorem phiC_fract (x : ℚ) : phiC x = phiC (Int.fract x) := by
  have hrow : ∀ LD ∈ pairsC, rowValC LD x = rowValC LD (Int.fract x) := fun LD hLD => by
    unfold rowValC
    rw [map_coe, map_coe, map_coe, map_coe, floor_sum_fract x LD.1, floor_sum_fract x LD.2, pairsC_sum LD hLD, ← cfun_fract]
    ring
  exact foldr_congr pairsC x (Int.fract x) hrow

/-! ### The cell statement -/

/-- For `0 < f < 1` off the Farey walls of order `19`, `ψ(f) = φ₁₀(f)`. -/
theorem psi_eq_phiC (f : ℚ) (h0 : 0 < f) (h1 : f < 1)
    (hf : ∀ a b : ℕ, 0 < b → b ≤ 29 → f ≠ (a : ℚ) / b) :
    (psi f : ℤ) = phiC f := by
  -- provenance: `CarryFacts.psi_eq_cfun_succ_on_cells`
  have hfB : f ∉ cellPts := fun hm => by
    rw [cellPts, List.mem_map] at hm
    obtain ⟨⟨a, b⟩, hp, he⟩ := hm
    exact hf a b (cellPairs_den _ hp).1 (cellPairs_den _ hp).2 he.symm
  obtain ⟨p, hp, hp1, hp2⟩ := locate _ cellPts_sorted f hfB
    ⟨0, cellPts_zero, h0⟩ ⟨1, cellPts_one, h1⟩
  have hcons := consecutive _ cellPts_sorted p hp
  obtain ⟨g, hg⟩ : ∃ g : ℚ, g = (p.1 + p.2) / 2 := ⟨_, rfl⟩
  have hlg : p.1 < g := by rw [hg]; linarith
  have hgr : g < p.2 := by rw [hg]; linarith
  have hgB : g ∉ cellPts := fun hm => by rcases hcons g hm with h | h <;> linarith
  have hT : ∀ q ∈ cellPts, q < f ↔ q < g := fun q hq => by
    rcases hcons q hq with h | h
    · exact iff_of_true (by linarith) (by linarith)
    · exact iff_of_false (by linarith) (by linarith)
  have hg0 : 0 < g := by rcases hcons 0 cellPts_zero with h | h <;> linarith
  have hg1 : g < 1 := by rcases hcons 1 cellPts_one with h | h <;> linarith
  obtain ⟨hpsi, hphi⟩ := transfer f g h0 h1 hg0 hg1 hfB hgB hT
  have hc' := List.all_eq_true.1 cells_check p hp
  rw [← hg, decide_eq_true_eq] at hc'
  rw [hpsi, hphi]
  exact hc'

/-- `{n/p}` avoids the Farey walls of order `29` (copy of `CarryFacts.fract_not_farey`). -/
theorem fract_not_farey (n p : ℕ) (hp : Eligible n p) (a b : ℕ) (hb0 : 0 < b) (hb : b ≤ 29) :
    Int.fract ((n : ℚ) / p) ≠ (a : ℚ) / b := by
  obtain ⟨hpr, h29, -, hnd⟩ := hp
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  intro heq
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hpr.ne_zero
  have hb0' : (b : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  rw [div_eq_div_iff hp0 hb0'] at heq
  have heqN : n % p * b = a * p := by exact_mod_cast heq
  have hdvd : p ∣ n % p * b := heqN ▸ dvd_mul_left p a
  rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
  · have hlt : n % p < p := Nat.mod_lt _ hpr.pos
    have h0 : n % p = 0 := by
      by_contra hne
      exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hne) h) (by omega)
    exact hnd (Nat.dvd_of_mod_eq_zero h0)
  · have := Nat.le_of_dvd hb0 h
    omega

end Meijer5255.BaselineProfile.Cells
