/-
# Helper for `WindowRootData.lean`: high roots of one interval, counting in `Icc`

* `hi_Icc`: the high roots (w.r.t. `k`, `p`) of the integers of `[a, b]` form the interval
  `[⌈(a-k)/p⌉, ⌊(b-k)/p⌋]`.
* `ceil_succ_div`: `⌈(m+1)/p⌉ = ⌊m/p⌋ + 1` for integers `m`.
* `count_Icc`: multiplicities in `(Icc a b).val`.
-/
import Meijer5255.definitions

open Finset

noncomputable section

namespace Meijer5255.WindowRootData

/-- The high roots of the integers of one interval. -/
theorem hi_Icc (p : ℕ) (hp : 0 < p) (k a b : ℤ) :
    (((Icc a b).val.filter fun x => (p : ℤ) ∣ x - k).map fun x => (x - k) / p) =
      (Icc ⌈((a : ℚ) - k) / p⌉ ⌊((b : ℚ) - k) / p⌋).val := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  apply (Multiset.Nodup.ext _ (Icc _ _).nodup).2
  · intro ℓ
    simp only [Multiset.mem_map, Multiset.mem_filter, Finset.mem_val, Finset.mem_Icc]
    rw [Int.ceil_le, Int.le_floor, div_le_iff₀ hp', le_div_iff₀ hp']
    constructor
    · rintro ⟨x, ⟨⟨hax, hxb⟩, c, hc⟩, rfl⟩
      rw [hc, Int.mul_ediv_cancel_left _ hpz]
      have e : (x : ℚ) - k = p * c := by exact_mod_cast hc
      have hax' : (a : ℚ) ≤ x := by exact_mod_cast hax
      have hxb' : (x : ℚ) ≤ b := by exact_mod_cast hxb
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      refine ⟨k + p * ℓ, ⟨⟨?_, ?_⟩, ℓ, by ring⟩, ?_⟩
      · have : (a : ℚ) ≤ k + p * ℓ := by linarith
        exact_mod_cast this
      · have : (k : ℚ) + p * ℓ ≤ b := by linarith
        exact_mod_cast this
      · rw [show k + p * ℓ - k = p * ℓ by ring, Int.mul_ediv_cancel_left _ hpz]
  · refine Multiset.Nodup.map_on ?_ ((Icc a b).nodup.filter _)
    intro x hx x' hx' h
    obtain ⟨c, hc⟩ := (Multiset.mem_filter.1 hx).2
    obtain ⟨c', hc'⟩ := (Multiset.mem_filter.1 hx').2
    rw [hc, hc', Int.mul_ediv_cancel_left _ hpz, Int.mul_ediv_cancel_left _ hpz] at h
    subst h
    linarith

/-- `⌈(m+1)/p⌉ = ⌊m/p⌋ + 1` for an integer `m`. -/
theorem ceil_succ_div (p : ℕ) (hp : 0 < p) (m : ℤ) :
    ⌈((m : ℚ) + 1) / p⌉ = ⌊(m : ℚ) / p⌋ + 1 := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  rw [Int.ceil_eq_iff]
  have h1 := Int.floor_le ((m : ℚ) / p)
  have h2 := Int.lt_floor_add_one ((m : ℚ) / p)
  set z := ⌊(m : ℚ) / p⌋
  rw [le_div_iff₀ hp'] at h1
  rw [div_lt_iff₀ hp'] at h2
  constructor
  · push_cast
    rw [lt_div_iff₀ hp']
    linarith
  · rw [div_le_iff₀ hp']
    have h3 : m < (z + 1) * p := by
      have : (m : ℚ) < ((z + 1) * p : ℤ) := by push_cast; linarith
      exact_mod_cast this
    have h4 : m + 1 ≤ (z + 1) * p := h3
    have : ((m + 1 : ℤ) : ℚ) ≤ ((z + 1) * p : ℤ) := by exact_mod_cast h4
    push_cast at this ⊢
    linarith

/-- Multiplicities in an interval. -/
theorem count_Icc (a b z : ℤ) :
    Multiset.count z (Icc a b).val = if a ≤ z ∧ z ≤ b then 1 else 0 := by
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (Icc a b).nodup (by simpa using h)
  · exact Multiset.count_eq_zero.2 (by simpa using h)

end Meijer5255.WindowRootData
