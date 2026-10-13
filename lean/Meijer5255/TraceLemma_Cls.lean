/-
# Helper for `TraceLemma.lean`: complete residue systems

For a complete system `R` of representatives modulo `p` (`∀ x, ∃! k ∈ R, p ∣ x - k`): the
bijection `R ≃ ZMod p`, `|R| = p`, complete residue sums of low-degree polynomials (pattern of
pfq54 `residue_block.sum_residues_dvd`, provenance), Wilson's theorem and the vanishing of
`∑_{s ≠ k} 1/(k - s)` modulo `p`, and the partition of a multiset of integers by classes.
-/
import Meijer5255.TraceLemma_Val

open Finset Polynomial

noncomputable section

namespace Meijer5255.TraceAux

open Meijer5255

set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] {R : Finset ℤ}

/-- Complete system of representatives modulo `p`. -/
def Complete (p : ℕ) (R : Finset ℤ) : Prop := ∀ x : ℤ, ∃! k, k ∈ R ∧ (p : ℤ) ∣ x - k

theorem cl_eq (hR : Complete p R) {k k' : ℤ} (hk : k ∈ R) (hk' : k' ∈ R)
    (h : (p : ℤ) ∣ k - k') : k = k' :=
  (hR k).unique ⟨hk, by simp⟩ ⟨hk', h⟩

theorem cl_ndvd (hR : Complete p R) {k s : ℤ} (hk : k ∈ R) (hs : s ∈ R) (hne : k ≠ s) :
    ¬ (p : ℤ) ∣ k - s := fun h => hne (cl_eq hR hk hs h)

theorem cl_zmod_inj (hR : Complete p R) {k k' : ℤ} (hk : k ∈ R) (hk' : k' ∈ R)
    (h : (k : ZMod p) = k') : k = k' :=
  (cl_eq hR hk' hk ((ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h)).symm

theorem cl_zmod_surj (hR : Complete p R) (x : ZMod p) : ∃ k ∈ R, (k : ZMod p) = x := by
  obtain ⟨k, ⟨hk, hd⟩, -⟩ := hR (x.val : ℤ)
  refine ⟨k, hk, ?_⟩
  have := (ZMod.intCast_eq_intCast_iff_dvd_sub k (x.val : ℤ) p).2 hd
  rw [this]; simp

theorem sum_R_zmod (hR : Complete p R) {M : Type*} [AddCommMonoid M] (f : ZMod p → M) :
    ∑ k ∈ R, f (k : ZMod p) = ∑ x : ZMod p, f x := by
  refine Finset.sum_bij (fun k _ => (k : ZMod p)) (fun _ _ => mem_univ _)
    (fun a ha b hb h => cl_zmod_inj hR ha hb h) (fun x _ => ?_) (fun _ _ => rfl)
  obtain ⟨k, hk, rfl⟩ := cl_zmod_surj hR x
  exact ⟨k, hk, rfl⟩

theorem card_R (hR : Complete p R) : R.card = p := by
  have := sum_R_zmod hR (M := ℕ) (fun _ => 1)
  simpa using this

/-- **Complete residue sums vanish** (`∑_{x ∈ 𝔽_p} x^i = 0` for `i < p - 1`). Adapted from
pfq54 `residue_block.sum_residues_dvd`. -/
theorem complete_sum_dvd_gen (hR : Complete p R) (T : ℤ[X]) (hT : T.natDegree ≤ p - 2) :
    (p : ℤ) ∣ ∑ k ∈ R, T.eval k := by
  have hp : p.Prime := Fact.out
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sum]
  set f := Int.castRingHom (ZMod p)
  have h1 : ∑ k ∈ R, ((T.eval k : ℤ) : ZMod p) = ∑ k ∈ R, (T.map f).eval (k : ZMod p) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.eval_map, show ((k : ℤ) : ZMod p) = f k by simp [f], Polynomial.eval₂_hom]
    rfl
  rw [h1, sum_R_zmod hR (fun x => (T.map f).eval x)]
  simp_rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [← Finset.mul_sum, FiniteField.sum_pow_lt_card_sub_one, mul_zero]
  have hi' := mem_range.mp hi
  have hdeg := Polynomial.natDegree_map_le (f := f) (p := T)
  rw [ZMod.card]
  have := hp.two_le
  omega

/-- Wilson's theorem over a complete system: `∏_{s ≠ k} (k - s) ≡ -1 (mod p)`. -/
theorem wilson_R (hR : Complete p R) {k : ℤ} (hk : k ∈ R) :
    (p : ℤ) ∣ (∏ s ∈ R.erase k, (k - s)) + 1 := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [add_eq_zero_iff_eq_neg, ← ZMod.prod_Ico_one_prime p]
  refine Finset.prod_bij (fun s _ => ((k : ZMod p) - s).val) (fun s hs => ?_) (fun a ha b hb h => ?_)
    (fun i hi => ?_) (fun s _ => by simp)
  · obtain ⟨hsk, hs⟩ := Finset.mem_erase.1 hs
    refine Finset.mem_Ico.2 ⟨Nat.one_le_iff_ne_zero.2 fun h0 => ?_, ZMod.val_lt _⟩
    rw [ZMod.val_eq_zero, sub_eq_zero] at h0
    exact hsk (cl_zmod_inj hR hs hk h0.symm)
  · have h' := ZMod.val_injective p h
    exact cl_zmod_inj hR (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb)
      (by linear_combination -h')
  · obtain ⟨hi1, hi2⟩ := Finset.mem_Ico.1 hi
    obtain ⟨s, hs, hseq⟩ := cl_zmod_surj hR ((k : ZMod p) - i)
    have hsk : s ≠ k := by
      rintro rfl
      have : ((i : ℕ) : ZMod p) = 0 := by linear_combination hseq
      rw [ZMod.natCast_eq_zero_iff] at this
      exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
    refine ⟨s, Finset.mem_erase.2 ⟨hsk, hs⟩, ?_⟩
    rw [hseq, sub_sub_cancel, ZMod.val_natCast_of_lt hi2]

/-- Fermat: `1/u ≡ u^{p-2} (mod p)` for an integer `u` prime to `p`. -/
theorem inv_cong_fermat {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) :
    ValGE p 1 ((u : ℚ)⁻¹ - (u : ℚ) ^ (p - 2)) := by
  have hp : p.Prime := Fact.out
  have hU := isPU_int (p := p) hu
  have hu' : (u : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hf := ZMod.pow_card_sub_one_eq_one hu'
  obtain ⟨w, hw⟩ : (p : ℤ) ∣ u ^ (p - 1) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [hf, sub_self]
  have e : (u : ℚ)⁻¹ - (u : ℚ) ^ (p - 2) = ((p : ℚ) * (-w)) * (u : ℚ)⁻¹ := by
    have h2 : (u : ℚ) ^ (p - 1) = (u : ℚ) ^ (p - 2) * u := by
      rw [← pow_succ]; congr 1; have := hp.two_le; omega
    have hw' : (u : ℚ) ^ (p - 1) - 1 = p * w := by exact_mod_cast hw
    field_simp [hU.1]
    linear_combination -hw' + h2
  rw [e]
  simpa using vge_mul (vge_p_mul (vge_int (p := p) (-w))) hU.inv.vge

/-- `∑_{s ≠ k} 1/(k - s) ≡ 0 (mod p)` over a complete system, `p` odd. -/
theorem inv_sum_R (hR : Complete p R) (hodd : p ≠ 2) {k : ℤ} (hk : k ∈ R) :
    ValGE p 1 (∑ s ∈ R.erase k, (((k - s : ℤ) : ℚ))⁻¹) := by
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  -- `∑_{s ∈ R} (k - s)^{p-2} ≡ 0`
  have hT : (p : ℤ) ∣ ∑ s ∈ R, ((C k - X : ℤ[X]) ^ (p - 2)).eval s := by
    refine complete_sum_dvd_gen hR _ ?_
    refine (natDegree_pow_le).trans ?_
    have : (C k - X : ℤ[X]).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_; simp
    nlinarith
  have hT' : ∑ s ∈ R.erase k, (k - s) ^ (p - 2) = ∑ s ∈ R, ((C k - X : ℤ[X]) ^ (p - 2)).eval s := by
    simp only [eval_pow, eval_sub, eval_C, eval_X]
    rw [Finset.sum_erase]
    rw [sub_self, zero_pow (by omega)]
  obtain ⟨w, hw⟩ := hT
  have hw' : ∑ s ∈ R.erase k, (((k - s : ℤ) : ℚ)) ^ (p - 2) = (p : ℚ) * w := by
    have := congrArg (fun z : ℤ => (z : ℚ)) (hT'.trans hw)
    push_cast at this ⊢; exact this
  have e : ∑ s ∈ R.erase k, (((k - s : ℤ) : ℚ))⁻¹ =
      ∑ s ∈ R.erase k, ((((k - s : ℤ) : ℚ))⁻¹ - (((k - s : ℤ) : ℚ)) ^ (p - 2)) + p * w := by
    rw [Finset.sum_sub_distrib, hw']; ring
  rw [e]
  refine vge_add (vge_sum _ _ _ fun s hs => inv_cong_fermat ?_) (vge_p_mul (vge_int w))
  exact cl_ndvd hR hk (Finset.mem_of_mem_erase hs) (Finset.ne_of_mem_erase hs).symm

/-! ### Partition of a multiset by classes -/

/-- `m = ∑_{s ∈ R} m|_{class s}`. -/
theorem msum_filter (hR : Complete p R) (m : Multiset ℤ) :
    ∑ s ∈ R, m.filter (fun y => (p : ℤ) ∣ y - s) = m := by
  ext y
  rw [Multiset.count_sum']
  simp only [Multiset.count_filter]
  obtain ⟨k, ⟨hk, hd⟩, hu⟩ := hR y
  rw [Finset.sum_eq_single k]
  · simp [hd]
  · intro s hs hsk
    rw [ite_eq_right_iff.2 (fun h => ?_)]
    exfalso
    exact hsk (hu s ⟨hs, h⟩)
  · intro h; exact absurd hk h

theorem card_hiRoots_sum (hR : Complete p R) (m : Multiset ℤ) :
    ∑ s ∈ R, ((hiRoots p s m).card : ℤ) = m.card := by
  have := congrArg Multiset.card (msum_filter hR m)
  rw [Multiset.card_sum] at this
  simp only [hiRoots, Multiset.card_map]
  exact_mod_cast this

theorem filter_fsum {ι : Type*} (q : ℤ → Prop) [DecidablePred q] (S : Finset ι)
    (f : ι → Multiset ℤ) : (∑ i ∈ S, f i).filter q = ∑ i ∈ S, (f i).filter q := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.filter_add, ih]

/-- The elements of `m` outside the class `k`, grouped by the other classes. -/
theorem filter_not_class (hR : Complete p R) {k : ℤ} (hk : k ∈ R) (m : Multiset ℤ) :
    m.filter (fun y => ¬ (p : ℤ) ∣ y - k) =
      ∑ s ∈ R.erase k, m.filter (fun y => (p : ℤ) ∣ y - s) := by
  conv_lhs => rw [← msum_filter hR m]
  rw [filter_fsum, ← Finset.add_sum_erase _ _ hk]
  rw [Multiset.filter_filter, Multiset.filter_eq_nil.2 (fun y _ h => h.1 h.2), zero_add]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [Multiset.filter_filter]
  refine Multiset.filter_congr fun y _ => ?_
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨fun h' => ?_, h⟩
    have : (p : ℤ) ∣ s - k := by
      have := dvd_sub h' h; simpa using this
    exact (Finset.ne_of_mem_erase hs) (cl_eq hR (Finset.mem_of_mem_erase hs) hk this)

theorem map_filter_class {α : Type*} (s : ℤ) (m : Multiset ℤ) (f : ℤ → α) :
    (m.filter (fun y => (p : ℤ) ∣ y - s)).map f = (hiRoots p s m).map (fun l => f (s + p * l)) := by
  rw [hiRoots, Multiset.map_map]
  refine Multiset.map_congr rfl fun y hy => ?_
  have hd := (Multiset.mem_filter.1 hy).2
  simp only [Function.comp]
  congr 1
  rw [Int.mul_ediv_cancel' hd]; ring

end Meijer5255.TraceAux
