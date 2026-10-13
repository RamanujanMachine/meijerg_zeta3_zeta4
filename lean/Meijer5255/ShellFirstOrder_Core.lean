/-
# Helper for `ShellFirstOrder` [2]–[7]: the core of the first-order shell argument

Copies of the objects of `ShellFirstOrder.lean` (`exT`, `Tq`, `classOf`, equal by `rfl`;
`resCount` is `Gen.rc`), the lemmas [2], [3], [5] (moved here so that [4], [6], [7] can use them),
the shape of the minimal classes (`shell_shape`, from the certificate [1] and [2]), and the proofs
of [4], [6], [7]. The heart is `core`: at a pole `-j = k + pℓ₀` the local scaling `Gen.scale`
writes `a_j, b_j` through the coefficients of the class kernel `N_k / D_k` at `ℓ₀`; on a minimal
class (`h_k = -1`) the kernel is the common `U = NU/DU` shifted by `ε_k` (`shell_shape`), the
harmonic index is `ε_k - ℓ₀` (`index_eq`), and the unit part is `≡ -𝒬(k)` (`Tq_supp`,
`Gen.unit_part`, Wilson); elsewhere `𝒬(k) = 0` and the valuations alone suffice.
-/
import Meijer5255.ShellFirstOrder_Cert
import Meijer5255.ShellFirstOrder_Gen

open Finset Polynomial

noncomputable section

namespace Meijer5255.ShellFirstOrder.Core

open Meijer5255 Meijer5255.ShellFirstOrder.Gen

/-- `1 + c(a) - d(a)` (copy of `ShellFirstOrder.exT`). -/
def exT (n p a : ℕ) : ℕ := 1 + rc (numRoots n) p a - rc (denRoots n) p a

/-- Copy of `ShellFirstOrder.Tq`. -/
def Tq (n p : ℕ) : ℤ[X] := ∏ a ∈ range p, (X - C (a : ℤ)) ^ exT n p a

/-- Copy of `ShellFirstOrder.classOf`. -/
def classOf (p j : ℕ) : ℕ := (p - j % p) % p

/-- The shift `ε = ⌊(2n - k)/p⌋ = 2t + ⌊2f - k/p⌋` of the class `k`. -/
def epsK (n p k : ℕ) : ℤ := ⌊((2 * n - k : ℤ) : ℚ) / p⌋

/-! ### [2] High roots for every lift (moved from `ShellFirstOrder.lean`) -/

/-- One interval: the high roots of `[a, b]` at the residue `k` form `[⌈(a-k)/p⌉, ⌊(b-k)/p⌋]`. -/
theorem hi_Icc (p : ℕ) (hp : 0 < p) (k a b : ℤ) :
    hiRoots p k (Icc a b).val =
      (Icc ⌈((a - k : ℤ) : ℚ) / p⌉ ⌊((b - k : ℤ) : ℚ) / p⌋).val := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold hiRoots
  refine (Multiset.Nodup.ext ?_ (Finset.nodup _)).mpr ?_
  · refine Multiset.Nodup.map_on ?_ (Multiset.Nodup.filter _ (Finset.nodup _))
    intro x hx y hy hxy
    obtain ⟨-, ⟨c, hc⟩⟩ := Multiset.mem_filter.mp hx
    obtain ⟨-, ⟨d, hd⟩⟩ := Multiset.mem_filter.mp hy
    rw [hc, hd, Int.mul_ediv_cancel_left _ hpz, Int.mul_ediv_cancel_left _ hpz] at hxy
    subst hxy
    linarith
  intro l
  rw [Multiset.mem_map, Finset.mem_val, mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hp',
    le_div_iff₀ hp']
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx, ⟨c, hc⟩⟩ := Multiset.mem_filter.mp hx
    rw [Finset.mem_val, mem_Icc] at hx
    rw [hc, Int.mul_ediv_cancel_left _ hpz]
    constructor
    · have : (a : ℚ) - k ≤ (p : ℚ) * c := by exact_mod_cast (by linarith : a - k ≤ p * c)
      push_cast; linarith
    · have : (p : ℚ) * c ≤ (b : ℚ) - k := by exact_mod_cast (by linarith : p * c ≤ b - k)
      push_cast; linarith
  · rintro ⟨h1, h2⟩
    refine ⟨k + p * l, Multiset.mem_filter.mpr ⟨?_, ⟨l, by ring⟩⟩, ?_⟩
    · rw [Finset.mem_val, mem_Icc]
      push_cast at h1 h2
      constructor
      · have : ((a - k : ℤ) : ℚ) ≤ ((p * l : ℤ) : ℚ) := by push_cast; linarith
        have := Int.cast_le.mp this
        linarith
      · have : ((p * l : ℤ) : ℚ) ≤ ((b - k : ℤ) : ℚ) := by push_cast; linarith
        have := Int.cast_le.mp this
        linarith
    · rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hpz]


theorem hi_add (p : ℕ) (k : ℤ) (s t : Multiset ℤ) :
    hiRoots p k (s + t) = hiRoots p k s + hiRoots p k t := by
  unfold hiRoots; rw [Multiset.filter_add, Multiset.map_add]

theorem floor_lift (n p k : ℕ) (hp : 0 < p) (u : ℤ) :
    ⌊((u * n - k : ℤ) : ℚ) / p⌋ =
      u * ⌊(n : ℚ) / p⌋ + ⌊u * Int.fract ((n : ℚ) / p) - k / p⌋ := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : ((u * n - k : ℤ) : ℚ) / p =
      ((u * ⌊(n : ℚ) / p⌋ : ℤ) : ℚ) + (u * Int.fract ((n : ℚ) / p) - k / p) := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [e, Int.floor_intCast_add]

theorem ceil_lift (n p k : ℕ) (hp : 0 < p) (u : ℤ) :
    ⌈((u * n - k : ℤ) : ℚ) / p⌉ =
      u * ⌊(n : ℚ) / p⌋ + ⌈u * Int.fract ((n : ℚ) / p) - k / p⌉ := by
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have e : ((u * n - k : ℤ) : ℚ) / p =
      ((u * ⌊(n : ℚ) / p⌋ : ℤ) : ℚ) + (u * Int.fract ((n : ℚ) / p) - k / p) := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [e, Int.ceil_intCast_add]

theorem ceil_succ (p : ℕ) (hp : 0 < p) (m : ℤ) :
    ⌈((m + 1 : ℤ) : ℚ) / p⌉ = ⌊(m : ℚ) / p⌋ + 1 := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  rw [Int.ceil_eq_iff]
  have h1 := Int.floor_le ((m : ℚ) / p)
  have h2 := Int.lt_floor_add_one ((m : ℚ) / p)
  rw [le_div_iff₀ hp'] at h1
  rw [div_lt_iff₀ hp'] at h2
  have h3 : m < p * (⌊(m : ℚ) / p⌋ + 1) := by exact_mod_cast (by linarith : (m : ℚ) < p * (⌊(m : ℚ) / p⌋ + 1))
  have h4 : m + 1 ≤ p * (⌊(m : ℚ) / p⌋ + 1) := h3
  have h4' : ((m + 1 : ℤ) : ℚ) ≤ p * (⌊(m : ℚ) / p⌋ + 1) := by exact_mod_cast h4
  constructor
  · push_cast
    rw [lt_div_iff₀ hp']
    linarith
  · rw [div_le_iff₀ hp']
    push_cast at h4' ⊢
    linarith

theorem hiRoots_lift (n p k : ℕ) (hp : 0 < p) :
    hiRoots p k (numRoots n) =
        (Icc (⌊-((k : ℚ) / p)⌋ + 1)
            (10 * ⌊(n : ℚ) / p⌋ + ⌊10 * Int.fract ((n : ℚ) / p) - k / p⌋)).val +
          (Icc (⌊(n : ℚ) / p⌋ + ⌊Int.fract ((n : ℚ) / p) - k / p⌋ + 1)
            (11 * ⌊(n : ℚ) / p⌋ + ⌊11 * Int.fract ((n : ℚ) / p) - k / p⌋)).val +
          (Icc (2 * ⌊(n : ℚ) / p⌋ + ⌊2 * Int.fract ((n : ℚ) / p) - k / p⌋ + 1)
            (12 * ⌊(n : ℚ) / p⌋ + ⌊12 * Int.fract ((n : ℚ) / p) - k / p⌋)).val ∧
      hiRoots p k (denRoots n) =
        (Icc (-17 * ⌊(n : ℚ) / p⌋ + ⌈-17 * Int.fract ((n : ℚ) / p) - k / p⌉)
            (-⌊(n : ℚ) / p⌋ + ⌊-Int.fract ((n : ℚ) / p) - k / p⌋)).val +
          (Icc (-16 * ⌊(n : ℚ) / p⌋ + ⌈-16 * Int.fract ((n : ℚ) / p) - k / p⌉)
            (-2 * ⌊(n : ℚ) / p⌋ + ⌊-2 * Int.fract ((n : ℚ) / p) - k / p⌋)).val := by
  -- the endpoint identities `⌊(un - k)/p⌋ = ut + ⌊uf - y⌋` etc.
  have F : ∀ u : ℤ, ⌊((u * n - k : ℤ) : ℚ) / p⌋ =
      u * ⌊(n : ℚ) / p⌋ + ⌊u * Int.fract ((n : ℚ) / p) - k / p⌋ := floor_lift n p k hp
  have C : ∀ u : ℤ, ⌈((u * n - k : ℤ) : ℚ) / p⌉ =
      u * ⌊(n : ℚ) / p⌋ + ⌈u * Int.fract ((n : ℚ) / p) - k / p⌉ := ceil_lift n p k hp
  have S : ∀ u : ℤ, ⌈((u * n + 1 - k : ℤ) : ℚ) / p⌉ =
      u * ⌊(n : ℚ) / p⌋ + ⌊u * Int.fract ((n : ℚ) / p) - k / p⌋ + 1 := fun u => by
    rw [show u * n + 1 - k = (u * n - k) + 1 by ring, ceil_succ p hp, ← F u]
  refine ⟨?_, ?_⟩
  · rw [numRoots, hi_add, hi_add, hi_Icc p hp, hi_Icc p hp, hi_Icc p hp]
    have e1 := S 0; have e2 := S 1; have e3 := S 2; have e4 := F 10; have e5 := F 11
    have e6 := F 12
    simp only [zero_mul, one_mul, zero_add, Int.fract] at e1 e2 e3 e4 e5 e6 ⊢
    push_cast at e1 e2 e3 e4 e5 e6 ⊢
    rw [e1, e2, e3, e4, e5, e6]
    simp
  · rw [denRoots, hi_add, hi_Icc p hp, hi_Icc p hp]
    have e1 := C (-17); have e2 := F (-1); have e3 := C (-16); have e4 := F (-2)
    simp only [neg_mul, one_mul, Int.fract] at e1 e2 e3 e4 ⊢
    push_cast at e1 e2 e3 e4 ⊢
    rw [e1, e2, e3, e4]
    simp

/-! ### [3] Separation -/

theorem separation (n p : ℕ) (hp : Eligible n p) :
    ∀ x ∈ numRoots n + denRoots n, ∀ x' ∈ numRoots n + denRoots n, x ≠ x' →
      ¬ ((p : ℤ) ^ 2 ∣ x - x') := by
  have hb : ∀ x ∈ numRoots n + denRoots n, -(17 * n : ℤ) ≤ x ∧ x ≤ 12 * n := fun x hx => by
    simp only [numRoots, denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hx
    omega
  intro x hx x' hx' hne hd
  have h1 := hb x hx
  have h2 := hb x' hx'
  have hp2 : (30 * n : ℤ) < (p : ℤ) ^ 2 := by exact_mod_cast hp.2.2.1
  obtain ⟨c, hc⟩ := hd
  rcases lt_trichotomy c 0 with h | h | h
  · nlinarith
  · subst h; apply hne; linarith
  · nlinarith

/-! ### [5] Harmonic numbers modulo `p` -/

theorem harm_split (p : ℕ) [Fact p.Prime] (r m : ℕ) (hr : 1 ≤ r) (hm : m < p ^ 2) :
    ValGE p 0 (harm r (m / p)) ∧ ValGE p 1 ((p : ℚ) ^ r * harm r m - harm r (m / p)) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hmp : m / p < p := Nat.div_lt_of_lt_mul (by rw [← pow_two]; exact hm)
  -- a term `1/k^r` with `p ∤ k` has valuation `0`
  have hunit : ∀ k : ℕ, 0 < k → ¬ p ∣ k → padicValRat p (1 / (k : ℚ) ^ r) = 0 := by
    intro k hk hnd
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    rw [padicValRat.div one_ne_zero (pow_ne_zero _ hk0), padicValRat.one, padicValRat.pow,
      padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hnd]
    simp
  refine ⟨vsum _ _ _ fun k hk => ?_, ?_⟩
  · obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
    right
    rw [hunit k hk1 fun h => by have := Nat.le_of_dvd hk1 h; omega]
  · have hsplit : (p : ℚ) ^ r * harm r m =
        ∑ k ∈ (Icc 1 m).filter (fun k => p ∣ k), (p : ℚ) ^ r * (1 / (k : ℚ) ^ r) +
        ∑ k ∈ (Icc 1 m).filter (fun k => ¬ p ∣ k), (p : ℚ) ^ r * (1 / (k : ℚ) ^ r) := by
      rw [harm, Finset.mul_sum, Finset.sum_filter_add_sum_filter_not]
    have hmul : ∑ k ∈ (Icc 1 m).filter (fun k => p ∣ k), (p : ℚ) ^ r * (1 / (k : ℚ) ^ r) =
        harm r (m / p) := by
      rw [harm]
      refine Finset.sum_nbij' (fun k => k / p) (fun i => p * i) (fun k hk => ?_) (fun i hi => ?_)
        (fun k hk => ?_) (fun i hi => ?_) (fun k hk => ?_)
      · obtain ⟨hk, ⟨c, rfl⟩⟩ := mem_filter.mp hk
        obtain ⟨hk1, hk2⟩ := mem_Icc.mp hk
        rw [mem_Icc, Nat.mul_div_cancel_left _ hp.pos]
        refine ⟨by rcases Nat.eq_zero_or_pos c with h | h <;> simp_all; omega, ?_⟩
        exact (Nat.le_div_iff_mul_le hp.pos).mpr (by linarith)
      · obtain ⟨hi1, hi2⟩ := mem_Icc.mp hi
        refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith [hp.pos], ?_⟩, dvd_mul_right _ _⟩
        have := (Nat.le_div_iff_mul_le hp.pos).mp hi2
        linarith
      · obtain ⟨-, ⟨c, rfl⟩⟩ := mem_filter.mp hk
        simp [Nat.mul_div_cancel_left _ hp.pos]
      · simp [Nat.mul_div_cancel_left _ hp.pos]
      · obtain ⟨-, ⟨c, rfl⟩⟩ := mem_filter.mp hk
        simp only [Nat.mul_div_cancel_left _ hp.pos]
        push_cast
        rw [mul_pow]
        field_simp
    rw [hsplit, hmul, add_sub_cancel_left]
    refine vsum _ _ _ fun k hk => ?_
    obtain ⟨hk, hnd⟩ := mem_filter.mp hk
    obtain ⟨hk1, -⟩ := mem_Icc.mp hk
    right
    have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [padicValRat.mul (pow_ne_zero _ hp0) (by positivity), hunit k hk1 hnd, padicValRat.pow,
      padicValRat.self hp.one_lt]
    omega

/-! ### The shape of the minimal classes -/

theorem shellRows_eq : shellRows = Cert.tbl.map Prod.fst := rfl

/-- `f = {n/p}` avoids the Farey fractions of order `≤ 29`. -/
theorem farey_free (n p : ℕ) (hp : Eligible n p) :
    ∀ q : ℕ, 0 < q → q ≤ 29 → ∀ m : ℤ, Int.fract ((n : ℚ) / p) * q ≠ m := by
  intro q hq0 hq m hm
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
  rw [Int.fract] at hm
  have e : (n : ℚ) * q = p * (m + ⌊(n : ℚ) / p⌋ * q) := by
    field_simp at hm ⊢; linarith
  have e' : ((n * q : ℕ) : ℤ) = p * (m + ⌊(n : ℚ) / p⌋ * q) := by exact_mod_cast e
  have hd : (p : ℤ) ∣ ((n * q : ℕ) : ℤ) := ⟨_, e'⟩
  rw [Int.natCast_dvd_natCast] at hd
  rcases (Nat.Prime.dvd_mul hp.1).mp hd with h | h
  · exact hp.2.2.2 h
  · have := Nat.le_of_dvd hq0 h; have := hp.2.1; omega

/-- The class count `c_k - d_k` is the `t = 0` count `h(f, k/p)`. -/
theorem count_eq (n p k : ℕ) (hp : 0 < p) (hk : k < p) :
    (rc (numRoots n) p k : ℤ) - rc (denRoots n) p k =
      Cert.hc0 (Int.fract ((n : ℚ) / p)) ((k : ℚ) / p) := by
  rw [rc_eq_card_hiRoots p hp k hk, rc_eq_card_hiRoots p hp k hk]
  obtain ⟨h1, h2⟩ := hiRoots_lift n p k hp
  rw [h1, h2]
  simp only [Multiset.card_add, Finset.card_val, Int.card_Icc, Nat.cast_add, Cert.hc0, Cert.icnt]
  set f := Int.fract ((n : ℚ) / p)
  set y := (k : ℚ) / p
  set t := ⌊(n : ℚ) / p⌋
  have ht : 0 ≤ t := Int.floor_nonneg.mpr (by positivity)
  have hf : 0 ≤ f := Int.fract_nonneg _
  have m1 : ⌊-y⌋ ≤ ⌊10 * f - y⌋ := Int.floor_mono (by linarith)
  have m2 : ⌊f - y⌋ ≤ ⌊11 * f - y⌋ := Int.floor_mono (by linarith)
  have m3 : ⌊2 * f - y⌋ ≤ ⌊12 * f - y⌋ := Int.floor_mono (by linarith)
  have m4 : ⌈-17 * f - y⌉ ≤ ⌊-f - y⌋ + 1 :=
    (Int.ceil_le_floor_add_one _).trans (by have := Int.floor_mono (show -17 * f - y ≤ -f - y by linarith); omega)
  have m5 : ⌈-16 * f - y⌉ ≤ ⌊-2 * f - y⌋ + 1 :=
    (Int.ceil_le_floor_add_one _).trans (by have := Int.floor_mono (show -16 * f - y ≤ -2 * f - y by linarith); omega)
  rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega),
    Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
  rw [max_eq_right (by omega), max_eq_right (by omega), max_eq_right (by omega),
    max_eq_right (by omega), max_eq_right (by omega)]
  ring

/-- **Shape of the classes.** On a shell, `d_k ≤ c_k + 1` for every class, and all minimal
classes have the same high roots up to the shift `ε_k`. -/
theorem shell_shape (n p : ℕ) (hp : Eligible n p) (hs : inRows shellRows ((n : ℚ) / p)) :
    (∀ k < p, (rc (denRoots n) p k : ℤ) ≤ rc (numRoots n) p k + 1) ∧
    ∃ NU DU : Multiset ℤ, ∀ k < p, (rc (denRoots n) p k : ℤ) = rc (numRoots n) p k + 1 →
      hiRoots p k (numRoots n) = NU.map (· + epsK n p k) ∧
        hiRoots p k (denRoots n) = DU.map (· + epsK n p k) := by
  have hp0 : 0 < p := hp.1.pos
  set f := Int.fract ((n : ℚ) / p) with hfdef
  set t := ⌊(n : ℚ) / p⌋ with htdef
  -- the row of the table
  obtain ⟨row, hrow, hf⟩ : ∃ row ∈ Cert.tbl, row.1.1 < f ∧ f < row.1.2 := by
    unfold inRows at hs
    rw [shellRows_eq, List.any_eq_true] at hs
    obtain ⟨r, hr, hd⟩ := hs
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
    exact ⟨row, hrow, of_decide_eq_true hd⟩
  have hF := farey_free n p hp
  have hy : ∀ k < p, 0 ≤ (k : ℚ) / p ∧ (k : ℚ) / p < 1 := fun k hk => by
    have : (0 : ℚ) < p := by exact_mod_cast hp0
    exact ⟨by positivity, (div_lt_one this).mpr (by exact_mod_cast hk)⟩
  have hcert := fun k (hk : k < p) => Cert.cert_main f ((k : ℚ) / p) row hrow hf hF (hy k hk)
  refine ⟨fun k hk => ?_, ?_⟩
  · have := count_eq n p k hp0 hk
    rw [← hfdef] at this
    have := (hcert k hk).1
    omega
  set r := row.2
  let L : ℕ → ℤ := fun i => (r.getD i (0, 0)).1
  let U : ℕ → ℤ := fun i => (r.getD i (0, 0)).2
  refine ⟨(Icc (L 0 - 2 * t) (U 0 + 8 * t)).val + (Icc (L 1 - t) (U 1 + 9 * t)).val +
      (Icc (L 2) (U 2 + 10 * t)).val,
    (Icc (L 3 - 19 * t) (U 3 - 3 * t)).val + (Icc (L 4 - 18 * t) (U 4 - 4 * t)).val,
    fun k hk hmin => ?_⟩
  have hh : Cert.hc0 f ((k : ℚ) / p) = -1 := by
    have := count_eq n p k hp0 hk; rw [← hfdef] at this; omega
  have hrow2 := (hcert k hk).2 hh
  set y := (k : ℚ) / p with hydef
  have heps : epsK n p k = 2 * t + ⌊2 * f - y⌋ := by
    have := floor_lift n p k hp0 2
    unfold epsK
    rw [show (2 * (n : ℤ) - k) = (2 * n - k : ℤ) from rfl] at this ⊢
    exact this
  have gd : ∀ i, r.getD i (0, 0) = ((Cert.e0 f y).map
      (fun e => (e.1 - ⌊2 * f - y⌋, e.2 - ⌊2 * f - y⌋))).getD i (0, 0) := fun i => by
    rw [hrow2]
  have g0 := gd 0; have g1 := gd 1; have g2 := gd 2; have g3 := gd 3; have g4 := gd 4
  simp only [Cert.e0, List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    at g0 g1 g2 g3 g4
  obtain ⟨h1, h2⟩ := hiRoots_lift n p k hp0
  rw [← hfdef, ← htdef, ← hydef] at h1 h2
  have shift : ∀ a b e : ℤ, (Icc a b).val.map (· + e) = (Icc (a + e) (b + e)).val := fun a b e =>
    Multiset.map_add_right_Icc a b e
  rw [h1, h2, Multiset.map_add, Multiset.map_add, Multiset.map_add, shift, shift, shift, shift,
    shift, heps]
  simp only [L, U, g0, g1, g2, g3, g4]
  refine ⟨?_, ?_⟩
  · congr 3 <;> ring_nf
  · congr 2 <;> ring_nf

/-! ### Cardinalities, the degree of `𝒬` ([4]) -/

theorem card_numRoots (n : ℕ) : Multiset.card (numRoots n) = 30 * n := by
  rw [numRoots, Multiset.card_add, Multiset.card_add, Finset.card_val, Finset.card_val,
    Finset.card_val, Int.card_Icc, Int.card_Icc, Int.card_Icc]
  omega

theorem card_denRoots (n : ℕ) : Multiset.card (denRoots n) = 30 * n + 2 := by
  rw [denRoots, Multiset.card_add, Finset.card_val, Finset.card_val, Int.card_Icc, Int.card_Icc]
  omega

/-- **[4]** `deg 𝒬 ≤ p - 2` (pfq54 `Tp_natDegree`, with the root-count bound from the shape). -/
theorem Tq_natDegree (n p : ℕ) (hp : Eligible n p) (hs : inRows shellRows ((n : ℚ) / p)) :
    (Tq n p).natDegree ≤ p - 2 := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hge := (shell_shape n p hp hs).1
  rw [Tq, natDegree_prod_of_monic (s := range p) (f := fun a => (X - C (a : ℤ)) ^ exT n p a)
    fun a _ => (monic_X_sub_C _).pow _]
  have hdeg : ∀ a ∈ range p, ((X - C (a : ℤ)) ^ exT n p a).natDegree = exT n p a := fun a _ => by
    rw [(monic_X_sub_C (a : ℤ)).natDegree_pow, natDegree_X_sub_C, mul_one]
  rw [Finset.sum_congr rfl hdeg]
  have hle : ∀ a ∈ range p, exT n p a + rc (denRoots n) p a = 1 + rc (numRoots n) p a :=
    fun a ha => by
      have := hge a (mem_range.mp ha)
      unfold exT
      omega
  have hsum := Finset.sum_congr rfl hle
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_rc p, sum_rc p, card_numRoots,
    card_denRoots, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hsum
  have := hp.1.two_le
  show ∑ a ∈ range p, exT n p a ≤ p - 2
  omega

theorem Tq_eval (n p : ℕ) (t : ℤ) :
    (Tq n p).eval t = ∏ a ∈ range p, (t - a) ^ exT n p a := by
  rw [Tq, eval_prod]
  exact Finset.prod_congr rfl fun a _ => by rw [eval_pow, eval_sub, eval_X, eval_C]

/-- Off the minimal classes `𝒬(k) = 0`. -/
theorem Tq_zero (n p k : ℕ) (hk : k < p)
    (h : (rc (denRoots n) p k : ℤ) ≤ rc (numRoots n) p k) : (Tq n p).eval (k : ℤ) = 0 := by
  rw [Tq_eval]
  refine Finset.prod_eq_zero (mem_range.mpr hk) ?_
  have hex : exT n p k ≠ 0 := by unfold exT; omega
  rw [sub_self, zero_pow hex]

/-- On a minimal class, `𝒬(k) D̄*(k) = -N̄*(k)` in `𝔽_p` (Wilson; pfq54 `Tp_supp`). -/
theorem Tq_supp (n p k : ℕ) [Fact p.Prime] (hk : k < p)
    (hge : ∀ a < p, (rc (denRoots n) p a : ℤ) ≤ rc (numRoots n) p a + 1)
    (hmin : (rc (denRoots n) p k : ℤ) = rc (numRoots n) p k + 1) :
    (((Tq n p).eval (k : ℤ) : ℤ) : ZMod p) *
        ∏ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (denRoots n) p a =
      -∏ a ∈ (range p).erase k, ((k : ZMod p) - a) ^ rc (numRoots n) p a := by
  have hk0 : exT n p k = 0 := by unfold exT; omega
  rw [Tq_eval, ← Finset.mul_prod_erase _ _ (mem_range.mpr hk), sub_self, hk0, pow_zero, one_mul,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  have e : ∀ a ∈ (range p).erase k, ((((k : ℤ) - a) ^ exT n p a : ℤ) : ZMod p) *
      ((k : ZMod p) - a) ^ rc (denRoots n) p a =
        ((k : ZMod p) - a) * ((k : ZMod p) - a) ^ rc (numRoots n) p a := fun a ha => by
    have hexp : exT n p a + rc (denRoots n) p a = 1 + rc (numRoots n) p a := by
      have := hge a (mem_range.mp (Finset.mem_of_mem_erase ha))
      unfold exT
      omega
    rw [Int.cast_pow, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, ← pow_add, hexp, pow_add,
      pow_one]
  rw [Finset.prod_congr rfl e, Finset.prod_mul_distrib, prod_erase_sub p k hk, neg_one_mul]

/-! ### Classes of poles and the harmonic index -/

theorem classOf_lt (p j : ℕ) (hp : 0 < p) : classOf p j < p := Nat.mod_lt _ hp

theorem classOf_dvd (p j : ℕ) (hp : 0 < p) : (p : ℤ) ∣ -(j : ℤ) - (classOf p j : ℤ) := by
  obtain ⟨r, q, hr, rfl⟩ : ∃ r q, r < p ∧ j = r + p * q :=
    ⟨j % p, j / p, Nat.mod_lt _ hp, (Nat.mod_add_div j p).symm⟩
  unfold classOf
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
  rcases Nat.eq_zero_or_pos r with h0 | h0
  · subst h0
    rw [Nat.sub_zero, Nat.mod_self]
    exact ⟨-(q : ℤ), by push_cast; ring⟩
  · rw [Nat.mod_eq_of_lt (by omega : p - r < p)]
    exact ⟨-(q : ℤ) - 1, by push_cast [Nat.cast_sub hr.le]; ring⟩

theorem classOf_eq (p j k : ℕ) (hp : 0 < p) (hk : k < p) (h : (p : ℤ) ∣ -(j : ℤ) - k) :
    classOf p j = k := by
  have h1 := classOf_dvd p j hp
  have h2 := classOf_lt p j hp
  have h3 : (p : ℤ) ∣ (k : ℤ) - classOf p j := by
    have := dvd_sub h1 h; rwa [show -(j : ℤ) - classOf p j - (-(j : ℤ) - k) =
      (k : ℤ) - classOf p j by ring] at this
  obtain ⟨c, hc⟩ := h3
  have : c = 0 := by
    rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
    · nlinarith
    · exact hc0
    · nlinarith
  subst this
  omega

/-- The harmonic index of the pole `-j = k + pℓ₀` is `ε_k - ℓ₀`. -/
theorem index_eq (n p j : ℕ) (hp : 0 < p) :
    (((j + 2 * n) / p : ℕ) : ℤ) =
      epsK n p (classOf p j) - (-(j : ℤ) - classOf p j) / p := by
  obtain ⟨c, hc⟩ := classOf_dvd p j hp
  have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
  unfold epsK
  rw [hc, Int.mul_ediv_cancel_left _ hp', Rat.floor_intCast_div_natCast, Int.natCast_ediv]
  rw [show ((j + 2 * n : ℕ) : ℤ) = (2 * n - classOf p j : ℤ) + p * (-c) by push_cast; linarith,
    Int.add_mul_ediv_left _ _ hp']
  ring

/-! ### Translation invariance of `pfCoeff` -/

theorem pfCoeff_shift (Nl Dl : Multiset ℤ) (z e : ℤ) (hz : z ∉ Nl) :
    pfCoeff (Nl.map (· + e)) (Dl.map (· + e)) (z + e) = pfCoeff Nl Dl z := by
  have hz' : z + e ∉ Nl.map (· + e) := fun h => by
    obtain ⟨w, hw, hwe⟩ := Multiset.mem_map.mp h
    exact hz (by rw [show z = w by linarith]; exact hw)
  have hinj : Function.Injective (· + e : ℤ → ℤ) := add_left_injective e
  have hcnt : (Dl.map (· + e)).count (z + e) = Dl.count z :=
    Multiset.count_map_eq_count' _ _ hinj z
  have hfil : (Dl.map (· + e)).filter (· ≠ z + e) = (Dl.filter (· ≠ z)).map (· + e) := by
    rw [Multiset.filter_map]
    congr 1
    exact Multiset.filter_congr fun w _ => by simp
  rw [pfCoeff_eq _ _ _ hz', pfCoeff_eq _ _ _ hz, hcnt, hfil, pr_shift, pr_shift, Ls_shift,
    Ls_shift]

/-! ### The core: local factorization and the class sums -/

/-- The poles of the class `k`. -/
def poles (n p k : ℕ) : Finset ℕ := (Icc n (17 * n)).filter (fun j => classOf p j = k)

/-- **Core of [6] and [7].** -/
theorem core (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p) (hs : inRows shellRows ((n : ℚ) / p)) :
    ∃ α β : ℕ → ℚ, ∃ I : Finset ℕ, (∀ i, ValGE p 0 (α i) ∧ ValGE p 0 (β i)) ∧
      (∀ i ∈ I, i < p) ∧
      (∀ j ∈ Icc n (17 * n),
        ValGE p 1 (aCoef n j / p +
          (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * α ((j + 2 * n) / p)) ∧
        ValGE p 1 (bCoef n j +
          (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * β ((j + 2 * n) / p))) ∧
      (∀ k < p, (Tq n p).eval (k : ℤ) = 0 ∨
        (Set.InjOn (fun j => (j + 2 * n) / p) (poles n p k) ∧
          (poles n p k).image (fun j => (j + 2 * n) / p) = I)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp0 : 0 < p := hp.1.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
  obtain ⟨hge, NU, DU, hshape⟩ := shell_shape n p hp hs
  classical
  let α : ℕ → ℚ := fun i =>
    if ValGE p 0 (pfCoeff NU DU (-(i : ℤ))).1 then (pfCoeff NU DU (-(i : ℤ))).1 else 0
  let β : ℕ → ℚ := fun i =>
    if ValGE p 0 (pfCoeff NU DU (-(i : ℤ))).2 then (pfCoeff NU DU (-(i : ℤ))).2 else 0
  -- the index set of a minimal class
  let I : Finset ℕ :=
    if h : ∃ k₀ < p, (rc (denRoots n) p k₀ : ℤ) = rc (numRoots n) p k₀ + 1 then
      (poles n p (Classical.choose h)).image (fun j => (j + 2 * n) / p)
    else ∅
  -- facts about a pole `-j`, `j ∈ [n, 17n]`
  have hxN : ∀ j ∈ Icc n (17 * n), -(j : ℤ) ∉ numRoots n := fun j hj h => by
    simp only [numRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at h
    have := (mem_Icc.mp hj).1
    omega
  have hxD : ∀ j ∈ Icc n (17 * n), -(j : ℤ) ∈ denRoots n := fun j hj => by
    have := mem_Icc.mp hj
    simp only [denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc]
    left; constructor <;> push_cast <;> omega
  -- separation of the high roots from the pole
  have hsepl : ∀ j ∈ Icc n (17 * n), ∀ m ∈ hiRoots p (classOf p j) (numRoots n) +
      hiRoots p (classOf p j) (denRoots n), m ≠ (-(j : ℤ) - classOf p j) / p →
      ¬ (p : ℤ) ∣ (-(j : ℤ) - classOf p j) / p - m := by
    intro j hj m hm hne hd
    rw [← hiRoots_add] at hm
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hm
    obtain ⟨hy, hyk⟩ := Multiset.mem_filter.mp hy
    have hxk := classOf_dvd p j hp0
    apply separation n p hp (-(j : ℤ)) (Multiset.mem_add.mpr (Or.inr (hxD j hj))) y hy
    · intro e; exact hne (by rw [e])
    · obtain ⟨a, ha⟩ := hxk
      obtain ⟨b, hb⟩ := hyk
      obtain ⟨c, hc⟩ := hd
      have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
      rw [ha, hb, Int.mul_ediv_cancel_left _ hp', Int.mul_ediv_cancel_left _ hp'] at hc
      exact ⟨c, by rw [sq]; linear_combination (p : ℤ) * hc + ha - hb⟩
  -- the local data of the pole `-j`
  have hloc : ∀ j ∈ Icc n (17 * n),
      ValGE p 0 (pfCoeff (hiRoots p (classOf p j) (numRoots n))
          (hiRoots p (classOf p j) (denRoots n)) ((-(j : ℤ) - classOf p j) / p)).1 ∧
      ValGE p 0 (pfCoeff (hiRoots p (classOf p j) (numRoots n))
          (hiRoots p (classOf p j) (denRoots n)) ((-(j : ℤ) - classOf p j) / p)).2 := by
    intro j hj
    refine vpf_local p _ _ _ ?_ (hsepl j hj)
    intro h
    obtain ⟨y, hy, hyl⟩ := Multiset.mem_map.mp h
    obtain ⟨hyN, hyk⟩ := Multiset.mem_filter.mp hy
    exact hxN j hj ((hi_eq_iff p _ _ y (classOf_dvd p j hp0) hyk hp0).mp hyl ▸ hyN)
  -- the unit part
  have hunit : ∀ j ∈ Icc n (17 * n),
      ValGE p 0 ((((pr ((numRoots n).filter fun y => ¬ (p : ℤ) ∣ y - classOf p j) (-(j : ℤ)) : ℤ)
          : ℚ) / ((pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - classOf p j) (-(j : ℤ)) : ℤ)
          : ℚ))) ∧
      ¬ (p : ℤ) ∣ pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - classOf p j) (-(j : ℤ)) ∧
      ValGE p 0 (Ls ((numRoots n).filter fun y => ¬ (p : ℤ) ∣ y - classOf p j) (-(j : ℤ)) -
        Ls ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - classOf p j) (-(j : ℤ))) := by
    intro j hj
    have hxk := classOf_dvd p j hp0
    have hG : ∀ s : Multiset ℤ, ∀ y ∈ s.filter (fun y => ¬ (p : ℤ) ∣ y - classOf p j),
        ¬ (p : ℤ) ∣ -(j : ℤ) - y := fun s y hy hd => (Multiset.mem_filter.mp hy).2 (by
      have := dvd_sub hxk hd
      rwa [show -(j : ℤ) - classOf p j - (-(j : ℤ) - y) = y - classOf p j by ring] at this)
    have hD := not_dvd_pr p _ _ (hG (denRoots n))
    refine ⟨?_, hD, vsub (vLs p _ _ (hG _)) (vLs p _ _ (hG _))⟩
    rw [div_eq_mul_inv]
    simpa using vmul (vint (p := p) _) (vinv_unit _ hD)
  have hl0N : ∀ j ∈ Icc n (17 * n),
      (-(j : ℤ) - classOf p j) / p ∉ hiRoots p (classOf p j) (numRoots n) := by
    intro j hj h
    obtain ⟨y, hy, hyl⟩ := Multiset.mem_map.mp h
    obtain ⟨hyN, hyk⟩ := Multiset.mem_filter.mp hy
    exact hxN j hj ((hi_eq_iff p _ _ y (classOf_dvd p j hp0) hyk hp0).mp hyl ▸ hyN)
  -- on a minimal class, `α, β` at the harmonic index are the local coefficients
  have hαβ : ∀ j ∈ Icc n (17 * n),
      (rc (denRoots n) p (classOf p j) : ℤ) = rc (numRoots n) p (classOf p j) + 1 →
      α ((j + 2 * n) / p) = (pfCoeff (hiRoots p (classOf p j) (numRoots n))
          (hiRoots p (classOf p j) (denRoots n)) ((-(j : ℤ) - classOf p j) / p)).1 ∧
      β ((j + 2 * n) / p) = (pfCoeff (hiRoots p (classOf p j) (numRoots n))
          (hiRoots p (classOf p j) (denRoots n)) ((-(j : ℤ) - classOf p j) / p)).2 := by
    intro j hj hmin
    obtain ⟨g1, g2⟩ := hloc j hj
    obtain ⟨hN, hD⟩ := hshape (classOf p j) (classOf_lt p j hp0) hmin
    have hidx := index_eq n p j hp0
    set l0 := (-(j : ℤ) - classOf p j) / p
    set e := epsK n p (classOf p j)
    have hi : -((((j + 2 * n) / p : ℕ) : ℤ)) = l0 - e := by rw [hidx]; ring
    have hnot : l0 - e ∉ NU := fun h => hl0N j hj (by
      rw [hN]; exact Multiset.mem_map.mpr ⟨l0 - e, h, by ring⟩)
    have key : pfCoeff NU DU (-((((j + 2 * n) / p : ℕ) : ℤ))) =
        pfCoeff (hiRoots p (classOf p j) (numRoots n)) (hiRoots p (classOf p j) (denRoots n))
          l0 := by
      rw [hi, hN, hD, ← pfCoeff_shift NU DU (l0 - e) e hnot, sub_add_cancel]
    simp only [α, β, key, g1, g2, ↓reduceIte, and_self]
  refine ⟨α, β, I, fun i => ⟨?_, ?_⟩, ?_, fun j hj => ?_, fun k hk => ?_⟩
  · simp only [α]; split_ifs with h
    · exact h
    · exact Or.inl rfl
  · simp only [β]; split_ifs with h
    · exact h
    · exact Or.inl rfl
  · -- indices are `< p`
    intro i hi
    simp only [I] at hi
    split_ifs at hi with h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      have hj' := (mem_Icc.mp (mem_filter.mp hj).1).2
      have h2 := hp.2.2.1
      have : j + 2 * n < p * p := by nlinarith
      exact Nat.div_lt_of_lt_mul this
    · simp at hi
  · -- the congruences
    set k := classOf p j
    have hxk := classOf_dvd p j hp0
    obtain ⟨hsa, hsb⟩ := scale p hp0 (numRoots n) (denRoots n) (-(j : ℤ)) k hxk (hxN j hj)
    obtain ⟨g1, g2⟩ := hloc j hj
    obtain ⟨hu, huD, hL⟩ := hunit j hj
    have hcN := rc_eq_card_hiRoots p hp0 k (classOf_lt p j hp0) (numRoots n)
    have hcD := rc_eq_card_hiRoots p hp0 k (classOf_lt p j hp0) (denRoots n)
    rw [← hcN, ← hcD] at hsa hsb
    unfold aCoef bCoef
    rw [hsa, hsb]
    set u := (((pr ((numRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) : ℤ) : ℚ) /
      ((pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) : ℤ) : ℚ))
    set A := (pfCoeff (hiRoots p k (numRoots n)) (hiRoots p k (denRoots n))
      ((-(j : ℤ) - k) / p)).1
    set B := (pfCoeff (hiRoots p k (numRoots n)) (hiRoots p k (denRoots n))
      ((-(j : ℤ) - k) / p)).2
    set L := Ls ((numRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) -
      Ls ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ))
    set h : ℤ := (rc (numRoots n) p k : ℤ) - rc (denRoots n) p k
    have hge' := hge k (classOf_lt p j hp0)
    by_cases hmin : (rc (denRoots n) p k : ℤ) = rc (numRoots n) p k + 1
    · -- minimal class
      have hh : h = -1 := by simp only [h]; omega
      obtain ⟨ea, eb⟩ := hαβ j hj hmin
      rw [ea, eb, hh]
      -- `u + 𝒬(k) ≡ 0`
      have hdvd : (p : ℤ) ∣ pr ((numRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) +
          (Tq n p).eval (k : ℤ) *
            pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) := by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_add, Int.cast_mul,
          unit_part p _ _ k (classOf_lt p j hp0) hxk, unit_part p _ _ k (classOf_lt p j hp0) hxk]
        linear_combination Tq_supp n p k (classOf_lt p j hp0) hge hmin
      have huT : ValGE p 1 (u + (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
        have hD0 : ((pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) : ℤ) : ℚ)
            ≠ 0 := Int.cast_ne_zero.mpr fun h0 => huD (h0 ▸ dvd_zero _)
        have e : u + (((Tq n p).eval (k : ℤ) : ℤ) : ℚ) =
            ((pr ((numRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) +
              (Tq n p).eval (k : ℤ) *
                pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) : ℤ) : ℚ) *
            ((pr ((denRoots n).filter fun y => ¬ (p : ℤ) ∣ y - k) (-(j : ℤ)) : ℤ) : ℚ)⁻¹ := by
          simp only [u]; push_cast; field_simp
        rw [e]
        simpa using vmul (vdvd _ hdvd) (vinv_unit _ huD)
      have hp1 : (p : ℚ) ^ ((-1 : ℤ) + 2) = p := by norm_num
      have hp0' : (p : ℚ) ^ ((-1 : ℤ) + 1) = 1 := by norm_num
      rw [hp1, hp0']
      constructor
      · have e : (p : ℚ) * u * A / p + (((Tq n p).eval (k : ℤ) : ℤ) : ℚ) * A =
            A * (u + (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by field_simp
        rw [e]
        simpa using vmul g1 huT
      · have e : 1 * u * B + p * u * A * L + (((Tq n p).eval (k : ℤ) : ℤ) : ℚ) * B =
            B * (u + (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) + (p : ℚ) * (u * A * L) := by
          ring
        rw [e]
        have vp : ValGE p 1 (p : ℚ) := by simpa using vzpow (p := p) 1
        refine vadd (by simpa using vmul g2 huT) ?_
        simpa using vmul vp (vmul (vmul hu g1) hL)
    · -- non-minimal class: `𝒬(k) = 0`
      have hT := Tq_zero n p k (classOf_lt p j hp0) (by omega)
      rw [hT]
      have hh : 0 ≤ h := by simp only [h]; omega
      simp only [Int.cast_zero, zero_mul, add_zero]
      have e2 : (p : ℚ) ^ (h + 2) = (p : ℚ) ^ (h + 1) * p := by
        rw [show h + 2 = (h + 1) + 1 by ring, zpow_add_one₀ hpq]
      constructor
      · have e : (p : ℚ) ^ (h + 2) * u * A / p = (p : ℚ) ^ (h + 1) * (u * A) := by
          rw [e2]; field_simp
        rw [e]
        exact vmono (by omega : (1 : ℤ) ≤ h + 1 + (0 + 0))
          (vmul (vzpow (p := p) (h + 1)) (vmul hu g1))
      · refine vadd ?_ ?_
        · exact vmono (by omega : (1 : ℤ) ≤ h + 1 + 0 + 0)
            (vmul (vmul (vzpow (p := p) (h + 1)) hu) g2)
        · exact vmono (by omega : (1 : ℤ) ≤ h + 2 + 0 + 0 + 0)
            (vmul (vmul (vmul (vzpow (p := p) (h + 2)) hu) g1) hL)
  · -- the class sums
    by_cases hmin : (rc (denRoots n) p k : ℤ) = rc (numRoots n) p k + 1
    swap
    · exact Or.inl (Tq_zero n p k hk (by have := hge k hk; omega))
    right
    -- characterization of the indices of a minimal class
    have hchar : ∀ k' < p, (rc (denRoots n) p k' : ℤ) = rc (numRoots n) p k' + 1 →
        ∀ i : ℕ, i ∈ (poles n p k').image (fun j => (j + 2 * n) / p) ↔ -(i : ℤ) ∈ DU := by
      intro k' hk' hmin' i
      obtain ⟨-, hD⟩ := hshape k' hk' hmin'
      constructor
      · intro hi
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
        obtain ⟨hjI, hjk⟩ := mem_filter.mp hj
        have hidx := index_eq n p j hp0
        rw [hjk] at hidx
        have hmem : (-(j : ℤ) - k') / p ∈ hiRoots p k' (denRoots n) :=
          Multiset.mem_map.mpr ⟨-(j : ℤ), Multiset.mem_filter.mpr ⟨hxD j hjI,
            hjk ▸ classOf_dvd p j hp0⟩, rfl⟩
        rw [hD] at hmem
        obtain ⟨ν, hν, hνe⟩ := Multiset.mem_map.mp hmem
        rw [hidx, show -(epsK n p k' - (-(j : ℤ) - k') / p) = ν by rw [← hνe]; ring]
        exact hν
      · intro hi
        have hmem : -(i : ℤ) + epsK n p k' ∈ hiRoots p k' (denRoots n) := by
          rw [hD]; exact Multiset.mem_map.mpr ⟨_, hi, rfl⟩
        obtain ⟨y, hy, hye⟩ := Multiset.mem_map.mp hmem
        obtain ⟨hyD, hyk⟩ := Multiset.mem_filter.mp hy
        have hyb : -(17 * n : ℤ) ≤ y ∧ y ≤ -(n : ℤ) := by
          simp only [denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hyD
          omega
        obtain ⟨j, hjy⟩ : ∃ j : ℕ, (j : ℤ) = -y := ⟨(-y).toNat, Int.toNat_of_nonneg (by omega)⟩
        have hjI : j ∈ Icc n (17 * n) := mem_Icc.mpr ⟨by omega, by omega⟩
        have hjk : classOf p j = k' :=
          classOf_eq p j k' hp0 hk' (by rw [hjy, neg_neg]; exact hyk)
        refine Finset.mem_image.mpr ⟨j, mem_filter.mpr ⟨hjI, hjk⟩, ?_⟩
        have hidx := index_eq n p j hp0
        rw [hjk, hjy, neg_neg, hye] at hidx
        have : (((j + 2 * n) / p : ℕ) : ℤ) = i := by rw [hidx]; ring
        exact_mod_cast this
    have hex : ∃ k₀ < p, (rc (denRoots n) p k₀ : ℤ) = rc (numRoots n) p k₀ + 1 := ⟨k, hk, hmin⟩
    refine ⟨fun j hj j' hj' hjj => ?_, ?_⟩
    · obtain ⟨-, hjk⟩ := mem_filter.mp (Finset.mem_coe.mp hj)
      obtain ⟨-, hjk'⟩ := mem_filter.mp (Finset.mem_coe.mp hj')
      have h1 := index_eq n p j hp0
      have h2 := index_eq n p j' hp0
      rw [hjk] at h1
      rw [hjk'] at h2
      have hjj' : (((j + 2 * n) / p : ℕ) : ℤ) = (((j' + 2 * n) / p : ℕ) : ℤ) := by
        exact_mod_cast hjj
      obtain ⟨c, hc⟩ := classOf_dvd p j hp0
      obtain ⟨c', hc'⟩ := classOf_dvd p j' hp0
      rw [hjk] at hc
      rw [hjk'] at hc'
      have hp' : (p : ℤ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
      rw [hc, Int.mul_ediv_cancel_left _ hp'] at h1
      rw [hc', Int.mul_ediv_cancel_left _ hp'] at h2
      have : c = c' := by linarith
      subst this
      have : (j : ℤ) = j' := by linarith
      exact_mod_cast this
    · simp only [I, hex, ↓reduceDIte]
      have hk0 := Classical.choose_spec hex
      ext i
      rw [hchar k hk hmin, hchar _ hk0.1 hk0.2]

/-! ### [6] and [7] -/

/-- **[6] Local factorization** (statement of `ShellFirstOrder.local_factorization`). -/
theorem local_factorization (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    ∃ α β : ℕ → ℚ, (∀ i, ValGE p 0 (α i) ∧ ValGE p 0 (β i)) ∧
      ∀ j ∈ Icc n (17 * n),
        ValGE p 1 (aCoef n j / p +
          (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * α ((j + 2 * n) / p)) ∧
        ValGE p 1 (bCoef n j +
          (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * β ((j + 2 * n) / p)) := by
  obtain ⟨α, β, -, hαβ, -, hcong, -⟩ := core n p hn hp hs
  exact ⟨α, β, hαβ, hcong⟩

/-- One residue class of a readout `p^s ∑ (a_j H^{(s+1)}_{j+2n} + b_j H^{(s)}_{j+2n} / d)`. -/
theorem class_gen (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) (s : ℕ) (hs1 : 1 ≤ s) (d : ℚ)
    (hd : ValGE p 0 d⁻¹) :
    ∃ c : ℚ, ValGE p 0 c ∧ ∀ k ∈ range p,
      ValGE p 1 (∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ s * (aCoef n j * harm (s + 1) (j + 2 * n) + bCoef n j * harm s (j + 2 * n) / d) -
        c * (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have hp0 : 0 < p := hp.1.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.1.ne_zero
  obtain ⟨α, β, I, hαβ, hI, hcong, hcls⟩ := core n p hn hp hs
  let g : ℕ → ℚ := fun i => α i * harm (s + 1) i + β i * harm s i / d
  have hm : ∀ j ∈ Icc n (17 * n), j + 2 * n < p ^ 2 := fun j hj => by
    have := (mem_Icc.mp hj).2; have := hp.2.2.1; omega
  -- harmonic numbers of small index are `p`-integral
  have hH : ∀ r i, 1 ≤ r → i < p → ValGE p 0 (harm r i) := fun r i hr hi => by
    have := (harm_split p r (i * p) hr (by rw [sq]; exact Nat.mul_lt_mul_of_pos_right hi hp0)).1
    rwa [Nat.mul_div_cancel _ hp0] at this
  refine ⟨-∑ i ∈ I, g i, vneg (vsum _ _ _ fun i hi => ?_), fun k hk => ?_⟩
  · have h1 := hH (s + 1) i (by omega) (hI i hi)
    have h2 := hH s i hs1 (hI i hi)
    have := vadd (vmul (hαβ i).1 h1) (vmul (vmul (hαβ i).2 h2) hd)
    simpa [g, div_eq_mul_inv, mul_assoc] using this
  -- the per-pole estimate
  have hterm : ∀ j ∈ Icc n (17 * n), ValGE p 1 ((p : ℚ) ^ s *
      (aCoef n j * harm (s + 1) (j + 2 * n) + bCoef n j * harm s (j + 2 * n) / d) +
      (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ) * g ((j + 2 * n) / p)) := by
    intro j hj
    obtain ⟨ga, gb⟩ := hcong j hj
    have hT := vint (p := p) ((Tq n p).eval (classOf p j : ℤ))
    set T := (((Tq n p).eval (classOf p j : ℤ) : ℤ) : ℚ)
    set i := (j + 2 * n) / p
    set m := j + 2 * n
    obtain ⟨hR0, hR1⟩ := harm_split p (s + 1) m (by omega) (hm j hj)
    obtain ⟨hS0, hS1⟩ := harm_split p s m hs1 (hm j hj)
    have hA : ValGE p 0 (aCoef n j / p) := by
      have := vsub (vmono (by norm_num) ga) (vmul hT (hαβ i).1)
      simpa using this
    have hB : ValGE p 0 (bCoef n j) := by
      have := vsub (vmono (by norm_num) gb) (vmul hT (hαβ i).2)
      simpa using this
    have e : (p : ℚ) ^ s * (aCoef n j * harm (s + 1) m + bCoef n j * harm s m / d) + T * g i =
        aCoef n j / p * ((p : ℚ) ^ (s + 1) * harm (s + 1) m - harm (s + 1) i) +
        (aCoef n j / p + T * α i) * harm (s + 1) i +
        bCoef n j * d⁻¹ * ((p : ℚ) ^ s * harm s m - harm s i) +
        (bCoef n j + T * β i) * d⁻¹ * harm s i := by
      simp only [g]; rw [pow_succ]; field_simp; ring
    rw [e]
    refine vadd (vadd (vadd ?_ ?_) ?_) ?_
    · simpa using vmul hA hR1
    · simpa using vmul ga hR0
    · simpa using vmul (vmul hB hd) hS1
    · simpa using vmul (vmul gb hd) hS0
  have hk' := mem_range.mp hk
  rcases hcls k hk' with h0 | ⟨hinj, himg⟩
  · rw [h0, Int.cast_zero, mul_zero, sub_zero]
    refine vsum _ _ _ fun j hj => ?_
    obtain ⟨hjI, hjk⟩ := mem_filter.mp hj
    have := hterm j hjI
    rwa [hjk, h0, Int.cast_zero, zero_mul, add_zero] at this
  · unfold poles at hinj himg
    rw [← himg, Finset.sum_image fun j hj j' hj' h => hinj hj hj' h]
    rw [neg_mul, sub_neg_eq_add, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine vsum _ _ _ fun j hj => ?_
    obtain ⟨hjI, hjk⟩ := mem_filter.mp hj
    have := hterm j hjI
    rw [hjk] at this
    simpa [mul_comm] using this

/-- `2⁻¹` and `3⁻¹` are `p`-integral for `p > 3`. -/
theorem vinv_small (p : ℕ) [Fact p.Prime] (_h3 : 3 < p) (c : ℕ) (hc0 : 0 < c) (hc : c < p) :
    ValGE p 0 ((c : ℚ)⁻¹) := by
  have := vinv_unit (p := p) (c : ℤ) (fun h => by
    have := Int.le_of_dvd (by omega) h; omega)
  simpa using this

/-- **[7] One residue class of the readout** (statement of `ShellFirstOrder.class_congruence`). -/
theorem class_congruence (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hs : inRows shellRows ((n : ℚ) / p)) :
    ∃ c3 c4 : ℚ, ValGE p 0 c3 ∧ ValGE p 0 c4 ∧ ∀ k ∈ range p,
      ValGE p 1 (∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ 2 * (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2) -
        c3 * (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) ∧
      ValGE p 1 (∑ j ∈ (Icc n (17 * n)).filter (fun j => classOf p j = k),
          (p : ℚ) ^ 3 * (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3) -
        c4 * (((Tq n p).eval (k : ℤ) : ℤ) : ℚ)) := by
  have : Fact p.Prime := ⟨hp.1⟩
  have h29 := hp.2.1
  obtain ⟨c3, hc3, h3⟩ := class_gen n p hn hp hs 2 (by norm_num) 2
    (by simpa using vinv_small p (by omega) 2 (by norm_num) (by omega))
  obtain ⟨c4, hc4, h4⟩ := class_gen n p hn hp hs 3 (by norm_num) 3
    (by simpa using vinv_small p (by omega) 3 (by norm_num) (by omega))
  exact ⟨c3, c4, hc3, hc4, fun k hk => ⟨h3 k hk, h4 k hk⟩⟩

end Meijer5255.ShellFirstOrder.Core
