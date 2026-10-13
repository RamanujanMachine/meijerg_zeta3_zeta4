/-
# Node blueprint: `Gnew_dvd` (paper §10, "The improved divisor and its density", (I2))

Target (restated verbatim from `Blueprint_5255.lean`):
  `(∀ i, ∃ z : ℤ, Z3v n i = Gnew n * z) ∧ (∀ i, ∃ z : ℤ, Z4v n i = Gnew n * z)` for `n ≥ 1`.

Strategy (paper §10, handoff §5.7). `G_n^{new} = ∏_{p ≤ 19n eligible} p^{gExp n p}` is a product of
powers of distinct primes, so it divides an integer `z` as soon as every factor `p^{gExp n p}`
does ([1]), and `p^k ∣ z` follows from `v_p(z) ≥ k` ([2]). The integrality of the forms is
`baseline_integrality`. Fix an eligible `p ≤ 19n` and put `x = n/p`, `c = c(x)`. By `carry_facts`,
`v_p(C_n) = c`, `v_p(d_{19n}) = 1` and `v_p(6) = 0` (`p > 29`), so by multiplicativity ([3])
`v_p(6 C_n d_{19n}^r X) ≥ c + r + v` whenever `v_p(X) ≥ v`. Three cases:
* `{x}` in a window: `carry_facts` gives `ψ(x) = c + 1`, `h₀ = 0`, and the window lies in a shell,
  so `gExp = c + 3`; `second_order_shell` (SG) gives `v_p(Q, P₃, P₄) ≥ (3, 0, -1)`, hence every
  entry has valuation `≥ c + 3` (`r = 3` rows use only `Q, P₃`).
* `{x}` in a shell but not a window: `gExp = c + 2`; `shell_first_order` (PS) gives
  `v_p(Q, P₃, P₄) ≥ (1, -1, -2)`, hence `≥ c + 2`.
* otherwise: `gExp = ψ + h₀`, which is `baseline_profile` (G) directly.

Supporting lemmas (3), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `prod_prime_pow_dvd` | 15 | yes (unique factorization, "prime by prime") |
| 2 | `int_dvd_of_valGE` | 15 | yes (standard) |
| 3 | `valGE_mul` | 15 | yes (standard: `v_p` is additive) |

The glue (≈ 100 lines below) does the exponent bookkeeping `gExp = c + 3 / c + 2 / ψ + h₀`, the
valuations of the normalizing constants, the case split, and the assembly over the primes.

Reuse: pfq54 `G_dvd_Z.lean` (`prod_prime_pow_dvd` is proved there, 6 lines; `block_valuation`
is the template of the case computation), pfq54 `pairing_bound.lean` (`int_dvd_of_valGE`,
`valGE_of_lam_mul`), zeta34 `ZetasAux.lean` (`ValGE.mul`, `ValGE.mono`).
-/
import Meijer5255.definitions
import Meijer5255.BaselineIntegrality
import Meijer5255.CarryFacts
import Meijer5255.BaselineProfile
import Meijer5255.ShellFirstOrder
import Meijer5255.SecondOrderShell

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.GnewDvd

open Meijer5255

/-! ### Supporting lemmas -/

/-- **[1] Coprime prime powers.** If `p^{e_p} ∣ z` for every `p` in a finite set of primes, then
`∏ p^{e_p} ∣ z`.
* Proved (≈ 5 lines).
* Directly from the PDF: yes ("prime by prime", unique factorization). -/
theorem prod_prime_pow_dvd (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (e : ℕ → ℕ) (z : ℤ)
    (h : ∀ p ∈ S, (p : ℤ) ^ e p ∣ z) : ((∏ p ∈ S, p ^ e p : ℕ) : ℤ) ∣ z := by
  -- provenance: pfq54 `G_dvd_Z.prod_prime_pow_dvd`
  rw [Nat.cast_prod]
  simp only [Nat.cast_pow]
  refine Finset.prod_dvd_of_coprime (fun a ha b hb hab => ?_) h
  exact (Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (hS a ha) (hS b hb)).mpr hab)).pow

/-- **[2] From valuations to divisibility.** An integer `z` with `v_p(z) ≥ k` (or `z = 0`) is
divisible by `p^k`.
* Proved (≈ 10 lines).
* Directly from the PDF: yes (standard). -/
theorem int_dvd_of_valGE {p : ℕ} (hp : p.Prime) (z : ℤ) (k : ℕ) (hv : ValGE p k (z : ℚ)) :
    (p : ℤ) ^ k ∣ z := by
  -- provenance: pfq54 `pairing_bound.int_dvd_of_valGE`
  have : Fact p.Prime := ⟨hp⟩
  refine (padicValInt_dvd_iff k z).mpr ?_
  rcases eq_or_ne z 0 with h | h
  · exact Or.inl h
  · right
    rcases hv with h0 | hv
    · exact absurd (by exact_mod_cast h0) h
    · rw [padicValRat.of_int] at hv
      exact_mod_cast hv

/-- **[3] Valuations add under multiplication.** `ValGE p a x → ValGE p b y → ValGE p (a+b) (xy)`
(if `x = 0` or `y = 0` the product is `0`; otherwise `padicValRat.mul`).
* Proved (≈ 11 lines).
* Directly from the PDF: yes (standard). -/
theorem valGE_mul {p : ℕ} (hp : p.Prime) {a b : ℤ} {x y : ℚ} (hx : ValGE p a x)
    (hy : ValGE p b y) : ValGE p (a + b) (x * y) := by
  -- provenance: zeta34 `ZetasAux.ValGE.mul`
  have : Fact p.Prime := ⟨hp⟩
  rcases hx with rfl | hx
  · left; simp
  rcases hy with rfl | hy
  · left; simp
  by_cases hx0 : x = 0
  · left; simp [hx0]
  by_cases hy0 : y = 0
  · left; simp [hy0]
  right; rw [padicValRat.mul hx0 hy0]; omega

/-! ### The node -/

/-- **The improved divisor** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[3] and the blueprint nodes `baseline_integrality`, `carry_facts`, `baseline_profile`,
`shell_first_order`, `second_order_shell`. -/
theorem Gnew_dvd (n : ℕ) (hn : 1 ≤ n) :
    (∀ i, ∃ z : ℤ, Z3v n i = Gnew n * z) ∧ (∀ i, ∃ z : ℤ, Z4v n i = Gnew n * z) := by
  -- monotonicity of `ValGE` in the exponent
  have mono : ∀ {p : ℕ} {a b : ℤ} {x : ℚ}, a ≤ b → ValGE p b x → ValGE p a x :=
    fun hab h => h.imp id (fun h => hab.trans h)
  -- the local statement at one eligible prime `p ≤ 19n`
  have key : ∀ p, Eligible n p → p ≤ 19 * n →
      (∀ i, ValGE p (gExp n p : ℕ) (Z3v n i)) ∧ (∀ i, ValGE p (gExp n p : ℕ) (Z4v n i)) := by
    intro p hp hle
    have hpr := hp.1
    obtain ⟨hC, hd, hsw, hwin⟩ := CarryFacts.carry_facts n p hn hp
    set x : ℚ := (n : ℚ) / p with hx
    -- valuations of the normalizing constants
    have v6 : ValGE p 0 (6 : ℚ) := by
      right
      have h6 : ¬ p ∣ 6 := fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        have := hp.2.1
        omega
      rw [show (6 : ℚ) = ((6 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
        padicValNat.eq_zero_of_not_dvd h6]
      simp
    have vC : ValGE p (cfun x) (Cn n) := Or.inr hC.ge
    have vd : ∀ r : ℕ, ValGE p r ((dlcm (19 * n) : ℚ) ^ r) := fun r => by
      right
      have : Fact p.Prime := ⟨hpr⟩
      rw [padicValRat.pow, hd hle]
      simp
    have scale : ∀ (r : ℕ) (v : ℤ) (X : ℚ), ValGE p v X →
        ValGE p (cfun x + r + v) (6 * Cn n * (dlcm (19 * n) : ℚ) ^ r * X) := by
      intro r v X hX
      have h := valGE_mul hpr (valGE_mul hpr (valGE_mul hpr v6 vC) (vd r)) hX
      exact mono (by omega) h
    by_cases hw : inRows windowRows x = true
    · -- second-order window: `gExp = c + 3`
      have hs := hwin hw
      obtain ⟨hpsi, hh0⟩ := hsw (Or.inr hw)
      have hg : ((gExp n p : ℕ) : ℤ) = cfun x + 3 := by
        simp only [gExp, ← hx, hs, hw, hh0, ite_true]
        push_cast
        rw [hpsi]
        ring
      obtain ⟨hQ, h3, h4⟩ := SecondOrderShell.second_order_shell n p hn hp hw
      rw [hg]
      refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
      · exact mono (by omega) (scale 3 3 _ hQ)
      · exact mono (by omega) (scale 3 0 _ h3)
      · exact mono (by omega) (scale 4 3 _ hQ)
      · exact mono (by omega) (scale 4 0 _ h3)
      · exact mono (by omega) (scale 4 (-1) _ h4)
    · by_cases hs : inRows shellRows x = true
      · -- first-order shell only: `gExp = c + 2`
        obtain ⟨hpsi, hh0⟩ := hsw (Or.inl hs)
        have hg : ((gExp n p : ℕ) : ℤ) = cfun x + 2 := by
          simp only [gExp, ← hx, hs, hw, hh0, ite_true]
          push_cast
          rw [hpsi]
          simp
          ring
        obtain ⟨hQ, h3, h4⟩ := ShellFirstOrder.shell_first_order n p hn hp hs
        rw [hg]
        refine ⟨fun i => ?_, fun i => ?_⟩ <;> fin_cases i
        · exact mono (by omega) (scale 3 1 _ hQ)
        · exact mono (by omega) (scale 3 (-1) _ h3)
        · exact mono (by omega) (scale 4 1 _ hQ)
        · exact mono (by omega) (scale 4 (-1) _ h3)
        · exact mono (by omega) (scale 4 (-2) _ h4)
      · -- baseline: `gExp = ψ + h₀`
        have hg : gExp n p = psi x + hgain n p := by
          simp only [gExp, ← hx, hs, hw]
          simp
        rw [hg]
        exact BaselineProfile.baseline_profile n p hn hp
  -- assembly over the primes
  have assemble : ∀ X : ℚ, (∃ z : ℤ, X = z) →
      (∀ p ∈ (range (19 * n + 1)).filter (Eligible n), ValGE p (gExp n p : ℕ) X) →
      ∃ z : ℤ, X = Gnew n * z := by
    rintro X ⟨z, rfl⟩ h
    obtain ⟨w, hw⟩ := prod_prime_pow_dvd _ (fun p hp => (mem_filter.1 hp).2.1) (gExp n) z
      (fun p hp => int_dvd_of_valGE (mem_filter.1 hp).2.1 z _ (h p hp))
    refine ⟨w, ?_⟩
    rw [hw, Gnew]
    push_cast
    rfl
  have hle : ∀ p ∈ (range (19 * n + 1)).filter (Eligible n), Eligible n p ∧ p ≤ 19 * n :=
    fun p hp => by
      obtain ⟨h1, h2⟩ := mem_filter.1 hp
      exact ⟨h2, by rw [mem_range] at h1; omega⟩
  obtain ⟨-, -, hZ3, hZ4, -⟩ := BaselineIntegrality.baseline_integrality n hn
  refine ⟨fun i => assemble _ (hZ3 i) fun p hp => ?_, fun i => assemble _ (hZ4 i) fun p hp => ?_⟩
  · exact (key p (hle p hp).1 (hle p hp).2).1 i
  · exact (key p (hle p hp).1 (hle p hp).2).2 i

end Meijer5255.GnewDvd
