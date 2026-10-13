/-
# Node blueprint: `window_root_data` (paper §9, "Application to the Meijer–G rational kernel",
table (S2))

Target (restated verbatim from `Blueprint_5255.lean`): for `n ≥ 1`, an eligible prime `p` and
`{n/p} ∈ (1/10, 2/19) ∪ (11/12, 15/16)`,
  `∃ NU DU : Multiset ℤ, TraceHyp p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) NU DU`.

Strategy (paper §9). Write `n/p = t + f`, `y = k/p` with representatives `k ∈ [1, p]`. The high
roots of the class `k` are the five intervals of `ends0 f y`, shifted affinely in `t` ([2]); the
counts gain `16t, 14t` resp. `10t` on each interval, so `h = #num - #den` does not depend on `t`
([3]). The exact certificate ([1]: Farey-29 chamber check at `t = 0` on the 9 window cells, then
symbolic affine-in-`t` endpoint arithmetic) gives `h ≥ -1`, the common minimal-class intervals
of the table (S2) (`NUw`, `DUw`), and for `h = 0` an affine factor `V - a(t)` from an explicit
list. `n/p` never lies on a Farey wall of order `29` ([4]). Distinct high roots differ by at most
`29n/p < p` ([5]); `1, …, p` is a complete residue system ([6]).

Glue (below): choose the window row from `hw`; take `NU, DU` the row's multisets at
`t = ⌊n/p⌋`; the fields `odd`, `deg`, `coprime`, `pole_le_two` directly from the definitions of
`numRoots`, `denRoots` (`Int.card_Icc`, `omega`, `Multiset.count` of a sum of nodup multisets);
`h_ge`, `minimal`, `affine` by rewriting each class with [2], converting counts with [3] and
applying [1] (with [4]); `complete` and `separated` from [6], [5].

Supporting lemmas (6), with estimated proof lengths and whether the PDF proves them directly:

| # | lemma | est. lines | directly from the PDF |
|---|---|---|---|
| 1 | `window_cert` | 300 | partially (certificate asserted; Lean chamber check + symbolic lift new) |
| 2 | `hiRoots_lift` | 80 | yes (high roots as affine intervals) |
| 3 | `count_lift` | 30 | yes ("adds `30t` numerator and `30t` denominator roots") |
| 4 | `fract_generic` | 15 | yes ("an excluded Farey boundary cannot occur when `p > 29`") |
| 5 | `separation` | 30 | yes ("distinct high poles differ by at most `16n/p + 1 < p`") |
| 6 | `complete_reps` | 15 | yes (representatives `1, …, p`) |

Formalization notes: [1] uses the chamber certificate `WindowRootData_Cert.lean` (kernel-checked
cell data) and the symbolic lifts `minimal_lift`, `zero_lift` below; [2] and [1] use the interval
helpers of `WindowRootData_Aux.lean`.

Reuse: pfq54 `residue_aux.lean` (`filter_class`, `card_class`: one interval in one class),
`residue_aux4.lean` (`count_Icc`, `card_nR`, `card_dR`); zeta34 `Chamber_dsl.lean`,
`Chamber_reduce.lean`, pfq54 `profile_aux.lean` (chamber certificates); the shell analogue
`ShellFirstOrder.lean` [1], [2].
-/
import Meijer5255.definitions
import Meijer5255.WindowRootData_Aux
import Meijer5255.WindowRootData_Cert

open Filter Topology Finset Polynomial
open scoped Matrix

noncomputable section

namespace Meijer5255.WindowRootData

open Meijer5255

/-! ### Objects -/

/-- Lower ends of the two windows `(1/10, 2/19)`, `(11/12, 15/16)`. -/
def winLo : Fin 2 → ℚ := ![1/10, 11/12]

/-- Upper ends of the two windows. -/
def winHi : Fin 2 → ℚ := ![2/19, 15/16]

/-- Numerator high roots of the minimal classes (table (S2)): `[0,10t] + [t,11t] + [2t,12t]`,
resp. `[0,10t+8] + [t+1,11t+9] + [2t+2,12t+10]`. -/
def NUw (w : Fin 2) (t : ℤ) : Multiset ℤ :=
  ![(Icc 0 (10 * t)).val + (Icc t (11 * t)).val + (Icc (2 * t) (12 * t)).val,
    (Icc 0 (10 * t + 8)).val + (Icc (t + 1) (11 * t + 9)).val +
      (Icc (2 * t + 2) (12 * t + 10)).val] w

/-- Denominator high roots of the minimal classes (table (S2)):
`[-17t-2,-t-1] + [-16t-2,-2t-1]`, resp. `[-17t-16,-t-2] + [-16t-15,-2t-3]`. -/
def DUw (w : Fin 2) (t : ℤ) : Multiset ℤ :=
  ![(Icc (-17 * t - 2) (-t - 1)).val + (Icc (-16 * t - 2) (-2 * t - 1)).val,
    (Icc (-17 * t - 16) (-t - 2)).val + (Icc (-16 * t - 15) (-2 * t - 3)).val] w

/-- The possible roots `a(t)` of the affine factors `U_k/U = V - a(t)` on the classes `h_k = 0`:
`V + 16t + 2`, `V + 2t + 1` (first window), `V - (2t+1)`, `V - (10t+9)`, `V + 17t + 16` (second). -/
def zeroFactors (w : Fin 2) (t : ℤ) : List ℤ :=
  ![[-(16 * t + 2), -(2 * t + 1)], [2 * t + 1, 10 * t + 9, -(17 * t + 16)]] w

/-- Number of integers in `[L, U]` (`0` for an empty interval). -/
def icount (L U : ℤ) : ℤ := max 0 (U - L + 1)

/-- The five `t = 0` high-root intervals `N₀, N₁, N₂, D₀, D₁` of the residue `y = k/p` at
`f = {n/p}`: `[⌊uf - y⌋ + 1, ⌊(u+10)f - y⌋]` (`u = 0,1,2`), `[⌈-17f - y⌉, ⌊-f - y⌋]`,
`[⌈-16f - y⌉, ⌊-2f - y⌋]`. -/
def ends0 (f y : ℚ) : Fin 5 → ℤ × ℤ :=
  ![(⌊-y⌋ + 1, ⌊10 * f - y⌋), (⌊f - y⌋ + 1, ⌊11 * f - y⌋), (⌊2 * f - y⌋ + 1, ⌊12 * f - y⌋),
    (⌈-17 * f - y⌉, ⌊-f - y⌋), (⌈-16 * f - y⌉, ⌊-2 * f - y⌋)]

/-- The `t = 0` count `h = #N₀ + #N₁ + #N₂ - #D₀ - #D₁`. -/
def hcount0 (f y : ℚ) : ℤ :=
  icount (ends0 f y 0).1 (ends0 f y 0).2 + icount (ends0 f y 1).1 (ends0 f y 1).2 +
      icount (ends0 f y 2).1 (ends0 f y 2).2 -
    icount (ends0 f y 3).1 (ends0 f y 3).2 - icount (ends0 f y 4).1 (ends0 f y 4).2

/-- The numerator high roots at the lift `t` of `t = 0` endpoint data `E`:
`[ut + L_u, (u+10)t + U_u]`, `u = 0, 1, 2`. -/
def hiN (E : Fin 5 → ℤ × ℤ) (t : ℤ) : Multiset ℤ :=
  (Icc (E 0).1 (10 * t + (E 0).2)).val + (Icc (t + (E 1).1) (11 * t + (E 1).2)).val +
    (Icc (2 * t + (E 2).1) (12 * t + (E 2).2)).val

/-- The denominator high roots at the lift `t`: `[-17t + L₃, -t + U₃]`, `[-16t + L₄, -2t + U₄]`. -/
def hiD (E : Fin 5 → ℤ × ℤ) (t : ℤ) : Multiset ℤ :=
  (Icc (-17 * t + (E 3).1) (-t + (E 3).2)).val + (Icc (-16 * t + (E 4).1) (-2 * t + (E 4).2)).val

/-! ### Supporting lemmas -/

/-! ### Auxiliary lifts for [1] (symbolic in `t`) -/

/-- The table's minimal-class intervals, for every lift `t ≥ 0`. -/
theorem minimal_lift (w : Fin 2) (t : ℤ) :
    hiN (Cert.Emin w) t = NUw w t ∧ hiD (Cert.Emin w) t = DUw w t := by
  fin_cases w <;> constructor <;> ext z <;>
    simp [hiN, hiD, NUw, DUw, Cert.Emin, Multiset.count_add, count_Icc]
  split_ifs <;> omega

theorem zero_lift_0a (t : ℤ) (ht : 0 ≤ t) :
    hiN ![(0, 0), (0, 0), (0, 0), (-2, -1), (-1, -1)] t + DUw 0 t =
      (-(16 * t + 2) ::ₘ NUw 0 t) + hiD ![(0, 0), (0, 0), (0, 0), (-2, -1), (-1, -1)] t := by
  ext z
  simp [hiN, hiD, NUw, DUw, Multiset.count_add, Multiset.count_cons, count_Icc]
  split_ifs <;> omega

theorem zero_lift_0b (t : ℤ) (ht : 0 ≤ t) :
    hiN ![(0, 0), (0, 0), (0, 0), (-2, -1), (-2, -2)] t + DUw 0 t =
      (-(2 * t + 1) ::ₘ NUw 0 t) + hiD ![(0, 0), (0, 0), (0, 0), (-2, -1), (-2, -2)] t := by
  ext z
  simp [hiN, hiD, NUw, DUw, Multiset.count_add, Multiset.count_cons, count_Icc]
  split_ifs <;> omega

theorem zero_lift_1a (t : ℤ) (ht : 0 ≤ t) :
    hiN ![(0, 8), (1, 9), (2, 10), (-15, -2), (-15, -3)] t + DUw 1 t =
      (-(17 * t + 16) ::ₘ NUw 1 t) + hiD ![(0, 8), (1, 9), (2, 10), (-15, -2), (-15, -3)] t := by
  ext z
  simp [hiN, hiD, NUw, DUw, Multiset.count_add, Multiset.count_cons, count_Icc]
  split_ifs <;> omega

theorem zero_lift_1b (t : ℤ) (ht : 0 ≤ t) :
    hiN ![(0, 8), (1, 9), (1, 10), (-16, -2), (-15, -3)] t + DUw 1 t =
      ((2 * t + 1) ::ₘ NUw 1 t) + hiD ![(0, 8), (1, 9), (1, 10), (-16, -2), (-15, -3)] t := by
  ext z
  simp [hiN, hiD, NUw, DUw, Multiset.count_add, Multiset.count_cons, count_Icc]
  split_ifs <;> omega

theorem zero_lift_1c (t : ℤ) (ht : 0 ≤ t) :
    hiN ![(0, 9), (1, 9), (2, 10), (-16, -2), (-15, -3)] t + DUw 1 t =
      ((10 * t + 9) ::ₘ NUw 1 t) + hiD ![(0, 9), (1, 9), (2, 10), (-16, -2), (-15, -3)] t := by
  ext z
  simp [hiN, hiD, NUw, DUw, Multiset.count_add, Multiset.count_cons, count_Icc]
  split_ifs <;> omega

/-- The `h = 0` data of the certificate have the listed affine factors, for every `t ≥ 0`. -/
theorem zero_lift (w : Fin 2) (E : Fin 5 → ℤ × ℤ) (hE : E ∈ Cert.Zs w) (t : ℤ) (ht : 0 ≤ t) :
    ∃ a ∈ zeroFactors w t, hiN E t + DUw w t = (a ::ₘ NUw w t) + hiD E t := by
  fin_cases w
  · change E ∈ [![(0, 0), (0, 0), (0, 0), (-2, -1), (-1, -1)],
      ![(0, 0), (0, 0), (0, 0), (-2, -1), (-2, -2)]] at hE
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl
    · exact ⟨_, by simp [zeroFactors], zero_lift_0a t ht⟩
    · exact ⟨_, by simp [zeroFactors], zero_lift_0b t ht⟩
  · change E ∈ [![(0, 8), (1, 9), (2, 10), (-15, -2), (-15, -3)],
      ![(0, 8), (1, 9), (1, 10), (-16, -2), (-15, -3)],
      ![(0, 9), (1, 9), (2, 10), (-16, -2), (-15, -3)]] at hE
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
    rcases hE with rfl | rfl | rfl
    · exact ⟨_, by simp [zeroFactors], zero_lift_1a t ht⟩
    · exact ⟨_, by simp [zeroFactors], zero_lift_1b t ht⟩
    · exact ⟨_, by simp [zeroFactors], zero_lift_1c t ht⟩

/-- **[1] The window certificate** (Farey-29 chamber check at `t = 0`, then symbolic `t`). For
`f` in the window `w`, away from the Farey walls of order `29`, and `y ∈ (0, 1]`: `h ≥ -1`; if
`h = -1`, then for every lift `t ≥ 0` the class has the table's minimal high roots; if `h = 0`,
then for every `t ≥ 0` its kernel is `(V - a(t)) U` with `a(t)` from the list `zeroFactors`.
Proof: on each of the 9 window cells and each `y`-stratum (open intervals and boundaries; the
lines `y = mf + c` with `m ∈ {0,1,2,10,11,12,-1,-2,-16,-17}` cross only at Farey-29 abscissas)
the endpoint data are constant; check them by `decide +kernel`. For the lift, every endpoint is
`slope · t + const` and the signed boundary multiset of `U_k/U` reduces to `+1` at `a(t)` and
`-1` at `a(t) + 1` identically in `t` (interval-difference lemma for `Icc` with affine ends).
(`y = 1`, i.e. `k = p`, is the residue `0` shifted by one: `h = 1`.)
* Proved (≈ 20 lines here, plus the symbolic lifts `minimal_lift`, `zero_lift` above, ≈ 75
  lines, and the chamber-certificate helper `WindowRootData_Cert.lean`, ≈ 330 lines).
* Directly from the PDF: partially (the PDF asserts the table and the output of
  `second_order_certificate.py`; the Lean check is new). -/
theorem window_cert (w : Fin 2) (f y : ℚ) (hf : winLo w < f ∧ f < winHi w)
    (hF : ∀ q : ℕ, 0 < q → q ≤ 29 → ∀ m : ℤ, f * q ≠ m) (hy : 0 < y ∧ y ≤ 1) :
    -1 ≤ hcount0 f y ∧
      (hcount0 f y = -1 → ∀ t : ℤ, 0 ≤ t →
        hiN (ends0 f y) t = NUw w t ∧ hiD (ends0 f y) t = DUw w t) ∧
      (hcount0 f y = 0 → ∀ t : ℤ, 0 ≤ t → ∃ a ∈ zeroFactors w t,
        hiN (ends0 f y) t + DUw w t = (a ::ₘ NUw w t) + hiD (ends0 f y) t) := by
  -- the `t = 0` chamber check on the 9 Farey-29 cells (`WindowRootData_Cert.lean`)
  have hgood : Cert.goodB w (Cert.endsQ f y) = true := by
    fin_cases w
    · have h29 := hF 29 (by norm_num) (by norm_num) 3
      push_cast at h29
      exact Cert.cert_w0 f y (by simpa [winLo, winHi] using hf) h29 hy
    · exact Cert.cert_w1 f y (by simpa [winLo, winHi] using hf) hF hy
  obtain ⟨h1, h2, h3⟩ := Cert.goodB_spec hgood
  have hE : ends0 f y = Cert.endsQ f y := rfl
  have hh : hcount0 f y = Cert.hcE (Cert.endsQ f y) := rfl
  refine ⟨hh ▸ h1, fun e t ht => ?_, fun e t ht => ?_⟩
  · -- minimal classes: the table's intervals, identically in `t`
    rw [hE, h2 (hh ▸ e)]
    exact minimal_lift w t
  · -- `h = 0`: the affine factor `V - a(t)`, identically in `t`
    rw [hE]
    exact zero_lift w _ (h3 (hh ▸ e)) t ht

/-- **[2] High roots for every lift.** With `t = ⌊n/p⌋`, `f = {n/p}`, `y = k/p`, the high roots of
the class `k` are `hiN (ends0 f y) t` (numerator) and `hiD (ends0 f y) t` (denominator).
Proof: `x = k + pℓ ∈ [a, b] ⟺ ⌈(a-k)/p⌉ ≤ ℓ ≤ ⌊(b-k)/p⌋`, `⌈(m+1)/p⌉ = ⌊m/p⌋ + 1`, and
`⌊u(t+f) - y⌋ = ut + ⌊uf - y⌋` (same for `⌈·⌉`).
* Proved (≈ 59 lines).
* Directly from the PDF: yes (§7/§9 root data, "Each interval denotes all integer high roots"). -/
theorem hiRoots_lift (n p : ℕ) (k : ℤ) (hp : 0 < p) :
    hiRoots p k (numRoots n) =
        hiN (ends0 (Int.fract ((n : ℚ) / p)) ((k : ℚ) / p)) ⌊(n : ℚ) / p⌋ ∧
      hiRoots p k (denRoots n) =
        hiD (ends0 (Int.fract ((n : ℚ) / p)) ((k : ℚ) / p)) ⌊(n : ℚ) / p⌋ := by
  have hp' : (0 : ℚ) < p := by exact_mod_cast hp
  have hqf := Int.floor_add_fract ((n : ℚ) / p)
  -- `⌊(un - k)/p⌋ = ut + ⌊uf - y⌋`, `⌈(un - k)/p⌉ = ut + ⌈uf - y⌉`, `⌈(un + 1 - k)/p⌉ = …`
  have hsplit : ∀ (u : ℤ) (A : ℚ), A = ((u : ℚ) * n - k) / p →
      A = ((u * ⌊(n : ℚ) / p⌋ : ℤ) : ℚ) + ((u : ℚ) * Int.fract ((n : ℚ) / p) - (k : ℚ) / p) := by
    intro u A hA
    rw [hA]
    have hf : Int.fract ((n : ℚ) / p) = (n : ℚ) / p - ⌊(n : ℚ) / p⌋ := by linarith
    rw [hf]
    push_cast
    field_simp
    ring
  have hF : ∀ (u : ℤ) (A : ℚ), A = ((u : ℚ) * n - k) / p →
      ⌊A⌋ = u * ⌊(n : ℚ) / p⌋ + ⌊(u : ℚ) * Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌋ := by
    intro u A hA
    rw [hsplit u A hA, Int.floor_intCast_add]
  have hC : ∀ (u : ℤ) (A : ℚ), A = ((u : ℚ) * n - k) / p →
      ⌈A⌉ = u * ⌊(n : ℚ) / p⌋ + ⌈(u : ℚ) * Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌉ := by
    intro u A hA
    rw [hsplit u A hA, Int.ceil_intCast_add]
  have hS : ∀ (u : ℤ) (A : ℚ), A = ((u : ℚ) * n + 1 - k) / p →
      ⌈A⌉ = u * ⌊(n : ℚ) / p⌋ + (⌊(u : ℚ) * Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌋ + 1) := by
    intro u A hA
    have h := ceil_succ_div p hp (u * n - k)
    rw [show (((u * n - k : ℤ) : ℚ) + 1) / p = A by rw [hA]; push_cast; ring] at h
    rw [h, hF u _ (by push_cast; ring)]
    ring
  constructor
  · unfold hiRoots numRoots
    rw [Multiset.filter_add, Multiset.filter_add, Multiset.map_add, Multiset.map_add,
      hi_Icc p hp, hi_Icc p hp, hi_Icc p hp]
    simp only [hiN, ends0, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    have e1 := hS 0 ((((1 : ℤ) : ℚ) - k) / p) (by push_cast; ring)
    have e2 := hF 10 ((((10 * (n : ℤ) : ℤ) : ℚ) - k) / p) (by push_cast; ring)
    have e3 := hS 1 (((((n : ℤ) + 1 : ℤ) : ℚ) - k) / p) (by push_cast; ring)
    have e4 := hF 11 ((((11 * (n : ℤ) : ℤ) : ℚ) - k) / p) (by push_cast; ring)
    have e5 := hS 2 ((((2 * (n : ℤ) + 1 : ℤ) : ℚ) - k) / p) (by push_cast; ring)
    have e6 := hF 12 ((((12 * (n : ℤ) : ℤ) : ℚ) - k) / p) (by push_cast; ring)
    simp only [Int.cast_zero, zero_mul, zero_sub, zero_add] at e1
    simp only [Int.cast_one, one_mul, Int.cast_ofNat] at e2 e3 e4 e5 e6
    rw [e1, e2, e3, e4, e5, e6]
  · unfold hiRoots denRoots
    rw [Multiset.filter_add, Multiset.map_add, hi_Icc p hp, hi_Icc p hp]
    simp only [hiD, ends0, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons]
    have e1 : ⌈(((-(17 * (n : ℤ)) : ℤ) : ℚ) - k) / p⌉ =
        -17 * ⌊(n : ℚ) / p⌋ + ⌈-17 * Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌉ := by
      rw [hC (-17) ((((-(17 * (n : ℤ)) : ℤ) : ℚ) - k) / p) (by push_cast; ring)]; norm_num
    have e2 : ⌊(((-(n : ℤ) : ℤ) : ℚ) - k) / p⌋ =
        -⌊(n : ℚ) / p⌋ + ⌊-Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌋ := by
      rw [hF (-1) ((((-(n : ℤ) : ℤ) : ℚ) - k) / p) (by push_cast; ring)]; norm_num
    have e3 : ⌈(((-(16 * (n : ℤ)) : ℤ) : ℚ) - k) / p⌉ =
        -16 * ⌊(n : ℚ) / p⌋ + ⌈-16 * Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌉ := by
      rw [hC (-16) ((((-(16 * (n : ℤ)) : ℤ) : ℚ) - k) / p) (by push_cast; ring)]; norm_num
    have e4 : ⌊(((-(2 * (n : ℤ)) : ℤ) : ℚ) - k) / p⌋ =
        -2 * ⌊(n : ℚ) / p⌋ + ⌊-2 * Int.fract ((n : ℚ) / p) - (k : ℚ) / p⌋ := by
      rw [hF (-2) ((((-(2 * (n : ℤ)) : ℤ) : ℚ) - k) / p) (by push_cast; ring)]; norm_num
    rw [e1, e2, e3, e4]

/-- **[3] The counts do not depend on the lift.** For `f ≥ 0` and `t ≥ 0`:
`#hiN - #hiD = hcount0 f y` (each `t = 0` interval has `U - L + 1 ≥ 0`, by monotonicity of `⌊·⌋`
in `f ≥ 0`, and the lift adds `10t, 10t, 10t` resp. `16t, 14t` points).
* Proved (≈ 17 lines).
* Directly from the PDF: yes ("Changing `f` to `t + f` adds `30t` numerator roots and `30t`
  denominator roots at every residue. Hence `h` … unchanged"). -/
theorem count_lift (f y : ℚ) (hf : 0 ≤ f) (t : ℤ) (ht : 0 ≤ t) :
    ((hiN (ends0 f y) t).card : ℤ) - ((hiD (ends0 f y) t).card : ℤ) = hcount0 f y := by
  have h0 : ⌊-y⌋ ≤ ⌊10 * f - y⌋ := Int.floor_le_floor (by linarith)
  have h1 : ⌊f - y⌋ ≤ ⌊11 * f - y⌋ := Int.floor_le_floor (by linarith)
  have h2 : ⌊2 * f - y⌋ ≤ ⌊12 * f - y⌋ := Int.floor_le_floor (by linarith)
  have hcf : ∀ a b : ℚ, a ≤ b → ⌈a⌉ ≤ ⌊b⌋ + 1 := by
    intro a b hab
    have h1 := Int.ceil_lt_add_one a
    have h2 := Int.lt_floor_add_one b
    have : (⌈a⌉ : ℚ) < ((⌊b⌋ + 2 : ℤ) : ℚ) := by push_cast; linarith
    have : ⌈a⌉ < ⌊b⌋ + 2 := by exact_mod_cast this
    omega
  have h3 := hcf (-17 * f - y) (-f - y) (by linarith)
  have h4 := hcf (-16 * f - y) (-2 * f - y) (by linarith)
  simp only [hiN, hiD, hcount0, icount, ends0, Multiset.card_add, Finset.card_val, Int.card_Icc,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  push_cast
  omega

/-- **[4] `{n/p}` avoids the Farey walls of order `29`.** For eligible `p`, `{n/p} = r/p` with
`0 < r < p`; `q r/p ∈ ℤ` would force `p ∣ q ≤ 29 < p`.
* Proved (≈ 20 lines).
* Directly from the PDF: yes ("an excluded Farey boundary cannot occur when `p > 29`"). -/
theorem fract_generic (n p : ℕ) (hp : Eligible n p) :
    ∀ q : ℕ, 0 < q → q ≤ 29 → ∀ m : ℤ, Int.fract ((n : ℚ) / p) * q ≠ m := by
  intro q hq hq29 m h
  have hp0 : 0 < p := hp.1.pos
  rw [Int.fract_div_natCast_eq_div_natCast_mod] at h
  have hpq : (p : ℚ) ≠ 0 := by positivity
  have h' : ((((n % p) * q : ℕ) : ℤ) : ℚ) = ((m * p : ℤ) : ℚ) := by
    rw [Int.cast_natCast, Int.cast_mul, Int.cast_natCast, ← h, Nat.cast_mul]
    field_simp
  have h'' : (((n % p) * q : ℕ) : ℤ) = m * p := Int.cast_inj.1 h'
  have hdvd : p ∣ n % p * q := by
    have : (p : ℤ) ∣ (((n % p) * q : ℕ) : ℤ) := ⟨m, by rw [h'']; ring⟩
    exact_mod_cast this
  rcases (Nat.Prime.dvd_mul hp.1).1 hdvd with h1 | h1
  · have hlt := Nat.mod_lt n hp0
    have hpos : 0 < n % p :=
      Nat.pos_of_ne_zero fun h0 => hp.2.2.2 (Nat.dvd_of_mod_eq_zero h0)
    have := Nat.le_of_dvd hpos h1
    omega
  · have := Nat.le_of_dvd hq h1
    have := hp.2.1
    omega

/-- **[5] Separation.** Distinct high roots of one class differ by a non-multiple of `p`: two
roots `x = k + pℓ`, `x' = k + pℓ'` of `F_n` lie in `[-17n, 12n]`, so
`0 < |ℓ - ℓ'| = |x - x'|/p ≤ 29n/p < p` (`30n < p²`).
* Proved (≈ 38 lines).
* Directly from the PDF: yes ("Distinct denominator high poles differ by at most `16n/p+1 < p`";
  the same bound with `29n` covers numerator roots). -/
theorem separation (n p : ℕ) (hp : Eligible n p) :
    ∀ k ∈ Icc 1 (p : ℤ), ∀ ℓ ∈ hiRoots p k (numRoots n + denRoots n),
      ∀ ℓ' ∈ hiRoots p k (numRoots n + denRoots n), ℓ ≠ ℓ' → ¬ (p : ℤ) ∣ ℓ - ℓ' := by
  intro k _ ℓ hℓ ℓ' hℓ' hne hdvd
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.1.pos
  have hpz : (p : ℤ) ≠ 0 := hp0.ne'
  have h30 : (30 * n : ℤ) < (p : ℤ) * p := by
    have := hp.2.2.1
    rw [sq] at this
    exact_mod_cast this
  unfold hiRoots at hℓ hℓ'
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 hℓ
  obtain ⟨x', hx', rfl⟩ := Multiset.mem_map.1 hℓ'
  rw [Multiset.mem_filter] at hx hx'
  obtain ⟨c, hc⟩ := hx.2
  obtain ⟨c', hc'⟩ := hx'.2
  rw [hc, hc', Int.mul_ediv_cancel_left _ hpz, Int.mul_ediv_cancel_left _ hpz] at hne hdvd
  obtain ⟨d, hd⟩ := hdvd
  -- all roots of `F_n` lie in `[-17n, 12n]`
  have hb : ∀ z ∈ numRoots n + denRoots n, -(17 * n : ℤ) ≤ z ∧ z ≤ 12 * n := by
    intro z hz
    simp only [numRoots, denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hz
    omega
  obtain ⟨hx1, hx2⟩ := hb x hx.1
  obtain ⟨hx1', hx2'⟩ := hb x' hx'.1
  -- `x - x' = p² d` with `d ≠ 0`, but `|x - x'| ≤ 29n < p²`
  have e : x - x' = p * (c - c') := by linarith
  rw [hd] at e
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hne (by linarith)
  have hpp : (0 : ℤ) ≤ p * p := by positivity
  rcases lt_or_gt_of_ne hd0 with h | h
  · have hd1 : d ≤ -1 := by omega
    have := mul_le_mul_of_nonneg_left hd1 hpp
    have e' : x - x' = p * p * d := by rw [e]; ring
    linarith
  · have hd1 : 1 ≤ d := by omega
    have := mul_le_mul_of_nonneg_left hd1 hpp
    have e' : x - x' = p * p * d := by rw [e]; ring
    linarith

/-- **[6] `1, …, p` is a complete residue system.** Every integer `x` has exactly one
`k ∈ [1, p]` with `p ∣ x - k` (namely `k = (x - 1) mod p + 1`).
* Proved (≈ 20 lines).
* Directly from the PDF: yes ("representatives `1, …, p`"). -/
theorem complete_reps (p : ℕ) (hp : 0 < p) :
    ∀ x : ℤ, ∃! k, k ∈ Icc 1 (p : ℤ) ∧ (p : ℤ) ∣ x - k := by
  intro x
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp
  have h0 := Int.emod_nonneg (x - 1) hp'.ne'
  have h1 := Int.emod_lt_of_pos (x - 1) hp'
  have h2 := Int.mul_ediv_add_emod (x - 1) p
  refine ⟨(x - 1) % p + 1, ⟨?_, ⟨(x - 1) / p, by linarith⟩⟩, ?_⟩
  · rw [Finset.mem_Icc]; omega
  · rintro k ⟨hk, c, hc⟩
    rw [Finset.mem_Icc] at hk
    -- `k - k₀ = p (⌊(x-1)/p⌋ - c)` with `|k - k₀| < p`
    have e : k - ((x - 1) % p + 1) = p * ((x - 1) / p - c) := by linarith
    generalize (x - 1) / p - c = d at e
    rcases lt_trichotomy d 0 with hd | hd | hd
    · have : d ≤ -1 := by omega
      have := mul_le_mul_of_nonneg_left this hp'.le
      linarith
    · subst hd; linarith
    · have : 1 ≤ d := by omega
      have := mul_le_mul_of_nonneg_left this hp'.le
      linarith

/-! ### The node -/

/-- **Root data on the windows** (statement verbatim from `Blueprint_5255.lean`), proved from
[1]–[6]. -/
theorem window_root_data (n p : ℕ) (hn : 1 ≤ n) (hp : Eligible n p)
    (hw : inRows windowRows ((n : ℚ) / p)) :
    ∃ NU DU : Multiset ℤ, TraceHyp p (numRoots n) (denRoots n) (Icc 1 (p : ℤ)) NU DU := by
  have hp0 : 0 < p := hp.1.pos
  set f := Int.fract ((n : ℚ) / p) with hf_def
  set t := ⌊(n : ℚ) / p⌋ with ht_def
  have ht : 0 ≤ t := Int.floor_nonneg.2 (by positivity)
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  -- the window containing `{n/p}`
  obtain ⟨w, hwin⟩ : ∃ w : Fin 2, winLo w < f ∧ f < winHi w := by
    simp only [inRows, windowRows, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_true, decide_eq_true_eq] at hw
    rcases hw with h | h
    · exact ⟨0, by simpa [winLo, winHi] using h⟩
    · exact ⟨1, by simpa [winLo, winHi] using h⟩
  have hgen := fract_generic n p hp
  -- the residue data at a representative `k ∈ [1, p]`
  have hy : ∀ k ∈ Icc 1 (p : ℤ), 0 < (k : ℚ) / p ∧ (k : ℚ) / p ≤ 1 := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hpq : (0 : ℚ) < p := by exact_mod_cast hp0
    have hk1' : (1 : ℚ) ≤ k := by exact_mod_cast hk1
    have hk2' : (k : ℚ) ≤ p := by exact_mod_cast hk2
    exact ⟨div_pos (by linarith) hpq, (div_le_one hpq).2 hk2'⟩
  refine ⟨NUw w t, DUw w t, ⟨?_, ?_, ?_, ?_, complete_reps p hp0, ?_, ?_, ?_, separation n p hp⟩⟩
  · -- `odd`
    have := hp.2.1; omega
  · -- `deg`: `30n + 2 = 30n + 2`
    simp only [numRoots, denRoots, Multiset.card_add, Finset.card_val, Int.card_Icc]
    omega
  · -- `coprime`: poles are negative, zeros positive
    intro x hx hxN
    simp only [numRoots, denRoots, Multiset.mem_add, Finset.mem_val, Finset.mem_Icc] at hx hxN
    omega
  · -- `pole_le_two`: two nodup intervals
    intro x
    simp only [denRoots, Multiset.count_add]
    have h1 := Multiset.nodup_iff_count_le_one.1 (Icc (-(17 * n : ℤ)) (-(n : ℤ))).nodup x
    have h2 := Multiset.nodup_iff_count_le_one.1 (Icc (-(16 * n : ℤ)) (-(2 * n : ℤ))).nodup x
    omega
  · -- `h_ge`
    intro k hk
    obtain ⟨hN, hD⟩ := hiRoots_lift n p k hp0
    rw [← hf_def, ← ht_def] at hN hD
    rw [hN, hD]
    have hc := count_lift f ((k : ℚ) / p) hf0 t ht
    have hh := (window_cert w f _ hwin hgen (hy k hk)).1
    omega
  · -- `minimal`
    intro k hk hcard
    obtain ⟨hN, hD⟩ := hiRoots_lift n p k hp0
    rw [← hf_def, ← ht_def] at hN hD
    rw [hN, hD] at hcard ⊢
    have hc := count_lift f ((k : ℚ) / p) hf0 t ht
    have h1 : hcount0 f ((k : ℚ) / p) = -1 := by omega
    obtain ⟨e1, e2⟩ := (window_cert w f _ hwin hgen (hy k hk)).2.1 h1 t ht
    rw [e1, e2]
  · -- `affine`
    intro k hk hcard
    obtain ⟨hN, hD⟩ := hiRoots_lift n p k hp0
    rw [← hf_def, ← ht_def] at hN hD
    rw [hN, hD] at hcard ⊢
    have hc := count_lift f ((k : ℚ) / p) hf0 t ht
    have h0 : hcount0 f ((k : ℚ) / p) = 0 := by omega
    obtain ⟨a, -, ha⟩ := (window_cert w f _ hwin hgen (hy k hk)).2.2 h0 t ht
    exact ⟨a, ha⟩

end Meijer5255.WindowRootData
