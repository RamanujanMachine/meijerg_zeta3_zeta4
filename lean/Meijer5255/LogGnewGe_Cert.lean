/-
# Helper for `LogGnewGe.lean`: the kernel certificate behind `gamma_cert` (sorry-free)

Each row `(a, b, v)` of the three families (`ψ`, shells, windows) is written as
`(aₙ, a_d, bₙ, b_d, v)` with `a = aₙ/a_d`, `b = bₙ/b_d`, so that
`v (1/(t+a) - 1/(t+b)) = v (a_d bₙ - aₙ b_d) / ((t a_d + aₙ)(t b_d + bₙ))`.
Scaling by `10¹⁶` and rounding down (`ℕ` division) gives lower bounds `natTerm t c` for the
periods `t < 1000` and `natTail K c` for the tail bound at `K = 1000`; their sums are evaluated by
`decide +kernel` (directed-rounding pattern of zeta2 `blueprint_gamma_sumA.lean`). The total
`6 + 24.4585472438030979 = 30.4585472438030979` exceeds `γ_new = 30.45854724` by `3.8 · 10⁻⁹`.
-/
import Meijer5255.definitions

open Finset

namespace Meijer5255.LogGnewGeCert

open Meijer5255

/-- A row `(aₙ, a_d, bₙ, b_d, v)`. -/
abbrev Row5 := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The rational row `(aₙ/a_d, bₙ/b_d, v)`. -/
def toRow (c : Row5) : ℚ × ℚ × ℕ := ((c.1 : ℚ) / c.2.1, (c.2.2.1 : ℚ) / c.2.2.2.1, c.2.2.2.2)

/-- The scale `10¹⁶` of the directed rounding. -/
def scale : ℕ := 10 ^ 16

/-- `⌊10¹⁶ v (1/(t+a) - 1/(t+b))⌋`. -/
def natTerm (t : ℕ) (c : Row5) : ℕ :=
  scale * c.2.2.2.2 * (c.2.1 * c.2.2.1 - c.1 * c.2.2.2.1) /
    ((t * c.2.1 + c.1) * (t * c.2.2.2.1 + c.2.2.1))

/-- `⌊10¹⁶ v 2(b-a)/(2K+a+b)⌋ + ⌊10¹⁶ v (1/(K+a) - 1/(K+b))/2⌋`. -/
def natTail (K : ℕ) (c : Row5) : ℕ :=
  2 * scale * c.2.2.2.2 * (c.2.1 * c.2.2.1 - c.1 * c.2.2.2.1) /
      (2 * K * c.2.1 * c.2.2.2.1 + c.1 * c.2.2.2.1 + c.2.2.1 * c.2.1) +
    scale * c.2.2.2.2 * (c.2.1 * c.2.2.1 - c.1 * c.2.2.2.1) /
      (2 * ((K * c.2.1 + c.1) * (K * c.2.2.2.1 + c.2.2.1)))

/-- The rounded contribution of period `t` of a family. -/
def periodNat (l : List Row5) (t : ℕ) : ℕ := (l.map (natTerm t)).sum

/-- The rounded tail of a family. -/
def tailNat (l : List Row5) (K : ℕ) : ℕ := (l.map (natTail K)).sum

/-- The rows of the `ψ` family. -/
def dPsi : List Row5 :=
  [(1, 15, 1, 13, 1), (1, 13, 1, 12, 2), (1, 12, 1, 10, 3), (2, 15, 2, 13, 1), (2, 13, 3, 17, 2),
   (3, 17, 2, 11, 1), (2, 11, 1, 5, 2), (1, 5, 4, 15, 1), (4, 15, 5, 17, 3), (5, 17, 3, 10, 2),
   (1, 3, 2, 5, 2), (2, 5, 7, 15, 1), (7, 15, 9, 19, 3), (9, 19, 1, 2, 2), (8, 15, 7, 13, 1),
   (7, 13, 3, 5, 2), (3, 5, 2, 3, 1), (2, 3, 11, 16, 3), (11, 16, 9, 13, 2), (9, 13, 7, 10, 3),
   (11, 15, 14, 19, 2), (14, 19, 3, 4, 1), (3, 4, 4, 5, 2), (4, 5, 13, 16, 1), (9, 11, 16, 19, 1),
   (13, 15, 7, 8, 2), (7, 8, 15, 17, 3), (15, 17, 9, 10, 2), (14, 15, 17, 18, 2),
   (17, 18, 18, 19, 1)]

/-- The rows of the shell family. -/
def dShell : List Row5 :=
  [(1, 11, 1, 8, 1), (3, 13, 4, 17, 1), (3, 11, 5, 18, 1), (4, 13, 5, 16, 1), (4, 11, 7, 19, 1),
   (5, 13, 7, 18, 1), (5, 12, 8, 19, 1), (5, 11, 8, 17, 1), (6, 11, 9, 16, 1), (7, 12, 10, 17, 1),
   (7, 11, 11, 17, 1), (7, 10, 12, 17, 1), (8, 11, 11, 15, 1), (10, 11, 16, 17, 1)]

/-- The rows of the window family. -/
def dWin : List Row5 := [(1, 10, 2, 19, 1), (11, 12, 15, 16, 1)]

/-- Positivity and order of a row: `0 < aₙ`, `0 < a_d`, `0 < b_d`, `a ≤ b`. -/
def RowOK (c : Row5) : Prop := 0 < c.1 ∧ 0 < c.2.1 ∧ 0 < c.2.2.2.1 ∧ c.1 * c.2.2.2.1 ≤ c.2.1 * c.2.2.1

instance (c : Row5) : Decidable (RowOK c) := by unfold RowOK; infer_instance

theorem psi_eq : psiRows = dPsi.map toRow := by decide +kernel

theorem shell_eq : shellRows.map (fun r => (r.1, r.2, 1)) = dShell.map toRow := by decide +kernel

theorem win_eq : windowRows.map (fun r => (r.1, r.2, 1)) = dWin.map toRow := by decide +kernel

theorem psi_ok : ∀ c ∈ dPsi, RowOK c := by decide +kernel

theorem shell_ok : ∀ c ∈ dShell, RowOK c := by decide +kernel

theorem win_ok : ∀ c ∈ dWin, RowOK c := by decide +kernel

theorem psi_sum : ∑ t ∈ range 1000, periodNat dPsi t = 202366642995109172 := by decide +kernel

theorem shell_sum : ∑ t ∈ range 1000, periodNat dShell t = 36747281958055130 := by decide +kernel

theorem win_sum : ∑ t ∈ range 1000, periodNat dWin t = 5458131713063922 := by decide +kernel

theorem psi_tail : tailNat dPsi 1000 = 11608558513562 := by decide +kernel

theorem shell_tail : tailNat dShell 1000 = 1546316457309 := by decide +kernel

theorem win_tail : tailNat dWin 1000 = 260896831884 := by decide +kernel

end Meijer5255.LogGnewGeCert
