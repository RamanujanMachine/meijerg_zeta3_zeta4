/-
# Definitions for the `A ζ(3) + B ζ(4)` formalization (MeijerG(5,2,5,5,1) trajectory)

All definitions shared by `Blueprint_5255.lean` and the node files `Meijer5255/<Node>.lean`:
zeta values, the native CMF and its block path `W_n`, the approximants and `δ_N` (§1); the kernel
`F_n` via its root multisets, partial-fraction coefficients and the readouts `Q_n, P_{3,n},
P_{4,n}` (§2); valuations, eligible primes, carry profiles, shells and windows; the data of the
second-order trace lemma; the numerical constants. Split out of `Blueprint_5255.lean` (whose
module docstring documents them) so that every node file can import them without the blueprint.
-/
import Mathlib

open Filter Topology Finset
open scoped Matrix

noncomputable section

namespace Meijer5255

/-! ## §1. Zeta values, the native CMF and the approximants -/

/-- `ζ(3)` as a real number. -/
def ζ3 : ℝ := (riemannZeta 3).re

/-- `ζ(4)` as a real number. -/
def ζ4 : ℝ := (riemannZeta 4).re

/-- The target `α_{A,B} = A ζ(3) + B ζ(4)`. -/
def alpha (A B : ℤ) : ℝ := A * ζ3 + B * ζ4

/-- A vertex `w = (a₀,…,a₄; b₀,…,b₄) ∈ ℤ¹⁰` of the MeijerG(5,2,5,5,1) lattice. -/
structure Vertex where
  /-- The upper parameters `a₀,…,a₄`. -/
  a : Fin 5 → ℤ
  /-- The lower parameters `b₀,…,b₄`. -/
  b : Fin 5 → ℤ

/-- `D_w(x) = ∏ᵢ (x - (aᵢ - 1)) - ∏ⱼ (x - bⱼ)`, a polynomial of degree `≤ 4`. -/
def Vertex.D (w : Vertex) : Polynomial ℚ :=
  ∏ i, (Polynomial.X - Polynomial.C ((w.a i : ℚ) - 1)) -
    ∏ j, (Polynomial.X - Polynomial.C (w.b j : ℚ))

/-- The companion matrix `θ(w)`: `θ_{i,j} = [i = j+1]` for `j < 3` and `θ_{i,3} = -d_i/d_4`, where
`D_w = ∑ d_k x^k`. It represents `θ = z d/dz` (i.e. `-t` in the Mellin variable). -/
def Vertex.theta (w : Vertex) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of fun i j =>
    if (j : ℕ) < 3 then (if (i : ℕ) = j + 1 then 1 else 0) else -(w.D.coeff i) / w.D.coeff 4

/-- An elementary move of one coordinate by `±1`. -/
inductive Move
  | aDown (i : Fin 5)
  | aUp (i : Fin 5)
  | bUp (j : Fin 5)
  | bDown (j : Fin 5)

/-- The vertex reached by a move. -/
def Move.next : Move → Vertex → Vertex
  | .aDown i, w => ⟨Function.update w.a i (w.a i - 1), w.b⟩
  | .aUp i, w => ⟨Function.update w.a i (w.a i + 1), w.b⟩
  | .bUp j, w => ⟨w.a, Function.update w.b j (w.b j + 1)⟩
  | .bDown j, w => ⟨w.a, Function.update w.b j (w.b j - 1)⟩

/-- The sign `sᵢ = +1` for `i ∈ {0,1}` (the `m = 2` upper parameters) and `-1` otherwise. -/
def aSign (i : Fin 5) : ℚ := if (i : ℕ) < 2 then 1 else -1

/-- The native step matrix of a move from `w` (to `v = m.next w`), exactly as in
`work/meijerg5255_arithmetic/paths/native.py`:
`aᵢ↓ : sᵢ (θ(w) - (aᵢ-1) I)`, `aᵢ↑ : (sᵢ (θ(v) - aᵢ I))⁻¹`, `bⱼ↑ : bⱼ I - θ(w)`,
`bⱼ↓ : ((bⱼ-1) I - θ(v))⁻¹`, where `aᵢ, bⱼ` are the coordinates of `w`. -/
def Move.mat : Move → Vertex → Matrix (Fin 4) (Fin 4) ℚ
  | .aDown i, w => aSign i • (w.theta - ((w.a i : ℚ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℚ))
  | .aUp i, w =>
      (aSign i • (((Move.aUp i).next w).theta - (w.a i : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ)))⁻¹
  | .bUp j, w => (w.b j : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) - w.theta
  | .bDown j, w =>
      (((w.b j : ℚ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℚ) - ((Move.bDown j).next w).theta)⁻¹

/-- The ordered product `E₁ E₂ ⋯ E_m` of step matrices along a list of moves starting at `w`. -/
def walkFrom : Vertex → List Move → Matrix (Fin 4) (Fin 4) ℚ
  | _, [] => 1
  | w, m :: ms => m.mat w * walkFrom (m.next w) ms

/-- The initial vertex `(1,1,0,0,0; 0,0,0,0,0)`. -/
def startVertex : Vertex := ⟨![1, 1, 0, 0, 0], ![0, 0, 0, 0, 0]⟩

/-- The paper's block path from `(1,1,0,0,0;0,0,0,0,0)` to
`(1+16n, 1+17n, -11n, -12n, -10n; 2n, n, 0, -n, -2n)`: first `a₂,a₃,a₄` down, then `a₀,a₁` up,
then `b₀,b₁` up, finally `b₃,b₄` down. -/
def blockPath (n : ℕ) : List Move :=
  List.replicate (11 * n) (.aDown 2) ++ List.replicate (12 * n) (.aDown 3) ++
    List.replicate (10 * n) (.aDown 4) ++ List.replicate (16 * n) (.aUp 0) ++
    List.replicate (17 * n) (.aUp 1) ++ List.replicate (2 * n) (.bUp 0) ++
    List.replicate n (.bUp 1) ++ List.replicate n (.bDown 3) ++ List.replicate (2 * n) (.bDown 4)

/-- The native CMF product `W_n` along the block path. -/
def W (n : ℕ) : Matrix (Fin 4) (Fin 4) ℚ := walkFrom startVertex (blockPath n)

/-- The initial-condition matrix `R_{A,B} = [[0, 0, -6A, 3A-2B], [12, 0, 0, 0]]`. -/
def readoutMat (A B : ℤ) : Matrix (Fin 2) (Fin 4) ℚ :=
  !![0, 0, -6 * A, 3 * A - 2 * B; 12, 0, 0, 0]

/-- The approximant `r_N(A,B)`: the quotient of the two entries of `R_{A,B} W_n e₀`. -/
def approxCMF (n : ℕ) (A B : ℤ) : ℚ :=
  let v := readoutMat A B *ᵥ (W n *ᵥ Pi.single 0 1)
  v 0 / v 1

/-- The exponent of a rational approximation `r = p/q` (reduced) of `α`:
`δ = -1 - log|α - r| / log q`, and `δ = +∞` for an exact approximant. (When `q = 1` and `α ≠ r`
the paper leaves `δ` undefined; the junk value here is never used, see `delta_criterion`.) -/
def deltaOf (α : ℝ) (r : ℚ) : EReal :=
  if α = r then ⊤ else ((-1 - Real.log |α - r| / Real.log r.den : ℝ) : EReal)

/-- The paper's `δ_N(A,B)`, at depth `N`, i.e. after `n = N - 1` steps. -/
def deltaN (N : ℕ) (A B : ℤ) : EReal := deltaOf (alpha A B) (approxCMF (N - 1) A B)

/-! ## §2. The rational kernel `F_n` and the readouts

`F_n(t) = ∏_{u=0}^{2} (t-(10+u)n)_{10n} / ((t+n)_{16n+1} (t+2n)_{14n+1})`, given by its root
multisets. Partial fractions: `F_n = ∑_{j=n}^{17n} (a_j/(t+j)² + b_j/(t+j))`. -/

/-- Numerator roots of `F_n`: `[1,10n] ∪ [n+1,11n] ∪ [2n+1,12n]` (with multiplicity). -/
def numRoots (n : ℕ) : Multiset ℤ :=
  (Icc (1 : ℤ) (10 * n)).val + (Icc ((n : ℤ) + 1) (11 * n)).val +
    (Icc (2 * (n : ℤ) + 1) (12 * n)).val

/-- Denominator roots of `F_n`: `[-17n,-n] ∪ [-16n,-2n]` (with multiplicity). -/
def denRoots (n : ℕ) : Multiset ℤ :=
  (Icc (-(17 * n : ℤ)) (-(n : ℤ))).val + (Icc (-(16 * n : ℤ)) (-(2 * n : ℤ))).val

/-- The monic polynomial `∏_{x ∈ s} (X - x)`. -/
def rootPoly (s : Multiset ℤ) : Polynomial ℚ :=
  (s.map fun x => Polynomial.X - Polynomial.C (x : ℚ)).prod

/-- Partial-fraction coefficients (double, simple) of `rootPoly Nr / rootPoly Dr` at the pole `x`.
With `E = ∏_{y ∈ Dr, y ≠ x} (X - y)`: at a double pole they are `(N/E)(x)` and `(N/E)'(x)`, at a
simple pole `0` and `(N/E)(x)`; `(0,0)` otherwise. -/
def pfCoeff (Nr Dr : Multiset ℤ) (x : ℤ) : ℚ × ℚ :=
  let N := rootPoly Nr
  let E := rootPoly (Dr.filter (· ≠ x))
  if Dr.count x = 2 then
    (N.eval (x : ℚ) / E.eval (x : ℚ),
      (Polynomial.derivative N * E - N * Polynomial.derivative E).eval (x : ℚ) /
        E.eval (x : ℚ) ^ 2)
  else if Dr.count x = 1 then (0, N.eval (x : ℚ) / E.eval (x : ℚ)) else (0, 0)

/-- The double-pole coefficient `a_j` of `F_n` at `t = -j`. -/
def aCoef (n j : ℕ) : ℚ := (pfCoeff (numRoots n) (denRoots n) (-(j : ℤ))).1

/-- The simple-pole coefficient `b_j` of `F_n` at `t = -j`. -/
def bCoef (n j : ℕ) : ℚ := (pfCoeff (numRoots n) (denRoots n) (-(j : ℤ))).2

/-- Generalised harmonic number `H^{(r)}_m = ∑_{k=1}^m k^{-r}`. -/
def harm (r m : ℕ) : ℚ := ∑ k ∈ Icc 1 m, 1 / (k : ℚ) ^ r

/-- `Q_n = ∑_j a_j`. -/
def Q (n : ℕ) : ℚ := ∑ j ∈ Icc n (17 * n), aCoef n j

/-- `P_{3,n} = ∑_j (a_j H^{(3)}_{j+2n} + b_j H^{(2)}_{j+2n} / 2)`. -/
def P3 (n : ℕ) : ℚ :=
  ∑ j ∈ Icc n (17 * n), (aCoef n j * harm 3 (j + 2 * n) + bCoef n j * harm 2 (j + 2 * n) / 2)

/-- `P_{4,n} = ∑_j (a_j H^{(4)}_{j+2n} + b_j H^{(3)}_{j+2n} / 3)`. -/
def P4 (n : ℕ) : ℚ :=
  ∑ j ∈ Icc n (17 * n), (aCoef n j * harm 4 (j + 2 * n) + bCoef n j * harm 3 (j + 2 * n) / 3)

/-- `C_n = (15n)!² / (10n)!³`. -/
def Cn (n : ℕ) : ℚ := ((15 * n).factorial : ℚ) ^ 2 / ((10 * n).factorial : ℚ) ^ 3

/-- `d_m = lcm(1, …, m)`. -/
def dlcm (m : ℕ) : ℕ := (Icc 1 m).lcm id

/-- The order-three integer form `6 C_n d_{19n}³ (Q_n, P_{3,n})` (used when `B = 0`). -/
def Z3v (n : ℕ) : Fin 2 → ℚ :=
  ![6 * Cn n * dlcm (19 * n) ^ 3 * Q n, 6 * Cn n * dlcm (19 * n) ^ 3 * P3 n]

/-- The order-four integer form `6 C_n d_{19n}⁴ (Q_n, P_{3,n}, P_{4,n})`. -/
def Z4v (n : ℕ) : Fin 3 → ℚ :=
  ![6 * Cn n * dlcm (19 * n) ^ 4 * Q n, 6 * Cn n * dlcm (19 * n) ^ 4 * P3 n,
    6 * Cn n * dlcm (19 * n) ^ 4 * P4 n]

/-! ## Local valuations, eligible primes, carry profiles -/

/-- `x = 0 ∨ k ≤ v_p(x)`, i.e. `x ∈ p^k ℤ_(p)` (avoids the junk value `v_p(0) = 0`). -/
def ValGE (p : ℕ) (k : ℤ) (x : ℚ) : Prop := x = 0 ∨ k ≤ padicValRat p x

/-- Eligible primes (E): `p > 29`, `p² > 30n`, `p ∤ n`. -/
def Eligible (n p : ℕ) : Prop := p.Prime ∧ 29 < p ∧ 30 * n < p ^ 2 ∧ ¬ p ∣ n

instance (n : ℕ) : DecidablePred (Eligible n) := fun p => by unfold Eligible; infer_instance

/-- `c(x) = 2⌊15x⌋ - 3⌊10x⌋`, the valuation of `C_n` at an eligible `p` with `x = n/p`. -/
def cfun (x : ℚ) : ℤ := 2 * ⌊15 * x⌋ - 3 * ⌊10 * x⌋

/-- `x` lies in a lift of one of the open intervals `(a,b)`, i.e. `a < {x} < b` for some row. -/
def inRows (rows : List (ℚ × ℚ)) (x : ℚ) : Bool :=
  rows.any fun r => decide (r.1 < Int.fract x ∧ Int.fract x < r.2)

/-- The periodic carry table of the appendix: rows `(a, b, ψ)` with `ψ ≠ 0` on one period. -/
def psiRows : List (ℚ × ℚ × ℕ) :=
  [(1/15, 1/13, 1), (1/13, 1/12, 2), (1/12, 1/10, 3), (2/15, 2/13, 1), (2/13, 3/17, 2),
   (3/17, 2/11, 1), (2/11, 1/5, 2), (1/5, 4/15, 1), (4/15, 5/17, 3), (5/17, 3/10, 2),
   (1/3, 2/5, 2), (2/5, 7/15, 1), (7/15, 9/19, 3), (9/19, 1/2, 2), (8/15, 7/13, 1),
   (7/13, 3/5, 2), (3/5, 2/3, 1), (2/3, 11/16, 3), (11/16, 9/13, 2), (9/13, 7/10, 3),
   (11/15, 14/19, 2), (14/19, 3/4, 1), (3/4, 4/5, 2), (4/5, 13/16, 1), (9/11, 16/19, 1),
   (13/15, 7/8, 2), (7/8, 15/17, 3), (15/17, 9/10, 2), (14/15, 17/18, 2), (17/18, 18/19, 1)]

/-- The baseline periodic profile `ψ({x})` (zero at the excluded rational endpoints). -/
def psi (x : ℚ) : ℕ :=
  (psiRows.map fun r => if r.1 < Int.fract x ∧ Int.fract x < r.2.1 then r.2.2 else 0).sum

/-- The upper harmonic gain `h₀(n/p)`: `3, 2, 1` for `p ∈ (18n,19n), (17n,18n), (16n,17n)`. -/
def hgain (n p : ℕ) : ℕ :=
  if 18 * n < p ∧ p < 19 * n then 3 else if 17 * n < p ∧ p < 18 * n then 2
  else if 16 * n < p ∧ p < 17 * n then 1 else 0

/-- The fourteen first-order shells `𝒮` (paper §7). -/
def shellRows : List (ℚ × ℚ) :=
  [(1/11, 1/8), (3/13, 4/17), (3/11, 5/18), (4/13, 5/16), (4/11, 7/19),
   (5/13, 7/18), (5/12, 8/19), (5/11, 8/17), (6/11, 9/16), (7/12, 10/17),
   (7/11, 11/17), (7/10, 12/17), (8/11, 11/15), (10/11, 16/17)]

/-- The two second-order windows `𝒯 = (1/10, 2/19) ∪ (11/12, 15/16)` (paper (S2)). -/
def windowRows : List (ℚ × ℚ) := [(1/10, 2/19), (11/12, 15/16)]

/-- The exponent of `p` in `G_n^{new}`: `ψ({n/p}) + h₀(n/p) + 𝟙[{n/p} ∈ 𝒮] + 𝟙[{n/p} ∈ 𝒯]`. -/
def gExp (n p : ℕ) : ℕ :=
  psi ((n : ℚ) / p) + hgain n p + (if inRows shellRows ((n : ℚ) / p) then 1 else 0) +
    (if inRows windowRows ((n : ℚ) / p) then 1 else 0)

/-- The improved divisor `G_n^{new} = ∏_{p eligible} p^{gExp n p}` (only `p ≤ 19n` matter). -/
def Gnew (n : ℕ) : ℕ := ∏ p ∈ (range (19 * n + 1)).filter (Eligible n), p ^ gExp n p

/-! ## Data of the second-order trace lemma -/

/-- High roots at the residue representative `k`: the multiset of `ℓ` with `k + pℓ ∈ s`. -/
def hiRoots (p : ℕ) (k : ℤ) (s : Multiset ℤ) : Multiset ℤ :=
  (s.filter fun x => (p : ℤ) ∣ x - k).map fun x => (x - k) / p

/-- Hypotheses of the trace lemma (T2) for `F = rootPoly Nr / rootPoly Dr`, representatives `R`,
and the common minimal-class kernel `U = rootPoly NU / rootPoly DU` (as root multisets). Writing
`N_k = hiRoots p k Nr`, `D_k = hiRoots p k Dr`, `h_k = |N_k| - |D_k|`: the identity of rational
functions `U_k = U` is `N_k + DU = NU + D_k`, and `U_k = (V - a) U` is
`N_k + DU = (a ::ₘ NU) + D_k`. -/
structure TraceHyp (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ) (NU DU : Multiset ℤ) : Prop where
  odd : p ≠ 2
  deg : Dr.card = Nr.card + 2
  coprime : ∀ x ∈ Dr, x ∉ Nr
  pole_le_two : ∀ x, Dr.count x ≤ 2
  complete : ∀ x : ℤ, ∃! k, k ∈ R ∧ (p : ℤ) ∣ x - k
  h_ge : ∀ k ∈ R, (hiRoots p k Dr).card ≤ (hiRoots p k Nr).card + 1
  minimal : ∀ k ∈ R, (hiRoots p k Dr).card = (hiRoots p k Nr).card + 1 →
    hiRoots p k Nr + DU = NU + hiRoots p k Dr
  affine : ∀ k ∈ R, (hiRoots p k Dr).card = (hiRoots p k Nr).card →
    ∃ a : ℤ, hiRoots p k Nr + DU = (a ::ₘ NU) + hiRoots p k Dr
  separated : ∀ k ∈ R, ∀ ℓ ∈ hiRoots p k (Nr + Dr), ∀ ℓ' ∈ hiRoots p k (Nr + Dr), ℓ ≠ ℓ' →
    ¬ (p : ℤ) ∣ ℓ - ℓ'

/-- `A_ℓ`: the sum of the double-pole coefficients over the poles `k + pℓ`, `k ∈ R`. -/
def highPoleA (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ) (ℓ : ℤ) : ℚ :=
  ∑ x ∈ Dr.toFinset.filter (fun x => x - p * ℓ ∈ R), (pfCoeff Nr Dr x).1

/-- `B_ℓ`: the sum of the simple-pole coefficients over the poles `k + pℓ`, `k ∈ R`. -/
def highPoleB (p : ℕ) (Nr Dr : Multiset ℤ) (R : Finset ℤ) (ℓ : ℤ) : ℚ :=
  ∑ x ∈ Dr.toFinset.filter (fun x => x - p * ℓ ∈ R), (pfCoeff Nr Dr x).2

/-! ## Constants -/

/-- Upper bound for the growth rate `σ = a` of `Q_n`: `a < 53.28758332263`. -/
def aGrowth : ℝ := 5328758332263 / 10 ^ 11

/-- Lower bound for the decay rate `b` of the linear forms: `b > 59.51995592483`. -/
def bDecay : ℝ := 5951995592483 / 10 ^ 11

/-- Upper bound for `30 log(3/2) = 12.16395324324…`. -/
def logCn : ℝ := 121639532433 / 10 ^ 10

/-- Lower bound for the density `γ_new ≥ 30.45854724380…` (DEN). -/
def gammaNew : ℝ := 3045854724 / 10 ^ 8

/-- The height exponent `κ_r = 30 log(3/2) + 19 r - γ_new` of `6 C_n d_{19n}^r / G_n^{new}`. -/
def kappa (r : ℕ) : ℝ := logCn + 19 * r - gammaNew

end Meijer5255
