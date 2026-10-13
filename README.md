# MeijerG(5,2,5,5,1) approximants to ζ(3) and ζ(4)

This repository studies the forward native CMF trajectory with starting point
`(1,1,0,0,0;0,0,0,0,0)` and direction
`(16,17,-11,-12,-10;2,1,0,-1,-2)`. Its two readouts give rational
approximants to fixed combinations `A ζ(3) + B ζ(4)`. The main account is the
[improved manuscript](results/meijerg5255_improved/meijerg_zeta3_zeta4_improved.pdf)
([TeX source](results/meijerg5255_improved/meijerg_zeta3_zeta4_improved.tex)).

**Main result.** Let `r_N(A,B)` be the prescribed approximant,
`q_N(A,B)` its *reduced* positive denominator, and

```text
δ_N(A,B) = -1 - log|A ζ(3) + B ζ(4) - r_N(A,B)| / log q_N(A,B).
```

For every fixed integer pair `(A,B) ≠ (0,0)`,

```text
liminf δ_N(A,B) > 0.01634832;
liminf δ_N(A,0) > 0.22626234   when A ≠ 0.
```

An exact approximant is assigned `δ_N = +∞`. The same exponents apply to fixed
rational coefficients after clearing a fixed denominator. These are bounds for
this sequence of reduced approximants; they are not irrationality-measure bounds
or claims about an exact limiting value.

## Proof and verification status

The manuscript proves the uniform arithmetic improvement using a rational
kernel, prime-carry chambers, first-order shells, and a second-order trace
cancellation on the periodic windows `{n/p} ∈ (1/10, 2/19)` and
`{n/p} ∈ (11/12, 15/16)`, where `n = N - 1`. Its common divisor has logarithmic
density greater than `30.45854724380549`. The growth and approximation-error
rates are accepted analytic inputs in the manuscript; the Lean formalization
below proves them too, so the complete result assumes only the prime number
theorem. See [REPORT.txt](results/meijerg5255_improved/REPORT.txt) for the
manuscript's scope, finite-depth checks, and limitations.

The [`lean/`](lean/) directory contains a Lean 4 formalization (Mathlib,
`leanprover/lean4:v4.35.0-rc4`) of the main theorems `main_joint` and
`main_pure3`, including the CMF readout identity and the analytic growth and
decay input (which the manuscript accepts but the formalization proves, from
code adapted from `../zetas_irr`). It builds with `lake build`; the only
unproved statement is the prime number theorem
([`lean/Meijer5255/PNT.lean`](lean/Meijer5255/PNT.lean)), so `#print axioms`
shows the standard axioms plus that one `sorry`. See
[`lean/DEPENDENCY_GRAPH.md`](lean/DEPENDENCY_GRAPH.md) for the structure and
[`lean/BUILD_TIMES.md`](lean/BUILD_TIMES.md) for build times; the original plan
is the [Lean handoff](LEAN_HANDOFF.md).

## Reproducing the certificates

From this repository root, install the Python dependencies and run the improved
checks:

```sh
python -m pip install -r work/meijerg5255_improved/requirements.txt
python work/meijerg5255_improved/arithmetic/second_order_certificate.py
python work/meijerg5255_improved/audit/independent_affine_chambers.py
python work/meijerg5255_improved/paths/check_periodic_trace.py
python work/meijerg5255_improved/residuals/infinite_density.py
python work/meijerg5255_improved/residuals/final_bound_certificate.py
python work/meijerg5255_improved/verify_improved.py
python work/meijerg5255_improved/residuals/measure_delta.py
```

The symbolic arithmetic and tail checks use exact rational arithmetic.
Finite-depth computations supplement the written trace proof; the scripts do
not establish the accepted analytic estimates. Existing profile and delta
files serve as checkpoints. For commands to generate a new depth, see the
[result bundle README](results/meijerg5255_improved/README.txt).

## Repository layout

| Path | Contents |
|---|---|
| [`results/meijerg5255_improved/`](results/meijerg5255_improved/) | Final manuscript, report, experiment specification, exact certificates, and finite-depth results. |
| [`work/meijerg5255_improved/`](work/meijerg5255_improved/) | Scripts and source material for the second-order trace, density, final bounds, and numerical checks. |
| [`results/meijerg5255_arithmetic/`](results/meijerg5255_arithmetic/) and [`work/meijerg5255_arithmetic/`](work/meijerg5255_arithmetic/) | Predecessor arithmetic proof, baseline certificates, native matrices, and spectral calculations. |
| [`results/meijerg5255_z3_z4_readout/`](results/meijerg5255_z3_z4_readout/) and [`work/meijerg5255_z3_z4_readout/`](work/meijerg5255_z3_z4_readout/) | Earlier readout checks and reproduction code. |
| [`LEAN_HANDOFF.md`](LEAN_HANDOFF.md) and [`lean/`](lean/) | Formalization plan and the Lean 4 formalization (only the prime number theorem is assumed). |
