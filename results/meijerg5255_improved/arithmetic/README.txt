Second-order arithmetic improvement for the MeijerG(5,2,5,5,1) trajectory

The mathematical argument is in second_order_trace.tex. Its root deformation
lemma proves a p-adic trace cancellation modulo p^2. The exact affine interval
certificate establishes its hypotheses uniformly in the integer lift t=floor(n/p),
not by sampling t. It identifies precisely the two fractional windows
    1/10 < frac(n/p) < 2/19,
    11/12 < frac(n/p) < 15/16.
For primes p>29 and p^2>30n, the resulting bounds are
    v_p(Q_n)>=3, v_p(P_3,n)>=0, v_p(P_4,n)>=-1.
This adds one prime factor beyond the previous first-order shell divisor.

The code certificate contains 270 exact Farey-29 abscissa cells, nine accepted
cells, and affine interval endpoint cancellation identities. Numerical checks
of trajectory readouts and denominators are recorded separately by the main
verification scripts. They are validation, not the uniform argument.

The certificate script currently runs from the repository root and uses
work/meijerg5255_arithmetic/arithmetic/all_shell_cells.py and its JSON table.
Run:
    work/.venv_4f3/bin/python work/meijerg5255_improved/arithmetic/second_order_certificate.py

The 1000-term density lower bound in this folder is deliberately conservative.
The stronger infinite-tail density certificate and the resulting numerical delta
bounds are in ../residuals/final_bound_certificate.json and infinite_density.json.
Those applications retain the accepted analytic growth/error assumptions.
