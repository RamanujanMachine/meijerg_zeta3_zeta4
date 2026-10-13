Start with meijerg_zeta3_zeta4_improved.pdf or its editable .tex source.
REPORT.txt records the result, verification, numerical data, and limitations.

The ZIP preserves the original work/ and results/ relative paths. Extract
it into a clean directory and run from that directory:

  python -m pip install -r work/meijerg5255_improved/requirements.txt
  python work/meijerg5255_improved/arithmetic/second_order_certificate.py
  python work/meijerg5255_improved/audit/independent_affine_chambers.py
  python work/meijerg5255_improved/paths/check_periodic_trace.py
  python work/meijerg5255_improved/residuals/infinite_density.py
  python work/meijerg5255_improved/residuals/final_bound_certificate.py
  python work/meijerg5255_improved/verify_improved.py
  python work/meijerg5255_improved/residuals/measure_delta.py

The symbolic arithmetic and tail checks use exact rational arithmetic.
The written trace lemma is part of the argument; executable checks are not
a replacement for that lemma or for the accepted analytic growth estimates.

Numerical scripts are checkpointed. To generate a new depth, for example:
  python work/meijerg5255_improved/residuals/profile.py 16000
  python work/meijerg5255_improved/residuals/measure_delta.py 16000

Existing profile and delta outputs are retained as checkpoints. To force
recalculation, move the relevant checkpoint aside before running the script.
The exact native matrix implementation is also included under
work/meijerg5255_arithmetic/paths/native.py.

The prior work/meijerg5255_arithmetic/ material is retained for dependencies
and comparison. The new manuscript and final_bound_certificate.json state
the final improved result. Earlier exploratory files are historical data.
