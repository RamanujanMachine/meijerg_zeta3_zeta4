import json,sys,time
from pathlib import Path
from native import *
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
for N in map(int,sys.argv[1:]or[50]):
    t=time.perf_counter();W=segment(START,endpoint(N-1))
    cached=decode(json.loads((ROOT/f'results/meijerg5255_z3_z4_readout/matrix_N{N}.json').read_text()))
    ratio=W[0,0]/cached[0,0]
    assert W==cached*ratio
    print(json.dumps(dict(N=N,steps=N-1,scalar_to_cached=str(ratio),seconds=time.perf_counter()-t)),flush=True)
