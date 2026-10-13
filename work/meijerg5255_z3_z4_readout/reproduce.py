"""Correct the native initial-condition readout and check reduced approximants."""
import csv,json,math,sys,time
from pathlib import Path
from sympy import symbols, Matrix
from ramanujantools import Position
from ramanujantools.cmf import MeijerG
from flint import arb,ctx

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'results/meijerg5255_z3_z4_readout'
OUT.mkdir(parents=True,exist_ok=True)
DEPTHS=(50,100,250,500)
axes=symbols('a0:5')+symbols('b0:5')
start_values=(1,1,0,0,0,0,0,0,0,0)
direction_values=(16,17,-11,-12,-10,2,1,0,-1,-2)
start=Position(dict(zip(axes,start_values)))
direction=Position(dict(zip(axes,direction_values)))
n=symbols('n')

def initial_condition(A,B):
    # V[2] -> -(2*zeta(3)+3*zeta(4)), V[3] -> -6*zeta(4).
    return Matrix([[0,0,-6*A,3*A-2*B],[12,0,0,0]])

begun=time.perf_counter()
print('Building the native trajectory matrix.',flush=True)
cmf=MeijerG(5,2,5,5,1)
M=cmf.trajectory_matrix(direction,start)
assert M.shape==(4,4)
build_seconds=time.perf_counter()-begun
print(json.dumps(dict(matrix_shape=M.shape,build_seconds=build_seconds)),flush=True)
walk_start=time.perf_counter()
walks=M.walk({n:1},[N-1 for N in DEPTHS],{n:0})
walk_seconds=time.perf_counter()-walk_start
print(json.dumps(dict(walk_seconds=walk_seconds)),flush=True)

rows=[]
for N,W in zip(DEPTHS,walks):
    checkpoint=OUT/f'matrix_N{N}.json'
    checkpoint.write_text(json.dumps([[str(W[i,j]) for j in range(4)] for i in range(4)]))
    V=(W/W[0,0]).col(0)
    height=max(max(len(str(abs(int(W[i,j].p)))),len(str(int(W[i,j].q)))) for i in range(4) for j in range(4))
    for A,B in [(1,0),(0,1),(1,1)]:
        pq=initial_condition(A,B)*V
        rat=pq[0]/pq[1]
        p,q=map(int,rat.as_numer_denom())
        assert q>1 and math.gcd(p,q)==1
        checks=[]
        for precision in [2*len(str(q))+300,2*len(str(q))+400]:
            ctx.dps=precision
            alpha=A*arb(3).zeta()+B*arb(4).zeta()
            error=abs(alpha-arb(p)/q)
            assert not error.contains(0)
            H=arb(q).log();E=-error.log();delta=E/H-1
            checks.append(dict(precision_dps=precision,error=error.str(30),
                delta=delta.str(30),delta_float=float(delta),
                digits_correct=float(E/arb(10).log()),log_q=float(H)))
        assert abs(checks[0]['delta_float']-checks[1]['delta_float'])<1e-12
        row=dict(N=N,walk_steps=N-1,A=A,B=B,p=str(p),q=str(q),
            reduced_denominator_digits=len(str(q)),approximation=str(rat.evalf(40)),
            matrix_entry_height_digits=height,precision_checks=checks,
            runtime_batch_walk_seconds=walk_seconds,**checks[-1])
        rows.append(row)
        print(json.dumps({k:row[k] for k in ['N','A','B','reduced_denominator_digits','approximation','delta','digits_correct']}),flush=True)

slopes={}
for A,B in [(1,0),(0,1),(1,1)]:
    group=[r for r in rows if (r['A'],r['B'])==(A,B)][-3:]
    xm=sum(r['N'] for r in group)/len(group)
    def slope(key):
        ym=sum(r[key] for r in group)/len(group)
        return sum((r['N']-xm)*(r[key]-ym) for r in group)/sum((r['N']-xm)**2 for r in group)
    slopes[f'{A},{B}']=slope('digits_correct')*math.log(10)/slope('log_q')-1
record=dict(status='NUMERICAL_CANDIDATE',cmf_family='MeijerG',m=5,n=2,p=5,q=5,z=1,
    initial_point=start_values,trajectory=direction_values,orientation='forward',
    dimension=4,column=0,gauge='native trajectory_matrix scalar gauge; normalized by W[0,0] for readout',
    index_convention='User convention: N-1 steps from trajectory-matrix index n=0',
    numerator_row=['0','0','-6*A','3*A-2*B'],denominator_row=[12,0,0,0],
    coordinate_limits={'V[2]':'-2*zeta(3)-3*zeta(4)','V[3]':'-6*zeta(4)'},
    depths=DEPTHS,build_seconds=build_seconds,batch_walk_seconds=walk_seconds,
    last_three_depth_delta_slopes=slopes,rows=rows,
    scope='Readout correction and finite numerical validation, not a new candidate search or proof of the stated coordinate limits.')
(OUT/'readout_check.json').write_text(json.dumps(record,indent=2)+'\n')
with (OUT/'approximants.csv').open('w') as f:
    fields=['N','A','B','p','q','reduced_denominator_digits','error','delta','digits_correct','precision_dps','matrix_entry_height_digits','runtime_batch_walk_seconds']
    writer=csv.DictWriter(f,fields,extrasaction='ignore');writer.writeheader();writer.writerows(rows)
print(json.dumps(dict(delta_slopes=slopes,total_seconds=time.perf_counter()-begun)),flush=True)
