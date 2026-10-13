"""Certified Arb errors for reduced native approximants at cached depths."""
import argparse,json,math,sys,time
from pathlib import Path
from flint import arb,ctx,fmpq
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_improved/residuals'
def measure(N):
    W=[fmpq(s)for s in json.loads((OUT/f'column_N{N}.json').read_text())['column']]
    ratios={(1,0):(-6*W[2]+3*W[3])/(12*W[0]),
            (1,1):(-6*W[2]+W[3])/(12*W[0])}
    precision=math.ceil(112.81*N/math.log(10))+150
    checks={k:[]for k in ratios}
    for dps in (precision,precision+100):
        ctx.dps=dps;begun=time.perf_counter()
        z3=arb(3).zeta();z4=arb.pi()**4/90
        for (A,B),rat in ratios.items():
            assert rat.denominator>1
            error=abs(A*z3+B*z4-arb(rat))
            assert not error.contains(0),(N,dps,A,B)
            E=-error.log();H=arb(rat.denominator).log();delta=E/H-1
            checks[(A,B)].append(dict(dps=dps,error=error.str(40),delta=delta.str(40),
                delta_float=float(delta),minus_log_error=float(E),log_q=float(H),
                digits_correct=float(E/arb(10).log()),elapsed_seconds=time.perf_counter()-begun))
        print(json.dumps(dict(N=N,dps=dps,elapsed_seconds=time.perf_counter()-begun)),flush=True)
    rows=[]
    for (A,B),rat in ratios.items():
        c=checks[(A,B)];assert abs(c[0]['delta_float']-c[1]['delta_float'])<1e-13
        rows.append(dict(N=N,n=N-1,A=A,B=B,p=str(rat.numerator),q=str(rat.denominator),
            reduced_denominator_digits=len(str(rat.denominator)),precision_checks=c,**c[-1]))
    record=dict(status='NUMERICAL_CANDIDATE',N=N,scope='Certified finite-depth Arb error enclosures for exact reduced approximants; no uniform arithmetic claim.',rows=rows)
    (OUT/f'delta_N{N}.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(dict(N=N,results=[{k:r[k]for k in('A','B','delta','digits_correct','log_q')}for r in rows])),flush=True)
    return record
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('depths',nargs='*',type=int,default=[1000,2000,4000,8000]);args=ap.parse_args()
    for N in args.depths:
        if not (OUT/f'delta_N{N}.json').exists():measure(N)
    records=[json.loads((OUT/f'delta_N{N}.json').read_text())for N in args.depths]
    summaries=[]
    for A,B in((1,0),(1,1)):
        rows=[r for z in records for r in z['rows']if(r['A'],r['B'])==(A,B)]
        grp=rows[-3:];xm=sum(r['N']for r in grp)/len(grp)
        def slope(k):
            ym=sum(r[k]for r in grp)/len(grp)
            return sum((r['N']-xm)*(r[k]-ym)for r in grp)/sum((r['N']-xm)**2 for r in grp)
        summaries.append(dict(A=A,B=B,depths=[r['N']for r in rows],deltas=[r['delta_float']for r in rows],
            E_slope=slope('minus_log_error'),H_slope=slope('log_q'),delta_slope=slope('minus_log_error')/slope('log_q')-1))
    (OUT/'delta_summary.json').write_text(json.dumps(dict(status='NUMERICAL_CANDIDATE',summaries=summaries),indent=2)+'\n')
    print(json.dumps(summaries,indent=2))
