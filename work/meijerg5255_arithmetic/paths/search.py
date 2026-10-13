"""Checkpointed whole-block exact CMF certificates; no asymptotic inference."""
import argparse,json,math,sys,time
from pathlib import Path
from itertools import product
from native import *
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_arithmetic/paths'
OUT.mkdir(parents=True,exist_ok=True)
ROWS=fmpq_mat([[0,0,-6,3],[0,0,0,-2],[12,0,0,0]])

def logabs(x):return math.log(abs(int(x.numerator)))-math.log(int(x.denominator))

def grid(T):
    """Separated roots and L>=3; keep at least4T coordinate moves in suffix."""
    for neg,pos,low in product((1,2,3,4),range(5),range(5)):
        n=[11*T*neg//4,12*T*neg//4,10*T*neg//4]
        a=[16*T*pos//4,17*T*pos//4]
        b=[2*T*low//4,T*low//4,0,-T*low//4,-2*T*low//4]
        if sum(a)>sum(n):continue
        if min(a)+1<=max(b) or min(n)<max(-x for x in b):continue
        ds=tuple(a+[-x for x in n]+b)
        if sum(abs(T*d-v)for d,v in zip(DIRECTION,ds))<4*T:continue
        yield f'negative{neg}_positive{pos}_lower{low}',ds,tuple(s+d for s,d in zip(START,ds))

def run(T):
    began=time.perf_counter();W=segment(START,endpoint(T));Y=ROWS*W
    cp=OUT/f'paths_T{T}.jsonl'
    done={r['name']:r for r in map(json.loads,cp.read_text().splitlines())}if cp.exists()else{}
    env=[fmpq(0)]*3;same=fmpq(0);best=fmpq(0);bestname=None
    rows=[]
    for name,ds,cut in grid(T):
        if name in done:r=done[name]
        else:
            try:A=segment(START,cut);B=segment(cut,endpoint(T))
            except(ZeroDivisionError,ValueError)as exc:r=dict(name=name,status='COMPUTATION_FAILED',error=str(exc))
            else:
                assert A*B==W
                Z=ROWS*A;suffix=[B[i,0]for i in range(4)]
                cc=[content(Z[j,i]*suffix[i]for i in range(4))for j in range(3)]
                assert all((Y[j,0]/cc[j]).denominator==1 for j in range(3))
                r=dict(T=T,name=name,status='NUMERICAL_CANDIDATE',direction_to_cut=ds,
                       prefix_rows=encode(Z),suffix_column=list(map(str,suffix)),
                       row_contents=list(map(str,cc)),all16_endpoint_entries_equal=True)
            with cp.open('a')as f:f.write(json.dumps(r)+'\n')
        if r['status']=='COMPUTATION_FAILED':continue
        cs=list(map(fmpq,r['row_contents']));env=[qlcm(x,y)for x,y in zip(env,cs)]
        common=content(cs);same=qlcm(same,common)
        if not best or common>best:best=common;bestname=name
        rows.append(r)
    independent=content(env);actual=content(Y[i,0]for i in range(3))
    assert(actual/independent).denominator==1
    s=dict(T=T,status='NUMERICAL_CANDIDATE',count=len(rows),index_convention='T=N-1 user steps',
           initial_rows=encode(ROWS),universal_content_actual=str(actual),
           best_fixed_name=bestname,best_fixed_content=str(best),
           prime_adaptive_same_path_content=str(same),independent_rows_content=str(independent),
           prime_adaptation_gain=str(same/best),row_adaptation_gain=str(independent/same),
           log_q_bound_best_fixed=logabs(Y[2,0]/best),
           log_q_bound_prime_adaptive=logabs(Y[2,0]/same),
           log_q_bound_independent_rows=logabs(Y[2,0]/independent),
           log_q_universal_actual=logabs(Y[2,0]/actual),seconds=time.perf_counter()-began)
    (OUT/f'summary_T{T}.json').write_text(json.dumps(s,indent=2)+'\n')
    print(json.dumps({k:v for k,v in s.items()if not k.endswith('content')and len(str(v))<300}),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('depths',type=int,nargs='*',default=[10,20,40,80])
    for T in ap.parse_args().depths:run(T)
