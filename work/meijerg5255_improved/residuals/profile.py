"""Exact residual gcds beyond the baseline plus fourteen periodic shells.

Checkpoints native first columns; uses no high-precision target evaluation.
All residual patterns are numerical evidence only.
"""
import argparse,bisect,json,math,sys,time
from fractions import Fraction as F
from pathlib import Path
from flint import fmpq,fmpz

sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_improved/residuals'
OUT.mkdir(parents=True,exist_ok=True)
SHELLS=json.loads((ROOT/'work/meijerg5255_arithmetic/arithmetic/all_shell_cells.json').read_text())['rows']
LO=[F(r['lo'])for r in SHELLS]

def sieve(n):
    a=bytearray(b'\1')*(n+1);a[:2]=b'\0\0'
    for p in range(2,math.isqrt(n)+1):
        if a[p]:a[p*p::p]=b'\0'*((n-p*p)//p+1)
    return [p for p in range(2,n+1)if a[p]]
def qgcd(vs):
    a=fmpz(0);b=fmpz(1)
    for v in vs:a=a.gcd(v.numerator);b=b.lcm(v.denominator)
    return fmpq(a,b)
def logabs(q):return math.log(abs(int(q.numerator)))-math.log(int(q.denominator))
def vp(v,p):
    z=0
    while v and v%p==0:v//=p;z+=1
    return z
def lcm_to(n,primes):
    z=fmpz(1)
    for p in primes:
        if p>n:break
        q=p
        while q*p<=n:q*=p
        z*=q
    return z
def record_for(n,p):
    x=F(n,p);f=x-int(x)
    if not f:return None
    i=bisect.bisect_right(LO,f)-1;r=SHELLS[i]
    if f==F(r['lo']) or f==F(r['hi']):return None
    assert F(r['lo'])<f<F(r['hi'])
    return dict(base3=r['g3']if x<1 else r['tail'],base4=r['g4']if x<1 else r['tail'],
        shell=int(r['valid']),cell=[r['lo'],r['hi']],hmin=r['hmin'])

def checkpoint_columns(depths):
    missing=[]
    for N in depths:
        dest=OUT/f'column_N{N}.json'
        if dest.exists():continue
        old=ROOT/f'results/meijerg5255_z3_z4_readout/matrix_N{N}.json'
        if old.exists():
            M=json.loads(old.read_text());dest.write_text(json.dumps(dict(N=N,column=[row[0]for row in M],source=str(old))))
        else:missing.append(N)
    if not missing:return
    from sympy import symbols
    from ramanujantools import Position
    from ramanujantools.cmf import MeijerG
    axes=symbols('a0:5')+symbols('b0:5');n=symbols('n')
    start=Position(dict(zip(axes,(1,1,0,0,0,0,0,0,0,0))))
    direction=Position(dict(zip(axes,(16,17,-11,-12,-10,2,1,0,-1,-2))))
    begun=time.perf_counter();M=MeijerG(5,2,5,5,1).trajectory_matrix(direction,start)
    print(json.dumps(dict(event='built_native_matrix',seconds=time.perf_counter()-begun)),flush=True)
    ts=time.perf_counter();walks=M.walk({n:1},[N-1 for N in missing],{n:0})
    elapsed=time.perf_counter()-ts
    for N,W in zip(missing,walks):
        item=dict(N=N,n=N-1,column=[str(W[i,0])for i in range(4)],batch_walk_seconds=elapsed,
            entry_height_digits=max(max(len(str(abs(int(v.p)))),len(str(int(v.q))))for v in W))
        (OUT/f'column_N{N}.json').write_text(json.dumps(item))
        print(json.dumps(dict(event='saved_native_column',N=N,seconds=elapsed,height=item['entry_height_digits'])),flush=True)

def profile(N):
    begun=time.perf_counter();n=N-1
    W=[fmpq(s)for s in json.loads((OUT/f'column_N{N}.json').read_text())['column']]
    P3=-6*W[2]+3*W[3];P4=-2*W[3];Q=12*W[0]
    C=fmpq(math.factorial(15*n)**2,math.factorial(10*n)**3)
    primes=sieve(30*n);D=lcm_to(19*n,primes)
    vec3=[6*C*D**3*v for v in(P3,Q)]
    vec4=[6*C*D**4*v for v in(P3,P4,Q)]
    assert all(v.denominator==1 for v in vec3+vec4)
    G3=qgcd(vec3).numerator;G4=qgcd(vec4).numerator
    G4pure=qgcd([vec4[1],vec4[2]]).numerator
    rem3,rem4=G3,G4
    rows=[];eligible=[0.0,0.0];certified=[0.0,0.0];known=[0.0,0.0]
    for p in primes:
        e3,e4=vp(rem3,p),vp(rem4,p)
        if e3:rem3//=fmpz(p)**e3
        if e4:rem4//=fmpz(p)**e4
        valid=p>29 and p*p>30*n
        rec=record_for(n,p)if valid else None
        if not valid or rec is None:
            if e3 or e4:rows.append(dict(p=p,v3=e3,v4=e4,eligible=False))
            continue
        bound3=rec['base3']+rec['shell'];bound4=rec['base4']+rec['shell']
        assert e3>=bound3 and e4>=bound4,(n,p,e3,e4,rec)
        extra3=e3-bound3;extra4=e4-bound4
        band=19*n<2*p<20*n
        for i,(e,b,eextra) in enumerate(((e3,bound3,extra3),(e4,bound4,extra4))):
            eligible[i]+=e*math.log(p);certified[i]+=b*math.log(p)
            if band:known[i]+=eextra*math.log(p)
        rows.append(dict(p=p,p_over_n=p/n,n_over_p=str(F(n,p)),fractional_n_over_p=str(F(n,p)%1),
            v3=e3,v4=e4,bound3=bound3,bound4=bound4,extra3=extra3,extra4=extra4,
            second_order_band=band,eligible=True,**rec))
    gp=qgcd([P3,P4,Q]);qjoint=(Q/gp).numerator
    q3=(P3/Q).denominator;q4=(P4/Q).denominator
    item=dict(status='NUMERICAL_CANDIDATE',N=N,n=n,normalization='C15=(15n)!^2/(10n)!^3; user raw rows; 6 C15 d19n^r',
        actual_gamma3=math.log(int(G3))/n,actual_gamma4=math.log(int(G4))/n,
        eligible_gamma=[v/n for v in eligible],certificate_finite_density=[v/n for v in certified],
        eligible_residual_density=[(a-b)/n for a,b in zip(eligible,certified)],
        second_order_band_residual_density=[v/n for v in known],
        residual_outside_second_order_density=[(a-b-c)/n for a,b,c in zip(eligible,certified,known)],
        qjoint_log=math.log(int(qjoint)),q3_log=math.log(int(q3)),q4_log=math.log(int(q4)),
        pure4_advantage=str(G4pure//G4),remaining3=str(rem3),remaining4=str(rem4),
        raw_Q_log=logabs(Q),C_log=logabs(C),D_log=math.log(int(D)),seconds=time.perf_counter()-begun,
        scope='Exact finite residual common factors beyond the existing uniform divisor; no new uniform shell inferred.',rows=rows)
    (OUT/f'profile_N{N}.json').write_text(json.dumps(item,indent=2)+'\n')
    print(json.dumps({k:v for k,v in item.items()if k!='rows'}),flush=True)
    return item

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('depths',type=int,nargs='*',default=[500,1000,2000]);args=ap.parse_args()
    checkpoint_columns(args.depths)
    reports=[profile(N)for N in args.depths]
    (OUT/'summary.json').write_text(json.dumps([{k:v for k,v in r.items()if k!='rows'}for r in reports],indent=2)+'\n')
