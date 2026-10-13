"""Independent exact audit of the 14-band local-kernel endpoint certificate.

No arithmetic-agent code is imported. Rational arrangement sampling represents
entire open cells and all horizontal-boundary strata; it is not finite-depth
sampling of n,p. The accompanying text proves the integer-period lift.
"""
import json
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
SRC = ROOT / 'work/meijerg5255_arithmetic/arithmetic/all_shell_cells.json'
OUT = ROOT / 'results/meijerg5255_arithmetic/rates/all_shell_audit.json'
SLOPES = (0, 1, 2, 10, 11, 12, -1, -2, -16, -17)

def fl(x): return x.numerator // x.denominator
def ce(x): return -fl(-x)

def endpoint_data(x, y):
    eps = fl(2*x-y)
    num = [(fl(u*x-y)+1, fl((u+10)*x-y)) for u in (0, 1, 2)]
    den = [(ce(-b*x-y), fl(-a*x-y)) for a, b in ((1, 17), (2, 16))]
    h = sum(b-a+1 for a,b in num) - sum(b-a+1 for a,b in den)
    labels = tuple(z-eps for ab in num+den for z in ab)
    return h, labels

def main():
    source = json.loads(SRC.read_text())
    rows = source['rows']
    farey = {F(r['lo']) for r in rows} | {F(rows[-1]['hi'])}
    assert len(rows) == 270
    lines = [(m,c) for m in SLOPES for c in range(-20,21)
             if max(c,m+c)>=0 and min(c,m+c)<=1]
    # Every wall where the order of two y-breakpoint lines changes is covered.
    walls = set()
    for m,c in lines:
        for k,d in lines:
            if m==k: continue
            x=F(d-c,m-k)
            if 0<x<1 and 0<=m*x+c<=1:
                assert x in farey
                walls.add(x)
    checked=0;valid=0;gain=F(0);bands=[];valid_rows=[]
    for r in rows:
        a,b=F(r['lo']),F(r['hi']);x=(a+b)/2
        cuts=sorted({F(0),F(1)} | {m*x+c for m,c in lines if 0<=m*x+c<=1})
        samples=cuts[:-1]+[(u+v)/2 for u,v in zip(cuts,cuts[1:])]
        ds=[endpoint_data(x,y) for y in samples];checked+=len(ds)
        if not r['valid']: continue
        valid+=1
        assert min(h for h,_ in ds)>=-1
        labels={z for h,z in ds if h==-1}
        assert len(labels)==1
        assert list(next(iter(labels)))==r['normalized_interval_endpoints']
        cv=2*fl(15*x)-3*fl(10*x)
        assert cv==r['C_v']
        assert cv+2-r['g3']==cv+2-r['g4']==cv+2-r['tail']==1
        assert a>=F(1,19)
        # Independent checks of the exact symbolic period-translation formulas.
        for t in (1,2,7):
            expected_shifts=[]
            for u in (0,1,2): expected_shifts.extend(((u-2)*t,(u+8)*t))
            for aa,bb in ((1,17),(2,16)):
                expected_shifts.extend((-(bb+2)*t,-(aa+2)*t))
            for y,(h,z) in zip(samples,ds):
                hh,zz=endpoint_data(x+t,y)
                assert hh==h
                assert zz==tuple(q+s for q,s in zip(z,expected_shifts))
        gain+=1/a-1/b
        if bands and bands[-1][1]==a: bands[-1][1]=b
        else: bands.append([a,b])
        valid_rows.append([str(a),str(b)])
    assert checked==5400 and valid==47 and len(bands)==14
    assert gain==F(195197,55440)
    result=dict(status='NUMERICAL_CANDIDATE',scope='Exact arrangement and endpoint audit supporting the separately written uniform proof; no inference from finite n,p tests.',
        all_cells=len(rows),arrangement_walls=len(walls),sampled_strata=checked,
        valid_cells=valid,valid_bands=[[str(a),str(b)]for a,b in bands],
        first_period_density=str(gain),first_period_density_decimal=float(gain),
        sufficient_prime_cutoff='p>29 and p^2>30n',
        omitted_prime_density=0,all_checks_passed=True)
    OUT.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
