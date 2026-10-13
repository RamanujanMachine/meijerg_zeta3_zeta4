"""Independent exact spot checks of the symbolic all-lift trace certificate.

The all-lift justification is the affine endpoint identity, not these checks.
"""
import json
from collections import Counter
from fractions import Fraction as F
from math import ceil,floor
from pathlib import Path
DATA=Path('work/meijerg5255_improved/arithmetic/second_order_certificate.json')
SLOPES=(0,1,2,10,11,12,-1,-2,-16,-17)
def roots(x,y):
    ns=[];ds=[]
    for u in (0,1,2):ns.extend(range(floor(u*x-y)+1,floor((u+10)*x-y)+1))
    for a,b in ((1,17),(2,16)):ds.extend(range(ceil(-b*x-y),floor(-a*x-y)+1))
    return ns,ds
count=0;cases=0
for row in json.loads(DATA.read_text())['rows']:
    z=row['second']
    if not z['valid']:continue
    left,right=F(row['lo']),F(row['hi'])
    for f in ((2*left+right)/3,(left+2*right)/3):
        cuts=sorted({F(0),F(1)}|{m*f+c for m in SLOPES for c in range(-20,21) if 0<=m*f+c<=1})
        for t in (0,1,4,11):
            x=t+f
            points=cuts[:-1]+[(a+b)/2 for a,b in zip(cuts,cuts[1:])]
            data=[roots(x,y) for y in points]
            assert all(len(ns)-len(ds)>=-1 for ns,ds in data)
            mins={(tuple(ns),tuple(ds)) for ns,ds in data if len(ns)-len(ds)==-1}
            assert len(mins)==1
            refn,refd=next(iter(mins));ref=Counter(refn);ref.subtract(refd)
            expected={m*t+c for m,c in z['h0_affine_factors']}
            got=set()
            for ns,ds in data:
                if len(ns)!=len(ds):continue
                diff=Counter(ns);diff.subtract(ds);diff.subtract(ref)
                diff={k:v for k,v in diff.items() if v}
                assert len(diff)==1 and next(iter(diff.values()))==1,(f,t,diff)
                got.add(next(iter(diff)))
            assert got==expected,(f,t,got,expected)
            ns,ds=roots(x,F(0));assert len(ns)-len(ds)==1
            count+=len(points);cases+=1
out={'status':'NUMERICAL_CANDIDATE','scope':'Independent exact checks complementing the affine all-lift symbolic argument; no numerical extrapolation used by that argument.','rational_cells_checked':cases,'residue_cells_and_boundaries_checked':count,'all_passed':True}
Path('results/meijerg5255_improved/paths/periodic_trace_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
