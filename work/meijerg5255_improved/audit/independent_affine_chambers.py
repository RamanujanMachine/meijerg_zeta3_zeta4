"""Independent exact audit of the sufficient second-order kernel criterion.

Integer lift t is symbolic: every surviving high root is the pair (slope,
intercept), representing slope*t+intercept. No finite sampling of t is used.
"""
from fractions import Fraction as F
from math import floor, ceil
from collections import Counter
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[3]
SLOPES = (0,1,2,10,11,12,-1,-2,-16,-17)
INTERVAL_SLOPES = ((0,10),(1,11),(2,12),(-17,-1),(-16,-2))

def labels(f,y):
    return tuple([(floor(u*f-y)+1,floor((u+10)*f-y)) for u in (0,1,2)]
                 + [(ceil(-b*f-y),floor(-a*f-y)) for a,b in ((1,17),(2,16))])

def height(z):
    return sum(b-a+1 for a,b in z[:3])-sum(b-a+1 for a,b in z[3:])

def quotient(z, ref):
    roots = Counter()
    for i, ((a,b),(c,d),(ls,us)) in enumerate(zip(z,ref,INTERVAL_SLOPES)):
        sign = 1 if i<3 else -1
        # Product on [a,b] / product on [c,d]; intercepts only vary here.
        for q in range(min(b,d)+1,max(b,d)+1):
            roots[(us,q)] += sign*(1 if b>d else -1)
        for q in range(min(a,c),max(a,c)):
            roots[(ls,q)] += sign*(-1 if a>c else 1)
    return {k:v for k,v in roots.items() if v}

def check(a,b):
    f=(a+b)/2
    bounds={F(0),F(1)}
    for m in SLOPES:
        for c in range(-20,21):
            y=m*f+c
            if 0<=y<=1: bounds.add(y)
    bounds=sorted(bounds)
    points=bounds[:-1]+[(x+y)/2 for x,y in zip(bounds,bounds[1:])]
    data=[(y, labels(f,y)) for y in points]
    minimum=min(height(z) for y,z in data)
    # Using representatives 1..p shifts residue zero by p. It is harmless
    # here because the certificate separately requires its height >=1.
    if minimum != -1 or height(labels(f,F(0)))<1:
        return dict(valid=False, strata=len(points))
    refs={z for y,z in data if height(z)==-1}
    if len(refs)!=1:
        return dict(valid=False, strata=len(points))
    ref=next(iter(refs)); extra=set()
    for y,z in data:
        if height(z)==0:
            q=quotient(z,ref)
            if len(q)!=1 or next(iter(q.values()))!=1:
                return dict(valid=False, strata=len(points))
            extra.add(next(iter(q)))
    return dict(valid=True,strata=len(points),minimal_intervals=ref,
                extra_affine_roots=sorted(extra),zero_height=height(labels(f,F(0))))

def main():
    walls=sorted({F(a,b) for b in range(1,30) for a in range(b+1)})
    rows=[]; runs=[]
    for a,b in zip(walls,walls[1:]):
        z=check(a,b);rows.append(dict(lo=str(a),hi=str(b),**z))
        if z['valid']:
            if runs and runs[-1][1]==str(a):runs[-1][1]=str(b)
            else:runs.append([str(a),str(b)])
    expected=[['1/10','2/19'],['11/12','15/16']]
    assert runs==expected,(runs,expected)
    out=dict(status='NUMERICAL_CANDIDATE',
             scope='Exact rational cell and symbolic-lift audit of the sufficient kernel criterion',
             total_cells=len(rows),total_strata=sum(r['strata']for r in rows),
             valid_cells=sum(r['valid'] for r in rows),windows=runs,rows=rows)
    path=ROOT/'results/meijerg5255_improved/audit/independent_affine_chambers.json'
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))

if __name__=='__main__':main()
