"""Exact rational carry chambers for a uniform prime-divisor lower bound."""
from fractions import Fraction as F
from functools import lru_cache
import math,json,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_arithmetic/profiles'
def fl(x):return x.numerator//x.denominator
def ce(x):return -fl(-x)
@lru_cache(None)
def harmonic(n):return sum((F(1,k)for k in range(1,n+1)),F(0))
def data(x,y,kind):
 c=2*fl(15*x)-3*fl(10*x)
 num=c+sum(fl(y+(10+u)*x)-fl(y+u*x)for u in (0,1,2))
 h=int(y+2*x>=1);l=int(x>=F(1,19))
 if kind=='d':
  s=num-fl(y-x)-fl(y-2*x)-fl(16*x-y)-fl(17*x-y)
  lp=sum(-harmonic(fl(y+(10+u)*x))+harmonic(fl(y+u*x))for u in (0,1,2))+harmonic(fl(y-x))-harmonic(fl(16*x-y))+harmonic(fl(y-2*x))-harmonic(fl(17*x-y))
  loss=int(lp!=0)
  return [min(s+r*l-r*h,s-loss+r*l-(r-1)*h)for r in (3,4)]
 if kind=='l':b=num+ce(2*x-y)-1-fl(16*x-y)-fl(y-x)-fl(17*x-y)
 else:b=num+ce(y-16*x)-1-fl(y-2*x)-fl(y-x)-fl(17*x-y)
 return [b+r*l-(r-1)*h for r in (3,4)]
def value(x):
 gains=[100,100]
 for kind,lo,hi,include_lo,include_hi in [('d',2*x,16*x,True,True),('l',x,2*x,True,False),('r',16*x,17*x,False,True)]:
  cuts={lo,hi}
  # Floor breakpoints of every factorial and harmonic cutoff used above.
  for slope in (-12,-11,-10,-2,-1,0,1,2,16,17):
   for k in range(fl(lo-slope*x)-1,ce(hi-slope*x)+2):
    v=k+slope*x
    if lo<=v<=hi:cuts.add(v)
  cuts=sorted(cuts)
  samples=[(a+b)/2 for a,b in zip(cuts,cuts[1:])]
  samples += [y for y in cuts if (y!=lo or include_lo)and(y!=hi or include_hi)]
  for y in samples:
   gs=data(x,y,kind)
   gains=[min(a,b)for a,b in zip(gains,gs)]
 return [max(0,g)for g in gains]
def build():
 begun=time.perf_counter()
 bs=sorted({F(a,b)for b in range(1,30)for a in range(b+1)})
 rows=[]
 for a,b in zip(bs,bs[1:]):
  x=(a+b)/2;g=value(x);tail=value(x+1)
  assert tail[0]==tail[1]
  # Above1, all harmonic cutoffs active and factorial-floor profiles are periodic.
  row=dict(lo=str(a),hi=str(b),g3=g[0],g4=g[1],tail=tail[0])
  rows.append(row)
 OUT.mkdir(exist_ok=True)
 (OUT/'exact_chambers.json').write_text(json.dumps(rows,indent=2)+'\n')
 for K in (1,2,5,10,50,1000):
  integral=[F(0),F(0)]
  for r in rows:
   a,b=F(r['lo']),F(r['hi'])
   for i,key in enumerate(('g3','g4')):
    if r[key]:integral[i]+=r[key]*(1/a-1/b)
    for t in range(1,K):integral[i]+=r['tail']*(1/(a+t)-1/(b+t))
  print(K,[float(v)for v in integral],flush=True)
 print('rows',len(rows),'seconds',time.perf_counter()-begun,flush=True)
if __name__=='__main__':build()
