"""Exact affine-interval certificate for a uniform second-order trace lemma."""
import sys,json,time
from fractions import Fraction as F
from math import floor,ceil
from collections import Counter
from pathlib import Path
sys.set_int_max_str_digits(0)
sys.path.insert(0,'work/meijerg5255_arithmetic/arithmetic')
from all_shell_cells import SLOPES,sig

def labels(x,y):
 ns=[];ds=[]
 for u in(0,1,2):ns.append(((u,floor(u*x-y)+1),(u+10,floor((u+10)*x-y))))
 for a,b in((1,17),(2,16)):ds.append(((-b,ceil(-b*x-y)),(-a,floor(-a*x-y))))
 return tuple(ns),tuple(ds)
def affine_quotient(cur,ref):
 c=Counter()
 for sign,ints in((1,cur[0]),(1,ref[1]),(-1,cur[1]),(-1,ref[0])):
  for a,b in ints:c[a]+=sign;c[(b[0],b[1]+1)]-=sign
 c={k:v for k,v in c.items()if v}
 pos=[k for k,v in c.items()if v==1];neg=[k for k,v in c.items()if v==-1]
 if len(c)==2 and len(pos)==len(neg)==1 and neg[0]==(pos[0][0],pos[0][1]+1):return pos[0]
 return None

def inspect(a,b):
 x=(a+b)/2;cuts={F(0),F(1)}
 for m in SLOPES:
  for c in range(-20,21):
   y=m*x+c
   if 0<=y<=1:cuts.add(y)
 cuts=sorted(cuts);points=cuts[:-1]+[(u+v)/2 for u,v in zip(cuts,cuts[1:])]
 mins=set();zeros=set();hmin=0
 for y in points:
  ns,ds,e=sig(x,y);h=len(ns)-len(ds);hmin=min(hmin,h)
  if h==-1:mins.add(labels(x,y))
  if h==0:zeros.add(labels(x,y))
 if hmin< -1 or len(mins)!=1:return dict(valid=False,hmin=hmin,min_signatures=len(mins))
 ref=next(iter(mins));qs=[affine_quotient(z,ref)for z in zeros]
 if any(q is None for q in qs):return dict(valid=False,hmin=hmin,min_signatures=1,failed_h0=True)
 ns,ds,e=sig(x,F(0));h0=len(ns)-len(ds)
 if h0<1:return dict(valid=False,hmin=hmin,residue_zero_h=h0)
 return dict(valid=True,hmin=hmin,min_signature=ref,h0_affine_factors=sorted(set(qs)),residue_zero_h=h0,point_count=len(points))
if __name__=='__main__':
 start=time.perf_counter();base=json.loads(Path('work/meijerg5255_arithmetic/arithmetic/all_shell_cells.json').read_text())['rows'];rs=[];gain=F(0);runs=[]
 for rec in base:
  a,b=F(rec['lo']),F(rec['hi']);z=inspect(a,b);row={**rec,'second':z};rs.append(row)
  if not z['valid']:continue
  assert rec['valid']
  if runs and runs[-1]['hi']==rec['lo']:runs[-1]['hi']=rec['hi'];runs[-1]['factors'].update(map(tuple,z['h0_affine_factors']))
  else:runs.append(dict(lo=rec['lo'],hi=rec['hi'],factors=set(map(tuple,z['h0_affine_factors']))))
  for t in range(1000):gain+=1/(t+a)-1/(t+b)
 for r in runs:r['factors']=sorted(r['factors'])
 out=dict(status='NUMERICAL_CANDIDATE',scope='Exact symbolic arrangement and affine-endpoint certificate, supporting the separate uniform trace proof.',rows=rs,runs=runs,periodic_density_lower_1000=str(gain),periodic_density_lower_1000_float=float(gain),seconds=time.perf_counter()-start)
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k not in('rows','periodic_density_lower_1000')},indent=2))
