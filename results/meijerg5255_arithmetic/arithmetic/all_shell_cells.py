"""Uniform root/kernel certificate on every Farey-29 arithmetic chamber."""
import json,sys,time
from pathlib import Path
from fractions import Fraction as F
from math import floor,ceil
if hasattr(sys,"set_int_max_str_digits"):sys.set_int_max_str_digits(0)
from high_kernel import evaluate
from shell_chamber_certificate import sig,SLOPES
BASE=Path('results/meijerg5255_arithmetic/profiles/exact_chambers.json')
def inspect_cell(a,b):
 x=(a+b)/2
 cuts={F(0),F(1)}
 for m in SLOPES:
  for c in range(-20,21):
   y=m*x+c
   if 0<=y<=1:cuts.add(y)
 cuts=sorted(cuts)
 points=cuts[:-1]+[(u+v)/2 for u,v in zip(cuts,cuts[1:])]
 sigs=set();labels=set();hmin=0
 for y in points:
  ns,ds,eps=sig(x,y);h=len(ns)-len(ds);hmin=min(hmin,h)
  if h==-1:
   sigs.add((ns,ds,eps))
   z=[]
   for u in(0,1,2):z.extend([floor(u*x-y)+1-eps,floor((u+10)*x-y)-eps])
   for aa,bb in((1,17),(2,16)):z.extend([ceil(-bb*x-y)-eps,floor(-aa*x-y)-eps])
   labels.add(tuple(z))
 if hmin< -1:return dict(valid=False,hmin=hmin,point_count=len(points))
 ks={tuple(evaluate(*z))for z in sigs}
 if len(ks)!=1:return dict(valid=False,hmin=hmin,K_count=len(ks),point_count=len(points))
 assert len(labels)==1,(a,b,labels)
 return dict(valid=True,normalized_interval_endpoints=list(next(iter(labels))),hmin=hmin,K=list(next(iter(ks))),point_count=len(points),signature_count=len(sigs),signatures=[dict(ns=ns,ds=ds,eps=eps)for ns,ds,eps in sorted(sigs)],C_v=2*floor(15*x)-3*floor(10*x))
if __name__=='__main__':
 start=time.perf_counter();rows=[];gain=[F(0),F(0)];counts=0
 for rec in json.loads(BASE.read_text()):
  a,b=F(rec['lo']),F(rec['hi']);res=inspect_cell(a,b);counts+=res['point_count']
  if res['valid']:
   assert a>=F(1,19)
   new=res['C_v']+2
   for i,r in enumerate((3,4)):
    inc=max(0,new-rec[f'g{r}']);gain[i]+=inc*(1/a-1/b);res[f'extra{r}']=inc
  rows.append({**rec,**res})
 periodic_gain=[F(0),F(0)]
 for rec in rows:
  if not rec['valid']:continue
  a,b=F(rec['lo']),F(rec['hi']);assert rec['C_v']+2-rec['tail']==1
  assert rec['extra3']==rec['extra4']==1
  for t in range(1000):
   for i in(0,1):periodic_gain[i]+=1/(t+a)-1/(t+b)
 assert periodic_gain[0]>F('3.6747281958')
 out=dict(periodic_extra_lower_1000=[str(v)for v in periodic_gain],periodic_extra_lower_1000_float=[float(v)for v in periodic_gain],status='NUMERICAL_CANDIDATE',scope='Exact exhaustive symbolic cells supporting the accompanying uniform proof; finite primes p<=29 omitted.',rows=rows,total_points=counts,gain=[str(z)for z in gain],gain_float=[float(z)for z in gain],seconds=time.perf_counter()-start)
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k not in('rows','periodic_extra_lower_1000')}),flush=True)
 runs=[]
 for r in rows:
  if r.get('extra3',0)or r.get('extra4',0):
   if runs and runs[-1]['hi']==r['lo'] and runs[-1]['extra3']==r['extra3'] and runs[-1]['extra4']==r['extra4']:runs[-1]['hi']=r['hi']
   else:runs.append({k:r[k]for k in('lo','hi','extra3','extra4')})
 print(json.dumps(runs,indent=2),flush=True)
