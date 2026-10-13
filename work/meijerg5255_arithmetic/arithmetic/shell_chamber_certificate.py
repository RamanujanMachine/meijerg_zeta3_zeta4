"""Exact rational arrangement certificate for first-order MeijerG prime shells.

This verifies all continuous cells and y-boundaries in each band. The finitely
many x-walls have reduced denominator<=29 and cannot contain n/p for prime
p>29, since these bands have 0<n/p<1. No finite-depth inference is used.
"""
import json,sys,time
from fractions import Fraction as F
from math import floor,ceil
from pathlib import Path
from high_kernel import evaluate
BANDS=[(F(8),F(11)),(F(17,4),F(13,3)),(F(16,5),F(13,4)),(F(18,5),F(11,3)),(F(18,7),F(13,5)),(F(19,7),F(11,4)),(F(17,8),F(11,5)),(F(19,8),F(12,5)),(F(16,9),F(11,6))]
SLOPES=(0,1,2,10,11,12,-1,-2,-16,-17)
def sig(x,y):
 ns=[];ds=[]
 for u in(0,1,2):
  ns += [l for l in range(floor(u*x-y)+1,floor((10+u)*x-y)+1)]
 for a,b in((1,17),(2,16)):
  ds += [l for l in range(ceil(-b*x-y),floor(-a*x-y)+1)]
 return tuple(sorted(ns)),tuple(sorted(ds)),floor(2*x-y)
def certify(a,b):
 lo,hi=1/b,1/a
 lines=set()
 for m in SLOPES:
  for c in range(-20,21):
   if max(m*lo+c,m*hi+c)>=0 and min(m*lo+c,m*hi+c)<=1:lines.add((m,c))
 lines|={(0,0),(0,1)}
 critical={lo,hi}
 for m,c in lines:
  for mm,cc in lines:
   if m==mm:continue
   x=F(cc-c,m-mm)
   if lo<x<hi and 0<=m*x+c<=1:critical.add(x)
 critical=sorted(critical)
 assert all(x.denominator<=29 for x in critical)
 cells=0;boundaries=0;signatures=set();strip_constants=[]
 for xl,xr in zip(critical,critical[1:]):
  x=(xl+xr)/2;ys=sorted({F(0),F(1)}|{m*x+c for m,c in lines if 0<=m*x+c<=1})
  points=ys[:-1]+[(yl+yr)/2 for yl,yr in zip(ys,ys[1:])]
  ks=set();strip_sigs=set()
  for y in points:
   ns,ds,eps=sig(x,y);h=len(ns)-len(ds)
   assert h>=-1,(a,b,x,y,ns,ds)
   if h==-1:
    K=tuple(evaluate(ns,ds,eps));ks.add(K);strip_sigs.add((ns,ds,eps))
    assert any(-l+eps>=1 for l in ds)
   if y in ys:boundaries+=1
   else:cells+=1
  assert len(ks)==1,(a,b,x,ks)
  signatures|=strip_sigs
  strip_constants.append(dict(x_interval=[str(xl),str(xr)],K=list(next(iter(ks))),C_v=2*floor(15*x)-3*floor(10*x)))
 return dict(p_over_n_interval=[str(a),str(b)],x_interval=[str(lo),str(hi)],open_cells=cells,y_boundary_cells=boundaries,x_walls=[str(x)for x in critical],signatures=[dict(ns=ns,ds=ds,eps=eps,K=evaluate(ns,ds,eps))for ns,ds,eps in sorted(signatures)],strips=strip_constants)
if __name__=='__main__':
 start=time.perf_counter();rows=[]
 for a,b in BANDS:
  z=certify(a,b);rows.append(z);print(json.dumps({k:z[k]for k in('p_over_n_interval','open_cells','y_boundary_cells','signatures')}),flush=True)
 out=dict(status='NUMERICAL_CANDIDATE',scope='Exact finite symbolic certificate for the uniform written root-count and high-kernel argument; not an extrapolation from numerical depths.',rows=rows,total_open_cells=sum(z['open_cells']for z in rows),total_boundary_cells=sum(z['y_boundary_cells']for z in rows),total_width=str(sum((b-a for a,b in BANDS),F(0))),seconds=time.perf_counter()-start)
 Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
