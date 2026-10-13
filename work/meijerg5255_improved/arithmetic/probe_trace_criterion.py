import sys,json
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
sys.path.insert(0,'work/meijerg5255_arithmetic/arithmetic')
from all_shell_cells import SLOPES,sig

def roots(x):
 cuts={F(0),F(1)}
 for m in SLOPES:
  for c in range(-100,101):
   y=m*x+c
   if 0<=y<=1:cuts.add(y)
 cuts=sorted(cuts);return[(y,*sig(x,y))for y in cuts[:-1]+[(u+v)/2 for u,v in zip(cuts,cuts[1:])]]
def quotient(a,b):
 ns,ds=a;nn,dd=b
 z=Counter(ns)+Counter(dd);w=Counter(ds)+Counter(nn)
 common=z&w;z-=common;w-=common
 return list(z.elements()),list(w.elements())
if __name__=='__main__':
 for base in(F(39,380),F(89,96),F(21,200),F(23,25)):
  for t in(0,1,3):
   data=roots(t+base);mins={(a,b)for y,a,b,e in data if len(a)-len(b)==-1};zeros={(a,b)for y,a,b,e in data if len(a)-len(b)==0};qs=[]
   if len(mins)==1:
    ref=next(iter(mins));qs=[quotient(z,ref)for z in zeros]
   print(base,t,'mins',len(mins),'min_eps',sorted({e for y,a,b,e in data if len(a)-len(b)==-1}),'h0',len(zeros),'ratios',qs,'hmin',min(len(a)-len(b)for y,a,b,e in data))
