"""Classify large-prime local rational kernels; exact rational signatures."""
import sys,json
from fractions import Fraction as Q
from collections import Counter,defaultdict
from functools import lru_cache
@lru_cache(None)
def evaluate(ns,ds,eps):
 H=lambda m,r:sum((Q(1,k**r)for k in range(1,m+1)),Q(0))
 ks=[]
 residues=[]
 for l,m in Counter(ds).items():
  f=Q(1)
  for z in ns:f*=l-z
  for z in ds:
   if z!=l:f/=l-z
  if m==1:a=Q(0);b=f
  elif m==2:
   a=f;b=f*(sum((Q(1,l-z)for z in ns),Q(0))-sum((Q(1,l-z)for z in ds if z!=l),Q(0)))
  else:raise ValueError((ns,ds,eps))
  residues.append((l,a,b))
 for r in(3,4):
  z=sum((a*H(-l+eps,r)+b*H(-l+eps,r-1)/(r-1)for l,a,b in residues),Q(0))
  ks.append(str(z))
 return ks

def signatures(n,p):
 nums=[q for u in(0,1,2)for q in range(u*n+1,(10+u)*n+1)]
 dens=[-q for q in [*range(n,17*n+1),*range(2*n,16*n+1)]]
 nr=defaultdict(list);dr=defaultdict(list)
 for r in nums:nr[r%p].append(r//p)
 for r in dens:dr[r%p].append(r//p)
 sig=defaultdict(list)
 for k in range(p):
  ns=tuple(sorted(nr[k]));ds=tuple(sorted(dr[k]));h=len(ns)-len(ds)
  assert h>=-1,(n,p,k,h)
  if h==-1:
   eps=(2*n-k)//p;sig[(ns,ds,eps)].append(k)
 return [dict(ns=ns,ds=ds,eps=eps,kmin=min(ks),kmax=max(ks),count=len(ks),K=evaluate(ns,ds,eps))for(ns,ds,eps),ks in sig.items()]
if __name__=='__main__':
 for p in(809,853,907,947,967,983,997,1031,1087):
  print(json.dumps(dict(n=99,p=p,signatures=signatures(99,p))))
