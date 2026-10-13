"""Large-prime termwise coefficient content; factorial floors exact."""
import json,math,time,argparse
from pathlib import Path
import numpy as np
from sympy import primerange
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_arithmetic/profiles';OUT.mkdir(exist_ok=True)
def calc(n):
 start=time.perf_counter(); rows=[]
 jd=np.arange(2*n,16*n+1,dtype=np.int64)
 jl=np.arange(n,2*n,dtype=np.int64)
 jr=np.arange(16*n+1,17*n+1,dtype=np.int64)
 def num(j,p):
  v=np.full_like(j,2*((15*n)//p)-3*((10*n)//p))
  for u in (0,1,2):v+=(j+(10+u)*n)//p-(j+u*n)//p
  return v
 for p in primerange(math.isqrt(30*n)+1,29*n+1):
  sd=num(jd,p)-(jd-n)//p-(jd-2*n)//p-(16*n-jd)//p-(17*n-jd)//p
  bl=num(jl,p)+(2*n-jl-1)//p-(16*n-jl)//p-(jl-n)//p-(17*n-jl)//p
  br=num(jr,p)+(jr-16*n-1)//p-(jr-2*n)//p-(jr-n)//p-(17*n-jr)//p
  # d_19n is divisible by these p iff p<=19n. Large primes only once.
  l=int(p<=19*n)
  phi=min(int(sd.min()), int(bl.min())+l,int(br.min())+l)
  # Derivative at a double pole loses at most one p; for p>19n no common gain assumed.
  if not l:phi=min(phi,int(sd.min())-1)
  phi=max(0,phi)
  # Harmonic range improves the readout-wise term bound if j+2n<p.
  shifts_d=(jd+2*n>=p).astype(np.int64)
  shifts_l=(jl+2*n>=p).astype(np.int64)
  shifts_r=(jr+2*n>=p).astype(np.int64)
  def readout_gain(r):
   # Q gets r*l. double b lower sd-1 even if p>19n (safe).
   return max(0,min(int((sd+r*l-r*shifts_d).min()),int((sd-1+r*l-(r-1)*shifts_d).min()),int((bl+r*l-(r-1)*shifts_l).min()),int((br+r*l-(r-1)*shifts_r).min())))
  g3=readout_gain(3);g4=readout_gain(4)
  if phi or g3 or g4:rows.append(dict(p=int(p),phi=phi,g3=g3,g4=g4))
 summary={k:sum(z[k]*math.log(z['p'])for z in rows)/n for k in ('phi','g3','g4')}
 out=dict(n=n,summary=summary,rows=rows,seconds=time.perf_counter()-start)
 (OUT/f'profile_{n}.json').write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:v for k,v in out.items()if k!='rows'}),flush=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('n',nargs='*',type=int,default=[100,500,1000]);args=ap.parse_args()
 for n in args.n:calc(n)
