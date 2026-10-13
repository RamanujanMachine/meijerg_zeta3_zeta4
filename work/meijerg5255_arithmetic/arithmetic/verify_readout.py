"""Independent exact finite checks of the uniform readout and shell lemmas."""
import json,math,sys,time
from pathlib import Path
from fractions import Fraction as Fr
from flint import fmpq
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'work/meijerg5255_arithmetic/paths'))
from native import START,endpoint,segment
from partial_fractions import pf,pf_fast,kernel_readout

def vp(z,p):
 if not z:return 10**9
 v=0
 while z%p==0:z//=p;v+=1
 return v

def vq(z,p):return vp(z.numerator,p)-vp(z.denominator,p)
def primes(n):
 a=bytearray(b'\1')*(n+1);a[:2]=b'\0\0'
 for k in range(2,math.isqrt(n)+1):
  if a[k]:a[k*k::k]=b'\0'*((n-k*k)//k+1)
 return [p for p in range(2,n+1)if a[p]]

def main():
 begun=time.perf_counter();rows=[]
 cert=json.loads(Path(__file__).with_name('all_shell_cells.json').read_text())
 cells=[(Fr(r['lo']),Fr(r['hi']))for r in cert['rows']if r['valid']]
 for n in range(0,13):
  if n<=3:assert pf(n)==pf_fast(n)
  Q,P3,P4=kernel_readout(n)
  if n<=5:
   W=segment(START,endpoint(n));assert Q==(-1)**n*W[0,0]
   assert P3==(-1)**n*(-W[2,0]/2+W[3,0]/4)
   assert P4==(-1)**n*(-W[3,0]/6)
  if n:
   C=fmpq(math.factorial(15*n)**2,math.factorial(10*n)**3);d16=math.lcm(*range(1,16*n+1));d19=math.lcm(*range(1,19*n+1))
   for a,b in pf_fast(n).values():assert (C*a).denominator==1 and(C*d16*b).denominator==1
   assert(6*C*d19**3*P3).denominator==1
   assert(6*C*d19**4*P4).denominator==1
   assert kernel_readout(n,3*n)==(Q,P3,P4)
  rows.append(dict(n=n,readout='passed',coefficient_baseline='passed'))
 for N in(50,100,250,500):
  n=N-1;m=json.loads((ROOT/f'results/meijerg5255_z3_z4_readout/matrix_N{N}.json').read_text());w=[fmpq(row[0])for row in m]
  Q,P3,P4=[(-1)**n*z for z in(w[0],-w[2]/2+w[3]/4,-w[3]/6)]
  if N<=100:assert kernel_readout(n)==(Q,P3,P4)
  tested=[]
  for p in primes(11*n):
   if p<=29 or p*p<=30*n:continue
   f=Fr(n%p,p)
   if not any(a<f<b for a,b in cells):continue
   vals=[vq(z,p)for z in(Q,P3,P4)]
   assert vals[0]>=1 and vals[1]>=-1 and vals[2]>=-2,(n,p,vals)
   tested.append(dict(p=p,valuations=vals))
  rows.append(dict(N=N,n=n,periodic_shell_prime_count=len(tested),prime_checks=tested))
 out=dict(status='NUMERICAL_CANDIDATE',scope='Exact finite regression checks; uniform claims follow from the separate written proof and complete symbolic chamber certificate.',rows=rows,seconds=time.perf_counter()-begun)
 dest=ROOT/'results/meijerg5255_arithmetic/arithmetic/verification.json';dest.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps(dict(status='passed',seconds=out['seconds'],shell_counts=[(r['N'],r['periodic_shell_prime_count'])for r in rows if'N'in r])))
if __name__=='__main__':main()
