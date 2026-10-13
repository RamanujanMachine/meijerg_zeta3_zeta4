"""Test the explicit factorial/lcm normalization and record finite gcd ceilings."""
import json,math,sys
from pathlib import Path
from flint import fmpz,fmpq
from inspect_exact import qgcd,logabs,sieve,vp,ROOT,SRC,OUT
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)

def lcm_to(n,primes):
 z=fmpz(1)
 for p in primes:
  if p>n:break
  q=p
  while q*p<=n:q*=p
  z*=q
 return z

def main():
 rows=[]
 for N in [50,100,250,500]:
  n=N-1;mat=json.loads((SRC/f'matrix_N{N}.json').read_text());w=[fmpq(mat[i][0])for i in range(4)]
  P3=-6*w[2]+3*w[3];P4=-2*w[3];Q=12*w[0]
  C=fmpq(math.factorial(14*n)*math.factorial(16*n),math.factorial(10*n)**3)
  primes=sieve(50*n);D=lcm_to(19*n,primes)
  t3=[6*C*D**3*v for v in(P3,Q)];t4=[6*C*D**4*v for v in(P3,P4,Q)]
  assert all(v.denominator==1 for v in t3+t4)
  G3=qgcd(t3).numerator;G4=qgcd(t4).numerator
  rem3,rem4=G3,G4;profile=[]
  for p in primes:
   e3,e4=vp(rem3,p),vp(rem4,p)
   if e3 or e4:
    rem3//=fmpz(p)**e3;rem4//=fmpz(p)**e4
    profile.append(dict(p=p,p_over_n=p/n,v_gcd3=e3,v_gcd4=e4,small_prime=p*p<=60*n))
  row=dict(N=N,n=n,C_log=logabs(C),D_log=math.log(int(D)),G3_log=math.log(int(G3)),G4_log=math.log(int(G4)),
   G3_remaining=str(rem3),G4_remaining=str(rem4),G3_log_per_n=math.log(int(G3))/n,G4_log_per_n=math.log(int(G4))/n,
   raw_Q_log=logabs(Q),scaled_Q_log=logabs(C*Q),eligible_G3_log_per_n=sum(x['v_gcd3']*math.log(x['p'])/n for x in profile if not x['small_prime']),
   eligible_G4_log_per_n=sum(x['v_gcd4']*math.log(x['p'])/n for x in profile if not x['small_prime']),profile=profile)
  rows.append(row);print(json.dumps({k:v for k,v in row.items()if k!='profile'}),flush=True)
 (OUT/'baseline_ceiling.json').write_text(json.dumps(dict(status='NUMERICAL_CANDIDATE',rows=rows,scope='Finite exact gcd under6 C_n d_(19n)^3 and6 C_n d_(19n)^4 normalizers; no uniform extra divisor inferred.'),indent=2))
if __name__=='__main__':main()
