"""Numerical arithmetic diagnostics for the fixed MeijerG5255 trajectory."""
import json,math,sys
from pathlib import Path
from flint import fmpq,fmpz
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3]
SRC=ROOT/'results/meijerg5255_z3_z4_readout';OUT=ROOT/'results/meijerg5255_arithmetic/rates'

def qgcd(vs):
 a=fmpz(0);b=fmpz(1)
 for v in vs:a=a.gcd(v.numerator);b=b.lcm(v.denominator)
 return fmpq(a,b)
def logabs(q):return math.log(abs(int(q.numerator)))-math.log(int(q.denominator))
def sieve(n):
 a=bytearray(b'\1')*(n+1);a[:2]=b'\0\0'
 for p in range(2,math.isqrt(n)+1):
  if a[p]:a[p*p::p]=b'\0'*((n-p*p)//p+1)
 return [p for p in range(2,n+1)if a[p]]
def vp(z,p):
 v=0
 while z and z%p==0:z//=p;v+=1
 return v
def main():
 check=json.loads((SRC/'readout_check.json').read_text());rows=[]
 for N in check['depths']:
  m=json.loads((SRC/f'matrix_N{N}.json').read_text());w=[fmpq(m[i][0])for i in range(4)]
  p3=-6*w[2]+3*w[3];p4=-2*w[3];q=12*w[0]
  g=qgcd([p3,p4,q]);g3=qgcd([p3,q]);g4=qgcd([p4,q])
  U,V,Q=[(v/g).numerator for v in (p3,p4,q)]
  assert all((v/g).denominator==1 for v in(p3,p4,q))
  D3=U.gcd(Q);D4=V.gcd(Q)
  assert D3.gcd(V)==1 and D4.gcd(U)==1
  remain3,remain4=D3,D4;factors=[]
  for p in sieve(50*N):
   v3,v4=vp(remain3,p),vp(remain4,p)
   if v3 or v4:factors.append(dict(p=p,p_over_N=p/N,D3_v=v3,D4_v=v4));remain3//=fmpz(p)**v3;remain4//=fmpz(p)**v4
  summaries=[{k:r[k]for k in('A','B','log_q','delta_float','digits_correct')}for r in check['rows']if r['N']==N]
  item=dict(N=N,raw_Q_log=logabs(q),common_content_log=logabs(g),pure3_content_log=logabs(g3),pure4_content_log=logabs(g4),
   primitive_Q_log=math.log(abs(int(Q))),D3_log=math.log(int(D3)),D4_log=math.log(int(D4)),
   D3=str(D3),D4=str(D4),D3_unfactored=str(remain3),D4_unfactored=str(remain4),factors=factors,readout_summaries=summaries)
  rows.append(item)
  print(json.dumps({k:v for k,v in item.items()if k not in('D3','D4','factors')}),flush=True)
 result=dict(status='NUMERICAL_CANDIDATE',rows=rows,scope='Exact finite arithmetic and observed rates; no all-N common divisor inferred.')
 (OUT/'exact_content.json').write_text(json.dumps(result,indent=2))
if __name__=='__main__':main()
