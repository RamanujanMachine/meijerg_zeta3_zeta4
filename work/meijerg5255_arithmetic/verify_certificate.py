"""Check all three integer forms against the uniform arithmetic divisor."""
import sys,json,math,time
from fractions import Fraction as F
from pathlib import Path
from bisect import bisect_right
from sympy import primerange
from flint import fmpq
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(Path(__file__).resolve().parent/'paths'))
from native import segment,START,endpoint,decode
sys.set_int_max_str_digits(0)
OUT=ROOT/'results/meijerg5255_arithmetic'
chambers=json.loads((OUT/'profiles/exact_chambers.json').read_text())
ends=[F(z['hi'])for z in chambers]
shells=json.loads((Path(__file__).resolve().parent/'arithmetic/all_shell_cells.json').read_text())['rows']
def exponents(n):
 out=[]
 for p in primerange(max(29,math.isqrt(30*n))+1,19*n+1):
  if n%p==0:continue
  x=F(n,p);z=x if x<1 else x-int(x)
  index=bisect_right(ends,z);row=chambers[index]
  base=row['g4']if x<1 else row['tail']
  shell=shells[index].get('extra4',0)
  if base+shell:out.append(dict(p=int(p),base=base,shell=shell,total=base+shell))
 return out

def run(n):
 t=time.perf_counter();cache=ROOT/f'results/meijerg5255_z3_z4_readout/matrix_N{n+1}.json'
 W=decode(json.loads(cache.read_text()))if cache.exists()else segment(START,endpoint(n))
 Q=W[0,0];P3=-W[2,0]/2+W[3,0]/4;P4=-W[3,0]/6
 C=fmpq(math.factorial(15*n)**2,math.factorial(10*n)**3)
 D=math.lcm(*range(1,19*n+1))
 es=exponents(n);G=math.prod(z['p']**z['total']for z in es)
 m3=6*C*D**3/G;m4=m3*D
 for label,r in [('Q3',m3*Q),('P3',m3*P3),('Q4',m4*Q),('P34',m4*P3),('P4',m4*P4)]:
  assert r.denominator==1,(n,label)
 def ln(a):return math.log(abs(int(a.numerator)))-math.log(int(a.denominator))
 records=[]
 for A,B in [(1,0),(0,1),(1,1),(1,-1),(2,3),(-7,5)]:
  r=(A*P3+B*P4)/Q;q=int(r.denominator)
  bound=abs((m3 if B==0 else m4)*Q)
  assert bound.denominator==1 and int(bound.numerator)%q==0
  records.append(dict(A=A,B=B,log_q=math.log(q),log_q_bound=ln(bound)))
 report=dict(n=n,user_N=n+1,forms_integral=True,all_reduced_q_divide_certificate=True,
             gcd_log_density=math.log(G)/n,records=records,seconds=time.perf_counter()-t,
             prime_exponents=es)
 (OUT/f'certificate_n{n}.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:v for k,v in report.items()if k!='prime_exponents'}),flush=True)
if __name__=='__main__':
 for n in [1,2,3,10,49,99,249,499]:run(n)
