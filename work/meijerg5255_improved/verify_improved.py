"""Exact finite validation of the improved uniform divisor and reduced q."""
import sys, json, math, time
from pathlib import Path
from fractions import Fraction as F
from flint import fmpq, fmpz

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'work/meijerg5255_arithmetic'))
from verify_certificate import exponents
sys.path.insert(0,str(ROOT/'work/meijerg5255_arithmetic/paths'))
from native import segment, START, endpoint
sys.path.insert(0,str(Path(__file__).resolve().parent/'residuals'))
from profile import sieve, lcm_to
sys.set_int_max_str_digits(0)
OUT=ROOT/'results/meijerg5255_improved'
BANDS=((F(1,10),F(2,19)),(F(11,12),F(15,16)))

def run(n):
    begun=time.perf_counter()
    checkpoint=OUT/f'residuals/column_N{n+1}.json'
    if checkpoint.exists():
        w=[fmpq(v) for v in json.loads(checkpoint.read_text())['column']]
    else:
        W=segment(START,endpoint(n));w=[W[i,0] for i in range(4)]
    Q=w[0];P3=-w[2]/2+w[3]/4;P4=-w[3]/6
    C=fmpq(math.factorial(15*n)**2,math.factorial(10*n)**3)
    D=lcm_to(19*n,sieve(19*n))
    es=exponents(n);count=0;G=fmpz(1)
    for row in es:
        p=row['p'];f=F(n%p,p)
        extra=any(a<f<b for a,b in BANDS)
        # Both new windows already have a positive old exponent.
        if extra:count+=1
        G*=fmpz(p)**(row['total']+extra)
    # Check that no second-order prime was lost by filtering zero old powers.
    old_primes={row['p'] for row in es}
    for p in sieve(19*n):
        if p>29 and p*p>30*n and any(a<F(n%p,p)<b for a,b in BANDS):
            assert p in old_primes
    m3=6*C*D**3/G;m4=m3*D
    for v in (m3*Q,m3*P3,m4*Q,m4*P3,m4*P4):
        assert v.denominator==1,(n,'nonintegral')
    records=[]
    for A,B in ((1,0),(0,1),(1,1),(1,-1),(2,3),(-7,5)):
        r=(A*P3+B*P4)/Q;q=r.denominator
        denominator=abs((m3 if B==0 else m4)*Q)
        assert denominator.denominator==1
        assert denominator.numerator % q == 0
        records.append(dict(A=A,B=B,log_reduced_q=math.log(int(q)),
                            log_integer_bound=math.log(int(denominator.numerator))))
    report=dict(status='NUMERICAL_CANDIDATE',n=n,N=n+1,
                all_integer_forms_pass=True,all_reduced_denominators_divide=True,
                new_prime_factors=count,gcd_log_density=math.log(int(G))/n,
                rows=records,seconds=time.perf_counter()-begun)
    (OUT/f'verification_n{n}.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k!='rows'}),flush=True)
    return report

if __name__=='__main__':
    ns=list(map(int,sys.argv[1:])) or [1,2,3,10,49,99,249,499,999,1999,3999,7999]
    reports=[run(n) for n in ns]
    (OUT/'verification_summary.json').write_text(json.dumps(reports,indent=2)+'\n')
