"""Exact rational lower certificate for the all-prime carry density."""
import json,sys
from pathlib import Path
from fractions import Fraction as F
sys.set_int_max_str_digits(0)
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'results/meijerg5255_arithmetic/profiles'
a=json.loads((OUT/'exact_chambers.json').read_text())
merged=[]
for r in a:
 if merged and merged[-1]['value']==r['tail']:merged[-1]['hi']=r['hi']
 else:merged.append(dict(lo=r['lo'],hi=r['hi'],value=r['tail']))
assert all(r['g3']==r['g4']for r in a)
for r in a:
 x=(F(r['lo'])+F(r['hi']))/2
 extra=3 if F(1,19)<x<F(1,18) else 2 if F(1,18)<x<F(1,17) else 1 if F(1,17)<x<F(1,16) else 0
 assert r['g4']==r['tail']+extra
K=1000
S=F(6)
for r in merged:
 if not r['value']:continue
 lo,hi=F(r['lo']),F(r['hi'])
 for t in range(K):S+=r['value']*(1/(t+lo)-1/(t+hi))
assert S>F(262366,10000)
record=dict(K=K,lower_rational=str(S),lower_decimal=float(S),upper_decimal=float(S+F(3,K)),
            certified_simple_lower='26.2366',inequality_checked_exactly=True,
            tail_bound='0 <= remainder <= 3/K',extra_broad_shell_density=3,
            total_certified_simple_lower='29.2366',periodic_profile=merged)
(OUT/'density_certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k not in ('lower_rational','periodic_profile')}))
