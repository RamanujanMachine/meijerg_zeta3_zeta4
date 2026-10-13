"""Exact finite tests of residual prime bands; no uniform assertion inferred."""
import json,math
from fractions import Fraction as F
from inspect_exact import OUT
BANDS=[(F(8),F(11),1),(F(19,2),F(10),1),(F(17,4),F(13,3),1),
       (F(16,5),F(13,4),1),(F(18,5),F(11,3),1),(F(18,7),F(13,5),1),
       (F(19,7),F(11,4),1),(F(17,8),F(11,5),1),(F(19,8),F(12,5),1),
       (F(16,9),F(11,6),1),(F(15,11),F(11,8),1),(F(24,17),F(10,7),1),
       (F(14,13),F(11,10),1),(F(14,13),F(12,11),1)]
records=json.loads((OUT/'profile_comparison.json').read_text())['results'];results=[]
for a,b,h in BANDS:
 tested=0;fails=[]
 for rec in records:
  n=rec['n']
  for z in rec['rows']:
   if a*n<z['p']<b*n:
    tested+=1
    if z['extra4']<h:fails.append(dict(n=n,p=z['p'],actual=z['extra4']))
 result=dict(lo=str(a),hi=str(b),extra=h,finite_tested_primes=tested,failures=fails,candidate_density=str(h*(b-a)))
 results.append(result)
 print(result)
(OUT/'window_probe.json').write_text(json.dumps(dict(status='NUMERICAL_CANDIDATE',scope='Each band independently finite-tested; overlapping extra requirements must be added only when separately checked.',bands=results),indent=2))
# Combined broad window8..11 plus its extra9.5..10 requirement.
for rec in records:
 for z in rec['rows']:
  n=rec['n'];p=z['p'];h=int(8*n<p<11*n)+int(19*n<2*p<20*n)
  assert z['extra4']>=h and z['extra3']>=h,(n,z,h)
