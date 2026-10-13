"""Compare exact gcd ceilings with termwise coefficient bounds, preserving inputs."""
import importlib.util,json,math,sys
from pathlib import Path
from fractions import Fraction as F
from inspect_exact import ROOT,OUT,sieve,vp
spec=importlib.util.spec_from_file_location('term_profile',ROOT/'work/meijerg5255_arithmetic/profiles/finite_profile.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
base.OUT=OUT

def main():
 data=json.loads((OUT/'baseline_ceiling.json').read_text());results=[]
 for row in data['rows']:
  n=row['n'];fn=OUT/f'profile_{n}.json'
  if not fn.exists():base.calc(n)
  pred={x['p']:x for x in json.loads(fn.read_text())['rows']}
  actual={x['p']:x for x in row['profile']}
  rec=[]
  for p in sieve(29*n):
   if p<=n:continue
   correction=2*((15*n)//p)-(14*n)//p-(16*n)//p
   a=actual.get(p,{'v_gcd3':0,'v_gcd4':0});b=pred.get(p,{'g3':0,'g4':0})
   vals=dict(p=p,p_over_n=p/n,x=str(F(n,p)),g3_bound=b['g3'],g4_bound=b['g4'],
      g3_actual=a['v_gcd3']+correction,g4_actual=a['v_gcd4']+correction)
   vals['extra3']=vals['g3_actual']-vals['g3_bound'];vals['extra4']=vals['g4_actual']-vals['g4_bound']
   assert min(vals['extra3'],vals['extra4'])>=0,(n,vals)
   rec.append(vals)
  result=dict(n=n,rows=rec,extra3_log_per_n=sum(x['extra3']*math.log(x['p'])/n for x in rec),
   extra4_log_per_n=sum(x['extra4']*math.log(x['p'])/n for x in rec))
  results.append(result)
  print(json.dumps(dict(n=n,extra3=result['extra3_log_per_n'],extra4=result['extra4_log_per_n'],positive4=[(v['p'],round(v['p_over_n'],5),v['extra4'])for v in rec if v['extra4']])),flush=True)
 (OUT/'profile_comparison.json').write_text(json.dumps(dict(status='NUMERICAL_CANDIDATE',normalizer='C15=(15n)!²/(10n)!³',results=results),indent=2))
if __name__=='__main__':main()
