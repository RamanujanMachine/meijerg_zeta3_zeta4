"""Exact rate arithmetic from a finite lower sum of the uniform divisor profile.

The supplied chamber labels and periodic-shell lemma are proof inputs. This
certifies their integrated lower bound and the ensuing numerical constants.
"""
import json,sys
from fractions import Fraction as F
from inspect_exact import ROOT,OUT
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
SCALE=10**18;PERIODS=1000

def scaled_floor(v):return(v.numerator*SCALE)//v.denominator

def main():
 cells=json.loads((ROOT/'results/meijerg5255_arithmetic/profiles/exact_chambers.json').read_text())
 totals=[0,0];count=[0,0]
 for cell in cells:
  a,b=F(cell['lo']),F(cell['hi'])
  for i,k in enumerate(('g3','g4')):
   if cell[k]:
    totals[i]+=scaled_floor(cell[k]*(1/a-1/b));count[i]+=1
  if cell['tail']:
   v=0
   for t in range(1,PERIODS):v+=scaled_floor(cell['tail']*(1/(a+t)-1/(b+t)))
   for i in (0,1):totals[i]+=v;count[i]+=PERIODS-1
 lows=[F(z,SCALE)for z in totals]
 assert min(lows)>F('26.2366')
 shells=json.loads((ROOT/'work/meijerg5255_arithmetic/arithmetic/all_shell_cells.json').read_text())
 shell_sum=0;shell_count=0
 for cell in shells['rows']:
  if not cell['valid']:continue
  a,b=F(cell['lo']),F(cell['hi'])
  assert cell['extra3']==cell['extra4']==1
  assert cell['C_v']+2-cell['tail']==1
  for t in range(PERIODS):
   shell_sum+=scaled_floor(1/(t+a)-1/(t+b));shell_count+=1
 shell_lower=F(shell_sum,SCALE)
 assert shell_lower>F('3.674728195806')
 gamma=F('29.91139')
 assert min(lows)+shell_lower>gamma
 spec=json.loads((OUT/'spectral_constant_certificate.json').read_text())
 h=F('65.451536565866');b=F('-47.356002681589')
 assert F(spec['bounds']['C15_scaled_height']['upper'])<h
 assert F(spec['bounds']['C15_scaled_error']['upper'])<b
 rates=[]
 for k in (3,4):
  sigma=h+19*k-gamma;tau=-b-19*k+gamma
  delta=tau/sigma
  assert tau>0
  rates.append(dict(lcm_power=k,scope='B=0'if k==3 else'B!=0, fixed integers A,B',sigma_upper=str(sigma),tau_lower=str(tau),
      delta_lower=str(delta),delta_lower_decimal=float(delta)))
 assert F(rates[0]['delta_lower'])>F('0.2190118')
 assert F(rates[1]['delta_lower'])>F('0.0113626')
 result=dict(status='NUMERICAL_CANDIDATE',periods=PERIODS,rounding_scale=SCALE,cell_count=len(cells),term_counts=count,
     base_profile_lower=[str(v)for v in lows],base_profile_lower_decimal=[float(v)for v in lows],
     extra_shell_term_count=shell_count,extra_shell_density_lower=str(shell_lower),
     extra_shell_density_lower_decimal=float(shell_lower),
     total_density_lower=[str(v+shell_lower)for v in lows],
     safe_total_density_lower=str(gamma),rates=rates,
     scope='Exact rational numerical consequence of the uniform profile, the fourteen periodic-shell lemma, and accepted analytic growth/error inputs. No irrationality-measure upper bound is asserted.')
 (OUT/'final_bound_certificate.json').write_text(json.dumps(result,indent=2))
 print(json.dumps(result,indent=2))
if __name__=='__main__':main()
