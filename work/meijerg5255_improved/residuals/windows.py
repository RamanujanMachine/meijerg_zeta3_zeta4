"""Check two additional periodic windows against exact finite gcd data."""
import json,math
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_improved/residuals'
BANDS=[(F(1,10),F(2,19)),(F(11,12),F(15,16))]
SCALE=10**18
def main():
    reports=[];totals=[0,0];failed=[]
    for path in sorted(OUT.glob('profile_N*.json'),key=lambda p:int(p.stem.split('N')[1])):
        data=json.loads(path.read_text());counts=[0,0];mins=[[100,100],[100,100]]
        extras=[0.0,0.0];residual=[]
        for r in data['rows']:
            if not r.get('eligible'):continue
            f=F(r['fractional_n_over_p']);member=next((i for i,(a,b)in enumerate(BANDS)if a<f<b),None)
            predicted=int(member is not None)
            if member is not None:
                counts[member]+=1;totals[member]+=1
                for k in (3,4):mins[member][k-3]=min(mins[member][k-3],r[f'extra{k}'])
                if min(r['extra3'],r['extra4'])<1:failed.append(dict(N=data['N'],**r))
            e3,e4=r['extra3']-predicted,r['extra4']-predicted
            extras[0]+=e3*math.log(r['p']);extras[1]+=e4*math.log(r['p'])
            if e3 or e4:residual.append(dict(p=r['p'],n_over_p=r['n_over_p'],f=r['fractional_n_over_p'],
                extra3_after_two_windows=e3,extra4_after_two_windows=e4,cell=r['cell'],old_shell=r['shell']))
        reports.append(dict(N=data['N'],n=data['n'],window_counts=counts,minimum_extra=mins,
            residual_after_two_windows_density=[v/data['n']for v in extras],residual_primes=residual,
            actual_gamma3=data['actual_gamma3'],actual_gamma4=data['actual_gamma4'],
            denominator_height_per_n=[data['q3_log']/data['n'],data['qjoint_log']/data['n']]))
    lowers=[];uppers=[]
    for a,b in BANDS:
        terms=[1/(t+a)-1/(t+b)for t in range(1000)]
        lo=F(sum(v.numerator*SCALE//v.denominator for v in terms),SCALE)
        # Positive decreasing term tail bounded above by integral from 999.
        # Elementary bound: term <= (b-a)/(t+a)^2 and sum <= integral from999.
        tail=(b-a)/(999+a)
        lowers.append(lo);uppers.append(lo+F(1000,SCALE)+tail)
    old=F(29911392495318512761,10**18)
    gamma=old+sum(lowers)
    h=F('65.451536565866');b=F('-47.356002681589')
    projection=[]
    for r in (3,4):
        sigma=h+19*r-gamma;tau=-b-19*r+gamma
        projection.append(dict(lcm_power=r,gamma_lower=str(gamma),delta_lower_if_uniform=float(tau/sigma),
            sigma_upper=float(sigma),tau_lower=float(tau)))
    out=dict(status='NUMERICAL_CANDIDATE',scope='Finite exact verification and conditional asymptotic projection only. Neither new window is established uniformly by this script.',
        bands=[[str(a),str(b)]for a,b in BANDS],prime_instances=totals,counterexamples=failed,
        densities_lower=[str(v)for v in lowers],densities_lower_decimal=[float(v)for v in lowers],
        densities_upper_decimal=[float(v)for v in uppers],conditional_total_gamma_lower=float(gamma),
        conditional_projection=projection,depths=reports)
    (OUT/'windows.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items()if k!='depths'},indent=2))
    for r in reports:print(json.dumps(r),flush=True)
    assert not failed
if __name__=='__main__':main()
