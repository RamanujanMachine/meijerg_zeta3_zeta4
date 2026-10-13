"""Certified infinite profile densities by exact sums and elementary tail bounds.

For f(t)=1/(t+a)-1/(t+b), convexity gives
  integral_K^infinity f + f(K)/2 <= sum_{t>=K} f(t)
                              <= integral_{K-1/2}^infinity f.
The upper inequality follows by integrating over each centered unit interval;
the lower follows from the trapezoid rule on every unit interval. Both
integrals are logarithms, enclosed here using an exact atanh series.
"""
import json,sys
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/'results/meijerg5255_improved/residuals'
SCALE=10**24;K=1000
def down(q):return F(q.numerator*SCALE//q.denominator,SCALE)
def up(q):return -down(-q)
def log_bounds(q):
    assert q>=1
    t=(q-1)/(q+1);J=4
    lo=2*sum((t**(2*j+1)/F(2*j+1)for j in range(J)),F(0))
    err=2*t**(2*J+1)/(F(2*J+1)*(1-t*t))
    return down(lo),up(lo+err)
def tail_bounds(a,b):
    lo,_=log_bounds((K+b)/(K+a))
    _,hi=log_bounds((K-F(1,2)+b)/(K-F(1,2)+a))
    return down(lo+(1/(K+a)-1/(K+b))/2),hi
def rate(gamma,r):
    h=F('65.451536565866');b=F('-47.356002681589')
    sigma=h+19*r-gamma;tau=-b-19*r+gamma
    return dict(lcm_power=r,sigma_upper=str(sigma),tau_lower=str(tau),
                delta_lower=str(tau/sigma),delta_decimal=float(tau/sigma))
def main():
    cells=json.loads((ROOT/'work/meijerg5255_arithmetic/arithmetic/all_shell_cells.json').read_text())['rows']
    old=json.loads((ROOT/'results/meijerg5255_arithmetic/rates/final_bound_certificate.json').read_text())
    baselo=F(old['base_profile_lower'][0]);basehi=baselo+F(old['term_counts'][0],old['rounding_scale'])
    shelllo=F(old['extra_shell_density_lower']);shellhi=shelllo+F(old['extra_shell_term_count'],old['rounding_scale'])
    base_tail=[F(0),F(0)];shell_tail=[F(0),F(0)]
    for c in cells:
        a,b=F(c['lo']),F(c['hi']);lo,hi=tail_bounds(a,b)
        base_tail[0]+=c['tail']*lo;base_tail[1]+=c['tail']*hi
        if c['valid']:shell_tail[0]+=lo;shell_tail[1]+=hi
    g0=baselo+shelllo+base_tail[0]+shell_tail[0]
    g1=basehi+shellhi+base_tail[1]+shell_tail[1]
    safe=down(g0)
    windows=json.loads((OUT/'windows.json').read_text());extra=[]
    for band,lower in zip(windows['bands'],windows['densities_lower']):
        a,b=map(F,band);lo,hi=tail_bounds(a,b)
        low=F(lower)+lo;high=F(lower)+F(K,10**18)+hi
        extra.append(dict(band=band,lower=str(low),upper=str(high),lower_decimal=float(low),upper_decimal=float(high)))
    gnew=g0+sum(F(r['lower'])for r in extra)
    report=dict(status='NUMERICAL_CANDIDATE',scope='Exact arithmetic consequence of the already established baseline and fourteen periodic shells. New two-window projection remains conditional on its uniform divisibility lemma.',
        periods_exactly_summed=K,tail_lower_formula='log((K+b)/(K+a)) + (1/(K+a)-1/(K+b))/2',
        tail_upper_formula='log((K-1/2+b)/(K-1/2+a))',
        baseline_tail_bounds=[str(v)for v in base_tail],shell_tail_bounds=[str(v)for v in shell_tail],
        established_density_lower=str(g0),established_density_upper=str(g1),
        established_density_lower_decimal=float(g0),established_density_upper_decimal=float(g1),
        established_rates=[rate(safe,r)for r in(3,4)],
        new_periodic_windows=extra,conditional_improved_density_lower=str(gnew),
        conditional_improved_density_lower_decimal=float(gnew),conditional_rates=[rate(gnew,r)for r in(3,4)])
    friendly_gamma=F('29.91270798')
    assert g0>friendly_gamma
    friendly_rates=[rate(friendly_gamma,r)for r in (3,4)]
    assert F(friendly_rates[0]['delta_lower'])>F('0.21902925')
    assert F(friendly_rates[1]['delta_lower'])>F('0.01137460')
    report['readable_established_density_lower']=str(friendly_gamma)
    report['readable_established_rates']=friendly_rates
    # Independent ball-arithmetic evaluation of the same complete series.
    from flint import arb,ctx,fmpq
    ctx.dps=60
    def ar(q):
        q=F(q);return arb(fmpq(q.numerator,q.denominator))
    total=arb(0)
    for c in cells:
        a,b=ar(c['lo']),ar(c['hi'])
        if c['g3']:total+=c['g3']*(1/a-1/b)
        if c['tail']:total+=c['tail']*((1+b).digamma()-(1+a).digamma())
        if c['valid']:total+=b.digamma()-a.digamma()
    assert total>ar(g0) and total<ar(g1)
    report['independent_arb_complete_density']=total.str(55)
    (OUT/'infinite_density.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
