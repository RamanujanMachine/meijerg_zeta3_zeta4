"""Final exact delta arithmetic after the uniform second-order shell lemma.

Inputs: the written uniform baseline and two shell lemmas, their exhaustive
affine-arrangement certificates, and the accepted analytic growth/error rates.
This script certifies integration and numerical consequences, not those
mathematical inputs. It never infers a uniform lemma from finite-depth gcds.
"""
import json,sys
from fractions import Fraction as F
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.set_int_max_str_digits(0)
OUT=ROOT/'results/meijerg5255_improved/residuals'
def main():
    second=json.loads((ROOT/'work/meijerg5255_improved/arithmetic/second_order_certificate.json').read_text())
    assert [(r['lo'],r['hi'])for r in second['runs']]==[('1/10','2/19'),('11/12','15/16')]
    assert len(second['rows'])==270
    valid=[r for r in second['rows']if r['second']['valid']]
    assert len(valid)==9
    for c in valid:
        assert c['valid']
        assert c['second']['hmin']==-1 and c['second']['residue_zero_h']>=1
        assert c['C_v']+3-c['g3']==c['C_v']+3-c['g4']==c['C_v']+3-c['tail']==2
    density=json.loads((OUT/'infinite_density.json').read_text())
    gamma_exact=F(density['conditional_improved_density_lower'])
    gamma=F('30.45854724')
    assert gamma_exact>F('30.45854724380549')>gamma
    spectral=json.loads((ROOT/'results/meijerg5255_arithmetic/rates/spectral_constant_certificate.json').read_text())
    height=F('65.451536565866');error=F('-47.356002681589')
    assert F(spectral['bounds']['C15_scaled_height']['upper'])<height
    assert F(spectral['bounds']['C15_scaled_error']['upper'])<error
    rows=[]
    for r,threshold in ((3,F('0.22626234')),(4,F('0.01634832'))):
        sigma=height+19*r-gamma;tau=-error-19*r+gamma;delta=tau/sigma
        assert sigma>0 and tau>0 and delta>threshold
        rows.append(dict(lcm_power=r,scope='B=0, A!=0'if r==3 else'B!=0, fixed A,B',
            sigma_upper=str(sigma),tau_lower=str(tau),delta_lower=str(delta),
            sigma_decimal=float(sigma),tau_decimal=float(tau),delta_decimal=float(delta),
            advertised_strict_lower=str(threshold)))
    out=dict(status='NUMERICAL_CANDIDATE',scope='Exact final arithmetic consequence of the established uniform divisor lemmas and accepted analytic rates. The second-order improvement is no longer conditional on an unproved shell pattern. No irrationality-measure bound is asserted.',
        inputs=dict(uniform_second_order_cells=9,all_cells=270,prime_conditions='p>29, p^2>30n, p does not divide n; fractional n/p lies off Farey walls',
            combined_divisor_profile='baseline + indicator(first-order fourteen bands) + indicator(second-order two bands)'),
        exact_density_lower=str(gamma_exact),exact_density_lower_decimal=float(gamma_exact),
        readable_density_lower=str(gamma),accepted_height_upper=str(height),accepted_linear_error_upper=str(error),rates=rows)
    (OUT/'final_bound_certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
