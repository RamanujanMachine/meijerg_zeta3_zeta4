"""Exact rational enclosures for spectral and factorial constants.

The rates' application to selected readouts is an accepted analytic input;
this script certifies constants, not annihilation of the exact -1 mode.
"""
from fractions import Fraction as F
import json,sys
from inspect_exact import OUT
if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
TERMS=40

def series(q):
 z=(q-1)/(q+1);s=sum(2*z**(2*j+1)/F(2*j+1)for j in range(TERMS))
 r=2*z**(2*TERMS+1)/(F(2*TERMS+1)*(1-z*z))
 return s,s+r

def logq(q):
 q=F(q);k=0
 while q>=2:q/=2;k+=1
 while q<1:q*=2;k-=1
 a,b=series(q);c,d=series(F(2))
 return (a+k*c,b+k*d)if k>=0 else(a+k*d,b+k*c)
def add(x,y):return x[0]+y[0],x[1]+y[1]
def scale(c,x):return(c*x[0],c*x[1])if c>=0 else(c*x[1],c*x[0])
def minus(x,y):return x[0]-y[1],x[1]-y[0]
def summary(x):return dict(lower=str(x[0]),upper=str(x[1]),lower_decimal=float(x[0]),upper_decimal=float(x[1]))

def main():
 data=json.loads((OUT/'spectral_rates.json').read_text())
 a,b=next([F(v)for v in row['interval']]for row in data['real_root_isolations']if F(row['interval'][0])>1)
 l=F(a.numerator//a.denominator);u=F(-((-b.numerator)//b.denominator))
 coeff=[F(v)for v in data['characteristic_coefficients']]
 assert coeff[0]==1
 aa=coeff[1]-1;bb=coeff[2]-aa;cc=coeff[3]-bb
 assert cc==coeff[4], 'Exact root -1 must factor out.'
 discr=aa*aa*bb*bb-4*bb**3-4*aa**3*cc-27*cc*cc+18*aa*bb*cc
 assert discr<0, 'The remaining cubic has one real root and a complex pair.'
 def evaluate(x):return ((x+aa)*x+bb)*x+cc
 assert evaluate(l)<0<evaluate(u)
 const=cc;assert const<0 and -const/l<1
 logL=(logq(l)[0],logq(u)[1])
 logR=scale(F(1,2),(logq(-const/u)[0],logq(-const/l)[1]))
 E=minus(logL,logR)
 c14=add(add(scale(14,logq(14)),scale(16,logq(16))),scale(-30,logq(10)))
 c15=scale(30,logq(F(3,2)))
 h14=add(logL,c14);b14=add(logR,c14)
 h15=add(logL,c15);b15=add(logR,c15)
 bounds=dict(raw_height=logL,raw_linear_form_error=logR,error_ratio_exponent=E,C14_exponent=c14,C15_exponent=c15,
             C14_scaled_height=h14,C14_scaled_error=b14,C15_scaled_height=h15,C15_scaled_error=b15)
 assert h15[1]<F('65.451536565866') and b15[1]<F('-47.356002681589') and E[0]>F('112.807539247454')
 result=dict(status='NUMERICAL_CANDIDATE',terms=TERMS,dominant_integer_bracket=[str(l),str(u)],
    quartic_has_exact_minus_one_root=True,cubic_discriminant_negative=True,dominant_root_sign_bracket_verified=True,
    bounds={k:summary(v)for k,v in bounds.items()},safe_C15_scaled_height_upper='65.451536565866',
    safe_C15_scaled_error_upper='-47.356002681589',safe_error_ratio_exponent_lower='112.807539247454',
    scope='Certified algebraic/logarithmic constants. Accepted rate applicability to ζ3/ζ4 readouts is separate from the exact quartic root -1.')
 (OUT/'spectral_constant_certificate.json').write_text(json.dumps(result,indent=2))
 print(json.dumps({k:(v['lower_decimal'],v['upper_decimal'])for k,v in result['bounds'].items()},indent=2))
if __name__=='__main__':main()
