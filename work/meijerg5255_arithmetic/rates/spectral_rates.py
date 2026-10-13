"""Exact limiting matrix and numerical spectral rates of native MeijerG5255."""
import json,time
from pathlib import Path
import sympy as s
from ramanujantools import Position
from ramanujantools.cmf import MeijerG
ROOT=Path(__file__).resolve().parents[3];OUT=ROOT/'results/meijerg5255_arithmetic/rates'
axes=s.symbols('a0:5')+s.symbols('b0:5');n=s.symbols('n')
start=(1,1,0,0,0,0,0,0,0,0);direction=(16,17,-11,-12,-10,2,1,0,-1,-2)
began=time.perf_counter();M=MeijerG(5,2,5,5,1).trajectory_matrix(Position(dict(zip(axes,direction))),Position(dict(zip(axes,start))))
T=s.zeros(4);degrees=[]
for i in range(4):
 row=[]
 for j in range(4):
  expr=s.cancel(M[i,j]);a,b=expr.as_numer_denom();pa,pb=s.Poly(a,n),s.Poly(b,n)
  deg=int(pa.degree()-pb.degree());row.append(deg)
  assert deg<=j-i,(i,j,deg)
  T[i,j]=pa.LC()/pb.LC() if deg==j-i else 0
 degrees.append(row)
print('limiting matrix done',time.perf_counter()-began,flush=True)
char=T.charpoly();pol=char.as_expr();coefs=char.all_coeffs()
roots=s.polys.polytools.intervals(pol,eps=s.Rational(1,10**40))
numroots=[z.evalf(80) for z in s.Poly(pol).all_roots(radicals=False)]
rootdata=[]
for z in sorted(numroots,key=lambda z:abs(complex(z)),reverse=True):
 rootdata.append(dict(root=str(z),modulus=str(abs(z).evalf(60)),log_modulus=str(s.log(abs(z)).evalf(60))))
result=dict(status='NUMERICAL_CANDIDATE',degree_pattern=degrees,leading_gauge='S_n=diag(1,n^-1,n^-2,n^-3); S_n^-1 M(n) S_(n+1) tends to T',
 limiting_matrix=[[str(v)for v in row]for row in T.tolist()],characteristic_coefficients=[str(v)for v in coefs],roots=rootdata,
 real_root_isolations=[dict(interval=[str(x)for x in ab],multiplicity=m)for ab,m in roots],elapsed_seconds=time.perf_counter()-began)
(OUT/'spectral_rates.json').write_text(json.dumps(result,indent=2));print(json.dumps({k:v for k,v in result.items()if k not in('limiting_matrix','characteristic_coefficients','real_root_isolations')},indent=2))
if len(rootdata)>1:
 print('largest gap',float(rootdata[0]['log_modulus'])-float(rootdata[1]['log_modulus']))
