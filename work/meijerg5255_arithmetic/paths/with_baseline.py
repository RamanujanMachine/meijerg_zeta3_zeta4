"""Combine exact path certificates with the uniform factorial/LCM bound."""
import sys,json,math
from bisect import bisect_left
from fractions import Fraction
from sympy import primerange
from native import *
from search import OUT,ROWS,logabs
sys.set_int_max_str_digits(0)

def uniform_shell_factor(T):
    root=OUT.parents[2]
    cells=json.loads((root/'results/meijerg5255_arithmetic/profiles/exact_chambers.json').read_text())
    ends=[Fraction(r['hi'])for r in cells];G=1
    for p in primerange(2,29*T+1):
        g=0
        if p>29 and p*p>30*T and T%p:
            x=Fraction(T,p);f=x%1;r=cells[bisect_left(ends,f)]
            g=r['g4']if x<1 else r['tail']
        if 8*T<p<11*T:g+=1
        G*=int(p)**g
    return G

def run(T,with_shells=False):
    paths=[r for r in map(json.loads,(OUT/f'paths_T{T}.jsonl').read_text().splitlines())if r['status']=='NUMERICAL_CANDIDATE']
    data=[(decode(r['prefix_rows']),list(map(fmpq,r['suffix_column'])))for r in paths]
    W=segment(START,endpoint(T));Y=ROWS*W
    C=fmpq(math.factorial(15*T)**2,math.factorial(10*T)**3)
    D=math.lcm(*range(1,19*T+1));reports=[]
    G=uniform_shell_factor(T)if with_shells else 1
    basis=[fmpq(0)]*3
    for r in paths:basis=[qlcm(x,fmpq(y))for x,y in zip(basis,r['row_contents'])]
    for A,B in[(1,0),(0,1),(1,1)]:
        base=2*G/(C*D**(3 if B==0 else 4))
        cs=[];env=[base,base];same=base;best=base
        for Z,b in data:
            cs.append([content((A*Z[0,i]+B*Z[1,i])*b[i]for i in range(4)),content(Z[2,i]*b[i]for i in range(4))])
        for c in cs:
            env=[qlcm(x,y)for x,y in zip(env,c)];com=qlcm(base,content(c));same=qlcm(same,com);best=max(best,com)
        direct=content(env)
        split=content([A*basis[0],B*basis[1]])
        split_bound=qgcd(qlcm(env[0],split),env[1])
        actual=qgcd(A*Y[0,0]+B*Y[1,0],Y[2,0])
        assert (actual/split_bound).denominator==1
        z=dict(T=T,A=A,B=B,uniform_carry_and_broad_shells=with_shells,log_q_base=logabs(Y[2,0]/base),log_q_best_fixed=logabs(Y[2,0]/best),
               log_q_prime_adaptive=logabs(Y[2,0]/same),log_q_direct_rows=logabs(Y[2,0]/direct),
               log_q_split_initial_row=logabs(Y[2,0]/split_bound),log_q_actual=logabs(Y[2,0]/actual),
               direct_row_gain=str(direct/same),split_row_gain=str(split_bound/direct),
               gain_over_baseline=str(split_bound/base))
        reports.append(z);print(json.dumps({k:v for k,v in z.items()if len(str(v))<180}),flush=True)
    prefix='shell_baseline'if with_shells else'baseline'
    (OUT/f'{prefix}_T{T}.json').write_text(json.dumps(reports,indent=2)+'\n')

if __name__=='__main__':
    for T in map(int,sys.argv[1:]or[10,20,40,80,160,320]):run(T)
