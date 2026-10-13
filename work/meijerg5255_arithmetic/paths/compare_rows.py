"""Fixed-target and universal comparisons with strict maximizing-set tests."""
import json,sys,math
from itertools import combinations
from sympy import primerange,factorint
from search import OUT,logabs
from native import *
sys.set_int_max_str_digits(0)

def vp(q,p):
    if not q:return 10**8
    v=0
    for sign,n in((1,abs(int(q.numerator))),(-1,int(q.denominator))):
        while n%p==0:n//=p;v+=sign
    return v

def run(T):
    paths=[r for r in map(json.loads,(OUT/f'paths_T{T}.jsonl').read_text().splitlines())if r['status']=='NUMERICAL_CANDIDATE']
    data=[(decode(r['prefix_rows']),list(map(fmpq,r['suffix_column'])))for r in paths]
    reports=[]
    for AB in [(1,0),(0,1),(1,1),None]:
        cs=[]
        for Z,b in data:
            numer=[[Z[0,i]*AB[0]+Z[1,i]*AB[1]for i in range(4)]]if AB else[[Z[j,i]for i in range(4)]for j in range(2)]
            rr=numer+[[Z[2,i]for i in range(4)]]
            cs.append([content(row[i]*b[i]for i in range(4))for row in rr])
        env=[fmpq(0)]*len(cs[0]);same=fmpq(0);best=fmpq(0)
        for c in cs:
            env=[qlcm(x,y)for x,y in zip(env,c)];common=content(c);same=qlcm(same,common);best=max(best,common)
        indep=content(env);gain=indep/same
        roww=[];primew=[];opts=[]
        for p in primerange(2,50*T+50):
            vs=[[vp(q,p)for q in c]for c in cs];maxima=[max(v[j]for v in vs)for j in range(len(vs[0]))]
            common=max(min(v)for v in vs)
            if min(maxima)>common:
                ex=[]
                for j,m in enumerate(maxima):
                    ii=next(i for i,v in enumerate(vs)if v[j]==m)
                    ex.append(dict(row=j,path=paths[ii]['name'],direction_to_cut=paths[ii]['direction_to_cut'],bounds=vs[ii]))
                roww.append(dict(prime=int(p),best_same_path=common,best_separate_rows=min(maxima),row_maxima=maxima,choices=ex))
            opts.append((p,{i for i,v in enumerate(vs)if min(v)==common},common,vs))
        for x,y in combinations(opts,2):
            if not x[1].isdisjoint(y[1]):continue
            i=min(x[1]);j=min(y[1])
            primew.append(dict(primes=[int(x[0]),int(y[0])],optimal_common=[x[2],y[2]],
                               first_path=paths[i]['name'],second_path=paths[j]['name'],
                               first_bounds=[x[3][i],y[3][i]],second_bounds=[x[3][j],y[3][j]],
                               complete_maximizing_sets_disjoint=True));break
        z=dict(A_B=AB,prime_adaptation_gain=str(same/best),row_adaptation_gain=str(gain),
               row_adaptation_gain_factorization={str(k):int(v)for k,v in factorint(int(gain)).items()},
               row_witnesses=roww,prime_witnesses=primew)
        reports.append(z)
        print(json.dumps(dict(T=T,**{k:v for k,v in z.items()if k not in('row_witnesses','prime_witnesses')})),flush=True)
    (OUT/f'witnesses_T{T}.json').write_text(json.dumps(reports,indent=2)+'\n')

if __name__=='__main__':
    for T in map(int,sys.argv[1:]or[10,20,40,80]):run(T)
