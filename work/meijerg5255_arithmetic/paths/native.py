"""Exact native MeijerG(5,2,5,5,1) shifted generators; no scalar gauge."""
from flint import fmpq, fmpq_mat
from math import gcd,lcm,prod

START=(1,1,0,0,0,0,0,0,0,0)
DIRECTION=(16,17,-11,-12,-10,2,1,0,-1,-2)
ORDER=(2,3,4,0,1,5,6,8,9)
I=fmpq_mat([[int(i==j) for j in range(4)]for i in range(4)])

def coefficients(roots):
    c=[1]
    for r in roots:
        z=[0]*(len(c)+1)
        for i,a in enumerate(c):z[i]-=r*a;z[i+1]+=a
        c=z
    return c

def theta(w):
    a=coefficients([x-1 for x in w[:5]]);b=coefficients(w[5:])
    c=[x-y for x,y in zip(a,b)]
    if not c[4]:raise ZeroDivisionError(('degree-drop',w))
    return fmpq_mat([[int(i==j+1) if j<3 else fmpq(-c[i],c[4])
                      for j in range(4)]for i in range(4)])

def move(w,ax,sign):
    v=list(w);v[ax]+=sign;v=tuple(v)
    if ax<5:
        s=1 if ax<2 else -1
        E=(theta(w)-I*(w[ax]-1))*s if sign<0 else ((theta(v)-I*w[ax])*s).inv()
    else:
        E=I*w[ax]-theta(w) if sign>0 else (I*v[ax]-theta(v)).inv()
    return v,E

def balanced(ms):
    if not ms:return I
    while len(ms)>1:ms=[ms[i]*ms[i+1]if i+1<len(ms)else ms[i]for i in range(0,len(ms),2)]
    return ms[0]

def segment(start,end,order=ORDER):
    w=tuple(start);ms=[]
    for ax in order:
        d=end[ax]-w[ax]
        for _ in range(abs(d)):
            w,E=move(w,ax,1 if d>0 else -1);ms.append(E)
    assert w==tuple(end)
    return balanced(ms)

def endpoint(T):return tuple(s+T*d for s,d in zip(START,DIRECTION))
def readout(A,B):return fmpq_mat([[0,0,-6*A,3*A-2*B],[12,0,0,0]])
def qgcd(a,b):return fmpq(gcd(int(a.numerator),int(b.numerator)),lcm(int(a.denominator),int(b.denominator)))
def qlcm(a,b):
    if not a:return abs(b)
    if not b:return abs(a)
    return fmpq(lcm(int(a.numerator),int(b.numerator)),gcd(int(a.denominator),int(b.denominator)))
def content(v):
    c=fmpq(0)
    for x in v:c=qgcd(c,x)
    return c
def encode(M):return [[str(M[i,j])for j in range(M.ncols())]for i in range(M.nrows())]
def decode(M):return fmpq_mat([[fmpq(s)for s in row]for row in M])

