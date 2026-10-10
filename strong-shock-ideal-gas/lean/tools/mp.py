# generic multivariate polynomial over Fractions with named vars
from fractions import Fraction as Fr
from math import comb
class MP:
    def __init__(s,vars,d=None):
        s.vars=tuple(vars); s.d={k:v for k,v in (d or {}).items() if v!=0}
    def z(s): return MP(s.vars)
    def c(s,x): return MP(s.vars,{(0,)*len(s.vars):Fr(x)})
    def v(s,name):
        e=[0]*len(s.vars); e[s.vars.index(name)]=1; return MP(s.vars,{tuple(e):Fr(1)})
    def _w(s,b): return b if isinstance(b,MP) else s.c(b)
    def __add__(a,b):
        b=a._w(b); d=dict(a.d)
        for k,v in b.d.items(): d[k]=d.get(k,0)+v
        return MP(a.vars,d)
    __radd__=__add__
    def __neg__(a): return MP(a.vars,{k:-v for k,v in a.d.items()})
    def __sub__(a,b): return a+(-a._w(b))
    def __rsub__(a,b): return a._w(b)-a
    def __mul__(a,b):
        b=a._w(b); d={}
        for k1,v1 in a.d.items():
            for k2,v2 in b.d.items():
                k=tuple(x+y for x,y in zip(k1,k2)); d[k]=d.get(k,0)+v1*v2
        return MP(a.vars,d)
    __rmul__=__mul__
    def __pow__(a,n):
        r=a.c(1)
        for _ in range(n): r=r*a
        return r
    def deg(a,i): return max((k[i] for k in a.d),default=0)
    def subs(a,i,p):  # substitute var i by poly p
        res=a.z(); cache={}
        for k,v in a.d.items():
            e=k[i]
            if e not in cache: cache[e]=p**e
            kk=list(k); kk[i]=0
            res=res+MP(a.vars,{tuple(kk):v})*cache[e]
        return res
    def divvar(a,i):
        d={}
        for k,v in a.d.items():
            if k[i]==0: return None
            kk=list(k); kk[i]-=1; d[tuple(kk)]=v
        return MP(a.vars,d)
    def ev(a,vals):
        t=0
        for k,v in a.d.items():
            x=v
            for e,val in zip(k,vals): x*=val**e
            t+=x
        return t
