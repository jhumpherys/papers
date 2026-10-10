from fractions import Fraction as Fr
import itertools
VARS=['g','P','G','n','N','s','z']
IDX={v:i for i,v in enumerate(VARS)}
class Poly:
    def __init__(s,d=None):
        s.d={k:v for k,v in (d or {}).items() if v!=0}
    @staticmethod
    def const(c): return Poly({(0,)*len(VARS):Fr(c)})
    @staticmethod
    def var(v):
        e=[0]*len(VARS); e[IDX[v]]=1; return Poly({tuple(e):Fr(1)})
    def __add__(a,b):
        b=b if isinstance(b,Poly) else Poly.const(b)
        d=dict(a.d)
        for k,v in b.d.items(): d[k]=d.get(k,0)+v
        return Poly(d).norm()
    __radd__=__add__
    def __neg__(a): return Poly({k:-v for k,v in a.d.items()})
    def __sub__(a,b): return a+(-(b if isinstance(b,Poly) else Poly.const(b)))
    def __rsub__(a,b): return Poly.const(b)-a
    def __mul__(a,b):
        b=b if isinstance(b,Poly) else Poly.const(b)
        d={}
        for k1,v1 in a.d.items():
            for k2,v2 in b.d.items():
                k=tuple(x+y for x,y in zip(k1,k2)); d[k]=d.get(k,0)+v1*v2
        return Poly(d).norm()
    __rmul__=__mul__
    def __truediv__(a,c): return a*Poly.const(Fr(1)/Fr(c))
    def __pow__(a,n):
        r=Poly.const(1)
        for _ in range(n): r=r*a
        return r
    def norm(a):
        # rules: gG->1, nN->1, gP->1-2P, GP->(G-P)/2
        changed=True; d=dict(a.d)
        while changed:
            changed=False
            nd={}
            for k,v in d.items():
                k=list(k); g,P,G,n,N=k[0],k[1],k[2],k[3],k[4]
                m=min(g,G); k[0]-=m; k[2]-=m
                m=min(n,N); k[3]-=m; k[4]-=m
                k=tuple(k)
                g,P,G=k[0],k[1],k[2]
                if g>0 and P>0:
                    changed=True
                    b=list(k); b[0]-=1; b[1]-=1
                    t1=tuple(b); b2=list(b); b2[1]+=1; t2=tuple(b2)
                    nd[t1]=nd.get(t1,0)+v; nd[t2]=nd.get(t2,0)-2*v
                elif G>0 and P>0:
                    changed=True
                    b=list(k); b[2]-=1; b[1]-=1
                    b1=list(b); b1[2]+=1; b2=list(b); b2[1]+=1
                    nd[tuple(b1)]=nd.get(tuple(b1),0)+v/2; nd[tuple(b2)]=nd.get(tuple(b2),0)-v/2
                else:
                    nd[k]=nd.get(k,0)+v
            d={k:v for k,v in nd.items() if v!=0}
        r=Poly(); r.d=d; return r
    def ev(a,**val):
        tot=0
        for k,v in a.d.items():
            t=v
            for i,e in enumerate(k): t*=val[VARS[i]]**e
            tot+=t
        return tot
    def deriv_var(a,v):
        i=IDX[v]; d={}
        for k,c in a.d.items():
            if k[i]>0:
                kk=list(k); kk[i]-=1; d[tuple(kk)]=d.get(tuple(kk),0)+c*k[i]
        return Poly(d)
    def deg(a,v): return max((k[IDX[v]] for k in a.d),default=0)
    def nterms(a): return len(a.d)
g,P,G,n,N,s,z=[Poly.var(v) for v in VARS]
f0=z*z+((g-2)*P+g*P*N)*z-g*P*N
f1=-(z-1)*(z-N)
F=(1-s)*f0+s*f1
SP=-s*(1-s)*z
def D(q): return q.deriv_var('s')*SP+q.deriv_var('z')*F
th=2*P*P; ith=(g+2)*(g+2)/2
V=g*P+2*P*s; a=2*P*(1-s)
c=s*(1-z)*G; d=s*z
cp=D(c); dp=D(d); Vp=D(V); Vpp=D(Vp); cpp=D(cp)
K=(1-n)*c*ith; Kp=(1-n)*cp*ith
B=(V*a-n*Vp+2*n*cp-g*c*c)*ith
L=(V*Vp-n*Vpp+g*c*Vp-(V+g*c)*cp+n*cpp)*ith
P1=(1-g/2)*a*d+d*d/4+dp/2
P2=(-n*d*d/4+d/2+g/2*(c*d-cp))*ith
R=Kp-d*K+B-g
C=-K*(d*d/4+dp/2)+(B+g)*d/2+L
