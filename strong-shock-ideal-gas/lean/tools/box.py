from lp import *
from mp import MP, Fr, comb
BV=('g','k','tau','s')
O=MP(BV)
gg,kk,tt,ss=[O.v(x) for x in BV]
t_=1+(kk-1)*tt
def to_box(Q):
    """Q Laurent in g,P,G,n,N,s,z -> (numerator MP, denominator description).
       substitution n=1+gk, z=1/(1+g t), P=1/(g+2), G=1/g, N=1/(1+gk)."""
    mx=[0]*7
    for k in Q.d:
        for i in (1,2,4,6): mx[i]=max(mx[i],k[i])
    num=O.z()
    for k,v in Q.d.items():
        eg,eP,eG,en,eN,es,ez=k
        term=O.c(v)*gg**(eg+mx[2]-eG)*(gg+2)**(mx[1]-eP)*(1+gg*kk)**(en+mx[4]-eN)*ss**es*(1+gg*t_)**(mx[6]-ez)
        num=num+term
    gpow=mx[2]
    while gpow>0:
        r=num.divvar(0)
        if r is None: break
        num=r; gpow-=1
    den=dict(g=gpow,gp2=mx[1],n=mx[4],zden=mx[6])
    return num,den
def bern(num,box,degs=None):
    """Bernstein coefficients of num on box [(lo,hi)...], returns dict multiindex->coef."""
    vars_=num.vars; m=len(vars_)
    p=num
    for i,(lo,hi) in enumerate(box):
        # x = lo + (hi-lo) u
        u=MP(vars_).v(vars_[i])
        p=p.subs(i,lo+(hi-lo)*u)
    degs=degs or [p.deg(i) for i in range(m)]
    # power coeffs a_alpha -> bernstein b_beta = sum_{alpha<=beta} prod C(beta_i,alpha_i)/C(d_i,alpha_i) a_alpha
    import itertools
    res={}
    for beta in itertools.product(*[range(d+1) for d in degs]):
        t=Fr(0)
        for alpha,a in p.d.items():
            if all(x<=y for x,y in zip(alpha,beta)):
                w=Fr(1)
                for x,y,d in zip(alpha,beta,degs): w*=Fr(comb(y,x),comb(d,x))
                t+=w*a
        res[beta]=t
    return res,degs
