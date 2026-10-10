from subdiv2 import *
from fractions import Fraction as Fr
from math import comb
LV=['g','k','τ','s']
def q(x):
    x=Fr(x)
    if x.denominator==1: return f"({x.numerator}:ℝ)"
    return f"(({x.numerator}:ℝ)/{x.denominator})"
def mono(e):
    parts=[]
    for v,p in zip(LV,e):
        if p==1: parts.append(v)
        elif p>1: parts.append(f"{v}^({p}:ℕ)")
    return parts
def poly_str(num):
    terms=[]
    for e,c in sorted(num.d.items()):
        terms.append(" * ".join([q(c)]+mono(e)))
    return " + ".join(terms) if terms else "0"
def leaf_proof(name,num,box,degs,b,used):
    # used: indices of vars appearing
    hyps=[]
    for i in used:
        lo,hi=box[i]
        hyps.append(f"(h{i}a : {q(lo)} ≤ {LV[i]}) (h{i}b : {LV[i]} ≤ {q(hi)})")
    U={};W={}
    for i in used:
        lo,hi=box[i]; inv=Fr(1)/(hi-lo)
        U[i]=f"(({LV[i]} - {q(lo)}) * {q(inv)})"; W[i]=f"(({q(hi)} - {LV[i]}) * {q(inv)})"
    terms=[]
    for beta,coef in b.items():
        cc=coef
        for i in used: cc*=comb(degs[i],beta[i])
        if cc==0: continue
        fs=[q(cc)]
        for i in used:
            if beta[i]>0: fs.append(f"{U[i]}^({beta[i]}:ℕ)")
            if degs[i]-beta[i]>0: fs.append(f"{W[i]}^({degs[i]-beta[i]}:ℕ)")
        terms.append(" * ".join(fs))
    bern_str=" + ".join(terms) if terms else "0"
    allv=" ".join(LV)
    L=[]
    L.append(f"lemma {name} ({allv} : ℝ) {' '.join(hyps)} :\n    0 ≤ {poly_str(num)} := by")
    for i in used:
        L.append(f"  have u{i} : 0 ≤ {U[i]} := by linarith")
        L.append(f"  have w{i} : 0 ≤ {W[i]} := by linarith")
    L.append(f"  have e : {poly_str(num)} =\n      {bern_str} := by ring")
    L.append("  rw [e]")
    L.append("  clear e")
    for i in used:
        L.append(f"  generalize {U[i]} = U{i} at u{i} ⊢")
        L.append(f"  generalize {W[i]} = W{i} at w{i} ⊢")
    L.append("  positivity")
    return "\n".join(L)
def gen(name,num,tree):
    used=[i for i in range(4) if num.deg(i)>0]
    out=[]; cnt=[0]
    def rec(t):
        if t[0]=='leaf':
            nm=f"{name}_leaf{cnt[0]}"; cnt[0]+=1
            out.append(leaf_proof(nm,num,t[1],t[2],t[3],used))
            return ('leaf',nm,t[1])
        _,i,mid,l,r=t
        return ('split',i,mid,rec(l),rec(r))
    st=rec(tree)
    # top lemma over root box
    root=tree
    while root[0]!='leaf': root=root[3]
    # root box = union; compute from tree
    def bx(t):
        if t[0]=='leaf': return t[2]
        a=bx(t[3]); b=bx(t[4]); return [(min(x[0],y[0]),max(x[1],y[1])) for x,y in zip(a,b)]
    B=bx(st)
    hyps=" ".join(f"(h{i}a : {q(B[i][0])} ≤ {LV[i]}) (h{i}b : {LV[i]} ≤ {q(B[i][1])})" for i in used)
    def proof(t,ind):
        if t[0]=='leaf':
            args=" ".join(f"(by linarith) (by linarith)" for i in used)
            return f"exact {t[1]} {' '.join(LV)} {args}"
        _,i,mid,l,r=t
        return (f"rcases le_total {LV[i]} {q(mid)} with h{i}m | h{i}m\n{ind}· "+proof(l,ind+"  ")+f"\n{ind}· "+proof(r,ind+"  "))
    out.append(f"lemma {name} ({' '.join(LV)} : ℝ) {hyps} :\n    0 ≤ {poly_str(num)} := by\n  "+proof(st,"  "))
    return "\n\n".join(out)
