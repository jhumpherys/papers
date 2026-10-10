from box import *
def solve_tree(num,box,depth=0,maxdepth=12):
    b,degs=bern(num,box)
    if min(b.values())>=0: return ('leaf',box,degs,b)
    assert depth<maxdepth, "fail"
    m=len(box); best=None
    for i in range(m):
        if degs[i]==0: continue
        lo,hi=box[i]; mid=(lo+hi)/2
        b1=box[:i]+[(lo,mid)]+box[i+1:]; b2=box[:i]+[(mid,hi)]+box[i+1:]
        sc=min(min(bern(num,b1)[0].values()),min(bern(num,b2)[0].values()))
        if best is None or sc>best[0]: best=(sc,i,mid,b1,b2)
    _,i,mid,b1,b2=best
    return ('split',i,mid,solve_tree(num,b1,depth+1),solve_tree(num,b2,depth+1))
