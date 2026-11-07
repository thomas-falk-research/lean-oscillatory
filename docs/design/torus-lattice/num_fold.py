# Numerics (tooling, never evidence): search for 2pi-periodic trig polynomials theta with
# (i) no point with D^2 theta = 0 and (ii) every rank-one point a fold (D^3[v,v,v] != 0, v in ker).
import numpy as np, itertools, sys
rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv)>1 else 0)
modes = [(1,0),(0,1),(1,1),(1,-1),(2,0),(0,2),(2,1),(1,2)]
def derivs(c, s, K1, K2):
    # theta = sum c_m cos(m.k) + s_m sin(m.k)
    H = np.zeros((2,2)+K1.shape); T = np.zeros((2,2,2)+K1.shape)
    for (m,cm,sm) in zip(modes,c,s):
        ph = m[0]*K1+m[1]*K2; C=np.cos(ph); S=np.sin(ph)
        d2 = -(cm*C+sm*S); d3 = (cm*S - sm*C)
        for i,j in itertools.product(range(2),repeat=2):
            H[i,j] += m[i]*m[j]*d2
            for l in range(2): T[i,j,l] += m[i]*m[j]*m[l]*d3
    return H,T
def score(c,s,n=300):
    g = np.linspace(-np.pi,np.pi,n,endpoint=False); K1,K2 = np.meshgrid(g,g,indexing='ij')
    H,T = derivs(c,s,K1,K2)
    fro = np.sqrt((H**2).sum(axis=(0,1)))
    det = H[0,0]*H[1,1]-H[0,1]**2
    # zero crossings of det along both grid directions -> refine by linear interpolation
    pts=[]
    for ax in (0,1):
        d2 = np.roll(det,-1,axis=ax); mask = det*d2<0
        lam = det[mask]/(det[mask]-d2[mask]); h = 2*np.pi/n
        k1 = K1[mask]+(lam*h if ax==0 else 0); k2 = K2[mask]+(lam*h if ax==1 else 0)
        pts.append((k1,k2))
    k1=np.concatenate([p[0] for p in pts]); k2=np.concatenate([p[1] for p in pts])
    if len(k1)==0: return fro.min(), np.inf, 0
    Hp,Tp = derivs(c,s,k1,k2)
    # kernel of symmetric 2x2: eigenvector of smaller |eig|
    a,b,d = Hp[0,0],Hp[0,1],Hp[1,1]
    tr=(a+d)/2; disc=np.sqrt(((a-d)/2)**2+b**2)
    l1=tr+disc; l2=tr-disc; lam=np.where(np.abs(l1)<np.abs(l2),l1,l2)
    v1 = np.where(np.abs(b)>1e-12, b, np.where(np.abs(a-lam)<np.abs(d-lam),1.0,0.0))
    v2 = np.where(np.abs(b)>1e-12, lam-a, np.where(np.abs(a-lam)<np.abs(d-lam),0.0,1.0))
    nv=np.sqrt(v1**2+v2**2); v1/=nv; v2/=nv
    cub = sum(Tp[i,j,l]*[v1,v2][i]*[v1,v2][j]*[v1,v2][l] for i in range(2) for j in range(2) for l in range(2))
    return fro.min(), np.abs(cub).min(), len(k1)
print("lattice Laplacian 2cos+2cos:", score([2,2,0,0,0,0,0,0],[0]*8))
best=[]
for trial in range(400):
    c = rng.normal(size=8)*np.array([1,1,.6,.6,.3,.3,.2,.2]); s = rng.normal(size=8)*np.array([1,1,.6,.6,.3,.3,.2,.2])
    f,g,npts = score(c,s,160)
    best.append((min(f,g),f,g,c,s))
best.sort(key=lambda r:-r[0])
for r in best[:3]:
    f2,g2,_=score(r[3],r[4],600)
    print(f"coarse min|D2|={r[1]:.3f} min|D3[v,v,v]| on parabolic={r[2]:.3f}; fine(600): {f2:.3f} {g2:.3f}")
    print("  c=",np.round(r[3],3).tolist()," s=",np.round(r[4],3).tolist())
print("fraction of trials with both > 0.05 at coarse grid:", np.mean([(r[1]>0.05 and r[2]>0.05) for r in best]))
