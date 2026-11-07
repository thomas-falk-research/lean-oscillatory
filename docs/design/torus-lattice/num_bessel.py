# Numerics (tooling, never evidence): lattice Laplacian kernel, theta = 2cos k1 + 2cos k2.
# K_t(x) = (2pi)^2 i^{x1+x2} J_{x1}(2t) J_{x2}(2t); sup_x |K_t(x)| = (2pi)^2 (sup_n |J_n(2t)|)^2.
import numpy as np
from scipy.special import jv
from scipy.integrate import quad
# identity check: int_{-pi}^{pi} e^{i(xk + 2t cos k)} dk = 2 pi i^x J_x(2t)
for (x,t) in [(3,5.0),(7,4.2),(0,10.0)]:
    re = quad(lambda k: np.cos(x*k+2*t*np.cos(k)), -np.pi, np.pi, limit=400)[0]
    im = quad(lambda k: np.sin(x*k+2*t*np.cos(k)), -np.pi, np.pi, limit=400)[0]
    print("identity", x, t, complex(re,im), 2*np.pi*(1j)**x*jv(x,2*t))
for t in [10,30,100,300,1000,3000,10000]:
    n = np.arange(0, int(4*t)+50)
    s = np.max(np.abs(jv(n, 2*t)))
    print(f"t={t:6d} sup_n|J_n(2t)|*t^(1/3)={s*t**(1/3):.4f}  sup_x|K_t|*t^(2/3)={(2*np.pi)**2*s*s*t**(2/3):.4f}")
