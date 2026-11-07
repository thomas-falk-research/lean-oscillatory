import numpy as np, sys
sys.argv=['x','0']
exec(open(sys.argv[0] if False else __import__('os').path.join(__import__('os').path.dirname(__file__),'num_fold.py')).read().split('print("lattice')[0])
for cc in [0.3,0.5,0.8,1.5,3.0]:
    for n in (300,900):
        print("theta=cos k1+cos k2+%.1f cos k1 cos k2"%cc, n, score([1,1,cc/2,cc/2,0,0,0,0],[0]*8,n))
