#!/usr/bin/env python3
"""Round73 numerical checks for exact SU2 Wilson star; NOT a proof of I7."""
import random, math
import mpmath as mp

mp.mp.dps = 50
random.seed(73)

def logZ(t):
    return mp.mpf(0) if t == 0 else mp.log(2 * mp.besseli(1,t) / t)

def quaternion():
    a = [random.gauss(0,1) for _ in range(4)]
    d = math.sqrt(sum(z*z for z in a))
    return [z/d for z in a]

def star(beta, a):
    m = len(a)
    h = [sum(x[i] for x in a) for i in range(4)]
    E = sum(sum((a[i][k]-a[j][k])**2 for k in range(4))
            for i in range(m) for j in range(i+1,m))
    D = logZ(m*beta)-logZ(beta*mp.sqrt(sum(z*z for z in h)))
    return D, mp.mpf(E)

for m in (4,6):
    for b in (mp.mpf("0.1"),mp.mpf("1"),mp.mpf("2.3"),
              mp.mpf("8"),mp.mpf("32")):
        for _ in range(80):
            D,E=star(b,[quaternion() for _ in range(m)])
            assert b*b*E/(2*(m*b+4))<=D+mp.mpf("1e-12")
            assert D<=b*b*E/8+mp.mpf("1e-12")
    print("SU2",m,"staples: 400 random tests passed")

for b in (mp.mpf("1"),mp.mpf("2.3"),mp.mpf("8"),mp.mpf("32")):
    flat=mp.exp(-2*b+logZ(3*b)-logZ(b))
    opp=mp.exp(2*b)
    print("beta",float(b),"flat",float(flat),"worst",mp.nstr(opp,10))

for z in (mp.mpf("0.1"),mp.mpf("1"),mp.mpf("4"),mp.mpf("32")):
    r=mp.besseli(2,z)/mp.besseli(1,z)
    assert z/(z+4)<=r<=z/4
print("Bessel ratio inequalities passed (numerical only)")
