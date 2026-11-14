#!/usr/bin/env python3
"""Exact-integer Sturm certificates for an isolated SU(2) plaquette.
This is NOT a certificate for 4D Yang--Mills I7.
Jacobi n>=0: H_nn=g^2*n*(n+2)/2+2/g^2, H_n,n+1=-1/g^2, a=1.
"""
from fractions import Fraction
from decimal import Decimal, getcontext
N=1000
BASE=10**6
getcontext().prec=23

def sturm_count(p,q,t):
    # Signs of leading minors of (2*p^2*q^2*BASE)*(J_N-t/BASE*I).
    B=2*q**4*BASE
    def entry(n):
        return BASE*(p**4*n*(n+2)+4*q**4)-2*p*p*q*q*t
    prevprev=1
    prev=entry(0)
    assert prev!=0
    signs=(prev<0)
    sign=1 if prev>0 else -1
    for n in range(1,N):
        nxt=entry(n)*prev-B**2*prevprev
        assert nxt!=0
        s=1 if nxt>0 else -1
        signs+=(s!=sign)
        prevprev,prev,sign=prev,nxt,s
    return int(signs)

def certificate(p,q,t0,t1):
    assert sturm_count(p,q,t0)==0
    assert sturm_count(p,q,t0+1)==1
    assert sturm_count(p,q,t1)==1
    assert sturm_count(p,q,t1+1)==2
    g=Fraction(p,q)
    # Whole Jacobi tail n>=N has quadratic form >= m,
    # m=g^2*N*(N+2)/2.  The link crossing the cut has size g^-2.
    m=g*g*N*(N+2)/2
    assert m/2>Fraction(t1+1,BASE)
    delta=Fraction(4*q**6,p**6*N*(N+2))
    lower=Fraction(t1-t0-1,BASE)-delta
    upper=Fraction(t1-t0+1,BASE)+delta
    assert lower>0
    todec=lambda x:Decimal(x.numerator)/Decimal(x.denominator)
    print(f'g={p}/{q}: {todec(lower):.12f} < gap(H_plaquette,a=1) '
          f'< {todec(upper):.12f}, delta={todec(delta):.12f}')

for data in [(1,2,1956434,4620625),
             (1,1,1451329,3647815),
             (3,2,830980,4286672),
             (2,1,489594,6504155)]:
    certificate(*data)
print('ALL EXACT STURM SIGN COUNTS PASS; isolated plaquette only.')
