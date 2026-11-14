#!/usr/bin/env python3
"""Exact 4D parity construction for optimal plaquette-independent SU(2) link decimation.
Pure finite combinatorial certificate; NOT a YM mass-gap proof and NOT Lean.
Axes 0,1,2 are spatial and 3 is Euclidean time.
"""
from collections import Counter, defaultdict
from itertools import product, combinations

F = {
 (0,0,0,0):3,(0,0,0,1):3,(0,0,1,0):0,(0,0,1,1):1,
 (0,1,0,0):2,(0,1,0,1):0,(0,1,1,0):2,(0,1,1,1):1,
 (1,0,0,0):1,(1,0,0,1):2,(1,0,1,0):0,(1,0,1,1):2,
 (1,1,0,0):1,(1,1,0,1):0,(1,1,1,0):3,(1,1,1,1):3,
}
def shift(x,i,L):
 y=list(x); y[i]=(y[i]+1)%L; return tuple(y)
def chosen(x,i): return F[tuple(c%2 for c in x)]==i

# Exhaustive universal 2^4*6 parity identity, independent of L.
for x in product(range(2),repeat=4):
 for i,j in combinations(range(4),2):
  assert (int(chosen(x,i))+int(chosen(shift(x,j,2),i))+
          int(chosen(x,j))+int(chosen(shift(x,i,2),j)))==1
print("universal 96-case 2-periodic plaquette identity: PASS")

for L in (2,4,6,8):
 V=list(product(range(L),repeat=4))
 stars=defaultdict(set); inc=Counter()
 for x in V:
  assert sum(chosen(x,i) for i in range(4))==1
  for i,j in combinations(range(4),2):
   edges=[(x,i),(shift(x,j,L),i),(x,j),(shift(x,i,L),j)]
   hit=[e for e in edges if chosen(*e)]
   assert len(hit)==1
   for e in edges:
    if e!=hit[0]:
     stars[hit[0]].add(e); inc[e]+=1
  reflected_spatial=x[:3]+((-x[3])%L,)
  reflected_time_base=x[:3]+((-x[3]-1)%L,)
  assert all(chosen(x,i)==chosen(reflected_spatial,i) for i in range(3))
  assert chosen(x,3)==chosen(reflected_time_base,3)
 if L>=4:
  assert Counter(map(len,stars.values()))=={18:len(V)}
  assert Counter(inc.values())=={6:3*len(V)}
 print(f'L={L}: removed={len(V)} / links={4*len(V)}, plaquettes={6*len(V)}, '
       f'fraction=1/4, site-reflection and time-2 compatibility=PASS, '
       f'star-size={18 if L>=4 else "boundary-degenerate"}, '
       f'retained-degree={6 if L>=4 else "boundary-degenerate"}')
print('optimality: 6|M|<=6|V|, |E|=4|V|, hence |M|/|E|<=1/4 (attained).')
