"""Independent exact reconstruction of Stembridge's naturally labelled example 14.

Source: https://websites.umich.edu/~jrs//data/pocon/ (section IV).
This script is a discovery/reproduction aid, not a Lean proof dependency.
"""
from functools import cache
from fractions import Fraction
import json

BASE = [(16,17),(4,13),(6,15),(4,6),(2,4),(14,16),(12,14),
        (1,4),(1,3),(13,17),(3,5),(5,7),(7,9),(9,11),
        (13,15),(11,13),(10,12),(6,8),(8,10),(2,11)]
EXTRA = [(3,6),(5,8),(7,10),(9,12),(11,14)]
N = 17
pred = [0] * N
for i,j in BASE + EXTRA:
    assert 1 <= i < j <= N
    pred[j-1] |= 1 << (i-1)
for j in range(N):
    for i in range(j):
        if pred[j] >> i & 1:
            pred[j] |= pred[i]

@cache
def counts(mask, previous):
    if mask == (1 << N)-1:
        return (1,) + (0,)*N
    out = [0]*(N+1)
    for i in range(N):
        if mask >> i & 1 or pred[i] & mask != pred[i]:
            continue
        child = counts(mask | (1 << i), i)
        shift = int(previous < N and previous > i)
        for d in range(N+1-shift):
            out[d+shift] += child[d]
    return tuple(out)

coeffs = [0] + list(counts(0,N))
expected = [0,1,32,336,1420,2534,1946,658,86,3] + [0]*9
assert coeffs == expected
def deriv(p): return [i*p[i] for i in range(1,len(p))]
def ev(p,x):
    r = 0
    for a in p[::-1]: r = r*x+a
    return r
x = -2
p0,p1,p2 = ev(coeffs,x),ev(deriv(coeffs),x),ev(deriv(deriv(coeffs)),x)
assert p1*p1-p0*p2 == -18495
print(json.dumps(dict(covers=BASE+EXTRA, predecessor_masks=pred,
    coefficients=coeffs, linear_extensions=sum(coeffs),
    evaluation=dict(x=x,p=p0,derivative=p1,second_derivative=p2,
                    laguerre=p1*p1-p0*p2),states=counts.cache_info().currsize),indent=2))
