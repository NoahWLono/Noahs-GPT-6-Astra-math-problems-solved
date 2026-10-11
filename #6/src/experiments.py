#!/usr/bin/env python3
"""ASTRA-01 bounded synthetic experiments. Python standard library only.

No network, external keys, production curves, or arbitrary-input attack interface.
All arithmetic is exact. None denotes infinity both on E and on P^1.
"""
from __future__ import annotations
import argparse
from collections import Counter
from itertools import product
import json
from math import gcd, isqrt, lcm
from pathlib import Path
import platform
import random
import sys
import time

Point = tuple[int, int] | None
PRIMES = (11, 17, 19, 23, 29, 31, 37, 43, 59, 83, 101, 127, 211)
SEED = 2026101101


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def prime(n: int) -> bool:
    return n >= 2 and all(n % j != 0 for j in range(2, isqrt(n) + 1))


class Curve:
    def __init__(self, p: int, a: int, b: int):
        require(prime(p) and p > 3, 'Toy model requires a prime p > 3')
        self.p, self.a, self.b = p, a % p, b % p
        require((4*self.a**3 + 27*self.b**2) % p != 0, 'Singular curve')
        self.add_calls = 0

    def contains(self, P: Point) -> bool:
        return P is None or (P[1]**2-P[0]**3-self.a*P[0]-self.b) % self.p == 0

    def neg(self, P: Point) -> Point:
        return None if P is None else (P[0], -P[1] % self.p)

    def add(self, P: Point, Q: Point) -> Point:
        self.add_calls += 1
        if P is None:
            return Q
        if Q is None:
            return P
        p = self.p
        x, y = P
        u, v = Q
        if x == u and (y+v) % p == 0:
            return None
        if P == Q:
            slope = (3*x*x+self.a)*pow(2*y, -1, p) % p
        else:
            slope = (v-y)*pow(u-x, -1, p) % p
        X = (slope*slope-x-u) % p
        result = X, (slope*(x-X)-y) % p
        require(self.contains(result), 'Addition left curve')
        return result

    def mul(self, k: int, P: Point) -> Point:
        if k < 0:
            return self.mul(-k, self.neg(P))
        result = None
        while k:
            if k & 1:
                result = self.add(result, P)
            P = self.add(P, P)
            k >>= 1
        return result

    def points(self) -> list[Point]:
        roots: dict[int, list[int]] = {}
        for y in range(self.p):
            roots.setdefault(y*y % self.p, []).append(y)
        return [None] + [(x,y) for x in range(self.p)
                         for y in roots.get((x**3+self.a*x+self.b) % self.p, [])]

    def orbit(self, G: Point, n: int) -> list[Point]:
        seq, P = [], None
        for _ in range(n):
            seq.append(P)
            P = self.add(P,G)
        require(P is None and len(set(seq)) == n, 'Incorrect order')
        return seq


def generated_curve(p: int) -> tuple[Curve, Point, int]:
    for a,b in product(range(p), repeat=2):
        if (4*a**3+27*b*b) % p == 0:
            continue
        E = Curve(p,a,b)
        pts = E.points()
        n = len(pts)
        if n > 7 and n != p and prime(n):
            return E, pts[1], n
    raise ValueError(f'No suitable synthetic curve found at p={p}')


def bsgs(E: Curve, G: Point, Q: Point, n: int) -> tuple[int, dict]:
    """Exact baby-step giant-step with final scalar verification."""
    before = E.add_calls
    m = isqrt(n-1)+1
    baby: dict[Point,int] = {}
    P = None
    for j in range(m):
        baby.setdefault(P,j)
        P = E.add(P,G)
    step = E.neg(P)
    R = Q
    probes = 0
    for i in range(m):
        probes += 1
        if R in baby:
            d = i*m+baby[R]
            if d < n and E.mul(d,G) == Q:
                return d, {'add_calls_including_verification':E.add_calls-before,
                           'stored_points':len(baby), 'giant_probes':probes}
        R = E.add(R,step)
    raise ValueError('Synthetic instance has no logarithm')


def trim(A: list[int], p: int) -> list[int]:
    A = [a % p for a in A]
    while len(A)>1 and A[-1] == 0:
        A.pop()
    return A


def poly_rem(A: list[int], B: list[int], p: int) -> list[int]:
    A,B = trim(A,p), trim(B,p)
    require(B != [0], 'Division by zero polynomial')
    while A != [0] and len(A) >= len(B):
        c, shift = A[-1]*pow(B[-1],-1,p) % p, len(A)-len(B)
        for i,b in enumerate(B):
            A[i+shift] = (A[i+shift]-c*b) % p
        A = trim(A,p)
    return A


def coprime(A: list[int], B: list[int], p: int) -> bool:
    A,B = trim(A,p),trim(B,p)
    while B != [0]:
        A,B = B,poly_rem(A,B,p)
    return len(A) == 1 and A[0] != 0


def horner(A: list[int], z: int, p: int) -> int:
    t=0
    for a in reversed(A):
        t=(t*z+a) % p
    return t


def rational(z: int | None, A: list[int], B: list[int], p: int) -> int | None:
    r = max(len(A),len(B))-1
    if z is None:
        u = A[r] if r<len(A) else 0
        v = B[r] if r<len(B) else 0
    else:
        u,v=horner(A,z,p),horner(B,z,p)
    require(u != 0 or v != 0, 'Uncancelled projective base point')
    return None if v == 0 else u*pow(v,-1,p) % p


def mobius(z: int | None, M: tuple[int,int,int,int], p: int) -> int | None:
    a,b,c,d=M
    u,v=(a,c) if z is None else ((a*z+b) % p,(c*z+d) % p)
    return None if v == 0 else u*pow(v,-1,p) % p


def matrices(p: int):
    """Exactly once per PGL_2(F_p) element; first nonzero matrix entry is 1."""
    for b,c,d in product(range(p), repeat=3):
        if (d-b*c) % p:
            yield (1,b,c,d)
    for c in range(1,p):
        for d in range(p):
            yield (0,1,c,d)


COORDINATES = (('x',2),('y',3),('x+y',3),('x^2+y',4),('x*y+y',5),
               ('1/(y+1)',3))


def coord(P: Point, name: str, p: int) -> int | None:
    if P is None:
        return 0 if name == '1/(y+1)' else None
    x,y=P
    if name == 'x':
        return x
    if name == 'y':
        return y
    if name == 'x+y':
        return (x+y) % p
    if name == 'x^2+y':
        return (x*x+y) % p
    if name == 'x*y+y':
        return (x*y+y) % p
    if name == '1/(y+1)':
        return None if (y+1) % p == 0 else pow((y+1) % p,-1,p)
    raise ValueError('Unknown coordinate')


def order_mod(a: int, n: int) -> int:
    require(gcd(a,n)==1, 'Multiplicative order requires a unit')
    z=1
    for e in range(1,n+1):
        z=z*a % n
        if z == 1:
            return e
    raise AssertionError('Order search failed')


def agreement_mask(values: list, M: tuple, p: int) -> int:
    action = {z:mobius(z,M,p) for z in set(values)}
    return sum(1<<i for i,z in enumerate(values) if action[z] == values[(i+1)%len(values)])


def exhaustive_mobius(E: Curve, H: list[Point]) -> tuple[list[dict],dict]:
    p,n=E.p,len(H)
    seqs = {name:[coord(P,name,p) for P in H] for name,_ in COORDINATES}
    best = {name:(-1,None,0) for name,_ in COORDINATES}
    hist = {name:Counter() for name,_ in COORDINATES}
    x_masks = {}
    count=0
    for M in matrices(p):
        count+=1
        for name,D in COORDINATES:
            mask=agreement_mask(seqs[name],M,p)
            score=mask.bit_count()
            require(score <= min(n,2*D), 'Degree-agreement violation')
            hist[name][score]+=1
            if score > best[name][0]:
                best[name]=(score,M,mask)
            if p==11 and name=='x':
                x_masks.setdefault(mask,M)
    require(count==p*(p*p-1), 'PGL enumeration is incomplete')
    rows=[]
    for name,D in COORDINATES:
        score,M,mask=best[name]
        rows.append({'coordinate':name,'degree':D,'maps_tested':count,
                     'max_agreements':score,'bound':min(n,2*D),
                     'best_map':M,'matching_scalars':[i for i in range(n) if mask>>i&1],
                     'histogram':dict(sorted(hist[name].items()))})
    return rows,x_masks


def random_rational(E: Curve, H: list[Point], rng: random.Random, trials: int=250) -> list[dict]:
    rows=[]
    for name,D in COORDINATES:
        values=[coord(P,name,E.p) for P in H]
        hist=Counter()
        maxes={r:0 for r in (1,2,3,4)}
        for _ in range(trials):
            r=rng.choice((1,2,3,4))
            while True:
                A=trim([rng.randrange(E.p) for _ in range(r+1)],E.p)
                B=trim([rng.randrange(E.p) for _ in range(r+1)],E.p)
                if max(len(A),len(B))==r+1 and coprime(A,B,E.p):
                    break
            action={z:rational(z,A,B,E.p) for z in set(values)}
            score=sum(action[z]==values[(i+1)%len(values)] for i,z in enumerate(values))
            require(score <= min(len(H),D*(r+1)), 'Rational degree-agreement violation')
            hist[r]+=1
            maxes[r]=max(maxes[r],score)
        rows.append({'coordinate':name,'degree':D,'trials':trials,
                     'trials_by_recurrence_degree':dict(hist),
                     'max_agreements_by_recurrence_degree':maxes})
    return rows


def minimal_cover(masks: dict, n: int) -> dict:
    """Exact tiny set cover via dynamic programming on 2^n states."""
    full=(1<<n)-1
    # Remove sets properly contained in another available set.
    maximal=[m for m in masks if m and not any(m != t and m|t == t for t in masks)]
    dp=[n+1]*(full+1)
    parent=[None]*(full+1)
    dp[0]=0
    for covered in range(full+1):
        if dp[covered]>n:
            continue
        for m in maximal:
            new=covered|m
            if dp[new]>dp[covered]+1:
                dp[new]=dp[covered]+1
                parent[new]=(covered,m)
    require(dp[full]<=n,'Set cover failed')
    witness=[]
    t=full
    while t:
        prev,m=parent[t]
        witness.append({'matrix':masks[m],'scalars':[i for i in range(n) if m>>i&1]})
        t=prev
    return {'minimum_branches':dp[full],'degree_bound_lower_branches':(n+3)//4,
            'witness':witness,'search_states':1<<n,
            'distinct_masks':len(masks),'maximal_masks':len(maximal)}


def permutation_order(action: list[int]) -> int:
    seen=set()
    order=1
    for x in range(len(action)):
        if x in seen:
            continue
        y=x; length=0
        while y not in seen:
            seen.add(y); length+=1; y=action[y]
        require(y==x,'Action is not a permutation')
        order=lcm(order,length)
    return order


def pgl_checks() -> list[dict]:
    rows=[]
    for p in (5,7,11,13,17,19):
        vals=list(range(p))+[None]
        index={v:i for i,v in enumerate(vals)}
        counts=Counter()
        for M in matrices(p):
            action=[index[mobius(z,M,p)] for z in vals]
            require(len(set(action))==p+1,'Singular Mobius action')
            o=permutation_order(action)
            require(o==p or (p-1)%o==0 or (p+1)%o==0,'PGL order classification failed')
            counts[o]+=1
        require(sum(counts.values())==p*(p*p-1),'PGL order check incomplete')
        rows.append({'p':p,'matrices':sum(counts.values()),'order_histogram':dict(sorted(counts.items()))})
    return rows


def controls() -> dict:
    E=Curve(7,0,1)
    G=(0,1)
    H=E.orbit(G,3)
    M=(1,-3 % 7,1,1)
    pts=E.points()
    matches=[P for P in pts if mobius(coord(P,'y',7),M,7)==coord(E.add(P,G),'y',7)]
    require(len(matches)==len(pts)==12,'Global semiconjugacy control failed')
    # Exact exponent size versus short evaluation chain; no timing inference.
    E2,G2,n=generated_curve(211)
    P=E2.mul(37,G2)
    high_degree=[]
    for t in range(1,9):
        T=P
        before=E2.add_calls
        for _ in range(t):
            T=E2.add(T,T)
        count=E2.add_calls-before
        require(T==E2.mul(2**t,P),'Repeated doubling check failed')
        high_degree.append({'t':t,'algebraic_degree_of_x_after_2t':2*4**t,
                            'point_doublings_for_evaluation':count,
                            'value':coord(T,'x',211)})
    return {'global_degree_equal_order':{'p':7,'a':0,'b':1,'G':G,'n':3,
                    'coordinate':'y','coordinate_degree':3,'matrix':M,
                    'total_rational_points':len(pts),'agreements_on_whole_curve':len(matches),
                    'orbit':H},
            'high_degree_short_evaluation':high_degree}


def addition_correspondence(E: Curve, G: Point, H: list[Point]) -> dict:
    require(G is not None,'G must be affine')
    u,v=G
    p=E.p
    count=0; ambiguous=0
    for P in H:
        if P is None or P[0]==u:
            continue
        x,y=P
        T=E.add(P,G)
        require(T is not None,'Unexpected exceptional point')
        z=T[0]
        B=(u*x*x+(u*u+E.a)*x+E.a*u+2*E.b) % p
        lhs=((x-u)**2*z-B)**2 - 4*v*v*(x**3+E.a*x+E.b)
        require(lhs % p==0,'Squared addition correspondence failed')
        s3=(x-u)**2*z*z-2*B*z+(x*u-E.a)**2-4*E.b*(x+u)
        require(s3 % p==0, 'Reduced Semaev correspondence failed')
        roots=[zz for zz in range(p) if (((x-u)**2*zz-B)**2-
                         4*v*v*(x**3+E.a*x+E.b)) % p==0]
        require(z in roots,'Actual translated x missing')
        ambiguous+=len(roots)==2
        count+=1
    return {'tested_nonexceptional_points':count,'two_root_cases':ambiguous,
            'excluded_scalars':[i for i,P in enumerate(H) if P is None or P[0]==u]}


def run(output: Path) -> dict:
    output.mkdir(parents=True,exist_ok=True)
    rng=random.Random(SEED)
    start=time.perf_counter()
    rows=[]; total_logs=0; exhaustive_cases=0; random_cases=0
    cover=None; sharp=None
    for p in PRIMES:
        E,G,n=generated_curve(p)
        H=E.orbit(G,n)
        require(set(H)==set(E.points()),'Prime-order orbit is not the entire group')
        costs=[]
        recovered=[]
        for d,Q in enumerate(H):
            found,cost=bsgs(E,G,Q,n)
            require(found==d,'BSGS differs from exhaustive orbit')
            costs.append(cost)
            recovered.append(found)
        total_logs+=n
        e=order_mod(p,n)
        k=e//gcd(e,2)
        require(pow(p,2*k,n)==1 and all(pow(p,2*j,n)!=1 for j in range(1,k)),
                'Embedding lower threshold failed')
        ex=[]
        if p in (11,17,19):
            ex,masks=exhaustive_mobius(E,H)
            exhaustive_cases+=sum(r['maps_tested'] for r in ex)
            if p==11:
                cover=minimal_cover(masks,n)
                xrow=next(r for r in ex if r['coordinate']=='x')
                M=tuple(xrow['best_map'])
                sharp={'p':p,'a':E.a,'b':E.b,'n':n,'G':G,'coordinate':'x','degree':2,
                       'matrix':M,'matching_scalars':xrow['matching_scalars'],
                       'matches':[{'d':i,'P':H[i],'P_plus_G':H[(i+1)%n],
                                   'predicted':mobius(coord(H[i],'x',p),M,p)}
                                  for i in xrow['matching_scalars']]}
                require(xrow['max_agreements']==4,'Sharpness witness missing')
        rr=random_rational(E,H,rng)
        random_cases+=sum(r['trials'] for r in rr)
        rows.append({'p':p,'a':E.a,'b':E.b,'n':n,'G':G,'trace':p+1-n,
                     'orbit':H,'baseline_solved_all':True,'baseline_instances':n,'baseline_recovered':recovered,
                     'baseline_max_stored_points':max(c['stored_points'] for c in costs),
                     'baseline_max_add_calls':max(c['add_calls_including_verification'] for c in costs),
                     'embedding_degree':e,'min_possible_mobius_field_extension':k,
                     'exhaustive_mobius':ex,'random_rational':rr,
                     'addition_correspondence':addition_correspondence(E,G,H)})
    results={'project':'ASTRA-01','seed':SEED,'synthetic_only':True,
             'curves':rows,'sharpness_counterexample':sharp,
             'piecewise_minimum_cover':cover,'pgl_order_checks':pgl_checks(),
             'controls':controls(),
             'totals':{'curves':len(rows),'all_dlog_instances':total_logs,
                       'exhaustive_coordinate_map_tests':exhaustive_cases,
                       'sampled_coordinate_rational_map_tests':random_cases,
                       'degree_bound_violations':0},
             'runtime_seconds_diagnostic_only':round(time.perf_counter()-start,6)}
    (output/'experiments.json').write_text(json.dumps(results,indent=2)+'\n')
    env={'python':sys.version,'implementation':platform.python_implementation(),
         'platform':platform.system(),'machine':platform.machine(),'external_dependencies':[]}
    (output/'environment.json').write_text(json.dumps(env,indent=2)+'\n')
    lines=['ASTRA-01 EXACT SYNTHETIC EXPERIMENTS','',json.dumps(results['totals'],indent=2),'',
           'p a b n G embedding_degree minimum_Mobius_extension']
    lines += [f"{r['p']} {r['a']} {r['b']} {r['n']} {tuple(r['G'])} {r['embedding_degree']} {r['min_possible_mobius_field_extension']}"
              for r in rows]
    lines += ['',f'Exact minimum branch cover on the 13-point example: {cover["minimum_branches"]}',
              f'Sharpness scalars: {sharp["matching_scalars"]}',
              f'Runtime (diagnostic, not complexity evidence): {results["runtime_seconds_diagnostic_only"]} s',
              'PASS: all active exact checks completed.']
    text='\n'.join(lines)+'\n'
    (output/'summary.txt').write_text(text)
    print(text)
    return results


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=Path(__file__).resolve().parents[1]/'results')
    args=parser.parse_args()
    run(args.output)
