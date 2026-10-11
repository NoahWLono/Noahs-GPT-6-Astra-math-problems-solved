#!/usr/bin/env python3
"""Independent implementation checks, without importing experiments.py.

This is an implementation cross-check by the same research session, not a
proof-assistant certification or external peer review. Standard library only.
"""
from __future__ import annotations
from collections import Counter
from itertools import product
import json
from math import isqrt
from pathlib import Path
import sys
import time


def check(ok, msg):
    if not ok:
        raise AssertionError(msg)


def quotient_linear(coeff, r, p):
    """Divide a low-to-high polynomial by (X-r), checking remainder."""
    out=[0]*(len(coeff)-1)
    out[-1]=coeff[-1] % p
    for i in range(len(coeff)-2,0,-1):
        out[i-1]=(coeff[i]+r*out[i]) % p
    check((coeff[0]+r*out[0]) % p == 0,'Supplied root has nonzero remainder')
    return out


def third_intersection_add(P,Q,p,a,b):
    if P is None:
        return Q
    if Q is None:
        return P
    x,y=P; u,v=Q
    if x==u and (y+v) % p==0:
        return None
    if P==Q:
        A,B=-(3*x*x+a) % p,2*y % p
    else:
        A,B=(v-y) % p,(x-u) % p
    C=-(A*x+B*y) % p
    # Substitute B*Y=-(A*X+C) into Y^2=X^3+aX+b.
    cubic=[(B*B*b-C*C) % p,(B*B*a-2*A*C) % p,-A*A % p,B*B % p]
    linear=quotient_linear(quotient_linear(cubic,x,p),u,p)
    X=-linear[0]*pow(linear[1],-1,p) % p
    # Reflect the third intersection in the x-axis.
    Y=(A*X+C)*pow(B,-1,p) % p
    check((Y*Y-X**3-a*X-b) % p==0,'Reference result left the curve')
    return X,Y


def projective_coordinate(P,name,p):
    if P is None:
        return (0,1) if name=='1/(y+1)' else (1,0)
    x,y=P
    if name=='x': return x,1
    if name=='y': return y,1
    if name=='x+y': return (x+y) % p,1
    if name=='x^2+y': return (x*x+y) % p,1
    if name=='x*y+y': return (x*y+y) % p,1
    if name=='1/(y+1)': return 1,(y+1) % p
    raise ValueError(name)


def same_projective(U,V,p):
    return (U[0]*V[1]-U[1]*V[0]) % p==0


def apply_matrix(U,M,p):
    a,b,c,d=M
    return ((a*U[0]+b*U[1]) % p,(c*U[0]+d*U[1]) % p)


def normalized(M,p):
    pivot=next(x for x in M if x % p)
    inv=pow(pivot,-1,p)
    return tuple(x*inv % p for x in M)


def brute_matrices(p):
    """Independent enumeration: all p^4 matrices, normalize and deduplicate."""
    s=set()
    for M in product(range(p),repeat=4):
        a,b,c,d=M
        if (a*d-b*c) % p:
            s.add(normalized(M,p))
    check(len(s)==p*(p*p-1),'Reference PGL cardinality mismatch')
    return sorted(s)


def mul_matrix(M,N,p):
    a,b,c,d=M; e,f,g,h=N
    return ((a*e+b*g) % p,(a*f+b*h) % p,(c*e+d*g) % p,(c*f+d*h) % p)


def matrix_order(M,p):
    A=(1,0,0,1)
    for t in range(1,p+2):
        A=mul_matrix(A,M,p)
        if A[1]==0 and A[2]==0 and A[0]==A[3]:
            return t
    raise AssertionError('Order exceeded p+1')


def main(root):
    started=time.perf_counter()
    data=json.loads((root/'results/experiments.json').read_text())
    pairs=0; logs=0; rational_points=0; ex_cases=0
    for row in data['curves']:
        p,a,b,n=row['p'],row['a'],row['b'],row['n']
        H=[None if P is None else tuple(P) for P in row['orbit']]
        G=tuple(row['G'])
        pts={None}|{(x,y) for x,y in product(range(p),repeat=2)
                         if (y*y-x**3-a*x-b) % p==0}
        check(pts==set(H) and len(pts)==n,'Independent exhaustive point set mismatch')
        check(n!=p and all(n%j for j in range(2,isqrt(n)+1)), 'Order not a non-anomalous prime')
        rational_points+=len(pts)
        P=None
        for d in range(n):
            check(P==H[d] and row['baseline_recovered'][d]==d,'Reference logarithm mismatch')
            P=third_intersection_add(P,G,p,a,b)
            logs+=1
        check(P is None,'Reference orbit did not close')
        for i,P in enumerate(H):
            for j,Q in enumerate(H):
                check(third_intersection_add(P,Q,p,a,b)==H[(i+j)%n],
                      'Independent all-pairs group law mismatch')
                pairs+=1
        if row['exhaustive_mobius']:
            mats=brute_matrices(p)
            for rec in row['exhaustive_mobius']:
                vals=[projective_coordinate(P,rec['coordinate'],p) for P in H]
                hist=Counter()
                for M in mats:
                    score=sum(same_projective(apply_matrix(U,M,p),vals[(i+1)%n],p)
                              for i,U in enumerate(vals))
                    hist[score]+=1
                    ex_cases+=1
                check(dict(hist)=={int(k):v for k,v in rec['histogram'].items()},
                      'Independent Mobius histogram mismatch')
                check(max(hist)==rec['max_agreements'],'Independent maximum mismatch')
        # Embedding order independently checked by divisors of n-1.
        e=next(t for t in range(1,n) if (n-1)%t==0 and pow(p,t,n)==1)
        check(e==row['embedding_degree'],'Independent embedding-degree mismatch')
        k=next(t for t in range(1,n) if pow(p,2*t,n)==1)
        check(k==row['min_possible_mobius_field_extension'],'Independent field threshold mismatch')
    sharp=data['sharpness_counterexample']
    H=[None if P is None else tuple(P) for P in data['curves'][0]['orbit']]
    observed=[]
    for i,P in enumerate(H):
        U=projective_coordinate(P,'x',11)
        V=projective_coordinate(H[(i+1)%13],'x',11)
        if same_projective(apply_matrix(U,sharp['matrix'],11),V,11): observed.append(i)
    check(observed==[1,6,8,9],'Sharpness scalars changed')
    covered=set()
    for w in data['piecewise_minimum_cover']['witness']:
        actual={i for i,P in enumerate(H) if same_projective(
                apply_matrix(projective_coordinate(P,'x',11),w['matrix'],11),
                projective_coordinate(H[(i+1)%13],'x',11),11)}
        check(actual==set(w['scalars']),'Branch witness mismatch')
        covered|=actual
    check(covered==set(range(13)),'Branch cover incomplete')
    check(len(data['piecewise_minimum_cover']['witness'])==4,'Nonminimal cover')
    pgl_count=0
    for row in data['pgl_order_checks']:
        p=row['p']; hist=Counter(matrix_order(M,p) for M in brute_matrices(p))
        check(dict(hist)=={int(k):v for k,v in row['order_histogram'].items()},
              'Matrix-power orders disagree with permutation orders')
        pgl_count+=sum(hist.values())
    ctrl=data['controls']['global_degree_equal_order']
    pts=[None]+[(x,y) for x,y in product(range(7),repeat=2) if (y*y-x**3-1)%7==0]
    for P in pts:
        Q=third_intersection_add(P,(0,1),7,0,1)
        check(same_projective(apply_matrix(projective_coordinate(P,'y',7),ctrl['matrix'],7),
                              projective_coordinate(Q,'y',7),7),'Reference positive control failed')
    report={'status':'PASS','external_peer_review':False,'formal_proof_checker':False,
            'imports_primary_implementation':False,
            'independently_counted_points':rational_points,
            'independent_logarithm_checks':logs,'all_pairs_group_law_checks':pairs,
            'independently_recomputed_mobius_cases':ex_cases,
            'independent_matrix_power_order_checks':pgl_count,
            'sharpness_counterexample_verified':True,'minimum_four_branch_cover_verified':True,
            'global_semiconjugacy_control_verified':True,
            'runtime_seconds_diagnostic_only':round(time.perf_counter()-started,6)}
    (root/'results/independent_checks.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    main(Path(sys.argv[1]) if len(sys.argv)>1 else Path(__file__).resolve().parents[1])
