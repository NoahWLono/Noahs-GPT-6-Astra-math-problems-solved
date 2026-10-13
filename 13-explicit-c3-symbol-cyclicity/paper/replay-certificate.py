"""External exact-arithmetic replay, not a Lean proof or a publication action.
Uses only the companion frozen data. No source files outside this draft are read.
"""
import json
from pathlib import Path
from time import process_time
ROOT = Path(__file__).resolve().parent
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)

def reduce_poly(values):
    a = list(values)
    while len(a) > 4:
        t = a.pop()
        base = len(a) - 4
        for j in range(4):
            a[base+j] -= t
    return tuple(a + [0] * (4-len(a)))

def cmul(a, b, shift=0):
    shift %= 5
    out = [0] * (7+shift)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[i+j+shift] += ai*bj
    return reduce_poly(out)

def cadd(a, b):
    return tuple(x+y for x,y in zip(a,b))

def scale(A, n):
    return {ij:tuple(n*a for a in v) for ij,v in A.items() if n and v != ZERO}

def add(*expressions):
    out = {}
    for A in expressions:
        for ij,v in A.items():
            out[ij] = cadd(out.get(ij,ZERO),v)
    return {ij:v for ij,v in out.items() if v != ZERO}

def sub(A,B):
    return add(A,scale(B,-1))

def mul(A,B):
    out = {}
    for (i,j),a in A.items():
        for (k,l),b in B.items():
            ij = (i+k,j+l)
            out[ij] = cadd(out.get(ij,ZERO),cmul(a,b,-j*k))
    return {ij:v for ij,v in out.items() if v != ZERO}

def mono(i,j,coefficient=ONE):
    return {(i,j):coefficient} if coefficient != ZERO else {}

def pair_mul(A,B):
    a,b = A
    d,e = B
    return sub(mul(a,d),mul(b,e)), sub(add(mul(a,e),mul(b,d)),mul(b,e))

def sigma(A):
    out = {}
    for (i,j),a in A.items():
        ij = (-j,i-j)
        phase = -j*(j+1)//2+i*j
        out[ij] = cadd(out.get(ij,ZERO),cmul(a,ONE,phase))
    return {ij:v for ij,v in out.items() if v != ZERO}

def compact():
    U,V = mono(1,0),mono(0,1)
    Ui,Vi = mono(-1,0),mono(0,-1)
    W = mono(-1,-1,cmul(ONE,ONE,-1))
    Wi = mono(1,1)
    AA = sub(U,W),sub(V,W)
    BB = sub(Ui,Wi),sub(Vi,Wi)
    square = pair_mul(AA,AA)
    fourth = pair_mul(square,square)
    c = scale(add(mono(0,0),mono(0,0,cmul(ONE,ONE,-1))),5)
    cubic_adjusted = sub(fourth[0],mul(c,AA[0])),sub(fourth[1],mul(c,AA[1]))
    P0,P1 = pair_mul(cubic_adjusted,BB)
    x,y,z = mono(5,0),mono(0,5),mono(-5,-5)
    d0,d1 = sub(x,y),sub(z,y)
    return add(mul(sub(scale(d0,2),d1),P0),mul(sub(scale(d1,2),d0),P1))

def main():
    start = process_time()
    data = json.loads((ROOT/'certificate-data.json').read_text())
    rows = data['numerator']
    N = {(i,j):tuple(v) for i,j,*v in rows}
    assert len(N)==len(rows)==69, 'Duplicate or missing numerator row'
    hrows = data['central_fifth_power']
    expected = {(5*a,5*b):(h,0,0,0) for a,b,h in hrows}
    assert len(expected)==len(hrows)==75, 'Duplicate or missing fifth-power row'
    assert compact()==N, 'Compact formula differs from the frozen numerator'
    assert sigma(N)==N, 'Frozen numerator is not invariant'
    coords13 = {ij:v for ij,v in N.items() if ij[0]%5==1 and ij[1]%5==3}
    coords23 = {ij:v for ij,v in N.items() if ij[0]%5==2 and ij[1]%5==3}
    assert coords13=={(-9,-7):(0,-2,0,0),(-4,3):(0,1,0,0),(1,-2):(0,1,0,0)}
    assert coords23=={(-3,-7):(0,0,0,1),(2,3):(0,0,0,1),(7,-2):(0,0,0,-2)}
    power = mono(0,0)
    records = []
    for k in range(1,6):
        power = mul(power,N)
        central = {ij:v for ij,v in power.items() if ij[0]%5==0 and ij[1]%5==0}
        records.append({'power':k,'support':len(power),'central_support':len(central)})
        if k < 5:
            assert not central
    assert power==expected, 'Full fifth-power identity fails'
    assert sigma(power)==power
    result = {'external_exact_arithmetic_replay':'passed','compact_equality':True,
              'sigma_invariance':True,'two_coordinate_rows':True,
              'complete_fifth_power_map_equality':True,'powers':records,
              'cpu_seconds':process_time()-start,
              'formal_status':'This Python replay is supplementary and does not replace Lean kernel verification.'}
    print(json.dumps(result,indent=2))
if __name__=='__main__':
    main()
