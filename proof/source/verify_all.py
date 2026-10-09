#!/usr/bin/env python3
"""Reproduce the explicit n=12 construction with Python 3.10+ only.

No floating-point arithmetic, third-party Python packages, or network access.
This checks all masks and all fast-Walsh coefficients, and raw-sum samples.
It is an independent executable check, not a substitute for a Lean proof.
"""
from pathlib import Path
from itertools import combinations
from collections import Counter
import hashlib, json, time

ROOT = Path(__file__).resolve().parent
CERT = json.loads((ROOT/'construction/certificate.json').read_text())
PAIR4 = list(combinations(range(4), 2))
PAIR12 = list(combinations(range(12), 2))
EXPECTED_BAD = [0, 4, 8, 13, 14, 15]

def require(test, message):
    if not test:
        raise ValueError(message)

def mul(a, b):
    """Polynomial-convolution multiplication modulo t^3+t+1."""
    p = 0
    for i in range(3):
        for j in range(3):
            if ((a >> i) & 1) and ((b >> j) & 1):
                p ^= 1 << (i + j)
    for i in range(4, 2, -1):
        if (p >> i) & 1:
            p ^= 11 << (i - 3)
    return p

def power(a, n):
    r = 1
    for _ in range(n): r = mul(r, a)
    return r

def trace(a):
    t = a ^ power(a, 2) ^ power(a, 4)
    require(t in [0, 1], 'Trace does not land in F2')
    return t

def entries(label):
    u,v,w,z,s,t,p,q = [(label >> i) & 1 for i in range(8)]
    return [u^v^mul(2,s^t), u^mul(2,s)^mul(4,q),
            w^mul(4,p^q), z^mul(4,p),
            v^mul(2,s)^mul(4,q), u^v^mul(2,t)]

def matrix(label):
    m = [[0]*4 for _ in range(4)]
    for (i,j),v in zip(PAIR4, entries(label)): m[i][j] = m[j][i] = v
    return m

def rank(m, field):
    m = [r[:] for r in m]
    nr, nc, r = len(m), len(m[0]), 0
    for c in range(nc):
        k = next((i for i in range(r,nr) if m[i][c]), None)
        if k is None: continue
        m[r], m[k] = m[k], m[r]
        if field == 8:
            inv = power(m[r][c], 6)
            m[r] = [mul(v,inv) for v in m[r]]
        for i in range(nr):
            if i != r and m[i][c]:
                fac = m[i][c]
                m[i] = [a ^ (mul(fac,b) if field == 8 else b)
                        for a,b in zip(m[i], m[r])]
        r += 1
    return r

def lift(m):
    return [[trace(mul(mul(1<<(i%3),m[i//3][j//3]),1<<(j%3)))
             for j in range(12)] for i in range(12)]

def fwht(a):
    a = a[:]
    h = 1
    while h < len(a):
        for start in range(0,len(a),2*h):
            for j in range(start,start+h):
                l,r = a[j],a[j+h]
                a[j],a[j+h] = l+r,l-r
        h *= 2
    return a

def main():
    start = time.monotonic()
    for a in range(1,8):
        require(mul(a,power(a,6)) == 1, 'Field inverse failed')
        require(trace(mul(a,power(a,6))) == 1, 'Trace pairing check failed')
    basis = [lift(matrix(1<<i)) for i in range(8)]
    coeff = [sum(basis[k][i][j]<<k for k in range(8)) for i,j in PAIR12]
    require(coeff == CERT['coordinate_masks_lex_pairs'], 'Coefficient list differs')
    require(basis == CERT['basis_matrices'], 'Basis matrices differ')
    require(rank([[b[i][j] for i,j in PAIR12] for b in basis],2)==8,
            'Effective coordinate dimension differs from eight')
    hist8,hist2,singular = Counter(),Counter(),[]
    for label in range(256):
        m = matrix(label)
        a,b,c,d,e,f = entries(label)
        pf = mul(a,f)^mul(b,e)^mul(c,d)
        u,v,w,z,s,t,p,q = [(label>>i)&1 for i in range(8)]
        P = u^v^(u&v)^(w&z)
        R = p^q^(p&q)
        Q = (s&t)^s^t^(q&(u^v))^(w&p)^(z&(p^q))
        require(pf == P^mul(2,R)^mul(4,Q^R), 'Pfaffian identity failed')
        r8,r2 = rank(m,8),rank(lift(m),2)
        require(r2 == 3*r8, 'Trace rank formula failed')
        require((pf==0)==(r8<4), 'Pfaffian singularity failed')
        hist8[r8]+=1; hist2[r2]+=1
        if pf == 0: singular.append(label)
    require(singular==EXPECTED_BAD, 'Unexpected singular labels')
    require(hist8=={0:1,2:5,4:250} and hist2=={0:1,6:5,12:250},
            'Unexpected rank histogram')
    table = []
    for x in range(4096):
        y = 0
        for (i,j),c in zip(PAIR12,coeff):
            if ((x>>i)&1) and ((x>>j)&1): y ^= c
        xx = [(x>>(3*i))&7 for i in range(4)]
        ytrace = 0
        for k in range(8):
            z = 0
            for (i,j),c in zip(PAIR4,entries(1<<k)):
                z ^= mul(c,mul(xx[i],xx[j]))
            ytrace |= trace(z)<<k
        require(y==ytrace, 'Binary formula differs from trace construction')
        table.append(y)
    table_hash = hashlib.sha256(bytes(table)).hexdigest()
    require(table_hash=='ae7383fd45347cbcf32eefec5a6750434967dd727fe6751a388f3ba6ff72bce3',
            'Unexpected truth-table byte hash')
    require(table==json.loads((ROOT/'independent/truth-table.json').read_text()),
            'Truth table differs from independent reference')
    spectra,bad = {},[]
    for b in range(256):
        signs = [1-2*((y&b).bit_count()&1) for y in table]
        walsh = fwht(signs)
        counts = dict(sorted(Counter(walsh).items()))
        spectra[str(b)] = {str(k):v for k,v in counts.items()}
        expected = ({0:4095,4096:1} if b==0 else
                    {-512:28,0:4032,512:36} if b in EXPECTED_BAD else
                    {-64:2016,64:2080})
        require(counts==expected, f'Unexpected exact Walsh spectrum at mask {b}')
        if any(w*w != 4096 for w in walsh): bad.append(b)
        for a in [0,1,7,83,1023,4095]:
            raw = sum(signs[x]*(1-2*((x&a).bit_count()&1)) for x in range(4096))
            require(raw==walsh[a], 'FWHT disagrees with a raw Walsh sum')
    require(bad==EXPECTED_BAD, 'Unexpected nonbent component masks')
    reference = json.loads((ROOT/'independent/verification.json').read_text())
    require(spectra==reference['spectra'], 'Spectra differ from independent reference')
    result = {'verified':True,'input_bits':12,'effective_output_bits':8,
              'zero_padding_bits':4,'effective_bad_masks':bad,
              'gf8_rank_histogram':dict(sorted(hist8.items())),
              'binary_rank_histogram':dict(sorted(hist2.items())),
              'nonzero_nonbent_masks':len(bad)*16-1,'nonzero_bent_masks':250*16,
              'truth_table_byte_sha256':table_hash,
              'walsh_coefficients_checked':256*4096,
              'raw_walsh_coefficients_checked':256*6,
              'exact_effective_spectra':spectra}
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results/reproduced.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: all 4096 inputs, 256 effective masks, 1048576 Walsh coefficients.')
    print('PASS: 1536 raw-sum cross-checks; ranks 0:1, 6:5, 12:250.')
    print('PASS: 4000 bent and 95 nonbent nonzero padded masks.')
    print('Truth-table byte SHA-256:', table_hash)
    print(f'Elapsed seconds: {time.monotonic()-start:.2f}')

if __name__=='__main__': main()
