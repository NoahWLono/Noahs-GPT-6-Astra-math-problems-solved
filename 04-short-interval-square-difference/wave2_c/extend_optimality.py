#!/usr/bin/env python3
"""Closed all-length optimality bridge; does not recompute all exact F entries.

Checks the proposed analytic F_144 envelope directly through h=146.
For competitors and h=65..146, uses exact density lower bounds, falling
back to an explicit lower-bound witness only if the average is insufficient.
"""
import hashlib
import json
import resource
import sys
import time
from fractions import Fraction
from pathlib import Path
from verify_minimax import independent_masks, require, rational

ROOT = Path(__file__).resolve().parent


def envelope(h):
    q, r = divmod(h, 24)
    b = 2*q + (0 if r == 0 else 1 if r <= 6 else 2)
    q, r = divmod(h, 72)
    k = 0 if r == 0 else 1 if r <= 2 else 2 if r <= 18 else 3 if r <= 26 else 4
    return max(b, 4*q+k)


def main():
    if len(sys.argv) != 1:
        raise SystemExit('This closed optimality bridge accepts no arguments.')
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (256*1024*1024, 256*1024*1024))
    start = time.process_time()
    original_path = ROOT/'results.json'
    original = json.loads(original_path.read_text())
    masks144 = independent_masks(144)
    actual = [0]*146
    witnesses = [None]*146
    popcounts = 0
    for n, bits in masks144.items():
        repeated = bits | (bits << 144) | (bits << 288)
        for s in range(144):
            window = repeated >> s
            for j in range(146):
                count = (window & ((1 << (j+1))-1)).bit_count()
                popcounts += 1
                if count > actual[j]:
                    actual[j] = count
                    witnesses[j] = {'n': n, 's': s}
    require(actual == [envelope(h) for h in range(1,147)], 'analytic envelope replay')
    require(actual[:64] == original['rows'][143]['F'], 'original F144 preserved')
    e = max([Fraction(0)] + [Fraction(actual[h-1])-Fraction(h,12) for h in range(1,144)])
    require(e == Fraction(7,4), 'E144 constant')
    density_rows = []
    average_discharged = 0
    explicit = []
    competitors = []
    for row in original['rows']:
        m, rmax = row['m'], row['Rmax']
        if m == 144:
            continue
        masks = independent_masks(m)
        require(max(bits.bit_count() for bits in masks.values()) == rmax, 'density replay')
        nmax = next(n for n, bits in masks.items() if bits.bit_count() == rmax)
        density_rows.append({'m': m, 'Rmax': rmax, 'attaining_n': nmax})
        competitors.append(Fraction(rmax,m))
        for h in range(65,147):
            target = actual[h-1]
            lower = (h*rmax+m-1)//m
            if lower >= target:
                average_discharged += 1
                continue
            found = None
            for n, bits in masks.items():
                repeated = 0
                for shift in range(0, m+h-1, m):
                    repeated |= bits << shift
                for s in range(m):
                    count = ((repeated >> s) & ((1 << h)-1)).bit_count()
                    if count >= target:
                        found = {'m':m,'h':h,'n':n,'s':s,'count':count,'target':target}
                        break
                if found:
                    break
            require(found is not None, 'competitor has no sufficient lower witness')
            explicit.append(found)
    require(min(competitors) == Fraction(2,21), 'next density constant')
    gap = min(competitors)-Fraction(1,12)
    require(gap == Fraction(1,84) and Fraction(147)*gap == e, 'tail threshold')
    result = {
        'status':'PASS',
        'purpose':'Independent optimality bridge, not an exact competing-F table beyond h64.',
        'input_results_sha256':hashlib.sha256(original_path.read_bytes()).hexdigest(),
        'F144_h1_through_146':actual,
        'F144_attaining_witnesses':witnesses,
        'F144_direct_popcounts':popcounts,
        'E144':rational(e), 'next_worst_density':rational(min(competitors)),
        'density_gap':rational(gap), 'analytic_tail_begins_at_h':147,
        'density_lower_bound_discharged_cells_h65_through_146':average_discharged,
        'explicit_lower_bound_witnesses_h65_through_146':explicit,
        'total_competitor_cells_h65_through_146':255*82,
        'density_attainment_certificate':density_rows,
        'theorem_scope':'Every integer h>=1, every integer modulus1<=m<=256; raw m-bit table model.',
        'proof_dependency':'The self-contained CRT envelope proof in review.txt certifies the infinite tail.',
        'claim':'F144(h)<=Fm(h) for every permitted m and every positive h.',
        'novelty':'Unestablished; finite certificate plus elementary analytic proof.'}
    encoded=(json.dumps(result,indent=2,sort_keys=True)+'\n').encode()
    (ROOT/'optimality_bridge.json').write_bytes(encoded)
    telemetry={'cpu_seconds':time.process_time()-start,
               'results_sha256':hashlib.sha256(encoded).hexdigest(),
               'cpu_limit_seconds':120,'address_space_limit_bytes':256*1024*1024}
    (ROOT/'bridge_telemetry.json').write_text(json.dumps(telemetry,indent=2,sort_keys=True)+'\n')
    print(json.dumps({key:result[key] for key in
                      ('status','F144_direct_popcounts','E144','next_worst_density',
                       'density_lower_bound_discharged_cells_h65_through_146',
                       'explicit_lower_bound_witnesses_h65_through_146')},indent=2))
    print(json.dumps(telemetry))


if __name__ == '__main__':
    main()
