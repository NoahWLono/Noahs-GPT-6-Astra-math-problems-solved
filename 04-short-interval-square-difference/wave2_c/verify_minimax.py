#!/usr/bin/env python3
"""Closed minimax certificate using difference-of-squares masks and popcounts.

Literal domain only: 1<=m<=256, unit n, all starts, 1<=h<=64.
No factor search, input integers, files used as input, or network operations.
"""
import hashlib
import json
import math
import resource
import sys
import time
from fractions import Fraction
from pathlib import Path

LIMIT_M, LIMIT_H = 256, 64
ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise AssertionError(message)


def rational(value):
    value = Fraction(value)
    return {'numerator': value.numerator, 'denominator': value.denominator}


def independent_masks(m):
    units = [n for n in range(m) if math.gcd(n, m) == 1]
    masks = dict.fromkeys(units, 0)
    unit_set = set(units)
    # Construct by the equation n=a^2-b^2, rather than testing each
    # candidate a against a precomputed square-residue predicate.
    bsquares = {b*b % m for b in range(m)}
    for a in range(m):
        aa, abit = a*a, 1 << a
        for bb in bsquares:
            n = (aa-bb) % m
            if n in unit_set:
                masks[n] |= abit
    if m % 2 == 0:
        halfmask = (1 << (m // 2)) - 1
        for bits in masks.values():
            require(bits & halfmask == bits >> (m // 2), 'even half-period')
    for n, bits in masks.items():
        for a in range(m):
            require((bits >> a) & 1 == (bits >> ((-a) % m)) & 1,
                    'reflection symmetry')
    return masks


def run():
    rows = []
    clips = [(1 << h) - 1 for h in range(1, LIMIT_H + 1)]
    popcount_windows = unit_cases = start_cases = 0
    density_mask_counterexample = None
    for m in range(1, LIMIT_M + 1):
        masks = independent_masks(m)
        rmax = max(bits.bit_count() for bits in masks.values())
        global_f = [0] * LIMIT_H
        witnesses = [None] * LIMIT_H
        density_f = [0] * LIMIT_H
        local_profiles = {}
        for n, bits in masks.items():
            unit_cases += 1
            repeated = 0
            for shift in range(0, m + LIMIT_H - 1, m):
                repeated |= bits << shift
            local_f = [0] * LIMIT_H
            local_s = [0] * LIMIT_H
            for s in range(m):
                start_cases += 1
                window = repeated >> s
                for j, clip in enumerate(clips):
                    value = (window & clip).bit_count()
                    if value > local_f[j]:
                        local_f[j], local_s[j] = value, s
            popcount_windows += m * LIMIT_H
            cardinality = bits.bit_count()
            local_profiles[n] = (cardinality, local_f)
            for j, value in enumerate(local_f):
                if value > global_f[j]:
                    global_f[j] = value
                    witnesses[j] = {'n': n, 's': local_s[j]}
                if cardinality == rmax and value > density_f[j]:
                    density_f[j] = value

        thresholds = []
        for remainder in range(min(m, LIMIT_H + 1)):
            gstar = density_f[remainder-1] if remainder else 0
            q0 = 0
            for cardinality, profile in local_profiles.values():
                if cardinality < rmax:
                    difference = (profile[remainder-1] if remainder else 0) - gstar
                    delta = rmax-cardinality
                    q0 = max(q0, (difference + delta - 1) // delta)
            bound = max(0, min(remainder, rmax-1)-gstar)
            require(q0 <= bound, 'eventual-density threshold bound')
            thresholds.append(q0)
        for j, value in enumerate(global_f):
            require(1 <= value <= j+1, 'window count bounds')
            require(j == 0 or value >= global_f[j-1], 'monotonicity')
            if value > density_f[j] and density_mask_counterexample is None:
                density_mask_counterexample = {
                    'm': m, 'h': j+1, 'F': value,
                    'max_density_only_F': density_f[j], 'Rmax': rmax,
                    'witness': witnesses[j],
                    'witness_R': local_profiles[witnesses[j]['n']][0]}
        rows.append({'m': m, 'unit_count': len(masks), 'Rmax': rmax,
                     'worst_period_density': rational(Fraction(rmax, m)),
                     'F': global_f, 'witnesses': witnesses,
                     'F_restricted_to_max_density_n': density_f,
                     'exact_eventual_max_density_q_thresholds_for_r_0_through_min_mminus1_64': thresholds})

    for row in rows:
        m = row['m']
        for d in range(1, m+1):
            if m % d == 0:
                require(all(x <= y for x, y in zip(row['F'], rows[d-1]['F'])),
                        'divisibility domination')
        if m % 2 == 0 and (m//2) % 2:
            require(row['F'] == rows[m//2-1]['F'], 'twice-odd equivalence')
    for h in range(1, LIMIT_H+1):
        quotient, remainder = divmod(h, 8)
        expected16 = 2*quotient + min(2, (remainder+1)//2)
        require(rows[15]['F'][h-1] == expected16, 'exact F16 formula')
        require(rows[3]['F'][h-1] == (h+1)//2, 'exact F4 formula')
        require(rows[7]['F'][h-1] == (h+1)//2, 'exact F8 formula')
        q9, r9 = divmod(h, 9)
        require(rows[8]['F'][h-1] == max((h+2)//3, 2*q9+min(r9, 2)),
                'exact F9 formula')

    optimum = []
    min_density = min(Fraction(row['Rmax'], row['m']) for row in rows)
    density_moduli = [row['m'] for row in rows
                      if Fraction(row['Rmax'], row['m']) == min_density]
    density_selection_counterexample = None
    for h in range(1, LIMIT_H+1):
        best = min(row['F'][h-1] for row in rows)
        ties = [row['m'] for row in rows if row['F'][h-1] == best]
        optimum.append({'h': h, 'minimum_F': best,
                        'all_optimal_moduli': ties, 'minimum_raw_bit_budget': min(ties)})
        density_best = min(rows[m-1]['F'][h-1] for m in density_moduli)
        if density_best > best and density_selection_counterexample is None:
            density_selection_counterexample = {
                'h': h, 'global_minimum_F': best,
                'all_global_optima': ties,
                'density_optimal_moduli': density_moduli,
                'best_F_among_density_optimal_moduli': density_best}
    require([x['minimum_F'] for x in optimum[:8]] == [1, 1, 2, 2, 2, 2, 2, 2],
            'small-h theorem')
    require([x['minimum_raw_bit_budget'] for x in optimum[:8]] == [1, 4, 3, 4, 9, 9, 16, 16],
            'small-h least-budget refinement')
    return {
        'schema_version': 1,
        'status': 'PASS',
        'method': 'Masks from n=a^2-b^2; repeated integer bitsets and independent window popcounts.',
        'domain': {'moduli': [1, 256], 'lengths': [1, 64],
                   'n': 'all units modulo m', 'starts': 'all residues modulo m',
                   'cost': 'm logical bits, one full uncompressed mask'},
        'coverage': {'moduli': len(rows), 'unit_masks': unit_cases,
                     'unit_start_pairs': start_cases,
                     'exact_window_popcounts': popcount_windows,
                     'F_entries': LIMIT_M * LIMIT_H},
        'rows': rows, 'optimum_by_length': optimum,
        'best_worst_period_density': rational(min_density),
        'all_density_optimal_moduli': density_moduli,
        'counterexample_to_restricting_n_to_max_density_masks': density_mask_counterexample,
        'counterexample_to_selecting_modulus_by_density_alone': density_selection_counterexample,
        'limits': [
            'The payload model deliberately excludes compression, metadata, setup, and temporary storage.',
            'Worst-case residues and starts need not describe a realizable correlated Fermat interval.',
            'Finite count certificate; no factor-recovery or timing-speedup claim.',
            'Novelty unestablished.'
        ]}


def main():
    if len(sys.argv) != 1:
        raise SystemExit('This closed verifier accepts no arguments.')
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (256*1024*1024, 256*1024*1024))
    cpu_start, wall_start = time.process_time(), time.monotonic()
    result = run()
    encoded = (json.dumps(result, indent=2, sort_keys=True)+'\n').encode()
    (ROOT/'results.json').write_bytes(encoded)
    telemetry = {'cpu_seconds': time.process_time()-cpu_start,
                 'wall_seconds': time.monotonic()-wall_start,
                 'cpu_limit_seconds': 120, 'address_space_limit_bytes': 256*1024*1024,
                 'results_sha256': hashlib.sha256(encoded).hexdigest(),
                 'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'telemetry.json').write_text(json.dumps(telemetry, indent=2, sort_keys=True)+'\n')
    print(json.dumps({'status': result['status'], 'coverage': result['coverage'],
                      'density_mask_counterexample': result['counterexample_to_restricting_n_to_max_density_masks'],
                      'density_selection_counterexample': result['counterexample_to_selecting_modulus_by_density_alone'],
                      'telemetry': telemetry}, indent=2))


if __name__ == '__main__':
    main()
