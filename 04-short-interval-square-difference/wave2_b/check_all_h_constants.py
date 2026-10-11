#!/usr/bin/env python3
"""Separate fixed-domain derivation of the proposed all-length constants."""
from fractions import Fraction
from math import gcd
from pathlib import Path
import hashlib
import json
import resource
import sys
import time


def main():
    if len(sys.argv) != 1:
        raise SystemExit('Closed constants check accepts no arguments.')
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024, 256 * 1024 * 1024))
    started = time.process_time()
    density_rows = []
    predicate_count = 0
    for m in range(1, 257):
        squares = {b * b % m for b in range(m)}
        best_R = -1
        witnesses = []
        for n in range(m):
            if gcd(n, m) != 1:
                continue
            cardinality = sum((a * a - n) % m in squares for a in range(m))
            predicate_count += m
            if cardinality > best_R:
                best_R, witnesses = cardinality, [n]
            elif cardinality == best_R:
                witnesses.append(n)
        fraction = Fraction(best_R, m)
        density_rows.append({'m': m, 'R': best_R,
                             'density': [fraction.numerator, fraction.denominator],
                             'all_attaining_n': witnesses})
    competitor_density = min(Fraction(row['R'], row['m'])
                             for row in density_rows if row['m'] != 144)
    competitor_moduli = [row['m'] for row in density_rows
                        if row['m'] != 144 and Fraction(row['R'], row['m']) == competitor_density]
    base_density = Fraction(density_rows[143]['R'], 144)

    m = 144
    squares = {b * b % m for b in range(m)}
    E12 = 0
    E_witnesses = []
    discrepancy_cases = 0
    for n in range(m):
        if gcd(n, m) != 1:
            continue
        mask = [int((a * a - n) % m in squares) for a in range(m)]
        prefix = [0]
        for keep in mask + mask:
            prefix.append(prefix[-1] + keep)
        for s in range(m):
            for r in range(m):
                count = prefix[s + r] - prefix[s]
                scaled = 12 * count - r
                discrepancy_cases += 1
                if scaled > E12:
                    E12, E_witnesses = scaled, [[n, s, r, count]]
                elif scaled == E12:
                    E_witnesses.append([n, s, r, count])
    E = Fraction(E12, 12)
    gap = competitor_density - base_density
    threshold = E / gap
    first_integer = (threshold.numerator + threshold.denominator - 1) // threshold.denominator
    require = lambda condition: condition or (_ for _ in ()).throw(AssertionError('constant mismatch'))
    require(base_density == Fraction(1, 12))
    require(E == Fraction(7, 4))
    require(competitor_density == Fraction(2, 21))
    require(gap == Fraction(1, 84))
    require(first_integer == 147)
    result = {
        'closed_domain': 'all m=1..256; all unit n; discrepancy all s,r modulo144',
        'independent_density_predicate_evaluations': predicate_count,
        'density_by_modulus': density_rows,
        'm144_worst_density': [base_density.numerator, base_density.denominator],
        'minimum_competitor_worst_density': [competitor_density.numerator, competitor_density.denominator],
        'all_moduli_attaining_competitor_minimum': competitor_moduli,
        'density_gap': [gap.numerator, gap.denominator],
        'E_definition': 'max over unit n, s, and 0<=r<144 of window_count-r/12',
        'E': [E.numerator, E.denominator],
        'E_witness_columns': ['n', 's', 'r', 'window_count'],
        'all_E_attaining_witnesses': E_witnesses,
        'discrepancy_cases': discrepancy_cases,
        'threshold_E_over_gap': [threshold.numerator, threshold.denominator],
        'all_h_dominance_from': first_integer,
        'argument': 'F144(h)<=h/12+7/4 and Fm(h)>=2h/21 for every m!=144; therefore F144(h)<=Fm(h) for every integer h>=147.',
        'remaining_finite_requirement': 'Certify h=1..146 separately before concluding all-length optimality.',
        'failures': 0,
    }
    encoded = (json.dumps(result, sort_keys=True, separators=(',', ':')) + '\n').encode()
    Path(__file__).with_name('all_h_constants.json').write_bytes(encoded)
    print(json.dumps({'E': result['E'], 'competitor_density': result['minimum_competitor_worst_density'],
                      'competitor_moduli': competitor_moduli, 'gap': result['density_gap'],
                      'threshold': first_integer, 'discrepancy_cases': discrepancy_cases,
                      'E_witness_count': len(E_witnesses), 'first_E_witness': E_witnesses[0],
                      'density_predicates': predicate_count, 'cpu_seconds': time.process_time() - started,
                      'result_sha256': hashlib.sha256(encoded).hexdigest()}, sort_keys=True))


if __name__ == '__main__':
    main()
