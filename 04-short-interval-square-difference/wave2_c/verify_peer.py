#!/usr/bin/env python3
"""Read-only full-table and witness cross-check of the sibling toy verifier."""
import hashlib
import json
import math
import resource
import sys
from pathlib import Path
from verify_minimax import independent_masks, require

ROOT = Path(__file__).resolve().parent


def main():
    if len(sys.argv) != 1:
        raise SystemExit('This closed peer verifier accepts no arguments.')
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (256*1024*1024, 256*1024*1024))
    peerroot = ROOT.parent/'construction'
    if not peerroot.exists():
        peerroot = ROOT.parent/'wave2_b'
    paths = {'independent': ROOT/'results.json',
             'construction': peerroot/'minimax_results.json',
             'certificate': peerroot/'minimax_certificate.json'}
    own, peer, cert = [json.loads(paths[key].read_text())
                       for key in ('independent', 'construction', 'certificate')]
    f = [row['F'] for row in own['rows']]
    require(peer['F_by_modulus'] == f, 'full F table differs')
    require(cert['columns'] == ['m', 'h', 'unit_n', 'start_s', 'attained_count'],
            'certificate columns')
    require(cert['record_count'] == 16384 and len(cert['witnesses']) == 16384,
            'certificate coverage')
    seen = set()
    direct_bit_checks = 0
    masks = {}
    for m, h, n, s, count in cert['witnesses']:
        require((m, h) not in seen, 'duplicate witness coordinate')
        seen.add((m, h))
        require(1 <= m <= 256 and 1 <= h <= 64 and 0 <= s < m,
                'witness coordinate domain')
        require(0 <= n < m and math.gcd(n, m) == 1, 'witness unit domain')
        if m not in masks:
            masks[m] = independent_masks(m)
        bits = masks[m][n]
        observed = sum((bits >> ((s+j) % m)) & 1 for j in range(h))
        direct_bit_checks += h
        require(observed == count == f[m-1][h-1], 'direct witness count')
        require(own['rows'][m-1]['witnesses'][h-1] == {'n': n, 's': s},
                'lexicographically first witness differs')
    require(len(seen) == 16384, 'full witness coverage')

    tie_coordinates = 0
    for budget in range(1, 257):
        for j in range(64):
            best = min(f[m-1][j] for m in range(1, budget+1))
            ties = [m for m in range(1, budget+1) if f[m-1][j] == best]
            require(peer['G_by_budget'][budget-1][j] == best, 'G budget value')
            require(peer['all_optimal_moduli_by_budget_and_h'][budget-1][j] == ties,
                    'all budget ties')
            tie_coordinates += 1
    for j, item in enumerate(own['optimum_by_length']):
        require(peer['G_256'][j] == item['minimum_F'], 'global minimum')
        require(peer['minimum_budget_attaining_G_256_by_h'][j] == item['minimum_raw_bit_budget'],
                'minimum attaining budget')
        require(peer['all_optimal_moduli_at_budget_256_by_h'][j] == item['all_optimal_moduli'],
                'global optimum ties')
    for row in own['rows']:
        entry = peer['worst_density_by_modulus'][row['m']-1]
        require(entry['max_R'] == row['Rmax'], 'density cardinality')
        require(entry['density'][0] * row['m'] == entry['density'][1] * row['Rmax'],
                'density fraction')
        actual_ties = [n for n, bits in masks[row['m']].items()
                       if bits.bit_count() == row['Rmax']]
        require(entry['all_attaining_n'] == actual_ties, 'all density ties')
    profile_optima = [row['m'] for row in own['rows'] if row['F'] == peer['G_256']]
    require(profile_optima == [144] == peer['pareto_undominated_moduli'],
            'profile Pareto frontier')
    result = {'status': 'PASS', 'full_F_entries_compared': 16384,
              'attaining_witnesses_directly_checked': len(seen),
              'witness_bit_examinations': direct_bit_checks,
              'budget_and_length_all_tie_coordinates': tie_coordinates,
              'all_density_ties_checked': 256,
              'lexicographic_witnesses_match': True,
              'profile_Pareto_frontier': profile_optima,
              'input_sha256': {key: hashlib.sha256(path.read_bytes()).hexdigest()
                               for key, path in paths.items()},
              'limits': 'Finite raw-mask domain only. No external actions or factor search.'}
    (ROOT/'peer_review.json').write_text(json.dumps(result, indent=2, sort_keys=True)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
