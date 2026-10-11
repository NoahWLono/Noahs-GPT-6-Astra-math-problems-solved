#!/usr/bin/env python3
"""Authorized h<=146 extension; original h<=64 artifacts are preserved."""
from math import gcd
from pathlib import Path
import hashlib
import json
import platform
import resource
import sys
import time

B = 256
H = 146
PROTOCOL_SHA256 = 'efd4009b56882fead3704b23c5b9fe714172bc670f0fe82bd376f452cd866f7d'
EXTENSION_SHA256 = 'd16ca503168351b02286570eb003b2a2b1e748419e1f6045d8d13d76087ceacb'
ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def fixture_counts(m, n, h):
    """Bounded hand-fixture inspector; never accepts an external N."""
    if not (isinstance(m, int) and isinstance(n, int) and isinstance(h, int)
            and 1 <= m <= B and 0 <= n < m and gcd(n, m) == 1 and 1 <= h <= H):
        raise ValueError('only fixed-domain modulus/residue/length indices are accepted')
    squares = {b * b % m for b in range(m)}
    return [sum(((s + j) * (s + j) - n) % m in squares for j in range(h))
            for s in range(m)]


def canonical_bytes(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n').encode('utf-8')


def closed_experiment():
    profiles, density_records, witness_rows, setup_rows = [], [], [], []
    total_masks = total_mask_entries = total_cycle_entries = 0
    for m in range(1, B + 1):
        residues = range(m)
        squares = bytearray(m)
        for b in residues:
            squares[b * b % m] = 1
        best = [-1] * H
        witnesses = [None] * H
        density_R = -1
        density_ns = []
        units = 0
        for n in residues:
            if gcd(n, m) != 1:
                continue
            units += 1
            mask = [squares[(a * a - n) % m] for a in residues]
            R = sum(mask)
            if R > density_R:
                density_R, density_ns = R, [n]
            elif R == density_R:
                density_ns.append(n)
            cycle_length = m + H - 1
            expanded = (mask * ((cycle_length + m - 1) // m))[:cycle_length]
            windows = [0] * m
            for offset in range(H):
                incumbent = best[offset]
                attaining_start = -1
                for s in residues:
                    count = windows[s] + expanded[s + offset]
                    windows[s] = count
                    if count > incumbent:
                        incumbent = count
                        attaining_start = s
                if attaining_start >= 0:
                    best[offset] = incumbent
                    witnesses[offset] = (n, attaining_start)
        require(units > 0 and all(w is not None for w in witnesses), 'complete unit/start scan')
        profiles.append(best)
        divisor = gcd(density_R, m)
        density_records.append({'m': m, 'max_R': density_R,
                                'density': [density_R // divisor, m // divisor],
                                'all_attaining_n': density_ns})
        for h, ((n, s), count) in enumerate(zip(witnesses, best), 1):
            direct = sum(squares[((s + j) * (s + j) - n) % m] for j in range(h))
            require(direct == count, f'direct witness check m={m}, h={h}')
            witness_rows.append([m, h, n, s, count])
        entries = units * m
        total_masks += units
        total_mask_entries += entries
        total_cycle_entries += units * (m + H - 1)
        setup_rows.append({'m': m, 'unit_n': units, 'gcd_checks': m,
                           'square_generation_iterations': m,
                           'square_residue_count': sum(squares),
                           'mask_predicate_evaluations': entries,
                           'mask_cardinality_addends': entries,
                           'expanded_cycle_entries': units * (m + H - 1),
                           'incremental_window_additions': H * entries,
                           'incumbent_comparisons': H * entries})

    require(profiles[0] == list(range(1, H + 1)), 'm=1 convention')
    divisibility_comparisons = factor_two_comparisons = exact_period_comparisons = 0
    for m, row in enumerate(profiles, 1):
        R = density_records[m - 1]['max_R']
        require(row[0] == 1, 'single-position maximum')
        require(row[1] == (1 if m % 4 == 0 else 2), 'exact h=2 theorem')
        for h, count in enumerate(row, 1):
            require(1 <= count <= h, 'count range')
            require(count >= (h * R + m - 1) // m, 'density averaging lower bound')
            if h > 1:
                require(row[h - 2] <= count <= row[h - 2] + 1, 'monotone one-step bound')
            if h % m == 0:
                require(count == h // m * R, 'exact full-period value')
                exact_period_comparisons += 1
        for d in range(1, m):
            if m % d == 0:
                require(all(x <= y for x, y in zip(row, profiles[d - 1])), 'divisibility dominance')
                divisibility_comparisons += H
        if m % 2 == 0 and (m // 2) % 2 == 1:
            require(row == profiles[m // 2 - 1], 'redundant factor two')
            factor_two_comparisons += H
    require(profiles[15][:8] == [1, 1, 2, 2, 2, 2, 2, 2], 'mod16 analytic profile')

    budget_profiles = []
    budget_ties = []
    incumbents = [H + 1] * H
    tied_moduli = [[] for _ in range(H)]
    for budget, row in enumerate(profiles, 1):
        for offset, count in enumerate(row):
            if count < incumbents[offset]:
                incumbents[offset] = count
                tied_moduli[offset] = [budget]
            elif count == incumbents[offset]:
                tied_moduli[offset].append(budget)
        budget_profiles.append(list(incumbents))
        budget_ties.append([list(moduli) for moduli in tied_moduli])
        if budget >= 16:
            require(incumbents[:8] == [1, 1, 2, 2, 2, 2, 2, 2], 'analytic optimum for budgets >=16')
    minimum_budgets = [next(m for m, row in enumerate(profiles, 1) if row[i] == incumbents[i])
                       for i in range(H)]
    for budget, (row, all_ties) in enumerate(zip(budget_profiles, budget_ties), 1):
        for i in range(H):
            independently_tied = [m for m in range(1, budget + 1) if profiles[m - 1][i] == row[i]]
            require(all_ties[i] == independently_tied, 'all optimum ties retained')

    profile_groups = {}
    for m, row in enumerate(profiles, 1):
        profile_groups.setdefault(tuple(row), []).append(m)
    pareto_moduli = []
    for m, row in enumerate(profiles, 1):
        dominated = any(other != row and all(a <= b for a, b in zip(other, row))
                        for other in profiles)
        if not dominated:
            pareto_moduli.append(m)
    pareto_groups = [{'moduli': moduli, 'profile': list(profile)}
                     for profile, moduli in profile_groups.items()
                     if moduli[0] in pareto_moduli]

    require(density_records[3]['density'] == [1, 2], 'm4 density hand case')
    require(density_records[8]['density'] == [1, 3], 'm9 density hand case')
    require(profiles[3][1] == 1 and profiles[8][1] == 2, 'density-order reversal')
    require(fixture_counts(9, 7, 2)[4] == 2, 'density reversal witness')
    profile_hash = hashlib.sha256(canonical_bytes(profiles)).hexdigest()
    certificate = {
        'schema_version': 1, 'protocol_sha256': PROTOCOL_SHA256, 'extension_scope_sha256': EXTENSION_SHA256,
        'domain': {'moduli': [1, B], 'lengths': [1, H]},
        'F_profiles_sha256': profile_hash,
        'columns': ['m', 'h', 'unit_n', 'start_s', 'attained_count'],
        'record_count': len(witness_rows),
        'witnesses': witness_rows,
        'witness_selection': 'smallest n then smallest start among attaining pairs',
        'meaning': 'Attainment lower bounds; exhaustive upper checks remain necessary.',
    }
    certificate_data = canonical_bytes(certificate)
    results = {
        'schema_version': 1, 'protocol_sha256': PROTOCOL_SHA256, 'extension_scope_sha256': EXTENSION_SHA256,
        'domain': {'moduli': [1, B], 'lengths': [1, H],
                   'n': 'all 0<=n<m with gcd(n,m)=1', 'start': 'all 0<=s<m',
                   'm1': 'one unit class n=0; mask [1]'},
        'representation': 'one raw full-period m-bit logical mask; metadata and transient verifier memory excluded',
        'matrix_indexing': 'outer index m-1 or budget-1; inner index h-1',
        'F_by_modulus': profiles,
        'F_profiles_sha256': profile_hash,
        'worst_density_by_modulus': density_records,
        'G_by_budget': budget_profiles,
        'all_optimal_moduli_by_budget_and_h': budget_ties,
        'G_256': incumbents,
        'all_optimal_moduli_at_budget_256_by_h': budget_ties[-1],
        'minimum_budget_attaining_G_256_by_h': minimum_budgets,
        'pareto_definition': 'F-profile only: another profile is <= in all 146 coordinates and < in at least one; equal-profile modulus ties are retained; raw-budget cost is not another Pareto coordinate',
        'pareto_undominated_moduli': pareto_moduli,
        'pareto_equal_profile_groups': pareto_groups,
        'distinct_F_profile_count': len(profile_groups),
        'density_order_counterexample': {
            'h': 2, 'lower_density_m': 9, 'lower_density': [1, 3], 'its_F': 2,
            'higher_density_m': 4, 'higher_density': [1, 2], 'its_F': 1,
            'm9_attaining_witness': {'n': 7, 's': 4, 'positions': [4, 5]}},
        'setup_by_modulus': setup_rows,
        'coverage': {
            'unit_n_masks': total_masks,
            'mask_predicate_evaluations': total_mask_entries,
            'square_generation_iterations': B * (B + 1) // 2,
            'unit_gcd_checks': B * (B + 1) // 2,
            'mask_cardinality_addends': total_mask_entries,
            'expanded_cycle_entries': total_cycle_entries,
            'all_length_all_start_indicator_additions': H * total_mask_entries,
            'incumbent_comparisons': H * total_mask_entries,
            'attaining_witness_records': len(witness_rows),
            'independent_direct_witness_bit_examinations': B * H * (H + 1) // 2,
            'density_counterexample_fixture_bit_examinations': 18,
            'divisibility_profile_coordinate_comparisons': divisibility_comparisons,
            'factor_two_profile_coordinate_comparisons': factor_two_comparisons,
            'exact_full_period_checks': exact_period_comparisons,
            'all_tie_coordinate_checks': B * H,
            'short_window_theorem_coordinate_checks': (B - 15) * 8,
            'failures': 0, 'partial': False},
        'certificate_sha256': hashlib.sha256(certificate_data).hexdigest(),
        'limitations': [
            'Counts are for arbitrary unit residues and cyclic starts, not correlated Fermat-search intervals.',
            'No factorization runtime, recovery method, or asymptotic speedup is measured.',
            'The 256-bit budget is representation-specific; compression optimality is not claimed.',
            'The exact finite table and elementary consequences have unestablished novelty.',
        ],
    }
    return results, certificate_data


def main():
    if len(sys.argv) != 1:
        raise SystemExit('The closed finite experiment accepts no arguments or external modulus.')
    resource.setrlimit(resource.RLIMIT_CPU, (120, 120))
    resource.setrlimit(resource.RLIMIT_AS, (256 * 1024 * 1024, 256 * 1024 * 1024))
    wall_start, cpu_start = time.monotonic(), time.process_time()
    initial_maxrss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    results, certificate_data = closed_experiment()
    result_data = canonical_bytes(results)
    (ROOT / 'minimax_146_certificate.json').write_bytes(certificate_data)
    (ROOT / 'minimax_146_results.json').write_bytes(result_data)
    memory = {}
    for line in Path('/proc/self/status').read_text().splitlines():
        if line.startswith(('VmPeak:', 'VmSize:', 'VmHWM:', 'VmRSS:')):
            label, value, unit = line.split()
            require(unit == 'kB', 'proc memory units')
            memory[label.rstrip(':') + '_kib'] = int(value)
    require(memory['VmHWM_kib'] < 256 * 1024, 'process-memory target')
    telemetry = {
        'python': sys.version, 'platform': platform.platform(),
        'cpu_cap_seconds': 120, 'address_space_cap_bytes': 256 * 1024 * 1024,
        'process_cpu_seconds': time.process_time() - cpu_start,
        'wall_seconds': time.monotonic() - wall_start,
        'proc_self_status_memory': memory,
        'rusage_maxrss_kib_at_start': initial_maxrss,
        'rusage_maxrss_kib_at_end': resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
        'rusage_note': 'May include a pre-exec launcher peak; proc VmHWM describes this Python image.',
        'protocol_sha256': PROTOCOL_SHA256, 'extension_scope_sha256': EXTENSION_SHA256,
        'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'results_sha256': hashlib.sha256(result_data).hexdigest(),
        'certificate_sha256': hashlib.sha256(certificate_data).hexdigest(),
        'telemetry_is_variable_and_separate_from_deterministic_results': True,
    }
    (ROOT / 'minimax_146_environment.json').write_bytes(canonical_bytes(telemetry))
    print(json.dumps({'status': 'PASS', 'coverage': results['coverage'],
                      'results_sha256': telemetry['results_sha256'],
                      'certificate_sha256': telemetry['certificate_sha256'],
                      'CPU_seconds': telemetry['process_cpu_seconds'],
                      'VmHWM_kib': memory['VmHWM_kib']}, sort_keys=True))


if __name__ == '__main__':
    main()
