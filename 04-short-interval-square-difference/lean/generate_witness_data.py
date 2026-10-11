#!/usr/bin/env python3
"""Produce untrusted finite witness literals; Lean checks their validity.

No arbitrary integer-to-factor interface. This is a fixed-domain data converter.
"""
from pathlib import Path
from math import gcd
import hashlib
import json
import sys

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'wave2_b'

def main():
    if len(sys.argv) != 1:
        raise SystemExit('The fixed witness converter accepts no arguments.')
    cert_data = (SOURCE / 'minimax_146_certificate.json').read_bytes()
    results_data = (SOURCE / 'minimax_146_results.json').read_bytes()
    cert = json.loads(cert_data)
    result = json.loads(results_data)
    assert cert['record_count'] == 256 * 146
    rows = [[(0, 0)] * 146 for _ in range(257)]
    seen = set()
    for m, h, n, s, count in cert['witnesses']:
        assert 1 <= m <= 256 and 1 <= h <= 146
        assert 0 <= n < m and gcd(n, m) == 1 and 0 <= s < m
        assert (m, h) not in seen
        seen.add((m, h))
        rows[m][h - 1] = (n, s)
    lower_rows = [(0, [])]
    for m in range(1, 257):
        n = result['worst_density_by_modulus'][m - 1]['all_attaining_n'][0]
        squares = {b * b % m for b in range(m)}
        mask = [int((a * a - n) % m in squares) for a in range(m)]
        prefix = [0]
        for bit in mask + mask:
            prefix.append(prefix[-1] + bit)
        starts = []
        for r in range(m):
            if m == 144:
                starts.append(0)
            else:
                starts.append(next(s for s in range(m)
                                   if 2 * r <= 21 * (prefix[s+r] - prefix[s])))
        lower_rows.append((n, starts))
    lines = ['/-! Untrusted encoded witness literals. Lean checks every used witness. -/',
             'namespace Astra.Certificates',
             'private def readNat (s : String) : Nat := s.toNat?.getD 0',
             'private def finiteRow (s : String) : Array (Nat × Nat) :=',
             '  ((s.splitOn ",").map fun t => let v := readNat t; (v / 256, v % 256)).toArray',
             'private def lowerRow (s : String) : Nat × Array Nat :=',
             '  let ts := s.splitOn ","',
             '  (readNat (ts.headD "0"), ((ts.drop 1).map readNat).toArray)',
             'def finiteWitnessData : Array (Array (Nat × Nat)) :=',
             '  (#["" ,']
    for m in range(1, 257):
        line = '"' + ','.join(str(256*n+s) for n, s in rows[m]) + '"'
        lines.append(line + (',' if m < 256 else ''))
    lines.extend([']).map finiteRow',
                  'def lowerWitnessData : Array (Nat × Array Nat) :=',
                  '  (#["0",'])
    for m in range(1, 257):
        n, starts = lower_rows[m]
        line = '"' + ','.join(map(str, [n] + starts)) + '"'
        lines.append(line + (',' if m < 256 else ''))
    lines.extend([']).map lowerRow', 'end Astra.Certificates', ''])
    text = '\n'.join(lines)
    (ROOT / 'WitnessData.lean').write_text(text)
    provenance = {
        'meaning': 'Untrusted data only; FiniteChecks.lean checks every needed inequality.',
        'source_certificate_sha256': hashlib.sha256(cert_data).hexdigest(),
        'source_results_sha256': hashlib.sha256(results_data).hexdigest(),
        'finite_witness_count': len(seen),
        'lower_remainder_witness_count_including_skipped_144': sum(range(1, 257)),
        'generated_source_sha256': hashlib.sha256(text.encode()).hexdigest(),
    }
    (ROOT / 'witness_data_provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print(json.dumps(provenance))

if __name__ == '__main__':
    main()
