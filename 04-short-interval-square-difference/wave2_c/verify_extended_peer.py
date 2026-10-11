#!/usr/bin/env python3
"""Check extended lower witnesses and the entries needed for optimality.

Does not claim independently recomputed competitor maxima for h>64.
"""
import hashlib
import json
import math
import resource
import sys
from pathlib import Path
from verify_minimax import independent_masks, require

ROOT=Path(__file__).resolve().parent


def main():
    if len(sys.argv)!=1:
        raise SystemExit('This closed peer review accepts no arguments.')
    resource.setrlimit(resource.RLIMIT_CPU,(120,120))
    resource.setrlimit(resource.RLIMIT_AS,(256*1024*1024,256*1024*1024))
    peerroot=ROOT.parent/'construction'
    if not peerroot.exists():
        peerroot=ROOT.parent/'wave2_b'
    paths={'extended_table':peerroot/'minimax_146_results.json',
           'extended_certificate':peerroot/'minimax_146_certificate.json',
           'own_table':ROOT/'results.json', 'own_bridge':ROOT/'optimality_bridge.json'}
    peer,cert,own,bridge=[json.loads(paths[key].read_text()) for key in paths]
    require(len(peer['F_by_modulus'])==256,'modulus rows')
    require(cert['columns']==['m','h','unit_n','start_s','attained_count'],'columns')
    require(cert['record_count']==37376 and len(cert['witnesses'])==37376,'records')
    for row,old in zip(peer['F_by_modulus'],own['rows']):
        require(len(row)==146 and row[:64]==old['F'],'full original table preserved')
    require(peer['F_by_modulus'][143]==bridge['F144_h1_through_146'],'all m144 counts')
    require(peer['G_256']==bridge['F144_h1_through_146'],'claimed optimum profile')
    masks={}
    seen=set()
    bit_checks=0
    for m,h,n,s,count in cert['witnesses']:
        require((m,h) not in seen,'duplicate coordinate')
        seen.add((m,h))
        require(1<=m<=256 and 1<=h<=146 and 0<=n<m and math.gcd(n,m)==1 and 0<=s<m,
                'witness domain')
        if m not in masks:
            masks[m]=independent_masks(m)
        observed=sum((masks[m][n]>>((s+j)%m))&1 for j in range(h))
        bit_checks+=h
        require(observed==count==peer['F_by_modulus'][m-1][h-1],'direct witness')
        require(count>=bridge['F144_h1_through_146'][h-1],'pointwise optimum lower witness')
    result={'status':'PASS','direct_attainment_witnesses_checked':len(seen),
            'direct_witness_bit_checks':bit_checks,
            'exact_competing_F_entries_independently_compared_h1_through_64':16384,
            'exact_F144_entries_independently_compared_h1_through_146':146,
            'all_h1_through_146_pointwise_optimality_lower_witnesses_checked':37376,
            'qualification':'Competitor upper bounds for h65..146 were not independently recomputed; independent averaging certificates suffice for the all-length optimality theorem.',
            'input_sha256':{k:hashlib.sha256(p.read_bytes()).hexdigest() for k,p in paths.items()}}
    (ROOT/'peer_extended_review.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
