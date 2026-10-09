#!/usr/bin/env python3
"""Finalize the reproducible source archive only after verified Lean status.

This is a packaging guard, not a checker of proof correctness. The caller must
first verify the exact Lean sources, clean build and reported axiom boundary.
"""
from pathlib import Path
import hashlib, json, zipfile
ROOT=Path(__file__).resolve().parent
STATUS=json.loads((ROOT/'certificate_status.json').read_text())
if not STATUS.get('verified') or not STATUS.get('uniform_verified'):
    raise SystemExit('Refusing final archive: complete concrete or uniform Lean certification is pending.')
for key in ['scope','theorems','command','report_paragraphs']:
    if not STATUS.get(key): raise SystemExit('Missing certification metadata: '+key)
required=STATUS.get('required_lean_files',[])
if not required: raise SystemExit('No certified Lean source/build/axiom files identified.')
for name in required:
    p=ROOT/name
    if not p.is_file() or not p.stat().st_size: raise SystemExit('Missing required file: '+name)
PDF=ROOT.parent/'output/pdf/gpt6_astra_extremal_quadratic_family.pdf'
if not PDF.is_file(): raise SystemExit('Final PDF missing.')
files=sorted(p for p in ROOT.rglob('*') if p.is_file() and p.name!='SHA256SUMS'
             and p.suffix not in ['.olean','.ilean','.pyc'] and '__pycache__' not in p.parts)
lines=[hashlib.sha256(p.read_bytes()).hexdigest()+'  '+str(p.relative_to(ROOT)) for p in files]
(ROOT/'SHA256SUMS').write_text('\n'.join(lines)+'\n')
files.append(ROOT/'SHA256SUMS')
OUT=ROOT.parent/'output/gpt6_astra_extremal_quadratic_family_source.zip'
with zipfile.ZipFile(OUT,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for p in files:
        info=zipfile.ZipInfo('gpt6_astra_extremal_quadratic_family/source/'+str(p.relative_to(ROOT)),(2026,10,9,0,0,0))
        info.compress_type=zipfile.ZIP_DEFLATED
        z.writestr(info,p.read_bytes())
    info=zipfile.ZipInfo('gpt6_astra_extremal_quadratic_family/output/pdf/'+PDF.name,(2026,10,9,0,0,0))
    info.compress_type=zipfile.ZIP_DEFLATED;z.writestr(info,PDF.read_bytes())
print(str(OUT));print('SHA-256:',hashlib.sha256(OUT.read_bytes()).hexdigest())
