"""Link existing pinned cache modules, with one private EulerIdentity output slot."""
from pathlib import Path
import os
mathlib=Path(os.environ['MATHLIB_ROOT'])
output=Path(os.environ['NAKAI_BUILD_DIR'])
cache=mathlib/'.lake/build/lib/lean/Mathlib'
def overlay(src,dst,parts):
    dst.mkdir(parents=True,exist_ok=True)
    for q in src.iterdir():
        if not parts and q.name.startswith("EulerIdentity."):
            continue
        target=dst/q.name
        if parts and q.name==parts[0]:
            overlay(q,target,parts[1:])
        elif not target.exists() and not target.is_symlink():
            target.symlink_to(q,target_is_directory=q.is_dir())
overlay(cache,output/'Mathlib',['RingTheory','MvPolynomial'])
