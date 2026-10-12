# Original scoped irreducibility Lean package

The exact root is `PillaiScoped.irreducible_composition_of_prime_valuation_bounds` in `Proofs/ScopedPillaiIrreducibility.lean`. It proves irreducibility of `((X^q - C(A))^p + C(k))` in `Q[X]` for primes `5 <= p < q`, integers `k, A`, `1 < |k|`, and `padicValInt ell k < p` for every prime `ell` dividing `k`.

## Contents and pins

- `Proofs/`: 51 unchanged production proof modules and the unchanged declaration-audit module.
- `SOURCE_SHA256SUMS`: 121 original source hashes, covering 52 local sources and 69 unchanged upstream Mathlib source copies.
- `source-manifest.json`: local module names, relative source paths, source hashes, recorded object hashes, direct imports, and dependency order. Machine-specific source origins and execution records have been omitted.
- `upstream-source-hashes.json`: module names, package-relative source paths and hashes for the 2,979 imported third-party source files at the pinned revisions.
- `upstream-mathlib-sources/`: the 69 pinned source copies and original Apache 2.0 license. They are unchanged upstream sources, not patches or extra axioms.
- `build-order.txt`, `direct-upstream-imports.txt`, and `expected-roots.json`: local build order, required upstream imports, and the 41 audited declarations.
- `lakefile.toml`, `lake-manifest.json`, and `lean-toolchain`: unchanged pinned configuration.

Lean is `leanprover/lean4:v4.32.2`, commit `f3b06c705e6c85f5314019d5d3baab0fec5b580c`. Mathlib is pinned to `905b95818eb32af7874a58b427f50c1711a5e96c`. The eight transitive package revisions are locked in `lake-manifest.json`. Do not run an unpinned dependency update.

The sequential `scripts/build.py` is unchanged. The two read-only verification scripts were adapted to use the public relative-path manifests. Their source-integrity and import-order preflight passed after adaptation. This packaging change did not modify any Lean source and was not a new Lean/checker run.

## Portable reproduction

Requirements: a POSIX environment, Git, Python 3.10 or newer, the official pinned Lean toolchain (normally through Elan), network access to the official package sources/cache, and sufficient disk and RAM for Mathlib. Run from this directory:

```sh
python3 scripts/verify_sources.py
lake exe cache get
python3 scripts/verify_dependencies.py
lake env python3 -c 'import os; print(os.pathsep.join(p for p in os.environ["LEAN_PATH"].split(os.pathsep) if os.path.isdir(p)))' > dependency-path.txt
LEAN_BIN="$(lake env which lean)"
python3 scripts/build.py --lean "$LEAN_BIN" \
  --dependency-path-file dependency-path.txt --output fresh-build \
  --module-memory ActualPadicSplit=3300
```

The supplied lockfile fixes the dependency revisions. `verify_dependencies.py` checks the installed revisions and all 2,979 recorded upstream source hashes. The path capture omits nonexistent Lake build directories. The local builder rejects dependency search roots containing prebuilt objects for any packaged local module, requires a nonexistent output directory, and builds all local sources sequentially.

It writes new objects to `fresh-build/objects`, logs to `fresh-build/logs`, and a machine-readable result to `fresh-build/build-result.json`. Its 41 recursive audits reject nonstandard axioms. Reported historical-object byte comparisons are additional correspondence information; compilation context can affect object bytes. A fresh source build is not itself a new independent export/replay check.

The builder uses a 3,200 MB helper limit, an explicit 3,300 MB exception for `ActualPadicSplit`, and 3,500 MB for the final union/audit modules. It uses one thread, samples Linux process-group RSS, and stops below 2 GiB free disk or 1 GiB available RAM, or above 3,879,000 KiB sampled RSS. Dependency setup can require additional resources.

## If the official cache is unavailable

Keep the same lockfile and build the required upstream imports in their normal package directories:

```sh
lake env true
python3 scripts/verify_dependencies.py
while IFS= read -r module; do
  lake build "+${module}:olean" || exit 1
done < direct-upstream-imports.txt
```

Then capture the dependency path and run the same clean-local build above. Upstream builds can be expensive and may schedule their own parallel jobs; the local builder's strict process limits do not govern dependency setup.

Do not prepend `upstream-mathlib-sources/` or a partial Mathlib object tree to `LEAN_PATH`. Lean selects the first matching package directory and may not fall back module by module. Use a complete pinned upstream namespace.

## Assurance limits

See [the public verification report](../../VERIFICATION.md) for the completed source rebuild, byte-identical export correspondence, independent checking and their limits. A fresh-network installation has not been independently tested, and this publication adaptation has not undergone a new complete Lean build. No compiled objects, dependency checkout, historical-machine staging helper, or raw execution records are included. No new project-wide license is assigned to the research sources.
