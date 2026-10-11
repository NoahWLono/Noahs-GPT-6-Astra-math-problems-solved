# Reproducing the Lean checks

Lean: `leanprover/lean4:v4.32.2`.
Mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c`.
The exact transitive dependency revisions from that Mathlib checkout are preserved in dependency-manifest.mathlib.json; their checked-out revisions matched the manifest during verification.

Provision the pinned compiler and compiled dependencies before running either script. The verified run reused pinned upstream objects and rebuilt every local module into a fresh directory. It did not download dependencies or rebuild Mathlib wholesale. A clean online dependency-provisioning run was not exercised.

With an existing compatible package cache, set:

```sh
export LEAN_BIN="$(command -v lean)"
export CACHE_PACKAGES="$PWD/.lake/packages"
# Set EXTRA_LEAN_PATH only if additional pinned upstream objects are in a separate overlay.
export LEAN_MEMORY_MB=3500
bash verify-cached.sh
```

Run from this lean directory and adapt CACHE_PACKAGES to the already-provisioned cache. The script checks the exact compiler version and source hashes, then places newly rebuilt local objects before the optional dependency overlay. It performs no network requests or installation. The alternative verify.sh uses an already-provisioned local Lake environment; that alternative was not the audited command.

The audited process additionally had a 3,879,000 KiB process-group RSS ceiling and a 450,000 KiB available-memory floor. CLEAN_BUILD_RECORD.json records the successful outcome and resource measurements. It uses portable command placeholders; no execution-machine paths are distributed.

CLEAN_AXIOM_AUDIT.json links source and successful per-module log hashes to printed transitive declaration closures. INDEPENDENT_REPLAY_MANIFEST.json links separately rerun endpoint source/log hashes. These reruns used the same trusted compiler/dependency environment, not external expert peer review. Only propext, Classical.choice and Quot.sound are permitted in the reported closures.

SOURCE_SHA256SUMS covers Lean source files; ../SHA256SUMS covers the entire curated package (run its check from the package root). No compiled objects or dependency caches are bundled.
