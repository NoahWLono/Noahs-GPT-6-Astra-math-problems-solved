# Reproducing the Lean proof

## Versions and prerequisites

- Official Lean 4.32.2, with `lean` and `lake` on `PATH`
- Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`
- Matching official Mathlib dependency caches already present
- Bash, Python 3, Git, GNU `timeout` and `stdbuf`

`lean-toolchain`, `mathlib-revision.txt` and `mathlib-manifest.json` record the pins. The scripts do not install software or fetch dependencies.

Set `MATHLIB_ROOT` to that Mathlib checkout and, from this folder, run:

```sh
bash build.sh
```

The script verifies the Lean version and Mathlib commit, then checks the eleven modules in dependency order. Each Lean invocation uses one compiler thread, `-M3072`, and a 60-second timeout. It writes generated proof objects, logs and resource JSON into `../build/`. Start with an absent or empty output directory for a fresh-output replay. Only official cached upstream proof objects are reused.

`SOURCE_SHA256SUMS` records the unchanged publication source bytes. `ZariskiExpected.lean` spells out the final concrete specification separately from the proof construction. The generic field result is `ZariskiCylinder.transitive_thirteen`; the original complex-cylinder endpoint is `ZariskiCylinder.complex_original_transitive_thirteen`.

All eleven modules passed a fresh-output replay using these exact portable scripts before publication. The logs and trust boundary are in `../verification/`. This is kernel checking with the official Lean toolchain, not a separate-kernel audit or a full rebuild of Mathlib from source.
