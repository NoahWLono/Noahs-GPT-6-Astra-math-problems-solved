# Source-only reproduction

## Dependencies

Use Linux, Python 3, and Lean `leanprover/lean4:v4.19.0` (release commit `6caaee842e94`). Obtain the official Lean release and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, including its pinned Lake dependencies. The audit reused the matching toolchain and mathlib dependency binaries; it did not bootstrap Lean or mathlib from source. No project proof binaries are distributed here.

Arrange a dependency directory as follows, and set LEAN_RESEARCH to its absolute path:

```
$LEAN_RESEARCH/lean-4.19.0-linux/bin/lean
$LEAN_RESEARCH/lean-4.19.0-linux/bin/lake
$LEAN_RESEARCH/mathlib4/lake-manifest.json
$LEAN_RESEARCH/mathlib4/.lake/...
```

Verify mathlib's commit with `git -C "$LEAN_RESEARCH/mathlib4" rev-parse HEAD` and the compiler with `"$LEAN_RESEARCH/lean-4.19.0-linux/bin/lean" --version`. In mathlib's directory, `lake env printenv LEAN_PATH` must resolve its matching dependencies.

## Clean project rebuild and exhaustive axiom audit

From this package root:

```
(cd lean && sha256sum -c SOURCE-SHA256SUMS-v2)
mkdir -p reproduction/source reproduction/logs
cp lean/*.lean lean/modules-v2.txt reproduction/source/
cp reproduction/AuditAxioms.lean reproduction/source/
export LEAN_RESEARCH=/absolute/path/to/lean-research
python3 reproduction/rebuild.py
```

Use a fresh reproduction/source directory, with no `.olean` files from any earlier project build. The runner compiles all 67 modules in dependency order, followed by AuditAxioms. It audits every theorem defined in those modules, including private/generated theorem declarations, and rejects dependencies beyond propext, Classical.choice and Quot.sound. It uses one worker, a shared dependency-directory lock, 120 seconds per module, and a 2,900,000 KiB resident-memory cap with termination escalation.

The distributed runner is the independently used runner with only its dependency root made explicit through LEAN_RESEARCH and log-directory creation added. It generates environment.json, results.json, logs and proof binaries locally. Its source inputs remain the frozen manifest files. The original frozen check.sh and build-all-v2.sh are also retained in lean/; those use the original repository-relative dependency layout, so the runner above is the portable entry point.

REPORT.md, module-metrics.tsv and results.json record the completed independent audit before redistribution. Re-running overwrites local metrics/logs; keep a separate copy if comparing. Audit code is an inspection tool, not an additional assumed axiom. The independent build covered 862 theorem declarations and observed a peak 1,639,044 KiB RSS. These timings are evidence from one environment, not performance promises.

## Paper

The reviewed PDF is paper/short-private-pools.pdf. Run `bash paper/build.sh` with a standard pdfLaTeX installation and the preamble's packages to reproduce its contents. Two passes resolve references. PDF metadata and toolchain/font versions can change byte hashes; the reviewed source hash is the stable content reference.

## Distributed evidence

`audit-logs/` preserves all independent module logs and the exhaustive 862-declaration axiom listing. Only the original absolute filesystem prefix was removed from compiler warning locations; theorem text, exit codes, timings and memory measurements are unchanged. `build.log` and the hash-verification logs are included. The original report refers to its original logs/ layout; the preserved logs here are in audit-logs/ to keep them separate from a new reproduction run. Environment-specific absolute paths and dependency binaries are omitted. The package SHA256SUMS authenticates these redistributed files; the frozen source manifest is unchanged.
