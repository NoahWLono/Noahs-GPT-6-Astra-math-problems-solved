# Independent APN eight-dimensional proof audit

## Status
**PASS — completed 2026-10-09 at approximately 17:29 UTC.** All 136 local modules compiled successfully from isolated source snapshots. Every exit status was zero; no timeout or memory-cap termination occurred. All original sources were compared again after completion and matched the recorded snapshot hashes.

All four final endpoints have precisely the standard Lean axioms `[propext, Classical.choice, Quot.sound]`, including the function-level theorem. No classification assumption remains. `SUCCESS`, `results.json`, and `logs/APNEightFinal.log` record the completed pass.

Total summed compiler wall time: 579.965 seconds. Longest individual module: 20.174 seconds. Maximum observed RSS: 2,156,332 KiB, below the 2,900,000 KiB cap. Final module: 7.728 seconds and 2,007,052 KiB peak RSS.

## Statement inspection
The final function-level endpoint is `APNRedo.quadratic_apn_function_nonBent_count_ge_thirty_three` in `APNEightFinal.lean`. It quantifies an arbitrary function `f : V 8 → V 8`, with `V 8 = Fin 8 → ZMod 2`, and assumes precisely:
1. Its actual normalized polar `f (x+y)+f x+f y+f 0` is represented by a bilinear map.
2. The actual APN property: every nonzero-direction derivative fiber contains at most two distinct points.

Its conclusion counts nonzero coordinate masks for which the encoded scalar component fails `FastWalsh.IsBent`. That predicate is defined using the integer Walsh sum over all 256 inputs and requires the square of every Walsh coefficient to equal 256. Thus the count is an actual non-bent component count, not a rank proxy. Encoding uses the mutually inverse coordinate/bit-vector maps. Constants are included through normalization; characteristic-two quadratic maps permit linear terms. No classification, rank-spectrum, residue-bound, or APN existence assumption is an argument of the final theorem.

The result proves a lower bound of 33 non-bent nonzero components for every quadratic APN function in eight dimensions. It does not prove existence of such a function, attainment of 33, a classification of APN functions, or publication novelty. “Quadratic” here is degree at most two, witnessed by bilinear normalized polar.

## Proof architecture inspected
- Genuine APN derivative fibers imply polar/radical incidence and disjointness.
- Alternating rank parity plus incidence give the non-bent-count residue 1 modulo 4.
- The actual singular-component indicator includes the zero component, has weight equal to count + 1, and has Boolean ANF degree at most four via the checked Pfaffian bridge.
- The proved low-weight residue bound forces indicator weight at least 30.
- The proved specialized weight-30 classification yields the support of two transverse affine four-flats.
- Actual APN rank geometry and the affine half-rank obstruction exclude count 29.
- Residue arithmetic then yields count at least 33, and the Walsh/degeneracy equivalence transfers this to actual bentness.

## Reproduction and scope
The recorded audit freshly rebuilt the complete non-standard dependency closure of `APNEightFinal`: 136 local modules. Source snapshots were isolated from the original local compiled proofs. Only the isolated snapshots and pinned upstream libraries were on the compilation search path. Every local module was compiled in topological order, with one compiler worker, a 120-second module timeout, and a 2,900,000-KiB RSS watchdog. No limit was reached.

For portable reproduction from this publication, follow [the Lean build instructions](../lean/README.md). The publication wrapper rebuilds the identical 136-module proof closure plus the additional endpoint-inspection module. The wrapper was smoke-tested on its first five modules; the full recorded pass below refers to the independent 136-module audit, not a second full pass of the publication wrapper.

Lean: 4.19.0, compiler commit `6caaee842e94`.
Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The standard library and pinned mathlib dependencies are used as installed, not rebuilt from source in this audit. This is a fresh rebuild of the entire local development, not an independent reimplementation of Lean or mathlib.

## Evidence
- `source-manifest.json`: portable source paths and snapshot SHA-256 hashes.
- `build-order.txt`: complete ordered local dependency closure.
- `external-imports.txt`: imports provided by mathlib/standard packages.
- `environment.json`: actual compiler version, mathlib commit and isolated search-path scope.
- `source-audit.json`: token scan of comment-stripped local sources for `sorry`, `admit`, `native_decide`, and `axiom` declarations; empty.
- `additional-trust-scan.json`: additional raw scan for `unsafe`, `implemented_by`, `extern`, `trustCompiler`, and `debug.skipKernelTC`; empty.
- `logs/`: fresh per-module compiler output and resource outcome.
- `results.json`: ordered module results, time and peak RSS.
- `logs/APNEightFinal.log`: final transitive axiom reports, checked successfully in this audit.

Final source snapshot SHA-256: `388edf2c359a8c122c866f650bdf6f899a1be6c37edfe978cbaed4009a4f2534`.

## Publication sanitization

Machine-specific source-directory prefixes in copied logs were replaced with `<LEAN_SOURCE>`; compiler diagnostics, axiom reports, module results, and all proof source bytes were preserved. Source-manifest paths are relative to `../lean/`. Absolute compilation search paths are summarized by their trust scope. See `publication-sanitization.json` for changed-log names and original report hashes. The audit’s workspace-specific driver is replaced by the portable publication wrapper, which is explicitly distinguished above from the driver used for the recorded full pass.

## Additional endpoint inspection

`APNEightFinalAudit` was separately compiled against the fresh independent outputs with exit 0. Its statement/definition inspection and final axiom report are in [the endpoint audit log](logs/APNEightFinalAudit.log); [the result](endpoint-audit-result.json) records 2.108 seconds and 1,971,200 KiB peak RSS. This extra check leaves the original 136-module rebuild result unchanged. The publication wrapper rebuilds this inspection module as its final step.
