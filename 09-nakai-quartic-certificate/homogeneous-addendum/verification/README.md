# Verification provenance

All sixteen project modules and the unchanged pinned upstream EulerIdentity module passed an independent fresh-output rebuild. No pre-existing project object files were used. The final expanded theorem was inspected against the algebraic statement. Its axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`.

`independent-rebuild.log` preserves the complete successful transcript with machine-specific path prefixes normalized to `<PACKAGE_ROOT>`, `<PROJECT_ROOT>`, `<BUILD_DIR>`, `<LEAN_TOOLCHAIN>`, and `<MATHLIB_ROOT>`. No mathematical source, source hash, exit code, resource measurement, or axiom report was altered. The receipt records both the original transcript hash and the normalized transcript hash. These are intentionally different files. The exact Lean source bytes are covered separately by `SOURCE_SHA256SUMS`.

The source manifest gives dependency order and successful component-check hashes. The independent replay checked the same bytes. A total of 17 modules ran successfully, in 53.913 seconds of summed check time, with maximum recorded process-group RSS 2,472,172 KiB. Every check used one Lean thread, `-M3072`, a 30-second limit, and a 3-GiB RSS guard. The guard monitors actual resident memory; no virtual-address-space limit is imposed.

The fifteen previously published fixed-quartic sources are unchanged, as documented by `published_15_unchanged.json`. They are not duplicated in this closure except for the common framework actually needed by this theorem.

A further fresh-output replay of the exact portable publication script passed all sixteen project modules and the unchanged upstream module. Its normalized transcript and separate receipt are `publication-rebuild.log` and `publication-replay-receipt.json`. This validates the delivered path-independent harness, rather than only the original source-environment command.
