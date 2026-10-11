# Lean verification artifacts

Start with [the dated formal-verification addendum](../FORMAL_VERIFICATION.md) and [exact semantic coverage](SEMANTIC_COVERAGE.md).

- 113 local proof modules, Lean 4.32.2, pinned Mathlib.
- All modules passed a fresh local-source rebuild; upstream dependencies were cached.
- Reported transitive axioms are limited to `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, admitted custom axioms or native-evaluation proof shortcuts.

## Reproduction and audit

- [Reproduction](LOCAL_REPRODUCTION.md)
- [Source checksums](SOURCE_SHA256SUMS)
- [Successful clean build record](CLEAN_BUILD_RECORD.json)
- [Declaration-level axiom audit](CLEAN_AXIOM_AUDIT.json)
- [Independent replay manifest](INDEPENDENT_REPLAY_MANIFEST.json)
- [Pinned upstream overlay inventory](OVERLAY_DEPENDENCY_MANIFEST.json)
- [Mathlib dependency manifest](dependency-manifest.mathlib.json)

`verification-output/` contains the successful clean-build logs. `independent-replay/` contains separate successful endpoint replays with the same trusted compiler and dependencies. These replays are internal verification, not outside expert peer review. No compiled objects, caches or historical failed-experiment logs are included.

Run `sha256sum -c SOURCE_SHA256SUMS` to check source integrity. Review the reproduction instructions before building. The audited workflow was `verify-cached.sh`; clean online dependency provisioning was not exercised as part of this audit.

Apache-2.0 attribution is retained in adapted foundation sources; see `APACHE-2.0.txt` and their headers. The original research artifacts are preserved separately and are not executed by either verification script.
