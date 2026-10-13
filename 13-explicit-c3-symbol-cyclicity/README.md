# 13 — An explicit invariant for a degree five symbol descent family

The scoped characteristic-zero theorem `PrimeFiveFamily.symbolFamily_cyclicity` proves that the explicit invariant generates a degree-five cyclic Galois maximal subfield in the fixed algebra of the precise semilinear symbol family. There is **no additional fifth-power hypothesis** in this final theorem. Historical novelty is **unestablished**. This does **not** solve unrestricted degree-five or prime-degree cyclicity.

- [Mathematical paper](paper/scoped-c3-cyclicity.pdf), with [LaTeX](paper/scoped-c3-cyclicity.tex), bibliography and full 69-term numerator and 75-term central-power tables
- [Exact scope](SCOPE.md) and [prior-art boundary](PRIOR_ART.md)
- [Readable final theorem](lean/FinalAssembly.lean), [family hypotheses](lean/FamilyInterface.lean), and [final audit source](lean/FinalAudit.lean)
- [Verification record](VERIFICATION.md) and [source-only reproduction instructions](REPRODUCIBILITY.md)
- [Complete compressed Lean sources](lean/sources.tar.gz), [source checksums](lean/SOURCE_SHA256SUMS), and [dependency order](lean/build-order.txt)

## Verification status

The initial complete final theorem and a staged independent replay passed. The final audit reports only `propext`, `Classical.choice`, and `Quot.sound`; literal fifth-power output alignment is axiom-free.

The final replay freshly compiled 418 N5 modules, a separate N5 audit, and the three support/final/audit modules. It reused 212 independently rebuilt N4 modules, 31 independently rebuilt structural modules, and 99 original earlier base/N2/N3 objects. Two of those 99 modules also had separate source rebuilds; the other 97 retain original checked-object provenance. This is not a fresh independent rebuild of all 763 custom sources. The terminal run completed 422 invocations with no failures or retries.

The included public verifier passed static and archive checks but has not completed an end-to-end replay. See the [exact verification record](VERIFICATION.md), [terminal summary](verification/staged-replay-summary.json), and [module inventory](verification/staged-source-inventory.json).

All 763 reachable custom Lean sources are included as exact bytes (81,210,652 bytes uncompressed; 8,308,558 bytes in deterministic gzip transport). The archive contains only regular `.lean` files, with no compiled objects or dependency checkout. Some necessary checked sources retain `Pilot` or `Diagnostic` in their names; these are reachable dependencies, not omitted or substituted experiments.

No project-wide license or authorship attribution is introduced by this package.
