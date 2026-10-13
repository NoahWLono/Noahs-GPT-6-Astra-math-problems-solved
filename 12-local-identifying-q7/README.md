# Local identifying codes in Q7: exact minimum 24

**Verification status:** the exact original-predicate theorem and its full 3,046-module independent source rebuild passed. All 162 required named theorem audits in 137 modules report only standard Lean axioms. The unchanged public verifier completed a fresh build of all 3,046 custom modules, with zero custom-object reuse. All 162 required named theorem audits in 137 modules passed, including the final original-predicate type check. See [public replay evidence](PUBLIC_VERIFICATION.md). See [independent verification](INDEPENDENT_VERIFICATION.md) and [STATUS.json](STATUS.json).

The seven-dimensional binary cube has 128 vertices. A local identifying code dominates every vertex by a closed neighborhood and gives different closed-neighborhood code traces to every adjacent pair, including edges whose endpoints belong to the code. The minimum size is **24**.

The Lean statement is:

```lean
(∃ C : ExactCubeCodes.Code 7,
  ExactCubeCodes.LocalIdentifying C ∧ ExactCubeCodes.cardinality C = 24) ∧
(∀ C : ExactCubeCodes.Code 7,
  ExactCubeCodes.LocalIdentifying C → 24 ≤ ExactCubeCodes.cardinality C)
```

Entry theorem: `ExactCubeCodes.localIdentifying_Q7_optimum24`, defined in [ExactQ7.lean](browse/Q7Mod/Integration/ExactQ7.lean). [ExactQ7Audit.lean](browse/Q7Mod/Integration/ExactQ7Audit.lean) explicitly checks its original-predicate type.

## Read and reproduce

- [Rendered paper](paper/q7-local-identifying-draft.pdf)
- [Paper source](paper/q7-local-identifying-draft.tex) and [bibliography](paper/q7-local-identifying-draft.bib)
- [Specification and semantic audit](SPEC.md)
- [Reproducibility instructions](VERIFICATION.md) and [verifier source](verify.py)
- [Trust boundary](TRUST.md)
- [Prior art and claim limits](PRIOR_ART.md)
- [Source manifest](manifests/SOURCE_MANIFEST.json), [quoted-data manifest](manifests/JSON_MANIFEST.json), [build order](manifests/BUILD_ORDER.json), and [named axiom requirements](manifests/AXIOM_REQUIREMENTS.json)

The complete frozen proof input is 3,046 custom Lean modules plus 1,444 quoted JSON payloads. Sources/data retain exact bytes and hashes. There are no custom compiled objects, dependency checkouts, caches, solver executables, or failed experiments in this bundle. The compiler freshly checks the quoted certificates; no external solver's answer is accepted as a theorem.

The repository's project name is its owner's label, not a claim of model identity. No new license or automated CI configuration is supplied here.

## One-command custom-proof build

After preparing official Lean 4.32.2 and the pinned Mathlib checkout as described in VERIFICATION.md, run:

```sh
python3 verify.py --lean-root "$LEAN_ROOT" --mathlib "$MATHLIB" --output .verify
```

The command automatically reassembles and checks the numbered archive parts, safely extracts all 4,490 exact source/data files, then freshly compiles all custom modules. The parts are transport packaging, not omitted proof data. `python3 verify.py --check-inputs` performs the same restoration and hash/order checks without running Lean. The source-only round trip, 12-module smoke test and complete public-verifier replay passed. The full replay used an external resource supervisor and existing pinned external dependencies; see [public replay evidence](PUBLIC_VERIFICATION.md).
