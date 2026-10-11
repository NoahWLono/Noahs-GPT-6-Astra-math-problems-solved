# Verification records

The main theorem is `GPT6Astra.every_order_ten_shf_is_trivial`, with corollary `GPT6Astra.not_openProblem10`. The [proof audit](../reviews/proof-audit.md) states their exact scope and dependency lists. The [prior-art review](../reviews/prior-art-review.md) addresses novelty separately.

## Main formal proof

The 15 local modules under `gpt6_astra/` are the complete local import closure of `MainTheorem.lean`. Lean 4.34.1 and all package revisions are pinned. `gpt6_astra/SHA256SUMS` fixes the checked source, script, configuration and certificate bytes.

Run `gpt6_astra/verify.sh` after preparing the pinned dependencies. It checks the manifest and version pins, builds each finite case sequentially, then builds the main theorem. Direct source checks subsequently replay all four certificates and the final theorem even if Lake already has cached artifacts. Warnings are errors in those source checks.

The original successful checks from 8 October 2026 are retained in `original-checks/`. Publication verification records are in `publication-checks/`; `publication-result.json` describes the final run. Paths in copied logs are normalized to `<PROJECT>` and `<PACKAGE>` for portability. The proof sources and certificates themselves are unchanged.

The final main-theorem axiom list contains `propext`, `Classical.choice`, `Quot.sound`, and exactly four generated `anchored_case_K._native.bv_decide.ax_36` evaluation axioms, for K = 2, 3, 4, 5. This is standard compiled `bv_check` trust, including the compiler/runtime evaluation path. No `sorryAx` is present. The project does not claim kernel-only checking of the main certificates.

## Optional independent CNF proofs

Four separately generated anchored CNFs were each proved unsatisfiable using ordinary Lean proof terms. Each input has 9,193 variables and 37,974 clauses. The proofs cover the original complete CNFs and report only `[propext]`. Their successful source-check logs are retained in `independent-cnf/`.

These proofs are corroboration. Their Python-generated encodings are not the final matrix theorem's reflection chain, and the main theorem imports none of their modules. They do not remove its compiled-evaluation dependencies.

The optional inputs are included under `research/direct-matrix/` and `research/certificate-inspection/`. After preparing the pinned main dependencies, run from the numbered problem folder:

```bash
bash research/certificate-inspection/verify_independent.sh --check-only
bash research/certificate-inspection/verify_independent.sh
```

The first command checks the relocated environment and inputs without rebuilding proofs. The second compiles `SharedLRAT`, `DagLRAT`, and all four case modules sequentially into a new output directory; it requires each case's axiom report to be exactly `[propext]`. On the original checking machine, individual case checks took about 99–128 seconds and 1.5–1.8 GiB of process memory. Keep them sequential. The publication preparation checked the portable script's syntax and relocated environment; the retained full proof logs record the earlier complete CNF checks.

The optional helper source headers retain mathlib attribution; `NOTICE.txt` and `LICENSE.mathlib` accompany their adaptations. These notices do not set a project-wide license. The publication headers add attribution without changing the proof-construction code.

The package excludes compiled `.olean` files. It includes no abandoned certificate-conversion experiments or unproved replacement for the standard checker.

## Paper

`paper-check.json` records the delivered paper and source hashes, the successful portable build, identical extracted text between the rebuilt and delivered PDFs, and visual review. The delivered paper has 11 pages and seven references. Its final TeX build has no unresolved references or overfull boxes.

The recorded audits were assisted by agents. They are not human peer review or certification of historical priority.
