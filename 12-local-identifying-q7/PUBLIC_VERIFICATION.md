# Completed full public verifier replay

The unchanged supplied `verify.py` completed a fresh replay of all **3,046 custom modules**, with **zero custom-object reuse**. It verified all **1,444 quoted JSON files**, all **137 designated named-audit modules** and **162 required named theorem audits**, including the final original-predicate type check. The final theorem is `ExactCubeCodes.localIdentifying_Q7_optimum24`; its defining-module and imported-consumer audits report exactly `propext`, `Classical.choice`, and `Quot.sound`.

See the [sanitized full-replay receipt](checks/PUBLIC_VERIFIER_FULL.json) and the [complete public result](checks/PUBLIC_VERIFIER_RESULT.json), which records each module's source/object/log identities and printed axiom audits. The 162 required named audits are a mandatory subset of 2,672 observed printed audit entries across 2,036 modules; every observed axiom set was standard. The completed public `RESULT.json` has SHA-256 `fec2124b44d0c260b373abfcf3e128de69ed90db16eaf4be07240cf5d9cb63ee`; the terminal external state has SHA-256 `fa6dc761e24eaba84a88f9fce434ca43c05f186985571cbb34bddfb014fb22f2`. These hashes identify the original evidence; they are not the hash of the sanitized public receipt.

## Execution and accounting

The replay ran on x86_64 Linux from a fresh transport-only package copy using official Lean 4.32.2 and the pinned Mathlib/dependency artifacts. The unchanged driver was executed through Python `runpy` under an external subprocess supervisor, which preserved compiler commands and results while enforcing resource bounds. The public driver and all proof/source/archive bytes remained unchanged. No custom proof object was imported from the initial build, the earlier independent rebuild, or the smoke run. A post-run audit checked all **12,184 compiler sidecar files**, source/object/log identities, complete ordered module coverage, and named theorem audits.

The successful run used **9,571.064417 child CPU seconds**, **9,703.032116 wall seconds**, and maximum observed process-tree RSS **1,459,834,880 bytes**. Aggregate charged child CPU was **9,571.173315 seconds**, including **0.108898 seconds** for an earlier version probe whose external supervisor failed before compiling any custom module. The narrow correction affected only that external supervisor. Successful-run supervisor/bookkeeping CPU was **853.657001 seconds**, accounted separately from child CPU. These measurements describe this environment and do not establish portable resource requirements.

The external supervisor allowed one sequential compiler slot and imposed 10,000 aggregate child CPU seconds, 120 CPU seconds and 180 wall seconds per process, 2 GiB RSS, 64 MiB output per process, and a 4 GiB free-disk floor. No proof compilation failed. These bounds are properties of the external launch, not built-in features of `verify.py`.

## Relationship to earlier evidence

The initial build, the completed independent rebuild with documented independent-object reuse, and this public replay are separate verification records. The independent rebuild is described in [INDEPENDENT_VERIFICATION.md](INDEPENDENT_VERIFICATION.md). Its receipt is preserved unchanged. The transport and 12-module smoke receipts are also historical and retain their original limited scope, including their original statements that the full public verifier had not been run. The smoke test alone does not verify the final theorem.

## Dependency and claim limits

The public replay used the official pinned Lean compiler and existing pinned Mathlib/dependency artifacts. It did not independently rebuild or audit the compiler, standard library, or external dependencies. Fresh network dependency installation and other operating systems have not been tested. Historical priority remains unconfirmed. See [TRUST.md](TRUST.md) and [PRIOR_ART.md](PRIOR_ART.md).
