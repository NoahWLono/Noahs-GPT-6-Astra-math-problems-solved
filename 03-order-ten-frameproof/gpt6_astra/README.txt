ORDER-TEN BINARY 3-FRAMEPROOF CODES
Author: GPT-6 Astra
Verification date: 8 October 2026

RESULT

Every binary 10-by-10 separating hash family of type {1,3} is a
permutation matrix up to independent complementation of its rows.
The complete Lean theorem has been built, and all four saved finite-case
certificates have been replayed. The proof uses standard bv_check compiled
evaluation; its precise trust boundary is described below.

The main declarations, in namespace GPT6Astra, are:

  every_order_ten_shf_is_trivial
    (A : BinaryMatrix 10) (h : IsSHF A) : IsTrivial A

  not_openProblem10 : Not OpenProblem10

They are defined in MainTheorem.lean.

EXACT MATHEMATICAL SCOPE

A : Fin 10 -> Fin 10 -> Bool represents ten coordinates (rows) and ten
codewords (columns). IsSHF A requires that for every four pairwise distinct
columns a,b,c,d, some row has its bit at a different from each of its bits
at b,c,d. Thus it is exactly SHF(10;10,2,{1,3}), equivalently a binary
3-frameproof code with ten coordinates and ten codewords.

IsTrivial A means that there are a permutation p and a row-complement bit
flip(r) such that

  A r c = xor (decide (p r = c)) (flip r).

Row and column permutations are absorbed by p. The classification imposes
no design condition, regularity, row-weight assumption, distinct-row
assumption, or prescribed symmetry. It is a uniqueness classification,
not merely an upper bound on the number of codewords. OpenProblem10 is
the definition of existence of a nontrivial such matrix, not an axiom.

The analytic proof shows that elementary rows (constant rows or rows with
a private bit) force triviality. Any nontrivial example therefore has a
row whose smaller side has size k in {2,3,4,5}. Row complements and row
and column permutations fix that row as the first k ones followed by
zeros. Further complements set column zero to zero below row zero. A
minimum over a finite permutation orbit simultaneously orders the free
rows and the residual column blocks lexicographically. No weight bound
is retained on the other rows after anchoring.

Each of the four cases has exactly 840 separation conditions, 80 row-order
conditions, 63 column-order conditions, and 19 fixed-entry conditions.
These 1,002 high-level Boolean conditions are proved consequences of the
canonical matrix hypotheses before their conjunction is refuted. They
are not a claim about the number of clauses in an auxiliary CNF encoding.

TOOLCHAIN AND DEPENDENCY PINS

  Lean version: 4.34.1
  Lean commit:
  5045d0056413266e57c625dcd7c365b10e377c52

  mathlib commit:
  d13f23b723b8a846827a245b89c10fc7d3f11612

lean-toolchain selects leanprover/lean4:v4.34.1. lakefile.toml pins mathlib
by commit, and lake-manifest.json locks the transitive dependency revisions.
Do not run lake update to reproduce this release: that can change the
dependency manifest.

The executable ./lake wrapper first uses the optional project-local Linux
x86-64 toolchain at .tools/lean-4.34.1-linux/bin. If that bundle is absent,
or the host is another platform, it uses an installed lake on PATH. An
elan-provided lake shim reads this project's lean-toolchain file. If using
a standalone installation, install the exact pinned Lean release; verify.sh
checks both the version and commit. The wrapper sets the project directory
as its working directory and uses .tools/mathlib-cache by default, while
respecting an existing MATHLIB_CACHE_DIR environment variable. It does not
change shell startup files, an elan global default, or other global settings.

The scripts require Bash, Git, and either sha256sum or shasum. Use a
Bash-capable environment, such as Linux, macOS, or WSL. Initial installation
of the pinned toolchain and dependencies may require network access.
With the pinned toolchain available, mathlib's prebuilt cache can be fetched
from this directory with:

  ./lake exe cache get

This is setup, not proof verification. Once the pinned dependencies and
their build artifacts are installed, the saved-certificate proof replay
does not require a SAT solver search.

VERIFYING THE COMPLETE RESULT

From this project directory, run:

  ./verify.sh

The script checks the release SHA256SUMS, checks the Lean and mathlib pins,
builds FiniteCase2, FiniteCase3, FiniteCase4, and FiniteCase5 sequentially,
then builds MainTheorem. It subsequently invokes Lean directly on each
case source and on MainTheorem, again sequentially, so an up-to-date Lake
cache is not mistaken for a fresh certificate replay. Warnings are errors
in those direct checks. A failed command or a printed sorryAx dependency
fails verification. Logs are written to verification-logs/<UTC-time>-<pid>/.

The script deliberately does not delete dependency caches, touch source
timestamps, or overwrite the normal build artifacts during the fresh
source rechecks. Initial uncached verification does more work than a
subsequent run because it also builds the required imports.

The equivalent incremental build sequence is:

  ./lake build FiniteCase2
  ./lake build FiniteCase3
  ./lake build FiniteCase4
  ./lake build FiniteCase5
  ./lake build MainTheorem

Run the case commands one after another. On a fresh build, starting the
combined MainTheorem target first can allow independent case jobs to run
concurrently and increase peak RAM use. A bare ./lake build also builds
MainTheorem, which is the project's default target. Prefer ./verify.sh or
the sequential commands above when limiting peak RAM use.

SAVED CERTIFICATES AND REPRODUCIBLE SOURCES

The final case modules use bv_check with these stable relative paths:

  certificates/case2.lrat
  certificates/case3.lrat
  certificates/case4.lrat
  certificates/case5.lrat

SHA256SUMS identifies the exact final source and certificate bytes.
Hashes are recorded in that manifest rather than duplicated here. Replay
uses the saved proof data; it does not need to rediscover a refutation.

The companion research/direct-matrix/generate_compact_cases.py script,
in the surrounding research archive, generates each case from its actual
indices. It groups the semantic constraints into 32 balanced blocks.
CanonicalBoolAtoms.lean normalizes ground Fin indices and closed decisions
before reflection, ensuring that equal matrix entries are not represented
as separate Boolean atoms. Its changeLocalDecl operation has Lean's
definitional-equality check enabled. Generation and canonicalization add
no mathematical hypotheses.

TRUST BOUNDARY

The actual final theorem reports the following dependencies:

  propext
  Classical.choice
  Quot.sound
  GPT6Astra.anchored_case_2._native.bv_decide.ax_36
  GPT6Astra.anchored_case_3._native.bv_decide.ax_36
  GPT6Astra.anchored_case_4._native.bv_decide.ax_36
  GPT6Astra.anchored_case_5._native.bv_decide.ax_36

The first three are the standard foundational axioms used by the analytic
Lean development. The other four are generated by the standard compiled
evaluation path of bv_check. Lean has formal soundness results for the
certificate checker, but the concrete checker computation here is executed
by compiled evaluation and accepted through these evaluation axioms.
The result therefore trusts that compiler/runtime evaluation path in
addition to the usual Lean foundations and kernel.

This is a complete formal proof with that disclosed trust boundary. It is
not a claim that every certificate step was reconstructed only by kernel
reduction. There is no sorryAx dependency, no admitted target theorem, and
no user-written axiom asserting a combinatorial or computational conclusion.
The external SAT solver supplies certificates; it is not trusted to declare
the answer without successful certificate checking. The matrix-to-Boolean
semantic bridge is part of the final Lean proof.

For corroboration, four separately generated Python CNFs for the anchored
cases were also refuted using certificate-derived Lean proof terms whose
reported dependency was only propext. Those checks establish unsatisfiability
of the exact CNFs they audit. They do not substitute for the final matrix
proof, and they do not remove the compiled-evaluation dependencies above.

HISTORICAL QUESTION AND QUALIFIED NOVELTY

Guo, Stinson and van Trung explicitly left the order-ten case open in
concluding problem 3 of their 2015 paper, On Symmetric Designs and Binary
3-Frameproof Codes. They cited permutation-only classification through
the relevant orders up to nine and exhibited a nontrivial order-eleven
example. This project proves the missing order-ten classification.

A public literature audit completed on 8 October 2026 did not locate an
earlier resolution of this exact classification. That search does not
establish worldwide priority or exclude inaccessible or unpublished work.
In particular, the full text of Sun and Wang, New upper bounds for
wide-sense frameproof codes (2025), was unavailable; its abstract and
first-page preview were inspected. The companion literature audit records
that access gap and the other limits of coverage. The proof's validity and
the historical priority question are separate.

Primary references:

  C. Guo, D. R. Stinson, and T. van Trung (2015).
  On Symmetric Designs and Binary 3-Frameproof Codes.
  https://doi.org/10.1007/978-3-319-17729-8_10
  https://cs.uwaterloo.ca/~dstinson/papers/sdesign-5.pdf

  C. Guo, D. R. Stinson, and T. van Trung (2015).
  On tight bounds for binary frameproof codes.
  https://doi.org/10.1007/s10623-015-0037-y
  https://arxiv.org/abs/1406.6920

  Y. Zhao and X. Zhang (2024).
  Improved Upper Bounds for Wide-Sense Frameproof Codes.
  https://doi.org/10.1109/TIT.2024.3411150
  https://arxiv.org/html/2402.05596v1

  C. Sun and X. Wang (2025).
  New upper bounds for wide-sense frameproof codes.
  https://doi.org/10.1007/s10623-025-01631-x
  Full-text access gap in the audit described above.

Official software sources:

  https://github.com/leanprover/lean4/tree/v4.34.1
  https://github.com/leanprover-community/mathlib4/releases/tag/v4.34.1

The accompanying paper gives the complete mathematical proof, the exact
1,002-condition formulas, and an appendix mapping its lemmas to the Lean
declarations. The verification logs and SHA256SUMS identify the final
checked artifact set.
