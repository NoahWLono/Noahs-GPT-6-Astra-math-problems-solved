# Noah's GPT-6 Astra math problems solved

A growing collection of mathematical research, formal proofs, papers, and reproducible artifacts. Each problem's materials live together in its numbered folder, with its own verification record.

## Results and verification

- [01 — Quadratic APN functions in dimension eight](01-quadratic-apn/README.md): **Completed and verified.** A Lean-checked proof that every quadratic APN function from F₂⁸ to F₂⁸ has at least **33 non-bent nonzero components**, equivalently at most 222 bent nonzero components. The author-side endpoint build and a separate fresh rebuild of all 136 local proof modules have passed. This proves a universal lower bound, not attainment or a new APN construction. Read the [full mathematical paper](01-quadratic-apn/paper/apn-eight-bound.pdf). The excluded i = 3 amplitude profile was explicitly still open in Beierle et al., 27 August 2026, §5.1. The completed literature review found no earlier proof of this exclusion in the sources checked; see [the paper’s prior-art discussion, §1.2](01-quadratic-apn/paper/apn-eight-bound.pdf#page=4).

- [02 — Adaptive progressive verification with short private check banks](02-progressive-signature-verification/README.md): **Completed and verified.** A narrowly scoped private verification method with adaptive-query error bounds, an executable finite machine, and exact field-multiplication accounting. All 67 Lean modules were independently rebuilt; 862 theorem declarations were audited for standard Lean axioms. Semantic, mathematical, and qualified prior-work reviews passed. This changes verification preprocessing and checking, not signature generation; it does not claim a new signature primitive or practical speedup. Read the [reviewed paper](02-progressive-signature-verification/paper/short-private-pools.pdf).

- [03 — Classification of order-ten binary 3-frameproof codes](03-order-ten-frameproof/README.md): **Complete computer-assisted proof, verified in Lean.** Every binary `SHF(10;10,2,{1,3})` is a permutation matrix up to independent row complementation. The full matrix theorem, structural reduction, and four finite cases are proved in Lean. Standard `bv_check` replays saved certificates using compiled evaluation; the [trust boundary](03-order-ten-frameproof/reviews/proof-audit.md) is explicit. Read the [11-page paper](03-order-ten-frameproof/paper/order_ten_frameproof.pdf). The exact case was explicitly left open in 2015; no earlier resolution was located in the documented search, with full-text access gaps recorded in the [prior-art review](03-order-ten-frameproof/reviews/prior-art-review.md).

- [04 — A uniform optimum for short-interval square-difference masks](04-short-interval-square-difference/README.md): **Complete computer-assisted proof with independently checked finite certificates; historical novelty unestablished.** Modulus 144 minimizes worst-case surviving-candidate counts among every raw residue table of at most 256 bits, simultaneously for all positive interval lengths. The analytic argument and exact Python verification are included; this result has not been formalized in Lean. It establishes candidate-count optimality under the stated model, without a faster-factorization claim. Read the [6-page paper](04-short-interval-square-difference/paper.pdf).

## Ongoing research

Current research-only WIP:

- Černý's conjecture
- Splay-tree dynamic optimality
- L versus NL
- NC versus P
- The log-rank conjecture (real matrix rank)
- The Hamiltonian quantum PCP conjecture

These are research directions, not completed solutions. Only completed, checked proofs will be added to the collection; experimental artifacts are not published.

“GPT-6 Astra” is the owner's project label. It does not attest to runtime model identity, affiliation, or peer review. The repository title does not mean that every listed research direction is solved.

## Reproducibility and preservation

Each problem folder contains its proof and verification sources, source hashes, reproduction instructions, paper assets, and verification records. The Lean projects additionally include their proof dependency closures and pinned Lean/mathlib configurations. Each entry identifies its verification method and trust boundary. See [publication notes](PUBLICATION.md). No compiled proof objects, dependency checkout, credentials, or build cache is distributed. No CI or project-wide license has been added. Existing third-party license notices remain with the archived assets.
