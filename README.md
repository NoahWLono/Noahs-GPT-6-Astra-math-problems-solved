# Noah's GPT-6 Astra math problems solved

A growing collection of mathematical research, formal proofs, papers, and reproducible artifacts. Status updated 9 October 2026. Each problem's materials live together in its numbered folder.

## Results and verification

- [01 — Quadratic APN functions in dimension eight](01-quadratic-apn/README.md): **Completed and verified.** A Lean-checked proof that every quadratic APN function from F₂⁸ to F₂⁸ has at least **33 non-bent nonzero components**, equivalently at most 222 bent nonzero components. The author-side endpoint build and a separate fresh rebuild of all 136 local proof modules have passed. This proves a universal lower bound, not attainment or a new APN construction. Read the [full mathematical paper](01-quadratic-apn/paper/apn-eight-bound.pdf). The excluded i = 3 amplitude profile was explicitly still open in Beierle et al., 27 August 2026, §5.1. The completed literature review found no earlier proof of this exclusion in the sources checked; see [the paper’s prior-art discussion, §1.2](01-quadratic-apn/paper/apn-eight-bound.pdf#page=4).

## Ongoing research

Current priorities:

- The Hadamard conjecture
- The union-closed sets conjecture
- The graceful tree conjecture
- New defensive digital signatures and mathematical security arguments

Continuing at lower priority:

- The Strong Exponential Time Hypothesis (SETH)
- Unconditional existence of one-way functions

These are research directions, not claims of completed solutions. The collection can grow as additional work is completed and checked.

“GPT-6 Astra” is the owner's project label. It does not attest to runtime model identity, affiliation, or peer review. The repository title does not mean that every listed research direction is solved.

## Reproducibility and preservation

The problem folder contains the proof dependency closure, pinned Lean/mathlib configuration, source hashes, build instructions, paper assets, and verification records. See [publication notes](PUBLICATION.md). No compiled proof objects, dependency checkout, credentials, or build cache is distributed. No CI or project-wide license has been added. Existing third-party license notices remain with the archived assets.
