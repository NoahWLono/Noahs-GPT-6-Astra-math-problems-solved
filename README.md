# Noah's GPT-6 Astra math problems solved

A growing collection of mathematical research, formal proofs, papers, and reproducible artifacts. Each problem's materials live together in its numbered folder, with its own verification record.

## Results and verification

- [01 — Quadratic APN functions in dimension eight](01-quadratic-apn/README.md): **Completed and verified.** A Lean-checked proof that every quadratic APN function from F₂⁸ to F₂⁸ has at least **33 non-bent nonzero components**, equivalently at most 222 bent nonzero components. The author-side endpoint build and a separate fresh rebuild of all 136 local proof modules have passed. This proves a universal lower bound, not attainment or a new APN construction. Read the [full mathematical paper](01-quadratic-apn/paper/apn-eight-bound.pdf). The excluded i = 3 amplitude profile was explicitly still open in Beierle et al., 27 August 2026, §5.1. The completed literature review found no earlier proof of this exclusion in the sources checked; see [the paper’s prior-art discussion, §1.2](01-quadratic-apn/paper/apn-eight-bound.pdf#page=4).

- [02 — Adaptive progressive verification with short private check banks](02-progressive-signature-verification/README.md): **Completed and verified.** A narrowly scoped private verification method with adaptive-query error bounds, an executable finite machine, and exact field-multiplication accounting. All 67 Lean modules were independently rebuilt; 862 theorem declarations were audited for standard Lean axioms. Semantic, mathematical, and qualified prior-work reviews passed. This changes verification preprocessing and checking, not signature generation; it does not claim a new signature primitive or practical speedup. Read the [reviewed paper](02-progressive-signature-verification/paper/short-private-pools.pdf).

- [03 — Classification of order-ten binary 3-frameproof codes](03-order-ten-frameproof/README.md): **Complete computer-assisted proof, verified in Lean.** Every binary `SHF(10;10,2,{1,3})` is a permutation matrix up to independent row complementation. The full matrix theorem, structural reduction, and four finite cases are proved in Lean. Standard `bv_check` replays saved certificates using compiled evaluation; the [trust boundary](03-order-ten-frameproof/reviews/proof-audit.md) is explicit. Read the [11-page paper](03-order-ten-frameproof/paper/order_ten_frameproof.pdf). The exact case was explicitly left open in 2015; no earlier resolution was located in the documented search, with full-text access gaps recorded in the [prior-art review](03-order-ten-frameproof/reviews/prior-art-review.md).

- [04 — A uniform optimum for short-interval square-difference masks](04-short-interval-square-difference/README.md): **Central all-length theorem verified in Lean; historical novelty unestablished.** Modulus 144 minimizes worst-case surviving-candidate counts among every raw residue table of at most 256 bits, simultaneously for all positive interval lengths. All nine local proof modules were rebuilt from the publication sources, including the finite checks and semantic bridge. The [native-evaluation trust boundary and formal scope](04-short-interval-square-difference/lean/README.md) are explicit; the analytic argument and Python verification are also included. It establishes candidate-count optimality under the stated model, without a faster-factorization claim. Read the [mathematical paper](04-short-interval-square-difference/paper.pdf).

- [05 — The minimum local identifying code in the binary 6-cube](05-local-identifying-q6/README.md): **Completed and verified in Lean: M^L(6) = 14.** An explicit 14-word code attains the minimum, and the unconditional Lean theorem proves that every local 1-identifying code has at least 14 words. Both the first build and an independent clean-source rebuild of all 257 modules passed using only standard Lean axioms. The exact certificate is replayed as kernel-checked proof terms; no SAT-solver answer or native-evaluation axiom is assumed. This improves the strongest located published bounds of 12–15; the [bounded prior-art comparison](05-local-identifying-q6/REPRODUCIBILITY.md#prior-art) does not claim absolute priority. Read the [9-page mathematical paper](05-local-identifying-q6/paper/main.pdf).

- [06 — Rational recurrences for elliptic-curve translation](06-elliptic-curve-recurrences/README.md): **Verified formalization; historical novelty unestablished.** The Lean formalization covers the recurrence obstruction and its stated supporting results, with the exact assumptions, theorem correspondence, trust boundary, and clean-rebuild evidence recorded in the [formal verification addendum](06-elliptic-curve-recurrences/FORMAL_VERIFICATION.md). The [original mathematical paper](06-elliptic-curve-recurrences/original-research/manuscript.pdf) and reproducible synthetic experiments are preserved unchanged as historical research assets. This is a result about the specified rational-recurrence model, not a faster ECDLP solver or a general algorithmic lower bound.

- [07 — Scoped irreducibility of shifted binomial compositions](07-scoped-binomial-irreducibility/README.md): **Completed scoped results, verified in Lean; historical novelty unestablished.** For prime `p >= 5`, integers `k, A` with `|k| > 1`, and every prime valuation of `k` below `p`, `(X^m - A)^p + k` is irreducible over the rationals whenever `m > 1` and every prime divisor of `m` exceeds `p`. Repeated prime factors are allowed. The [original prime-inner-exponent paper](07-scoped-binomial-irreducibility/original/paper/scoped-binomial-irreducibility.pdf) and [composite-inner-exponent addendum](07-scoped-binomial-irreducibility/addendum/composite-inner-addendum.pdf) are preserved with their Lean/LaTeX sources and reproduction records. Both exact roots passed requested-type comparison and full-closure checking in a patched official Lean 4.34.1 kernel and independent nanoda, with only the three standard Lean axioms. The [non-isolated checking and rebuild limits](07-scoped-binomial-irreducibility/VERIFICATION.md) are explicit. **The full fixed-gap Pillai conjecture remains unresolved.**

## Ongoing research

Current research-only WIP (seven active targets; status updated 12 October 2026):

- **koalaIRS12 soundness benchmark at better.codes:** a profile-interval counting bound has been independently checked, but the full global soundness benchmark remains open. No eligible improved benchmark score is established.
- **Total coloring conjecture:** a paper-level argument gives the exact repair distance for a constructed family. Lean verification and novelty review remain pending; the full Δ+2 conjecture for finite simple graphs remains unresolved here.
- **[Four exponentials conjecture](https://www.dpmms.cam.ac.uk/~pv270/diophantine.pdf):** activated from queue item 15. Initial investigation; no verified result is established.
- **[Irrationality of Euler’s constant](https://arxiv.org/abs/1303.1856):** activated from queue item 16. Initial investigation; no verified result is established.
- **[Base-ten normality of pi](https://www.tandfonline.com/doi/abs/10.4169/amer.math.monthly.121.03.191):** activated from queue item 17. Initial investigation; no verified result is established.
- **[Markov-number uniqueness conjecture](https://link.springer.com/article/10.1007/s11139-026-01468-5):** activated from queue item 18. Initial investigation; no verified result is established.
- **[Uniformity of rational points on curves of fixed genus](https://link.springer.com/article/10.1007/s40993-026-00783-6):** activated from queue item 19. Initial investigation; no verified result is established.

These are research directions, not completed solutions. Only completed, checked proofs will be added to the collection; experimental artifacts are not published. The five newly activated targets retain their saved queue order; source review and assessment of feasible scoped approaches are part of the initial investigation.

### Shelved research

Paused on 12 October 2026 pending a materially stronger route:

- **Pillai’s full fixed-gap conjecture:** the completed scoped shifted-binomial irreducibility theorem and composite-inner-exponent addendum remain unchanged in [folder 07](07-scoped-binomial-irreducibility/README.md). Those results do not settle the full conjecture, which remains unresolved here; historical novelty of the scoped results is unestablished.
- **List edge-coloring conjecture:** the current investigation does not establish equality of the list edge-chromatic and edge-chromatic numbers for all finite loopless multigraphs. No completed solution is claimed.
- **Kummer–Vandiver conjecture:** tested height and transfer approaches do not establish the required plus-class saturation. The conjecture remains unresolved here.
- **Inverse Galois problem over the rationals:** an explicit Sz(8) dessin has been verified, but numerical Belyi reconstruction is not yet exact. No new realization over the rationals is established.
- **Uniform boundedness of number-field abelian-variety torsion:** no new torsion bound depending only on the abelian-variety dimension g and number-field degree d is established.

Previously shelved: the exact covering number C(13,6,4); Lehmer’s Mahler-measure gap problem; Lehmer’s totient problem; Carmichael’s totient conjecture; Erdős–Moser equation conjecture; Brocard–Ramanujan factorial-square problem; Beal’s conjecture; Littlewood’s simultaneous-approximation conjecture; Zaremba’s explicit bound-5 conjecture; Gauss circle error-term conjecture; Dirichlet divisor error-term conjecture.

### Queued research

The following targets are waiting, in the order listed. Their inclusion does not imply a proof, a feasible completion time, or a claim of novelty. Source and open-status screening was performed on 11 October 2026.

<details>
<summary>View the research queue</summary>


**Number theory**

20. [Serre’s uniformity conjecture for elliptic curves over Q](https://arxiv.org/html/2602.20964v1)

**Algebra, geometry and topology**

21. [Nakai conjecture](https://arxiv.org/abs/2604.24508)
22. [Bounded negativity conjecture](https://arxiv.org/abs/2408.15187)
23. [Zariski cancellation for complex affine three-space](https://arxiv.org/abs/2208.14736)
24. [Andrews–Curtis conjecture](https://github.com/SAIRcompetition/Andrews-Curtis/blob/main/competition/rules/overview.md)
25. [Hadwiger–Boltyanski illumination conjecture](https://arxiv.org/abs/2507.08712)
26. [Dürer edge-unfolding conjecture](https://arxiv.org/abs/2607.09606)
27. [Square peg problem](https://arxiv.org/abs/2203.02613)
28. [Chern second-gap conjecture for minimal hypersurfaces](https://arxiv.org/abs/2610.05276)
29. [Borsuk's problem in four dimensions](https://arxiv.org/abs/2605.19068)
30. [Five-dimensional kissing number](https://doi.org/10.1007/s00454-026-00841-x)
31. [Finitely presented groups of intermediate growth](https://jep.centre-mersenne.org/item/10.5802/jep.295.pdf)
32. [Cabling conjecture](https://link.springer.com/article/10.1007/s40590-025-00722-y)
33. [Jones polynomial unknot-detection problem](https://epubs.siam.org/doi/10.1137/25M1806703)
34. [Additivity of knot crossing number](https://doi.org/10.1080/10586458.2025.2542174)
35. [Kashaev–Murakami–Murakami volume conjecture](https://arxiv.org/abs/1002.0126)
36. [Kaplansky's sixth conjecture](https://arxiv.org/abs/1409.2545)
37. [Prime-degree cyclicity problem for division algebras](https://arxiv.org/abs/2409.07240)
38. [Berge conjecture for lens-space surgeries](https://arxiv.org/abs/2609.39260)
39. [Foulkes' conjecture](https://www.imsc.res.in/~combinatorics/ICC2026/)
40. [Essential dimension of S₈ over C](https://www.numdam.org/articles/10.5802/crmath.577/)

**Analysis, dynamics, probability and mathematical physics**

41. [Mazur rotation problem](https://arxiv.org/abs/2012.08344)
42. [Furstenberg ×2×3 measure-rigidity conjecture](https://arxiv.org/abs/2410.22701)
43. [Mandelbrot local-connectivity conjecture](https://arxiv.org/abs/2512.24171)
44. [Exact Landau constant](https://arxiv.org/abs/2609.23236)
45. [Pólya's Dirichlet eigenvalue conjecture](https://doi.org/10.1112/jlms.70425)
46. [Bochner–Riesz conjecture in the remaining dimensions](https://arxiv.org/html/2610.06181v1)
47. [Erdős similarity conjecture](https://arxiv.org/abs/2604.01493)
48. [Pointwise convergence of triple ergodic averages](https://arxiv.org/abs/2603.18974)
49. [Global regularity of inviscid SQG](https://arxiv.org/abs/2608.16641)
50. [Large-data inhomogeneous Coulomb Landau regularity](https://arxiv.org/abs/2608.18407)
51. [Nonradial soliton resolution for the energy-critical wave equation](https://doi.org/10.3934/dcds.2026115)
52. [Exact Bloch constant](https://arxiv.org/abs/2608.17660)
53. [Planar first-passage-percolation fluctuation exponent](https://arxiv.org/abs/1511.03262)
54. [Planar self-avoiding walk converges to SLE8/3](https://arxiv.org/abs/math/0204277)
55. [Non-Gaussian scaling limit of critical three-dimensional Ising](https://arxiv.org/abs/2112.04248)
56. [Positive-temperature spin-glass order in three-dimensional Edwards–Anderson](https://arxiv.org/abs/2301.04112)
57. [Quantum unique ergodicity on negatively curved surfaces](https://arxiv.org/abs/2606.12098)
58. [Engliš–Zhang Fefferman–Szegő conjecture](https://arxiv.org/html/2605.25455v1)
59. [Large-data classical hard-sphere Boltzmann existence](https://arxiv.org/html/2608.18407v1)

**Combinatorics and optimization**

60. [Metric TSP four-thirds integrality-gap conjecture](https://arxiv.org/abs/2603.12995)
61. [Strongly polynomial linear programming](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.STACS.2025.2)
62. [Polynomial Hirsch conjecture](https://arxiv.org/abs/2607.11628)
63. [Tutte's five-flow conjecture](https://arxiv.org/abs/2602.21526)
64. [Berge–Fulkerson conjecture](https://arxiv.org/abs/2501.05348)
65. [Caccetta–Häggkvist conjecture](https://doi.org/10.1016/j.disc.2025.114868)
68. [Ryser's odd-order Latin transversal conjecture](https://arxiv.org/abs/2310.19779)
69. [Missing Moore graph of degree 57](https://arxiv.org/abs/2610.04815)
70. [Tuza's triangle packing–covering conjecture](https://arxiv.org/abs/2609.13831)
71. [Gallai's path-decomposition conjecture](https://ir.cwi.nl/pub/36262/36262.pdf)
72. [The one-third–two-thirds conjecture for finite posets](https://arxiv.org/abs/2609.30888)
73. [Vizing's domination-product conjecture](https://arxiv.org/abs/2607.01109)
74. [Reed's omega–delta–chi conjecture](https://arxiv.org/abs/2502.10147)
75. [Kotzig's perfect one-factorization conjecture](https://arxiv.org/abs/2607.09459)
76. [Stanley's chromatic-symmetric-function conjecture for trees](https://arxiv.org/abs/2608.18179)
77. [Conway's planar thrackle conjecture](https://arxiv.org/abs/2506.11808)
78. [Bermond–Thomassen conjecture](https://arxiv.org/abs/2608.12948)
79. [Albertson's crossing-number conjecture](https://arxiv.org/abs/2609.01682)
80. [Thomassen's Hamiltonian line-graph conjecture](https://doi.org/10.1002/jgt.70113)

**Cryptography**

81. [Public-key encryption from one-way functions](https://eprint.iacr.org/2018/555)
82. [Exponential share-size lower bounds for general perfect secret sharing](https://eprint.iacr.org/2025/518)
83. [Circular security from full homomorphic composability](https://cic.iacr.org/p/2/1/1/pdf)
84. [Two-group-element pairing-based SNARGs](https://doi.org/10.1007/978-3-662-49896-5_11)
85. [Public-coin near-circuit-size black-box zero knowledge](https://eccc.weizmann.ac.il/report/2025/162/revision/1/download/)

**Computer science**

86. [Fourier entropy-influence conjecture](https://link.springer.com/article/10.1007/s00493-024-00133-z)
87. [Aanderaa-Karp-Rosenberg evasiveness conjecture](https://arxiv.org/abs/1306.0110)
88. [Distribution-free efficient PAC learning of DNF](https://raw.githubusercontent.com/mlresearch/v291/main/assets/heidari25a/heidari25a.pdf)
89. [Deterministic linear-time minimum spanning trees](https://people.csail.mit.edu/dmoshkov/papers/mst/high-girth.pdf)
90. [Skolem problem over the integers](https://arxiv.org/abs/2607.15510)
91. [Generalized star height one problem](https://doi.org/10.1016/0890-5401(92)90063-L)
92. [Linear-size universal point sets for planar graphs](https://arxiv.org/abs/2609.10916)
93. [Aaronson-Ambainis influential variable conjecture](https://arxiv.org/abs/2609.35327)
94. [NP-completeness of the Minimum Circuit Size Problem](https://eccc.weizmann.ac.il/report/2026/091/download/)

**Logic and foundations**

95. [Vaught's conjecture](https://arxiv.org/abs/2508.06854)
96. [Kolmogorov-Loveland versus Martin-Lof randomness](https://arxiv.org/abs/2403.19817)
97. [Stable fields conjecture](https://arxiv.org/abs/2009.02319)
98. [Cherlin-Zilber algebraicity conjecture](https://ivv5hpp.uni-muenster.de/u/tent/ICM.pdf)
99. [Pseudofiniteness of the triangle-free Henson graph](https://sites.math.rutgers.edu/~cherlin/Paper/census.pdf)
100. [Weiss's Borel hyperfiniteness question](https://arxiv.org/abs/1308.5853)

</details>



“GPT-6 Astra” is the owner's project label. It does not attest to runtime model identity, affiliation, or peer review. The repository title does not mean that every listed research direction is solved.

## Reproducibility and preservation

Each problem folder contains its proof and verification sources, source hashes, reproduction instructions, paper assets, and verification records. The Lean projects additionally include their proof dependency closures and pinned Lean/mathlib configurations. Each entry identifies its verification method and trust boundary. See [publication notes](PUBLICATION.md). No compiled proof objects, dependency checkout, credentials, or build cache is distributed. No CI or project-wide license has been added. Existing third-party license notices remain with the archived assets.
