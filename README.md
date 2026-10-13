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

- [08 — Critical scaling of iterated rational approximants to Euler’s constant](08-euler-critical-limit/README.md): **Completed scoped results, verified in Lean; historical novelty unresolved.** For natural-valued integer-pair sequences with `n -> infinity` and `n^3 / 2^p -> lambda0 > 0`, the original weighted approximants converge to `3 gamma + log(lambda0) - 2 S1(lambda0)/S0(lambda0)`. The concrete sequence `n=2^l, p=3l` converges to a limit strictly below gamma and therefore does not converge to gamma. All twelve local proof modules, including an explicit finite-sum statement fixture, were rebuilt from the publication sources using pinned Lean/Mathlib 4.32.2; the final axiom audits list only the three standard Lean axioms. The [scope and trust boundary](08-euler-critical-limit/verification/README.md) are explicit, and [prior-art gaps](08-euler-critical-limit/reviews/prior-art-review.md) remain. Read the [five-page mathematical paper](08-euler-critical-limit/paper/euler-critical-limit.pdf). **Euler’s constant is not proved irrational.**

- [09 — Formal Jacobian ideal operator separation](09-nakai-quartic-certificate/README.md): **Completed fixed-quartic and ordinary-homogeneous theorems, verified in Lean; historical novelty unestablished.** The explicit order-at-most-two quotient operator lies outside the full algebra generated by multiplication and all derivations, with arbitrary finite words allowed. The [four-page homogeneous addendum](09-nakai-quartic-certificate/homogeneous-addendum/paper/homogeneous-operator-addendum.pdf) proves this for ordinary homogeneous polynomials of degree at least two in at least three variables over any characteristic-zero field, assuming the actual gradient quotient is finite-dimensional. Hessian nonmembership is proved internally. All sixteen addendum proof modules and the expanded statement fixture passed an independent fresh-output rebuild and a further replay of the portable publication script, with only the three standard Lean axioms. The [original six-page mixed-quartic paper](09-nakai-quartic-certificate/paper/nakai-quartic-certificate.pdf) and its fifteen proof sources remain unchanged. See the [addendum verification record](09-nakai-quartic-certificate/homogeneous-addendum/verification/README.md) and [prior-art comparison](09-nakai-quartic-certificate/reviews/prior-art-review.md). The ordinary-homogeneous operator construction is prior art in every dimension; the weighted extension is not formalized here, and **the unrestricted Nakai conjecture remains unresolved here.**

- [10 — Four additive group actions on polynomial cylinders](10-polynomial-cylinder-transitivity/README.md): **Completed scoped theorem, verified in Lean; historical novelty provisional.** For every nonconstant complex polynomial `P`, four explicit polynomial additive-group actions connect any two points of `x^2*y + z^2 + x + P(t) = 0` in at most thirteen moves. The generic algebraically closed characteristic-zero result is also checked. All eleven unchanged Lean modules passed the original build, an independent clean rebuild and a fresh-output replay of the public script; final axiom reports list only the three standard Lean axioms. The construction extends Poloni's cubic case, with the [bounded prior-art comparison](10-polynomial-cylinder-transitivity/reviews/prior-art-review.md) stating the originality limitation. Read the [eight-page paper](10-polynomial-cylinder-transitivity/paper/polynomial-cylinder-transitivity.pdf) and [formal boundary](10-polynomial-cylinder-transitivity/verification/README.md). Tangent-space flexibility and infinite transitivity are separately attributed geometric consequences outside the Lean proof. **Affine-space cancellation remains unresolved by this work.**

- [11 — Sharp distance bound for composite planar rotation centers](11-sharp-rotation-center-bound/README.md): **Completed scoped theorem and sharpness, verified in Lean; historical novelty unestablished.** For a finite list of planar rotations with nonnegative angles and total `0 < Theta <= pi`, the unique composite center is within `(D/2) tan(Theta/4)` of the convex hull of the input centers, where `D` is their diameter. Two equal-angle rotations attain equality for every permitted total angle. The six-module theorem closure, literal-map fixture, and separate exact source-context certificate passed fresh-output checks with pinned Lean/Mathlib 4.32.2; the axiom reports contain only the three standard Lean axioms. Read the [three-page paper](11-sharp-rotation-center-bound/paper/rotation-center-bound.pdf), [formal specification](11-sharp-rotation-center-bound/SPEC.md), and [verification record](11-sharp-rotation-center-bound/verification/README.md). The paper's counterexample addresses the stated planar-rotation ingredient of a cited preprint, not the truth of its later unfolding theorem. **Dürer's edge-unfolding conjecture remains unresolved by this work.**

- [12 — The minimum local identifying code in the binary 7-cube](12-local-identifying-q7/README.md): **Completed and independently verified in Lean: M^L(7) = 24.** An explicit 24-word code attains the minimum, and the unrestricted lower bound applies to every original `ExactCubeCodes.Code 7` satisfying `LocalIdentifying`, without a linearity, symmetry or search-family assumption. All 3,046 custom proof modules were independently checked; the final theorem's axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. Saved certificates are checked by Lean rather than accepted as external solver answers. This improves the strongest located published bounds of 21–28; the [bounded prior-art comparison](12-local-identifying-q7/PRIOR_ART.md) makes no absolute-priority claim. Read the [mathematical paper](12-local-identifying-q7/paper/q7-local-identifying-draft.pdf), [formal specification](12-local-identifying-q7/SPEC.md), and [verification record](12-local-identifying-q7/VERIFICATION.md). The separate public verifier has passed a 12-module smoke test; its full portable workflow has not been executed.

## Ongoing research

Research lineup updated 13 October 2026. The following targets have entered active investigation in their existing queue order. Initial work checks the precise statement, current literature and claimed resolutions before attempting new mathematics. No completed result or Lean proof is claimed for these entries.

- **32 — [Cabling conjecture](https://link.springer.com/article/10.1007/s40590-025-00722-y): investigation started.** Determine whether every reducible Dehn surgery on a nontrivial knot in the three-sphere is a cable surgery at the cabling-annulus slope. The current investigation checks known classes and the remaining unrestricted case.
- **33 — [Jones polynomial unknot detection](https://epubs.siam.org/doi/10.1137/25M1806703): investigation started.** Determine whether a knot with normalized Jones polynomial equal to one must be the unknot. Recent claimed resolutions are being assessed; their correctness is not assumed. This is distinct from Khovanov homology detecting the unknot.
- **34 — [Additivity of knot crossing number](https://doi.org/10.1080/10586458.2025.2542174): investigation started.** Determine whether c(K # L) = c(K) + c(L) for arbitrary knots, using their minimal crossing numbers. Recent claimed resolutions are being assessed; diagram-level and restricted-knot results do not settle this target.
- **35 — [Kashaev–Murakami–Murakami volume conjecture](https://arxiv.org/abs/1002.0126): investigation started.** Establish the predicted asymptotic relation between the appropriately normalized colored Jones evaluations at roots of unity and knot-complement volume. The precise hyperbolic and simplicial-volume formulations and known cases are being checked before selecting a proof route.
- **36 — [Kaplansky's sixth conjecture](https://arxiv.org/abs/1409.2545): investigation started.** For a finite-dimensional semisimple Hopf algebra over an algebraically closed field of characteristic zero, determine whether the dimension of every simple module divides the algebra's dimension. Known special classes and remaining gaps are being checked.

Completion requires a genuinely new result solving the full stated target, a checked Lean proof, and a reviewed mathematical paper. Supporting lemmas, restricted cases and preliminary approaches are not counted as completion. Prior-art review and proof verification remain separate requirements. Only completed, checked proof packages are published; experimental research files remain unpublished. The independent full-closure verification of the completed Q7 result in folder 12 is unchanged.

### Shelved research

Rotated out of active research on 13 October 2026, with private checkpoints preserved and no full solution claimed:

- **[Perfect one-factorization of K64](https://arxiv.org/pdf/2607.09459v1#page=1) (finite open case associated with queue item 75): restricted obstruction established computationally; investigation paused.** The goal is a complete partition of the 2,016 edges of the complete graph on 64 vertices into exactly 63 perfect matchings, each containing 32 edges, such that every one of the 1,953 unordered pairs of distinct matchings has a union that is a single Hamiltonian cycle through all 64 vertices. The checkpoint excludes a restricted family, but supplies neither a complete factorization nor an unrestricted nonexistence proof; it is not Lean-certified. The July 2026 primary-source paper linked here lists 64 as the smallest open order.

- **[Borsuk's problem in four dimensions](https://arxiv.org/html/2605.19068v1) (former queue item 29): candidate-screening and supporting checks completed; investigation paused.** Determine whether every bounded subset of R4 with positive diameter can be partitioned into five subsets of strictly smaller diameter. The checked May 2026 source gives **5 <= b(4) <= 8**, with the upper bound in Theorem 2. No five-part construction, counterexample, improved bound or full Lean proof is established; the unrestricted problem remains unresolved.

- **[Five-dimensional kissing number](https://doi.org/10.1007/s00454-026-00841-x) (former queue item 30): partial analytic reductions recorded; investigation paused.** Determine the exact maximum number of nonoverlapping unit spheres that can simultaneously touch a central unit sphere in R5. Cohn and Rajagopal's July 2026 paper, Section 2, records **40 <= tau(5) <= 44**. Supporting inequalities remain incomplete, and the unrestricted upper-bound argument is still missing. No improved bound or full Lean proof is established; a complete result requires an attaining configuration and a matching unrestricted upper bound.

- **[Finitely presented groups of intermediate growth](https://jep.centre-mersenne.org/item/10.5802/jep.295.pdf) (former queue item 31): construction routes screened; investigation paused.** Determine whether a finitely presented group can have subexponential but nonpolynomial growth. Babenko and Sabourau's 2025 paper explicitly records this as open on pp. 486 and 501. The checkpoint rules out specified construction routes, but produces neither a qualifying finite presentation nor a general nonexistence theorem. No full Lean proof or novelty claim is made; the unrestricted existence question remains unresolved.

**Prior-art correction, 12 October 2026: ordinary locating-dominating Q6 has known optimum 16 and is retired as a novelty target.** Charon, Hudry and Lobstein's 2022 paper [*Codes in the q-ary Lee Hypercube*, Table 2, p. 183](https://wseas.com/journals/mathematics/2022/a485106-009%282022%29.pdf#page=11) reports a 16-word radius-one locating-dominating code for the Lee graph with q = 4 and n = 3; the [authors' construction file](https://perso.telecom-paristech.fr/hudry/codesLD/3_1_4) is available. Its Definition 2, p. 173, uses the same ordinary locating-dominating condition. Applying the Gray map 0 → 00, 1 → 01, 2 → 11, 3 → 10 in each coordinate gives an isomorphism from that graph, C4 × C4 × C4, to Q6, preserving the code condition. Combined with the [published lower bound of 16](https://fi.episciences.org/13881/pdf#page=8), this gives exact minimum 16. The earlier 16–18 entry relied on an out-of-date upper bound in the 2024 binary table. This is known prior art, and no new paper or new completion is claimed. It remains distinct from the completed **local 1-identifying Q6 minimum of 14** in [folder 05](05-local-identifying-q6/README.md).

Retired from the active roster on 12 October 2026 after publication of folder 11, with their completed results and research checkpoints retained:

- **[Nakai conjecture](https://arxiv.org/abs/2604.24508): checked ordinary-homogeneous theorem; broader investigation retired.** The Hessian nonmembership bridge and full unrestricted-word operator separation are now formalized for ordinary homogeneous polynomials of degree at least two in at least three variables over any characteristic-zero field with finite-dimensional gradient quotient. The reviewed [addendum in folder 09](09-nakai-quartic-certificate/homogeneous-addendum/README.md) records the exact theorem and independent rebuild. The fixed-quartic certificate remains unchanged. Weighted and general nonhomogeneous cases are outside this completed formal scope; historical novelty is unestablished, and the unrestricted conjecture remains unresolved here.
- **[Bounded negativity conjecture](https://arxiv.org/abs/2408.15187): checked algebraic checkpoint; analytic bridge pending.** The algebraic proof component has been checked. The analytic bridge needed for the intended result remains open; no full bounded-negativity solution is established.
- **[Andrews–Curtis conjecture](https://github.com/SAIRcompetition/Andrews-Curtis/blob/main/competition/rules/overview.md): shelved; former queue item 24.** Initial source review and assessment of feasible scoped approaches; no verified result is established.
- **[Hadwiger–Boltyanski illumination conjecture](https://arxiv.org/abs/2507.08712): shelved; former queue item 25.** Initial source review and assessment of feasible scoped approaches; no verified result is established.
- **[Dürer edge-unfolding conjecture](https://arxiv.org/abs/2607.09606): checked planar rotation-center theorem; unfolding geometry pending.** The sharp distance bound and examples attaining it are fully formalized in [folder 11](11-sharp-rotation-center-bound/README.md). The theorem concerns actual finite planar rotation maps; a chain-specific separation margin and a successful actual-edge unfolding are not established. Historical novelty remains unestablished, and the general edge-unfolding conjecture remains unresolved here.
- **[Square peg problem](https://arxiv.org/abs/2203.02613): shelved; former queue item 27.** Initial source review and assessment of feasible scoped approaches; no verified result is established.
- **[Chern second-gap conjecture for minimal hypersurfaces](https://arxiv.org/abs/2610.05276): shelved; former queue item 28.** Initial source review and assessment of feasible scoped approaches; no verified result is established.

Rotated out of the active roster on 12 October 2026, with their checkpoints retained:

- **[Zariski cancellation for complex affine three-space](https://arxiv.org/abs/2208.14736):** the completed arbitrary-polynomial cylinder transitivity theorem is published in [folder 10](10-polynomial-cylinder-transitivity/README.md), with a thirteen-move pointwise bound. No new cancellation proof attempt is running. Affine-space cancellation remains unresolved, and historical novelty of the scoped result remains provisional.
- **[Markov-number uniqueness conjecture](https://link.springer.com/article/10.1007/s11139-026-01468-5):** supporting results have been checked. The larger verification effort is paused pending resource-feasibility assessment; the full uniqueness conjecture remains unresolved here.
- **[Serre’s uniformity conjecture for elliptic curves over Q](https://arxiv.org/html/2602.20964v1):** a candidate argument is recorded, but the main formal proof remains pending. No completed solution is claimed.
- **Total coloring conjecture:** a paper-level argument gives the exact repair distance for a constructed family. Lean verification and novelty review remain pending; the full Δ+2 conjecture for finite simple graphs remains unresolved here.
- **koalaIRS12 soundness benchmark at better.codes:** a profile-interval counting bound has been independently checked. Global improvement remains blocked by auxiliary cases; no eligible improved benchmark score is established.

Paused on 12 October 2026 pending a materially stronger route:

- **Four exponentials conjecture:** paused by the project owner. No completed solution is claimed; the conjecture remains unresolved here.
- **Base-ten normality of pi:** paused by the project owner. No completed solution is claimed; the conjecture remains unresolved here.
- **Uniformity of rational points on curves of fixed genus:** paused by the project owner. No completed solution is claimed; the conjecture remains unresolved here.

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

**Algebra, geometry and topology**

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
75. [Kotzig's perfect one-factorization conjecture](https://arxiv.org/abs/2607.09459) — The finite K64 investigation is shelved above; the universal conjecture remains waiting.
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


