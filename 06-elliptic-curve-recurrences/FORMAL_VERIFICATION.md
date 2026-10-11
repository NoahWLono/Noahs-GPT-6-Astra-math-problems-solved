# Formal verification addendum

Date: 11 October 2026. Applies to the preserved ASTRA-01 research snapshot from commit `31ce2acb2f90f9ca515c60fa56de01b9d576226b`.

A compact two-page [PDF summary](FORMAL_VERIFICATION.pdf) and its [LaTeX source](FORMAL_VERIFICATION.tex) accompany this declaration-level index.

## Updated status

The main T1–T6 obstruction statements and E1–E4 mathematical examples now have Lean 4 proof artifacts in the precise formulations below. The original research snapshot's statements that formal verification had not been performed are historical and are superseded by this addendum for these endpoints. The original manuscript, claim ledger, scripts and certificates remain byte-for-byte preserved in `original-research/`; the preservation manifest lists all 24 assets.

Verification is distinct from novelty. The [independent novelty review](reviews/06-independent-novelty-review.md) does not establish historical priority or a new ECDLP algorithm. Formalizing the classical Hasse bound and other prerequisites is not itself evidence of a new mathematical discovery.

## Exported mathematical endpoints

| Claim | Lean declaration | Scope |
|---|---|---|
| T1 | `Astra01.EllipticPointDivisor.global_projective_recurrence_obstruction` | Actual nonsingular Weierstrass curve over algebraically closed constants, arbitrary characteristic, exact translation order n≥2, actual nonconstant function-field element and reduced nonconstant rational map. Global projective recurrence implies r=1 and n divides actual pole degree. |
| T2 | `Astra01.EllipticPointDivisor.full_agreement_set_bound` | Complete agreement subset of the actual cyclic group, including simultaneous poles; bound min(n,D(r+1)). |
| T3 | `Astra01.EllipticPointDivisor.full_menu_agreement_set_bound` | Fixed finite family of reduced nonconstant maps; complete union of agreement subsets bounded by min(n,D·Σ(r_j+1)). |
| T4 | `Astra01.pgl_cyclic_subgroup_recurrence` | Actual finite field extension and actual PGL quotient element; odd prime cyclic order; nonconstancy and recurrence only on the cyclic subgroup. Proves injectivity, exact PGL order, field alternatives and extension-degree divisibility. The function is presented on the ambient group and restricted to that subgroup. |
| T5 | `Astra01.prime_full_group_pgl_recurrence_constant` | p prime ≥17, actual full elliptic group over ZMod p of prime cardinality n≠p, nonzero G, arbitrary projective function and actual base-field PGL element. Every full recurrence forces the function constant. Hasse, point order and full-group generation are derived. |
| T6 | `Astra01.prime_recurrence_injective` | Arbitrary deterministic map, prime-length closed orbit, nonconstancy within the first n entries; all n values are distinct. |
| E1 | `Astra01.SharpnessActual.geometric_exact_count` and `geometric_exact_indices` | Actual F11 curve/group and faithful base change, degree(x)=2, exactly four agreements at 1,6,8,9. Actual count and generator order 13 are separately proved. |
| E2 | `Astra01.SharpnessActual.base_field_cover_minimum` and `base_field_four_cover` | Literal F11 arbitrary reduced degree-one menus require at least four members; the displayed four maps cover. |
| E3 | `Astra01.CharacteristicSeven.characteristic_seven_global_example` | Concrete F7 curve, degree-three y semiconjugacy; actual point order three and curve count twelve are separately proved. |
| E4 | `Astra01.EllipticDuplication.exponential_degree_linear_doublings` | Characteristic different from two; actual pole degree 2·4^t, actual projective value x([2^t]P), and the specified recursive evaluator charges exactly t point doublings. |

Exact source statements and proof dependencies take precedence over this summary. See [semantic coverage](lean/SEMANTIC_COVERAGE.md) and the source files listed there.

The universal Semaev factorization and denominator-cleared addition/duplication identities in K1 are also checked. The examples provide the mathematical counterexamples behind F1–F3. No claim is made to have re-executed the original experimental scripts or independently reproduced all reported sampled-test histories.

## Trust and reproducibility

The package pins Lean 4.32.2 and Mathlib commit `905b95818eb32af7874a58b427f50c1711a5e96c`. All 113 local proof modules were rebuilt from source into a fresh object directory in the final successful audit (535.05 seconds; peak sampled RSS 3346960 KiB), while pinned upstream dependencies were cached. No compiled objects or caches are distributed. The build record, source checksums, successful logs and printed transitive axiom closures are in `lean/`.

The permitted reported axioms are `propext`, `Classical.choice` and `Quot.sound`. The local source contains no admitted proofs, custom axioms or native-evaluation proof shortcuts. Selected endpoints were separately replayed with the same trusted compiler/dependencies. This is independent re-execution within the verification work, not outside expert peer review.

The [reproduction instructions](lean/LOCAL_REPRODUCTION.md) distinguish the audited cached-dependency workflow from an untested clean online provisioning workflow. Apache-2.0 attribution is retained for reviewed adapted divisor foundations.

## Remaining boundaries

- The curve/function-field formulation uses genuine nonsingular Weierstrass models. A scheme-level theorem transporting every abstract elliptic-curve presentation into this model is not supplied.
- T3's uniform-probability restatement follows from its finite cardinality bound; there is no separate probability-space API wrapper.
- E4 uses an explicit group-operation cost model, not a bit-complexity or general circuit lower bound.
- The source's U1–U5 algorithmic, complexity, sufficiency and novelty claims remain unproved or unestablished. No cryptographic attack or faster solver is supplied.
- Outside expert peer review and the original experimental execution histories are not certified by these Lean artifacts.
