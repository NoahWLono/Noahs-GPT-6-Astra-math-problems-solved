# Independent audit: local 1-identifying codes in Q6

## Result

**PASS, exact certificate level: the minimum is 14 for the definition below.**
The explicit size-14 code passes an independently implemented exhaustive check. The size-at-most-13 instance has an exact contradiction certificate verified both by a new standard-library Python RUP checker and by the official `lrat-check` program. The reduction from the graph problem to that instance is checked separately, including a symbolic satisfying extension for every possible small code. No floating-point optimization conclusion is used in the lower bound.

This exact-certificate audit does not establish novelty or publication readiness. The subsequent independent Lean replay and clean-build audit, recorded in `LEAN_REPLAY_AUDIT.md`, now also verifies the full lower bound through the ordinary Lean kernel.

## Definition and source scope

Herva–Laihonen–Lehtilä, *Optimal local identifying and local locating-dominating codes*, journal PDF <https://fi.episciences.org/13881/pdf>, Definition 1.3, printed page 353: a local 1-identifying code dominates **all** vertices and has different closed-neighborhood code intersections at every pair of adjacent vertices. In particular, adjacent code vertices are included. Restricting separation to non-code vertices would instead concern the local locating-dominating notion.

The same paper's Table 1 (printed page 358) lists 12–16 for Q6, but Proposition 2.9 (printed page 362) explicitly proves the stronger upper bound 15. The arXiv v3 HTML renumbers this as Proposition 2.15: <https://arxiv.org/html/2302.13351v3#S2.SS3>. I independently checked its 15-word witness as well. Any comparison should use the located bound 15 rather than the table's stale 16. The literature search is a separate task and this audit makes no priority claim.

## Upper-bound check

Represent vertices by integers 0 through 63, with adjacency defined by Hamming distance one. The code is

`{0,4,15,23,26,29,31,33,35,36,41,49,58,62}`.

`independent_witness_check.py` constructs closed balls using the Hamming-distance predicate independently of the producer's bit-flip routine. It checks all 64 nonempty signatures and all 192 unordered cube edges, recording a separating codeword for each edge. This includes 10 code–code edges and 74 edges with at least one code endpoint. Signature cardinalities are 38 of size one, 20 of size two, four of size three, and two of size four. Exact output is in `independent_witness_results.json`.

## Reduction used for the lower bound

For vertex v, let x_(v+1) indicate membership in C. The first 64 clauses require a selected vertex in each closed ball. For each of the 192 unordered edges uv, require a selected vertex in N[u] symmetric-difference N[v]. This is equivalent to distinct signatures because

`(N[u] intersect C) symmetric-difference (N[v] intersect C) = (N[u] symmetric-difference N[v]) intersect C`.

The next unit clause requires x_1, that is, vertex 0 in C. This loses no potential solution: domination makes C nonempty; translation by any member c of C maps C to a code containing 0, preserves cardinality and all Hamming distances, and preserves this definition.

`independent_encoding_check.py` reconstructs these exact 257 clauses from the Hamming-distance definition and compares them in full against `exclude13.cnf`.

### Auxiliary encoding: explicit extension, not a library assumption

The remaining 1,364 clauses use 663 auxiliary variables. The independent check infers and verifies a bijection from them to symbols s(i,j), where `1 <= j <= 13` and `j <= i <= j+50`. It then checks that every actual clause has exactly one of these four forms:

* 51 input clauses: `not x_i or s(i,1)`;
* 650 monotonicity clauses: `not s(i,j) or s(i+1,j)`;
* 612 increment clauses: `not x_(i+1) or not s(i,j) or s(i+1,j+1)`;
* 51 overflow clauses: `not x_(i+1) or not s(i,13)`.

For **every** assignment of the original variables with total at most 13, set s(i,j) true precisely when the prefix x_1 through x_i contains at least j true variables. Input, monotonicity and increment clauses then hold by counting. An overflow clause could fail only if the prefix already contained 13 selected vertices and the next input were also selected, contradicting the total bound. Thus every hypothetical code of size at most 13 extends to a model of all auxiliary clauses. This direction alone suffices for the lower bound; it avoids trusting the SAT library's encoding implementation or needing the reverse implication.

## Exact contradiction verification

Input: `exclude13.cnf`, 727 variables, 1,621 clauses.
Certificate: `exclude13.lrat`.

`independent_lrat_check.py` is an independently written standard-library-only checker. It maintains the active indexed clauses, honors deletions, and requires every added clause to have a reverse-unit-propagation contradiction under its negation. It accepts only positive LRAT hint IDs, so no RAT reasoning is hidden in this check. Each cited clause must be unit or conflicting under the current assignment. The checked derivation reaches the empty clause. The checker imports no SAT library and does not call a solver or the official checker.

Result: **343,158 additions; 8,592,222 hints; 344,702 deletions; exact RUP verification passed.** The independent official `lrat-check` invocation also reports `VERIFIED` (log: `independent_official_lrat.log`).

SHA-256 identifiers:

* CNF: `ec2ade9e14fcc744150cf36405a5502f13729e185875f166d2ec6b6c8a5f3762`
* LRAT: `7c828a1133cd93f31a6d602a254e4086d1d8744e4f1e362bc282565e7b665eb6`

The complete inference is: a smaller code translates to one containing 0; its indicators satisfy the graph clauses and extend by prefix counts to the auxiliary clauses; this contradicts the checked unsatisfiability proof. Together with the size-14 witness, the minimum is therefore 14, subject to the ordinary trust boundary of these exact software checks and the audited elementary reduction. The subsequent separate Lean development and clean rebuild have now passed; see `LEAN_REPLAY_AUDIT.md` for the precise kernel trust boundary and verified final theorem.

## Reproduction

From this directory:

```
python independent_witness_check.py
python independent_encoding_check.py
python independent_lrat_check.py exclude13.cnf exclude13.lrat
/tmp/q6-drat-trim/lrat-check exclude13.cnf exclude13.lrat
```

The initial audit above used the larger certificate. The smaller path certificate was subsequently independently audited as detailed below.

## Addendum: smaller path-normalized certificate

The main conclusion above does not require this alternative, but the smaller certificate also has a justified normalization. Every local identifying code of size less than 16 contains an induced-code vertex with at least two code neighbors. Indeed, if every induced degree is at most one, any code edge would form a K2 component whose endpoints both have signature consisting of its two vertices, violating separation. Thus the code would be independent. Every outside vertex must then have at least two code neighbors: zero violates domination; one gives the same singleton signature as its unique (isolated) code neighbor. Counting edges between code and complement gives `6|C| >= 2(64-|C|)`, hence `|C| >= 16`, a contradiction.

For a code of size at most 13, take a vertex with two code neighbors, translate its center to 0, and permute coordinates so the two neighbor directions are bits 0 and 1. The resulting code contains `{0,1,2}`. This justifies precisely the three unit clauses `[1],[2],[3]` in `exclude13-path.cnf`. An independent comparison checked that all other graph clauses equal the audited graph clauses as a multiset and all counter clauses agree exactly with the main instance. No stronger structural assumption is needed.

The same independent RUP checker verifies the smaller certificate; output and hashes are in `independent_path_lrat_results.json`. This shorter route may help formalization, but does not by itself resolve Lean resource limits.

## Compact distribution reproduction

The compact release retains the original `exclude13.cnf` for the independent encoding comparison, but omits the larger original LRAT proof. The original-proof verification record above is historical evidence from the research workspace, not a command guaranteed to run from the compact archive. The release supplies the fully audited smaller path certificate in compressed form. From the compact release root, run:

```
python materialize_certificates.py
python independent_witness_check.py
python independent_encoding_check.py
python independent_path_encoding_check.py
python independent_lrat_check.py exclude13-path.cnf exclude13-path.lrat
python independent_replay_data_check.py
```

The path normalization argument above establishes the same lower bound. The release's materialization helper verifies the expected hashes while decompressing the supplied certificates. The official external `lrat-check` is optional additional verification and is not assumed to be installed at the research workspace's `/tmp` path on another machine. Lean reconstruction is covered by the release's `REPRODUCIBILITY.md` and clean-build harness.
