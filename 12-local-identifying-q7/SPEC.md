# Q7 exact-24 semantic and specification audit

Date: 2026-10-13. Read-only source review; no Lean invocation or modification of existing sources, objects, receipts, or running builds. Newly created audit files only.

## Verdict

No substantive specification gap, hidden code restriction, vacuous endpoint condition, missing top-level classification branch, or circular final-bound premise was found in the inspected definitions and reduction interfaces. The exported result genuinely concerns every Boolean subset of the 128 vertices of Q7, with closed-neighborhood domination and distinct closed-neighborhood code traces for **all adjacent pairs**, including selected endpoints. The 24-word witness independently passes this exact predicate.

This is a semantic/interface audit, not a substitute for the independent kernel rebuild. The initial kernel acceptance and axiom output are supporting evidence, not the sole basis for this conclusion. The subsequently completed independent rebuild is documented in INDEPENDENT_VERIFICATION.md. Historical priority remains unconfirmed.

## Sources and identity

Paths below are relative to `source/`; a bare canonical filename means `Q7Mod/Canonical/<filename>.lean`.

- `CubeSemantics:10–26`: `Vertex d = Fin (2^d)`, `Code d = Vertex d → Bool`; vertices are `List.finRange`, adjacency is XOR by exactly one power of two below d, closed neighborhoods add equality, and cardinality filters the entire vertex list. `LocalIdentifying` requires domination and `∀ u v, adjacent u v = true → signature C u ≠ signature C v`. No linear, symmetry, or endpoint-membership hypothesis occurs.
- `CubeSemanticsBridge:32–80` connects this exact Boolean predicate to the generic Prop-valued graph predicate through full trace-function equality. `IsolateSurgery:40–41` also quantifies over every edge; its selected-K2 exclusion at lines 98–105 explicitly uses the selected-selected edge. Thus similarly named predicates are bridged rather than silently substituted.
- `Q7Mod/Integration/ExactQ7:10–26` exports the original universal lower bound and the existential size-24 witness. `ExactQ7Audit:8–15` type-ascribes the complete conjunction with fully qualified original names. The final integration sources were checked byte-for-byte against the frozen source manifest.

## Lower-bound chain and completeness

1. **Independent Q6 numerical base.** `Q6CoverSemantics:278–285` derives normalization and a classified profile for any dominating `Code 6` of size at most 11. `Q6CoverLowerBound:172–202` exhausts all 20 profile alternatives and proves `∀ C : Code 6, Dominating C → 12 ≤ cardinality C`. It does not assume the desired Q7 bound. `Q7ParityTransfer:128–155,195–213` turns each Q7 total-dominating parity half into a Q6 closed-dominating code and proves exact cardinality addition. `Q7TotalDominationBound:12–14` therefore supplies 24 for total domination, a different predicate proved sufficient only after surgery.

2. **Actual isolate count.** `Q7IsolateCount:25–46,99–123` defines selected isolates and equates the Boolean test with the graph predicate; counting uses duplicate-free vertices. Its share calculation gives `384 + 6 * isolateCount C ≤ 19 * cardinality C` at lines 360–364. Lines 371–374 yield at most eight total original isolates under size ≤23. This bound, not a hypothesis of restricted input codes, controls all later families.

3. **Arbitrary C5 obstruction.** `Q7C5Normalization:132–170` normalizes an arbitrary injective induced distance-two C5 by XOR and coordinate permutation, preserving exact cardinality, local identification, and the five selected isolates. `C5CNFTransfer:25–50` retains all original 128 membership bits and constructs a satisfying extension of the exact frozen CNF from any size≤23 code containing those five isolates. There is no assertion that these are all isolates. `C5SemanticBridge` constructs graph, isolation-unit and totalizer satisfaction; `C5Mod/Canonical/FormulaEquality` proves full clause-list equality, not merely equal hashes/counts. `C5Mod/Canonical/ExactUnsat:13–20` composes that equality, semantic equivalence, and the actual refutation. The apparent import of conditional Q7 assembly here is for its explicitly defined `ExactC5Unsat` proposition, not a use of the final lower bound.

4. **Full C7 branch.** `Q7C7EightNumerical:55–98` starts with any seven same-parity selected isolates inducing C7. Under size≤23 it derives the side bound ≤8. If there is no extra side isolate, the seven-cycle family is complete; otherwise adding any extra vertex gives exactly the whole side by injectivity and cardinality. Completeness is constructed internally. `Q7C7EightExclusion:69–132` also proves that an eight-point side exhausts all isolates, then splits on multiple-neighborhood count ≤18 versus >18. The first branch is numerically impossible; the second constructs a repair and invokes the independent total-domination bound. No failed-repair or complete-family premise survives the wrapper.

5. **Remaining small families.** `CubeFamilyLabeling:20–61` labels every selected vertex injectively and completely. `familyGraph_berge` derives the exact finite exclusions C5, C7, and seven-antihole, using the geometric seven-antihole theorem. For ≤8 vertices these cover the required odd-hole/antihole cases; C5 is self-complementary. `BergeEightTransport` explicitly handles complement/padding and defines a clique cover as a total label map. `BergeEightIndependentMaximum` derives a maximum independent tuple from finiteness and treats the empty graph separately. `BergeEightFamily` handles k=8 directly and k=1,…,7 by exact cores; `BergeMod/Canonical/CoreFamily` supplies all seven refutations. `Integration/FiniteBergeCover` discharges the finite-cover proposition.

6. **Tetrahedra are not omitted.** `CubeCliqueRepair:193–203` splits on containing a noncentered four-clique. `GlobalTetrahedronAdapter:13–17` supplies the full arbitrary-placement result. `FullTetrahedronRepair:20–39` normalizes any same-parity support of size≤8 and transports the repair back. `CanonicalSizeEightRepair` derives the exact outside-list decomposition. `CanonicalListRepair:32–84` covers attached supports of size≤6, attached supports with three/four outside points, and disconnected supports. The final input is not merely a canonical-placement or size≤5 result.

7. **No collision or sequential-repair shortcut.** In the non-tetrahedral branch, `CubeCliqueRepair:128–180` uses an injective independent tuple to remove exactly k points and at most k distinct clique centers to cover the family. Center collisions improve the budget; they are never counted as distinct without proof. `ParityRepairAssembly` combines both repairs against the original code with Boolean union. It proves hitting, covering and the sum budget, then applies one simultaneous all-isolate surgery. `SurgeryCardinality:27–54` proves the counting inequality pointwise even when retained/added sets overlap. No preservation of local identification after surgery is required or asserted; total domination suffices.

`Q7GlobalAssembly:62–80` combines these ingredients after the exhaustive case split size≤23 versus ≥24. The three explicit inputs (exact C5 UNSAT, finite Berge cover, full tetrahedral repair) are all supplied by the final integration; no final-bound hypothesis remains.

## Independent witness check

`checks/check_witness.py` reads the actual list from `LocalQ7W24Base:11`, then defines signatures independently as `{c in C : popcount(v XOR c) ≤ 1}`. It checks all vertices and every unordered edge without restricting selected endpoints.

Result: 24 distinct words, 128 dominated vertices, 448 separated unordered edges (896 directed). Edge classes: 300 with zero selected endpoints, 128 with one, 20 with both. No failure. For example the selected-selected edge 0–1 has signatures {0,1,2,64} and {0,1}. Machine-readable output: `checks/WITNESS_CHECK.json`.

## Trust and limits

The final independent receipt/log reports only `propext`, `Classical.choice`, and `Quot.sound`, the standard Lean foundations used here. A broad source scan found no declared custom `axiom`, `sorry`, `native_decide`, `implemented_by`, or `unsafe` in this closure (matched explanatory comments only). This text scan is supporting evidence, not a parser/kernel audit.

`ExactQ7Audit:18–22` intentionally sees `.axiomInfo` for the body-hidden imported public interface. That check alone cannot establish trust: it must be paired with verification of the defining theorem's checked private body and coherent dependency closure. The actual final source contains a theorem proof, and the supplied final receipt records its standard-axiom dependency list. The completed independent rebuild of the full closure provides the stronger check against stale or mismatched objects. This audit did not execute Lean, rederive every finite enumeration/refutation, audit Lean itself, or certify novelty. Some source comments still say “source-only” or “unfinished”; the final supplied theorem terms, rather than those stale status comments, determine the mathematical scope.
