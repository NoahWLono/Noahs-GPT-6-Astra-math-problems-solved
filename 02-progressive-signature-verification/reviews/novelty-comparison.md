# Independent novelty/comparison/attribution review

2026-10-09, 22:28 UTC. Reviewed `short-private-pools.tex`; mathematical and visual audits are separate. No publication performed.

## Decision

Contribution/attribution: PASS, subject to the specific comparison wording edits below. The paper consistently identifies the modest combined compiler contribution and credits known conditioning, sampling, preprocessing and refresh. The finite ideal-sampling scope, source-security separation, conservative denominator, RNG/write bursts and coordinate-only memory accounting are substantively present. No new exact prior-art match was found. This review does not independently repeat the clean Lean build.

## Required edits before release

### 1. Make the comparison table's confidence slack explicit

At current lines 330–339, `Target confidence 1-2^{-b}` obscures that the pool bound is `2^{-b}+epsilon`, where epsilon<2^{-222}, whereas the displayed RS thresholds are exact. The returned nominal confidence is indeed 1−2^{-b}, but the table must not silently present a strict equal-error comparison.

Change the heading to `Nominal confidence 1-2^{-b}, b` and add immediately below: “For the pool, these are the main-term confidence levels: its certified invalid-acceptance bound is 2^{-b}+epsilon with epsilon<2^{-222}. The RS and terminal bounds meet the same error target with this slack. The comparison does not assert an exact pool error cap of 2^{-b}.”

At current line314, replace “first six confidence levels” by “first six nominal confidence levels, with the explicit additive history term”. Alternatively give all methods the common target error 2^{-b}+epsilon explicitly.

### 2. Disclose a smaller terminal block, and avoid suggesting a terminal frontier

The stated seven-row comparison is mathematically valid, but it is a chosen high-confidence block. It is not the best terminal block for weak confidence targets. The same proof already given in §8.1 yields `(Q+1)/q^3<2^{-25}` for Q<=2^64 and q=1073741789. I checked the equivalent integer inequality exactly. Thus three complete rows suffice for each of the first six weak targets, although they do not reach the chosen 128-bit terminal target.

Replace “a deliberately strong comparator” with “a fixed high-confidence terminal comparator”. Rename the table row “Fixed seven-row high-confidence block”. Add this paragraph:

“A terminal verifier configured only for weaker assurance can use fewer rows. In this example, a three-row block has error below 2^{-25} for the same lifetime bound and costs 3d products online. Therefore the first-six comparison is specific to the fixed seven-row high-confidence block, not a frontier over all terminal configurations. Against the three-row block, the pool's initialized average-product advantage survives at the first two nominal checkpoints. A staged combination of independently keyed terminal blocks is another comparator worth considering; no optimality over such constructions is claimed.”

The three-row numerical observation is a direct consequence of the paper's own baseline proof, not a newly quoted prior theorem and not part of the existing Lean certificate unless separately added. An independent three-row early block followed by an independent seven-row full block also prevents assuming that the low-confidence comparator necessarily lacks any high-confidence extension. No detailed new staged security theorem is needed if it is only identified as an excluded alternative, rather than claimed to be fully analyzed.

This does not invalidate the short-bank theorem or the precise seven-row inequality. It narrows the interpretation of the utility example. The first1–2 checkpoints still use less than3d average products at N>=R, and the source-backed novelty assessment remains intact.

### 3. Narrow the abstract's accounting verb

Current abstract says “charge actual initialization, incremental matrix preparation, buffer promotion and the final invocation.” Readers can reasonably take this to include all initialization and promotion work, despite later exclusions.

Replace with “account for field arithmetic in initialization, incremental matrix preparation, and the final invocation across actual buffer promotions”. Keep the adjacent sentence denying whole-resource superiority. Add `provided L+s<q` to the abstract's tail statement.

## Attribution/bibliography checks

- BFP's five-author 2024 journal citation matches the primary version of record and its §8.3 construction. No correction required.
- Banegas–Le Dévéhat–Smith: arXiv currently lists only v1 dated3September2025 and CANS2025 as the publication reference. The cautious existing bibliographic wording is accurate. Its §3.4 excluded-key attribution is appropriate. Source: https://arxiv.org/abs/2509.03098 .
- Nguyen–Roscoe: the ePrint record identifies the paper as a long version of FCS-ARSPA-WITS2008, latest revision28November2009. Improve the bibliography to “FCS-ARSPA-WITS2008; extended version, Cryptology ePrint2009/003 (revised28November2009)” rather than making the concept appear to originate only in2009. Source: https://eprint.iacr.org/2009/003 .
- TV code sampling and Slalom's layer-level reusable checks are correctly distinguished from this experiment. No need to imply that Slalom proves unrestricted repeated-session security.
- The restrained “to our knowledge ... primary statements reviewed” paragraph is defensible. No first-ever, universal polynomial-modulus, new primitive, or source-hardness claim needs removal.

## Release recommendation

Apply edits1–3, add the small bibliographic precision, and regenerate the PDF. Then the novelty/comparison/attribution review can pass without a broad new research gate. Preserve the separate math audit and frozen-source audit evidence. Do not enlarge the claim from the proved field-multiplication comparison to total work, latency or memory.

## Final revised-source decision: PASS

2026-10-09, 22:34 UTC.

Reviewed and hash-verified source: `short-private-pools.tex`

SHA-256: `b305c71785d72c8d91d585e738e9d9ba0cbe1e4570e19573c1fb7d0b1d608d33`

**PASS for novelty, comparisons, attribution, and resource scope.** This final decision supersedes the revision-required disposition above for this exact source snapshot. The earlier findings remain as the review history.

The revised source incorporates all requested corrections: explicit nominal-confidence/additive-error slack; the three-row terminal and staged-block alternatives; a first-two-only initialized average-product crossing against the shorter terminal block; narrowly stated field-arithmetic accounting with sampling and zero-fill exclusions; the abstract's field-margin hypothesis; and corrected Nguyen–Roscoe attribution.

The modest combined-compiler novelty claim remains defensible under the documented primary-source comparison. No remaining correction was identified in this review scope. Mathematical correctness, independent Lean build/axiom verification, and final PDF rendering are separately reviewed; this PASS does not replace those checks or authorize publication.
