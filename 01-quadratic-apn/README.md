# 01 — Quadratic APN functions in dimension eight

**Status: Completed and verified (9 October 2026).**

## The result

Every quadratic APN function f: F₂⁸ → F₂⁸ has at least **33 non-bent nonzero scalar components**. There are 255 nonzero masks, so at most 222 of these components are bent.

Quadraticity means that the normalized polar f(x+y)+f(x)+f(y)+f(0) is bilinear. Constants and linear terms are allowed. APN means every nonzero-direction derivative fiber has at most two points. Bentness is expressed using the actual integer Walsh transform, not a rank proxy.

The final function-level Lean theorem is:

`APNRedo.quadratic_apn_function_nonBent_count_ge_thirty_three`

It has only the quadraticity and APN hypotheses. No unproved classification, spectrum, rank, incidence, or support-normal-form assumption remains. The theorem does not establish an attaining example or a new APN construction.

## Contents

- [Formal proof and reproducible build](lean/README.md)
- [Endpoint source](lean/APNEightFinal.lean) and [statement/axiom inspection](lean/APNEightFinalAudit.lean)
- [Verification scope and current status](verification/README.md)
- [Full mathematical paper (PDF)](paper/apn-eight-bound.pdf), [editable LaTeX](paper/apn-eight-bound.tex), and [paper build instructions](paper/README.md)
- [Archived known extremal family](archive-known-extremal-family/README.md)

The proof consists of 136 modules in the actual endpoint dependency closure, plus one endpoint inspection module. The build imports no archived-family files: all needed dependencies are included in the new `lean/` tree.

## Proof outline

The singular-component indicator has Boolean ANF degree at most four, includes the zero mask, and has weight one greater than the non-bent component count. APN incidence forces that count to be 1 modulo 4. A proved low-weight residue theorem gives indicator weight at least 30. The proved specialized weight-30 classification, together with APN rank geometry and the affine half-rank obstruction, excludes component count 29. The next permitted count is 33. Checked quadratic/Walsh semantics transfer the statement to arbitrary functions with bilinear normalized polar.

## Verification and limits

The author-side final theorem build passed with Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. A separate isolated source rebuild of all 136 local proof modules passed on 9 October 2026. The [audit report](verification/AUDIT.md) records its scope and evidence. The additional endpoint-inspection module also passed against those fresh outputs. The portable publication wrapper has a five-module smoke test; that is distinguished from the complete independent audit.

Standard Lean axioms at the endpoint are `propext`, `Classical.choice`, and `Quot.sound`. Formal checking verifies the theorem; the literature evidence is summarized separately below.

## Literature review

The excluded i = 3 amplitude profile, [0^226, 2^15, 4^14], was explicitly still open in Beierle et al., *Millions of inequivalent quadratic APN functions in eight variables*, revision dated 27 August 2026, §5.1. The literature recheck completed on 9 October 2026 found no earlier proof of this exact exclusion in the sources checked. This is a bounded finding, not an absolute priority guarantee. The established Pfaffian, Reed–Muller, and APN ingredients are credited in [the paper’s prior-art discussion, §1.2](paper/apn-eight-bound.pdf#page=4), which identifies the additional affine rank obstruction and its application.

## Earlier family archive

`archive-known-extremal-family/` preserves the latest published package with its internal layout and all 1,954 files, including the collection README revision. It concerns a known construction in dimensions divisible by four, with a Jha–Johnson cyclic-semifield correspondence. It is not an APN result. Its original papers and recorded proof replays remain available for reference. The archived collection README is a historical snapshot and its research-status text is superseded by this problem README.
