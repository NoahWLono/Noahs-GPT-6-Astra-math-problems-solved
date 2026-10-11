# Independent novelty review of Research Note #6

Reviewed 11 October 2026. Scope: manuscript.tex and CLAIMS.md, with targeted primary-source comparison. This review concerns historical novelty and scope, not a new execution of the package or a formal proof check. The manuscript and claim ledger were not modified.

## Bottom line

The paper is not a novel solution to ECDLP: it supplies no new ECDLP-solving algorithm at all. It gives a narrow obstruction to a proposed one-coordinate, low-degree recurrence approach, together with examples delimiting that obstruction. Its mathematical arguments can be useful and correct without establishing historical priority.

The current record supports describing it as an independently checked exposition/research note with explicit finite certificates. It does not support calling T1–T6 a verified new mathematical discovery. T3, T4's classification input, T5's deduction, T6, and E4 are particularly elementary or directly established material. T1–T2's exact packaging and the specific E1–E3 certificates have no demonstrated priority, but neither has an exact prior occurrence of every sentence and numerical example been established by this review. These are different statements.

## Claim-by-claim assessment

### T1: Global identity implies deg(R)=1 and n divides deg(f)

The two steps are standard mechanisms: multiplicativity of morphism degree, then a fixed fiber divisor invariant under a free order-n translation action. Every orbit in that divisor has n points with constant multiplicity, so its degree is divisible by n. Milne's author-hosted text supplies the fiber-degree fact in Remark I.4.26 and the projective-line automorphism facts in Remark I.5.4. [Milne, Elliptic Curves](https://www.jmilne.org/math/Books/EC2.pdf).

Assessment: a concise application of classical curve theory. The proof's treatment of multiplicities and arbitrary characteristic is worth retaining. I have not located a source stating precisely this lemma with precisely these hypotheses; that is not evidence that it is historically new. Do not label it a new ECDLP obstruction theorem merely because it is independently derived.

### T2: Agreement bound min(n,D(r+1))

For distinct maps, this is the usual coincidence-divisor bound with degrees D and Dr. T1 handles the exceptional identical-map case, where the asserted subgroup bound becomes trivial. The useful feature is an explicit projective treatment of poles and a global-identity exception, rather than a new zero-counting mechanism.

Close recurrence literature is genuinely relevant but should not be overstated. Mérai–Winterhof study the same sequences f(nG), but their target is linear complexity of multi-step linear recurrences, with conditions on poles and an Edwards-curve formulation. Their Theorem 1, Lemma 1, and proof use nonconstancy and degree/zero counts. Section 3.1 describes Hess–Shparlinski's earlier restricted pole-divisor hypothesis and linear-complexity bound. These are methodological and subject-matter precedents, not an exact theorem identifying every arbitrary one-step rational R in T2. [Mérai–Winterhof, §§3.1 and 4](https://arxiv.org/pdf/1509.06909).

Assessment: a broader-in-one-direction reformulation of standard degree reasoning, with nearby established recurrence work; exact formulation priority remains unestablished. It does not imply that every result of the earlier multi-step recurrence papers is subsumed.

### T3: Fixed finite menu

This is the cardinality union bound applied to T2. Arbitrary branch choice does not increase coverage beyond the union. Its probability restatement simply divides by n for a uniform independently drawn point.

Assessment: useful corollary, not evidence of an independent new mathematical principle. Its fixed-family quantifier should stay explicit. It does not analyze adaptive construction of unbounded menus or the cost of selecting a branch.

### T4: Möbius field condition

Garion's primary paper explicitly lists the PGL2 finite-field element types and orders: unipotent order p, split order dividing q−1, and nonsplit order dividing q+1 (§2.2, Table 1, PDF p. 8). Substituting q^k gives exactly the manuscript's three alternatives. The manuscript's prime-cycle argument identifies the recurrence's order with n; ord_n(q) dividing 2k is an immediate modular consequence. [Garion, On Beauville structures for PSL2(q)](https://arxiv.org/pdf/1003.2792).

Assessment: an application of standard group theory to recurrence language. The field threshold does not construct an efficiently evaluable coordinate or solve an orbit-index problem. It cannot be presented as a new pairing transfer or an ECDLP algorithm.

### T5: Cofactor-one prime-field consequence

This is T4 plus Hasse and parity. For p≥17, Hasse yields n≥p+1−2√p>(p+1)/2. An odd prime divisor n of either even integer p−1 or p+1 is at most (p+1)/2. The only remaining T4 case is n=p, expressly excluded. Hasse is standard; the displayed inequality and divisibility deduction are elementary. The assumptions of full prime group order, not merely a prime subgroup, are essential.

Assessment: potentially a convenient stated corollary, but no nontrivial new ingredient is identified. An exact matching prior citation is not required to recognize the deduction as elementary; conversely, elementary does not logically prove prior publication of the identical statement.

### T6: Prime cycle injectivity

A deterministic periodic orbit has least period dividing n. With n prime, a nonconstant orbit therefore has period n and n distinct states.

Assessment: standard finite dynamics. No elliptic-curve geometry, rational-map hypothesis, or new theorem is needed.

## Sharp examples and their limits

### E1: Four matches for D=2 over F11

This finite certificate proves that a proposed universal 2D−1 replacement fails: one counterexample suffices. It does not prove equality is attainable for every D, every subgroup order, or every curve. The manuscript correctly avoids that stronger claim.

The exact numerical example may have been newly generated during the research session. That establishes provenance of this computation, not historical priority or a significant new structural theorem. This pass did not rerun its arithmetic; other correctness checks must establish the certificate.

### E2: Four-branch exact cover

The lower bound is ceil(13/4)=4 using T2; the displayed four-map witness supplies the upper bound. The exact-cover certificate is a concrete combinatorial illustration. No efficient selector is exhibited and no ECDLP solver follows. An independently generated tiny instance can be worthwhile exposition without establishing a new general result.

### E3: Degree-three global semiconjugacy

The example correctly guards against the overly strong claim that global semiconjugacy is always impossible. Its formula is not an isolated mysterious construction. Direct substitution into the standard addition law gives, for the nonsingular family y²=x³+b² in characteristic other than 2 or 3 and b≠0, with G=(0,b),

    y(P+G) = b (y(P) − 3b) / (y(P) + b).

This is my algebraic observation from the usual chord-and-tangent formulas, not an assertion that I located a publication of this exact formula. On the dense open set, the slope is (y−b)/x; substituting x³=(y−b)(y+b) yields the displayed expression. Equality then extends as rational morphisms. Setting b=1 and reducing modulo 7 recovers E3.

Assessment: a useful elementary illustration within a standard special elliptic-curve family, with no established priority. It does not satisfy T5's full prime-order-group hypothesis and so is not a counterexample to T5.

### E4: Large degree, short evaluation

Composition of multiplication-by-2 maps gives degree 4^t; composing with x gives 2·4^t, while evaluation uses t doublings. This is standard multiplication-map theory and ordinary straight-line evaluation. [Milne's author-hosted text](https://www.jmilne.org/math/Books/EC2.pdf).

Assessment: explicitly established material, correctly used to prevent an invalid inference from algebraic degree to runtime. It undermines an alleged ECDLP runtime lower bound rather than supplying one.

## Access limits and historical inference

Fresh access to the Hess author-hosted PDF failed through the web tool. A subsequent read-only download attempt was cancelled by the approval reviewer; it was not retried. I therefore did not independently reread Hess Lemma 1 in this pass. Its scope above is grounded in Mérai–Winterhof's primary-paper account, while the supplied manuscript reports its own earlier direct inspection. Do not conflate those provenance levels.

Primary texts actually inspected here: Mérai–Winterhof arXiv:1509.06909, Garion arXiv:1003.2792, and relevant parts of Milne's author-hosted book. The search was targeted, not exhaustive. No historical claim rests on a failed exact-phrase search. No outside expert review or priority certification occurred.

## Recommended wording

“This note gives a self-contained, pole-aware derivation of degree and finite-field obstructions to a specified rational-recurrence model of elliptic-curve translation, with concrete sharpness and boundary examples. Its ingredients are largely classical, and historical novelty of the precise formulation or examples has not been established. It does not provide a new solution to ECDLP.”

For a scholarly submission, first add the explicit PGL2 comparison, distinguish the one-step rational formulation from the earlier multi-step linear-complexity results, and obtain expert assessment of whether the formulation or certificates add sufficient value. Do not convert successful finite checks into a novelty claim.
