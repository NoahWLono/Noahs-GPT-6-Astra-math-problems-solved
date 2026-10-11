# Claim ledger

The manuscript supplies written proofs of the stated general results. Finite checks corroborate them but are not a formal proof of the universal claims. Historical novelty is tracked separately from correctness.

## T1: proved analytically

A global identity f o tau_G = R o f forces deg(R)=1 and n divides deg(f).

**Assumptions:** Smooth projective elliptic curve over an algebraically closed field; any characteristic; G exact order n>=2; f and R nonconstant rational morphisms.

**Verification:** Complete divisor and degree proof in the manuscript.

**Historical novelty:** unestablished

## T2: proved analytically

The number of P in <G> satisfying f(P+G)=R(f(P)) is at most min(n,D*(r+1)).

**Assumptions:** As T1, with D=deg(f), r=deg(R)>=1; values interpreted in P^1 at poles.

**Verification:** Coincidence-divisor bound plus T1; exhaustive and sampled synthetic checks.

**Historical novelty:** unestablished

## T3: proved analytically

A fixed finite menu R_j covers at most min(n,D*sum_j(r_j+1)) points, even with arbitrary per-point branch choice.

**Assumptions:** Fixed coordinate and finite recurrence menu; degrees r_j>=1. Uniform-point probability corollary fixes the family before drawing the point.

**Verification:** Union bound applied to T2; exact tiny minimum-cover certificate.

**Historical novelty:** unestablished

## T4: proved analytically

For odd prime n, a nonconstant full Mobius recurrence over F_(q^k) has exact order n and requires n=p or n divides q^k-1 or q^k+1. For n!=p, ord_n(q) divides 2k.

**Assumptions:** H subset E(F_q), G exact odd prime order n, p=char(F_q), k>=1, any f:H->P^1(F_(q^k)) not constant on H, M in PGL2(F_(q^k)).

**Verification:** Finite orbit argument and explicit eigenvalue classification; prime-field PGL order checks.

**Historical novelty:** unestablished

## T5: proved analytically

For p>=17 prime and #E(F_p)=n prime with n!=p, no nonconstant full base-field Mobius translation recurrence exists, even for an arbitrary coordinate on the finite group.

**Assumptions:** The entire group has prime order, not merely a subgroup; f is nonconstant on that group.

**Verification:** T4 plus Hasse bound and divisibility/parity argument.

**Historical novelty:** unestablished

## T6: proved analytically

A nonconstant deterministic full recurrence on a prime-length cyclic orbit has n distinct coordinate values.

**Assumptions:** A sequence z_(i+1)=T(z_i), z_n=z_0, n prime, not constant. T need not be invertible.

**Verification:** The least period divides n.

**Historical novelty:** standard_finite_dynamics_fact

## E1: verified finite certificate

On E/F_11: y^2=x^3+x+6 with G=(2,4), f=x and M(z)=z/(z+5) agree at exactly d=[1,6,8,9].

**Assumptions:** Specified synthetic curve of order 13; arithmetic modulo 11, including infinity.

**Verification:** Primary exhaustive search and separate homogeneous-coordinate checker.

**Historical novelty:** unestablished

## E2: verified finite certificate

The same 13-point orbit needs and admits exactly four Mobius maps to cover all points under arbitrary branch selection.

**Assumptions:** Fixed f=x, maps over F_11. No efficient branch selector is claimed.

**Verification:** T2 implies at least ceil(13/4)=4; explicit four-map witness; exact DP and separate checker.

**Historical novelty:** unestablished

## E3: proved analytically and checked finitely

On y^2=x^3+1 over F_7, G=(0,1) of order 3 and f=y have global recurrence M(z)=(z-3)/(z+1).

**Assumptions:** Specified curve; f degree 3. The full curve has 12 rational points.

**Verification:** Symbolic reduction modulo curve equation and all 12 rational-point checks.

**Historical novelty:** unestablished

## E4: established identity with executed control

The morphism f_t(P)=x([2^t]P) has degree 2*4^t but can be evaluated by t point doublings.

**Assumptions:** Characteristic different from two; degree concerns the algebraic morphism.

**Verification:** Multiplication-map degrees and exact repeated-doubling controls t=1..8.

**Historical novelty:** not_claimed

## K1: established prior art rederived

The derived biquadratic addition relation is the third Semaev summation polynomial, not a new formula.

**Assumptions:** Short Weierstrass model, characteristic neither two nor three; displayed affine addition derivation excludes x(P)=x(G).

**Verification:** Exact symbolic identity, Galbraith Chapter 15 formula, and 724 finite checks.

**Historical novelty:** known

## F1: refuted

A universal bound of 2D-1 suffices for a single Mobius recurrence.

**Counterexample:** E1 reaches 2D=4.

## F2: refuted

Global rational semiconjugacy of elliptic-curve translation is impossible in all degrees.

**Counterexample:** E3 has D=n=3.

## F3: refuted as an inference

A degree lower bound by itself implies a comparably large arithmetic evaluation time.

**Counterexample:** E4 has exponentially growing degree and a linear-length doubling circuit.

## U1: unproved

A faster-than-generic classical ECDLP algorithm for ordinary cryptographic prime-order curves.

## U2: unproved

A general non-generic runtime lower bound for ECDLP.

## U3: unproved

An efficient construction and inversion of a useful high-degree compact rational coordinate or multivalued correspondence.

## U4: unproved

Sufficiency of the extension-degree condition for an efficient ECDLP reduction.

## U5: unestablished

Historical novelty of the assembled obstruction theorem or exact sharpness example.

## U6: not performed

Formal proof-assistant verification or external expert peer review.
