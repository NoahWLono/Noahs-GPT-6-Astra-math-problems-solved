# Prior-art comparison for the critical Euler limit

Date: 12 October 2026

Publication scope: the completed public results are the joint critical limit in explicit series form and the concrete sequence whose limit is strictly less than gamma. This bounded source-comparison record also mentions a broader quantitative analysis screened during the research; those estimates and the diverging-parameter regime are not included as completed results in this release. The Bessel expression below records classical analytic context, not a certified special-function identity. See the [paper](../paper/euler-critical-limit.pdf) and [verification record](../verification/README.md) for the exact formal scope. The [additional review](additional-prior-art-review.md) records later source screening and unresolved access gaps.

## Conclusion

The approximant family, its starting case, the differential-operator construction, and the harmonic-number Bessel identity all have identified prior art. The part requiring further originality assessment is the joint limit with growing iteration count and its explicit finite-sum error estimate. This focused screening did not identify a theorem in the checked sections that directly gives that joint limit or estimate. This is not evidence sufficient to claim novelty.

The result being compared concerns weights

\[
w_{n,p}(k)=\binom nk^2\binom{n+k}{k}^{p}/k!,\qquad
a_{n,p}(k)=(p+3)H_k-2H_{n-k}-pH_{n+k},
\]

and their weighted-average ratio. Its critical limit, for \(n^3 2^{-p}\to\lambda\in(0,\infty)\), is

\[
\gamma-2\frac{K_0(2\sqrt\lambda)}{I_0(2\sqrt\lambda)}.
\]

The quantitative comparison uses endpoint weights \(v_j=\lambda^j/(j!)^2\), the defect bound \(0\le 1-r_j/v_j\le(p+3)j(j-1)/(2n)\), and \(\varepsilon=(p+3)\lambda/(2n)\).

## What was actually checked

This was targeted full-text screening: theorem statements, relevant proof sections, and text searches. It was not an exhaustive page-by-page review or a complete citation search. The sources were the 2025 arXiv v3 HTML; the 2012 paper's 2010 arXiv v1 preprint; the 2011 paper's Russian 2010 arXiv v1 preprint; Rivoal's author-hosted manuscript dated January 2009; and the 2023 paper's arXiv v2. Final journal versions were not independently compared against those preprints. None of the five comparisons below relies only on an abstract.

## Van Assche and Wolfs 2025

Proposition 2.2 gives the exact \(p=0\) harmonic-number numerator and denominator. Section 5 explicitly gives the repeated operator \(T_nf=(x^nf)^{(n)}/n!\) and the same denominator \(\sum_k\binom nk^2\binom{n+k}{k}^{p}x^k/k!\). Thus the family itself is established prior art. The stated numerator follows by applying that operator to the logarithmic term.

Section 5 presents asymptotic ideas in \(n\) with the iteration parameter \(p\); it does not supply a uniform growing-\(p\) remainder in the checked text. Its fixed-parameter expressions cannot simply be evaluated at \(p=p(n)\). No endpoint Bessel limit or displayed \(\varepsilon\)-estimate was identified there. [Full text, Sections 2.1 and 5](https://arxiv.org/html/2404.09799v3).

## Hessami Pilehrood and Hessami Pilehrood 2012

Theorem 1 and Corollary 2 of the preprint give the family

\[
Q_n=\sum_k\binom nk^a k!,\qquad
P_n=\sum_k\binom nk^a k!\,[aH_{n-k}-(a-1)H_k].
\]

For \(a=3\), replacing \(k\) by \(n-k\) and dividing both sums by \(n!\) gives exactly the present \(p=0\) pair. For general \(a\), the similarly normalized weights are \(\binom nk^{a-1}/k!\), a different family from the present positive-\(p\) weights.

Theorem 1, Corollaries 1–2, and the saddle-point estimates in Sections 5–6 have constants explicitly depending on \(a\). They do not state uniformity for \(a=a(n)\). These checked results therefore do not directly imply the proposed growing-\(p\) theorem. [Full preprint, especially PDF pages 5–6 and 22–24](https://arxiv.org/pdf/1011.3833v1).

## Hessami Pilehrood and Hessami Pilehrood 2011

Theorem 1 treats approximations to \(\log b-\psi(a+1)\), with denominator \(\sum_k\binom nk^2(a+1)_{n+k}b^{n-k}\) and parameter-dependent asymptotics. Theorem 2 treats recursively iterated generalized Laguerre polynomials and proves denominator/integrality statements for arbitrary integer order \(s\).

This is relevant prior art for iteration and arithmetic control. An identity valid for every \(s,n\), however, is not itself a uniform asymptotic theorem as \(s\) grows with \(n\). No matching joint endpoint limit was identified in the checked theorem statements and associated sections. The paper uses a different polynomial/integral construction. [Full Russian preprint, Theorems 1–2, PDF pages 3 and 7](https://arxiv.org/pdf/1004.0578v1).

## Rivoal 2009

Section 4.2 defines generalized Laguerre polynomials recursively for every integer order \(s\). Theorem 1 and the detailed asymptotic analysis give rational approximation to \(\gamma+\log x\); the later sections work out higher-derivative simultaneous approximation. This establishes that varying the available iteration order is an old construction idea.

The checked asymptotic results concern fixed argument and specific approximation systems. The review did not identify a result controlling a growing number of iterations in the present finite binomial family, nor the critical \(n^3 2^{-p}\) scaling. Its general-order algebraic construction should not be confused with a growing-order error theorem. [Author's full manuscript, Theorem 1, Sections 4.2 and 6–9](https://rivoal.perso.math.cnrs.fr/articles/eulerconstant.pdf).

## Van Assche and Wolfs 2023

Section 4.2 supplies explicit type-I and mixed-type formulas, including Proposition 4.6 and the Rodrigues formula in Theorem 4.8. These underlie the later Euler-approximation construction.

There is genuine endpoint-related prior art here: Section 3.4.1, Proposition 3.6 proves a Mehler–Heine limit to a \({}_0F_2\) function, with degree split \(n_1/n,n_2/n\) tending to fixed proportions. Section 5 discusses related K-Bessel-weight systems and extensions to more weights. These are different limits and objects from the \(I_0,K_0\) ratio obtained by increasing the iteration count. They demonstrate established hypergeometric endpoint methods, but no direct implication of the proposed joint-limit statement was identified. [Full preprint, PDF pages 18 and 30–35](https://arxiv.org/pdf/2211.04858v2).

## Additional direct overlap with Brent and McMillan

The Bessel identity is classical. Brent–Johansson's introduction states

\[
\gamma=\frac{S_0(2x)-K_0(2x)}{I_0(2x)}-\log x,
\quad S_0(2x)=\sum_{j\ge0}H_j\frac{x^{2j}}{(j!)^2},
\]

and attributes the computational approach to Brent–McMillan (1980). Setting \(x=\sqrt\lambda\) gives exactly the identity used to simplify the proposed limit. The factor \(-2\) arises from this approximant's numerator decomposition; it is not a newly discovered Bessel identity. Brent–Johansson's explicit bounds concern truncation and asymptotic evaluation of Bessel functions, rather than comparison with the present finite endpoint weights. [Full text, introduction](https://fredrikj.net/math/brent.pdf).

## Remaining coverage and appropriate description

Further checking should include the final journal texts, forward citations of the 2025 family, and general hypergeometric limits with a growing number of parameters. The elementary product-defect estimate may also be a specialization of a broader standard estimate. No claim about priority follows from not finding the exact displayed inequality in this short list.

An accurate description at this stage is: a mathematically audited growing-parameter analysis of an established approximant family, with originality unresolved. The controlled \(\lambda\to\infty\) corollary, including \(n=4^\ell,p=5\ell\), likewise needs this comparison; convergence alone supplies no irrationality result or improved arithmetic-quality claim.


## Exact scope of the original paper's asymptotics

Theorem 1.2 of arXiv v3, page 3 (proof in Section 2.2), concerns the one-iteration case p=1. Proposition 2.5 and Section 5's instruction to apply the operator p−1 additional times identify this case. General p occurs in the unnumbered Section 5, “Further improvement,” pages 20–21, as a proposed extension, rather than in a numbered theorem.

The authors say they will “only provide the key ideas” and that “one should be able to prove” the proposed general-p asymptotics. The finite construction is meaningful for any integer p, including a value selected separately for each n. Its asymptotic discussion, however, gives neither a theorem for p=p(n) nor a uniform remainder across p. It treats p as a parameter while n tends to infinity. Section 5 does not literally introduce a “fix p” hypothesis, so that wording should not be attributed to the authors.

The precise conclusion is: the proved main theorem fixes p=1; the general-p discussion does not establish a moving-p limit. This conclusion follows from the theorem's actual scope and the status of the Section 5 argument, rather than from an absence of search keywords. It supplies no originality certificate for the present moving-parameter analysis.

Primary source: [author manuscript, pages 3 and 20–21](https://arxiv.org/pdf/2404.09799v3), and [Section 5 in HTML](https://arxiv.org/html/2404.09799v3#S5).

## Additional journal-version and forward-citation checks

On 12 October 2026 the DOI resolved to the publisher article page for volume 14, issue 2, pages 141–162. The publisher records acceptance on 14 April 2025 and publication on 30 April 2025. Its journal PDF required a subscription, so the journal-text comparison could not be completed. No claim of textual identity with the public arXiv v3 is made. [Publisher record](https://msp.org/cnt/2025/14-2/p04.xhtml).

A forward-citation search identified a relevant later survey to check: A. I. Aptekarev, “Multiple orthogonal polynomials and strong Szegő asymptotics,” Russian Mathematical Surveys 81(2) (2026), 209–273, DOI 10.4213/rm10281e. The accessible bibliographic record and a citation excerpt indicate discussion of the Van Assche–Wolfs approximants, but retrieval of the primary full text failed. Its relevant section has therefore not been screened, and this remains an explicit originality-review gap. [Primary bibliographic record](https://www.mathnet.ru/eng/rm10281).

The formal certificate establishes correctness of the critical series limit and the concrete lambda=1 nonconvergence statement. It does not settle these remaining historical comparisons or certify a novel result.
