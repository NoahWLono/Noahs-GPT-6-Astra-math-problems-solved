# Prior-art assessment

**Conclusion:** the written theorem is supported by the proof, but historical novelty is unestablished. This assessment does not certify that no equivalent statement exists, and it does not claim an exhaustive review through October 2026.

## Closest located work

Hess and Shparlinski, *On the Linear Complexity and Multidimensional Distribution of Congruential Generators over Elliptic Curves*, use translated pole divisors to show that combinations of rational functions are nonconstant, then bound their zeros. Their Lemma 1 and Theorem 4 are close methodological precedents. The author-hosted draft was inspected, including the proof page.

Merai and Winterhof, *On the Linear Complexity Profile of Some Sequences Derived from Elliptic Curves*, provide additional relevant work on elliptic-curve sequences and degree-based recurrence constraints. Their recurrence settings do not by themselves establish identity with the present one-step rational-map formulation, but a difference in presentation is not evidence of novelty.

The general coincidence bound and divisibility of an invariant fiber divisor are short consequences of established curve theory. The PGL2 classification, orbit-period argument, Hasse bound, multiplication-map degrees, and BSGS baseline are also established ingredients. The narrow base-field consequence is derived here, without asserting priority.

## A relationship that was not relabeled as new

The elimination of y from elliptic-curve addition gives

    S3(x,u,z) = (x-u)^2*z^2
                - 2*((x+u)*(x*u+a)+2*b)*z
                + (x*u-a)^2 - 4*b*(x+u).

This is the known third Semaev summation polynomial. It was independently derived and symbolically checked, then matched to Galbraith's explicit chapter formula. The Semaev ePrint abstract was accessible; the full ePrint PDF was not. No new index-calculus method follows merely from rederiving this polynomial.

## Search scope and access limitations

The review covered generic lower bounds, exact BSGS and rho context, known trace-one and pairing-transfer exceptions, extension-field/summation-polynomial directions, translated-pole recurrence arguments, elementary algebraic dynamics, and official definitions of the two named production curves. Only the low-degree rational translation recurrence avenue was developed experimentally.

The Galbraith-Gaudry survey was used through its accessible abstract and record, not claimed to have been fully reviewed. Some ePrint PDF requests failed. This is one reason the package makes no novelty certification or blanket claim about the absence of every possible contemporary algorithm.

## Sources

Exact source locations, reviewed scope, and how each source was used are stored in `sources.json`. The manuscript supplies a conventional bibliography with working source labels. No third-party paper or font file is redistributed in this package.

Core primary-source identifiers:

```text
Shoup: https://www.shoup.net/papers/dlbounds1.pdf
Galbraith Ch. 13: https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch13.pdf
Galbraith Ch. 14: https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch14.pdf
Galbraith Ch. 15: https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch15.pdf
Smart: https://link.springer.com/article/10.1007/s001459900052
MOV: https://ieeexplore.ieee.org/document/259647/
Semaev: https://eprint.iacr.org/2004/031
Galbraith-Gaudry: https://eprint.iacr.org/2015/1022
Milne: https://www.jmilne.org/math/Books/EC2.pdf
Hess-Shparlinski: https://uol.de/f/5/inst/mathe/personen/florian.hess/pdf/lincomplex.pdf
Merai-Winterhof: https://arxiv.org/abs/1509.06909
SEC 2: https://www.secg.org/sec2-v2.pdf
NIST SP 800-186: https://nvlpubs.nist.gov/nistpubs/SpecialPublications/NIST.SP.800-186.pdf
```

## Publication recommendation

Retain this as a research note unless the precise formulation and sharpness certificate receive a more complete comparison with the relevant literature and outside mathematical review. Do not describe it as a new ECDLP algorithm, a security proof for secp256k1/P-256, or a formally verified cryptographic breakthrough.
