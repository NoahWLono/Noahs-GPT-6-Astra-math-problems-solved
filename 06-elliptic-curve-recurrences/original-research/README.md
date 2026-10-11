# ASTRA-01: rational recurrences for elliptic-curve translation

**Result:** a proved, narrow mathematical obstruction, with a sharp synthetic example. No faster classical ECDLP solver or verified historical novelty is claimed.

Prepared for Noah Weinberger in a ChatGPT cloud research session on 11 October 2026. All finite-field instances and scalar values were self-generated. No third-party key or production-curve logarithm was used. This folder was prepared from that research session and published to the specified GitHub repository after the owner explicitly authorized publication on 11 October 2026.

## Main statements

Let G have exact order n on an elliptic curve E, H = <G>, f: E -> P^1 a nonconstant rational morphism of degree D, and R: P^1 -> P^1 a rational map of degree r >= 1. Degree includes pole multiplicities, and equality is projective at every point.

The manuscript proves:

    #{P in H : f(P+G) = R(f(P))} <= min(n, D*(r+1)).

If the recurrence is a global identity of morphisms, necessarily r = 1 and n divides D. A fixed menu of recurrences of degrees r_j covers at most min(n, D*sum_j(r_j+1)) points, even when a branch may be selected arbitrarily for each point.

For odd prime n, a nonconstant full Mobius recurrence on H over F_(q^k) requires n = characteristic, n | q^k-1, or n | q^k+1. If n differs from the characteristic and e = ord_n(q), k must be a positive multiple of e/gcd(e,2).

Consequently, when p >= 17 and the entire E(F_p) has prime order n != p, no nonconstant base-field Mobius recurrence exists, even for an arbitrary finite function f. This applies only to the specified recurrence model, not to general ECDLP algorithms.

## Why this is not a cryptographic break or a runtime lower bound

The proof excludes low-degree single-coordinate rational recurrences. It does not exclude multiple coordinates, algebraic correspondences, point-dependent families, or high-degree functions with compact evaluation circuits.

In particular, f_t(P) = x([2^t]P) has algebraic degree 2*4^t but needs only t point doublings to evaluate. High degree is not a certificate of high runtime. The exact Semaev addition correspondence also survives, with two branches; resolving that correspondence efficiently has not been proved here.

## What actually ran

| Check | Result |
| :--- | ---: |
| Self-generated curves | 13 |
| All possible scalar instances solved by exact BSGS | 763 |
| Exhaustive coordinate/Mobius pairs | 78,336 |
| Sampled coordinate/rational-map pairs | 19,500 |
| Degree-bound violations | 0 |
| Separate all-pairs group-law checks | 79,813 |
| Separately recomputed coordinate/Mobius pairs | 78,336 |
| Separate matrix-order checks | 15,696 |

The second implementation uses line/cubic intersection instead of the primary slope formula and does not import the primary code. This is implementation independence within the same session, not outside peer review. The optional SymPy checks were also executed. No proof assistant was used.

The finite tests corroborate the written proofs. Their small sizes and recorded wall times do not establish asymptotic performance.

## Exact sharpness witness

    E/F_11: y^2 = x^3 + x + 6
    G = (2,4), order 13
    f = x, degree 2
    M(z) = z/(z+5)
    matching scalar indices = [1, 6, 8, 9]

This attains four agreements and disproves a universal 2D-1 bound. A four-map cover of the same 13-point orbit is also supplied and certified minimal. Branch selection is not an ECDLP algorithm.

## Reproduce without changing the shipped results

Python 3.10 or later is required. The execution environment recorded CPython 3.13.5. The core checks need no third-party library. Run from the extracted package:

```sh
python3 verify_package.py
```

The runner validates `SHA256SUMS`, copies the three experiment scripts into a temporary directory, reruns them, and compares exact mathematical results with the shipped JSON. Timing diagnostics are excluded from the comparison. It runs the symbolic check when SymPy is present; otherwise it explicitly reports that optional check as skipped. The runner itself makes no network requests and does not install anything. Checksums detect byte changes relative to the supplied manifest; they are not a digital signature.

The optional symbolic dependency used here is:

```text
sympy==1.14.0
```

For direct individual runs, which overwrite the corresponding result files:

```sh
python3 src/experiments.py
python3 src/independent_check.py
python3 src/symbolic_check.py
```

Run the scripts normally, without Python's `-O` option; the symbolic checker uses assertions. After a direct run, timing changes will invalidate the original checksum manifest. Prefer `verify_package.py` for integrity-preserving reproduction.

The seeded experiment is deterministic for the recorded environment. Cross-version differences in pseudorandom-library behavior may change the sampled-map record even when all mathematical assertions continue to hold.

## Files

| File | Purpose |
| :--- | :--- |
| `manuscript.pdf`, `manuscript.tex` | Definitions, complete proofs, exact examples, methods, limits, references |
| `src/experiments.py` | Synthetic curves, exact BSGS, exhaustive and sampled recurrence tests |
| `src/independent_check.py` | Separate point arithmetic, exhaustive histograms, certificate checks |
| `src/symbolic_check.py` | Exact polynomial identities, optional SymPy |
| `results/experiments.json` | Full orbits, recovered scalars, histograms, witnesses, all primary records |
| `results/independent_checks.json` | Separate implementation results |
| `results/symbolic_checks.json` | Symbolic verification results |
| `results/summary.txt` | Compact execution summary |
| `CLAIMS.md`, `claims.json` | Proven, refuted, and unproved claims |
| `COMPLEXITY.md` | Cost models, preprocessing, memory, distributions, limitations |
| `PRIOR_ART.md`, `sources.json` | References and limits of the priority assessment |
| `PUBLICATION_STATUS.md` | Original no-write decision and subsequent owner authorization |
| `verify_package.py`, `SHA256SUMS` | Reproduction and file-integrity checks |

Rebuild the PDF with two `pdflatex` passes, or `latexmk -pdf manuscript.tex`, if a TeX installation is available. TeX is not required to rerun the mathematical experiments.

## Prior art and publication

Translated-pole arguments are established, with close work by Hess and Shparlinski and by Merai and Winterhof. The Semaev polynomial and the group/field classification ingredients are established. Historical priority for the exact formulation and witness is unestablished.

`PUBLICATION.md` in the requested repository was read. After the initial research-only preparation, the owner authorized posting this reproducible partial result to folder `#6/` on 11 October 2026. This is not a claim of historical novelty or an ECDLP break. The release adds no CI configuration or project-wide license.
