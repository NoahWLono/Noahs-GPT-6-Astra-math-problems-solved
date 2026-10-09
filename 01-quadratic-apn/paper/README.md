# Quadratic APN component bound paper

The paper proves that every quadratic APN function from F₂⁸ to F₂⁸ has at least 33 non-bent nonzero scalar components and at most 222 bent components. It excludes the amplitude profile [0^226, 2^15, 4^14].

## Files

- `apn-eight-bound.pdf`: the compiled paper.
- `apn-eight-bound.tex`: the main editable LaTeX source.
- `sections/*.tex`: the full proof, formalization appendices, and bibliography.
- `build.sh`: the standard LaTeX build command.

The proof is self-contained, including the low-weight residue argument, all four coefficient-code cases in the specialized weight-30 classification, the affine rank-four obstruction, and the APN/Walsh interpretation. The appendices document the independently successful fresh rebuild of all 136 local Lean dependencies, the exact final statement, source correspondence, and reproduction limits.

## Build

With TeX Live and latexmk installed, run:

```sh
bash build.sh
```

The build uses standard LaTeX packages and does not require network access or shell escape. The source includes its bibliography directly, so BibTeX is unnecessary.

The paper credits the established classification and Pfaffian/APN ingredients. Its literature-priority statement is limited to the sources checked; no absolute priority, peer-review acceptance, or attainment of the bound is claimed.
