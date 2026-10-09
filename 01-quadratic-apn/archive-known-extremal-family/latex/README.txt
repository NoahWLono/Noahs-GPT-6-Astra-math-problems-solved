EXTREMAL QUADRATIC MAPS IN DIMENSIONS DIVISIBLE BY FOUR
LaTeX edition, 9 October 2026
Project label: GPT-6 Astra (not runtime attribution or affiliation)

BUILD
-----
This archive is a self-contained LaTeX source project. It needs a standard
TeX Live or MiKTeX installation with pdfLaTeX, Latin Modern, AMS-LaTeX,
mathtools, geometry, microtype, booktabs, fancyhdr, fvextra, needspace,
xcolor and hyperref. These are standard distribution packages.

From this directory, run twice:

  pdflatex -interaction=nonstopmode -halt-on-error extremal_quadratic_maps.tex
  pdflatex -interaction=nonstopmode -halt-on-error extremal_quadratic_maps.tex

Alternatively, run:

  latexmk -pdf extremal_quadratic_maps.tex

There are no external images, bibliography files, or custom font files.
References are embedded in the .tex source. Internet access is not required
once the TeX distribution and standard packages are installed.

CONTENTS
--------
extremal_quadratic_maps.tex  Full editable mathematical paper
certificate_status.json     Frozen status metadata from the proof package
coefficient_certificate.json  Original finite coefficient certificate
README.txt                  These build and scope notes
SHA256SUMS                  Source-file checksums

The companion PDF contains the complete algebraic arguments and appendices,
all 66 binary coefficients, the formal verification boundaries, successful
fresh-dependency bootstrap status, and the cyclic-semifield correspondence.

RELATION TO THE ORIGINAL PROOF PACKAGE
--------------------------------------
This is a typeset derivative of the 16-page canonical report. It preserves
its mathematical content and caveats while adding conventional theorem,
proof, equation, and reference formatting. It does not modify or replace
the original report or the original reproducible proof archive.

The Lean projects, verification scripts, logs, and frozen source manifests
remain in the separate original proof package. Paths and commands for them
in Appendix D are relative to that package's source directory, not this
LaTeX archive. The source archive here compiles the paper; it is not a
replacement for the full Lean/Python reproducibility archive.

SCOPE
-----
Both independent source-only Lean replays passed. The uniform result makes
classical choices; its e=3 witness is not identified byte-for-byte with the
separately certified explicit twelve-bit polynomial. The universal lower
bound is cited, not formalized. The underlying construction is established;
novelty of the exact component-count corollary is unestablished.

QUALITY CHECKS
--------------
Compiled with pdfTeX (TeX Live 2025/dev/Debian). All pages were rendered and
visually reviewed. No overfull boxes, missing glyphs, undefined references,
or unresolved citations remain. Independent transcription review matched
all 66 coefficient entries to the certificate and checked all displayed
formulas, the hypotheses, the correspondence, and the formal scope.
