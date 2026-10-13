# Paper source

The editable TeX and bibliography describe the exact Q7 result, the completed independent source rebuild with documented independent-object reuse, and the subsequent full public-verifier replay with zero custom-object reuse. No priority claim is made. The included PDF is built from the included manuscript source.

Build locally with `bash build-paper.sh`, using TeX Live with pdfLaTeX, BibTeX, Latin Modern, amsmath/amsthm, microtype, xurl and hyperref. The script only typesets and does not invoke Lean or access the network. The reviewed rendered PDF is included as `q7-local-identifying-draft.pdf`; generated TeX caches and compiled proof objects are excluded.

All 13 rendered pages were visually reviewed after the full-public-replay update, with no layout/reference warnings; repeated builds produced byte-identical PDF files. See QA.json. This typesetting check does not replace proof verification.
