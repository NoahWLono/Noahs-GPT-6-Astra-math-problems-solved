# Paper source

The editable TeX and bibliography describe the exact Q7 result and its completed independent source rebuild, with documented independent-object reuse. No priority claim is made. The manuscript source is byte-identical to the reviewed 13-page draft.

Build locally with `bash build-paper.sh`, using TeX Live with pdfLaTeX, BibTeX, Latin Modern, amsmath/amsthm, microtype, xurl and hyperref. The script only typesets and does not invoke Lean or access the network. The reviewed rendered PDF is included as `q7-local-identifying-draft.pdf`; generated TeX caches and compiled proof objects are excluded.

All 13 rendered pages were visually reviewed, with no layout/reference warnings; repeated builds produced byte-identical PDF files. See QA.json. This typesetting check does not replace proof verification.
