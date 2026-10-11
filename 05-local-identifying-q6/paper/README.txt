Manuscript build and verification

main.pdf is the nine-page final manuscript corresponding to main.tex.
The exact-minimum theorem and all 61,970 RUP steps passed both the first full
Lean kernel build and the independent clean-source rebuild. The latter checked
257 modules from 451 source/JSON files, with only propext, Classical.choice,
and Quot.sound in the unconditional theorem's axiom report.

PDF build: ./build.sh
A normal TeX Live installation may instead run pdflatex main.tex twice.
The supplied build script includes a fallback for this container's TeX setup.
This PDF build script is distinct from the artifact-root build.sh, which
checks the full Lean proof.

QA.json records final manuscript hashes, visual review, and verification data.
The final-rendered/ images are layout-review intermediates and need not ship.
The release-docs/ directory contains superseded packaging planning notes and
is not part of the frozen manuscript or intended distribution. The final
artifact-root README/build.sh are authoritative for proof reproduction.

No public upload, publication, submission, or external contact was performed
as part of manuscript preparation. Global priority and human peer review are
not established. The correct located prior interval is 12-15.
