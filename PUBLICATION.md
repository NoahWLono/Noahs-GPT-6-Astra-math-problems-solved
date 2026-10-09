# Publication record

This repository packages the completed quadratic-family project only.

- All 956 Lean proof modules and the Lean lakefile are byte-for-byte unchanged from the verified source package.
- Frozen proof-source manifests, successful replay evidence, theorem/axiom reports, the two final reports, and source-only reproduction instructions are retained.
- One existing uniform replay log was sanitized: its build-directory prefix was replaced by `<SOURCE_ROOT>/`. Log diagnostics and proof source bytes were not changed.
- The proof-package `SHA256SUMS` was regenerated after that log-only sanitization. The root manifest additionally covers the publication layout.
- The canonical report remains in the directory layout expected by its renderer and archive-sealing script.
- Only editable LaTeX, frozen metadata, its README and manifest, and the final typeset PDF were copied from the LaTeX project. Intermediate `.aux`, `.log`, `.out`, and `.toc` files were omitted.
- Old report versions, working notes, private conversation information, unrelated projects, unsuccessful experiments, compiled proof objects, vendored mathlib, and build caches are excluded.
- No project-wide license or copyright assignment was added. Existing third-party font license notices are preserved.

The long Lean replays described in the reports are recorded completed checks from the original verification work. Publication does not imply that another full Lean replay has occurred. Publication-time integrity and finite-check results are recorded in `publication-checks.json`.
