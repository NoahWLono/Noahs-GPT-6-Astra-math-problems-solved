# Publication format and artifact integrity

This public release preserves the exact Lean, LaTeX and PDF mathematical content, upstream license notices, toolchain pins, source hashes, and theorem statements from the delivered research packages. The original and extension papers remain separate.

The publication ZIPs are newly assembled and clearly named `scoped-irreducibility-public-20261012.zip` and `composite-inner-addendum-public-20261012.zip`. They are not the historical sealed archives named and hashed in the unchanged papers. Historical source-origin paths, execution logs, environment inventories, adapter handoffs, and raw verification metadata have been omitted. The verification outcomes and limitations are summarized in `VERIFICATION.md`.

All 54 local Lean proof/audit modules, 70 upstream Lean source copies, both LaTeX files, and both PDFs match their selected delivered inputs byte-for-byte. The public relative-path manifests retain the original local source hashes and 2,979 pinned third-party source hashes. Only the source/dependency manifest readers were adapted for the public manifest layout; the sequential original build script is unchanged. The source/import preflight and Python syntax checks passed after adaptation. No new Lean build or proof-checker run is claimed for publication packaging.

## Original paper

The published original PDF is the canonical copy preserved in the historical sealed source archive:

- 12 pages, 344,091 bytes
- SHA-256: `bdf82ebc76e544738c0e88fdb29306d329403a795da867a4e162c1a0ccd7a52e`

The separately delivered 397,247-byte copy has an embedded Content Credentials manifest. Its text, document metadata, and decoded pre-existing page, content and font objects match the canonical PDF. The differences are object-stream expansion, cross-reference representation, and the Content Credentials manifest and references. The canonical archived copy is published here.

## Addendum

The published addendum is the exact delivered PDF, retaining its embedded Content Credentials manifest:

- 3 pages, 280,394 bytes
- SHA-256: `6ac97c0dc2b11cf22c739636e7a3fc666f89d8606aa44c929c9f2a78dddc3a7e`

An earlier PDF build was recorded as SHA-256 `f436d464b9aa7263f5ae89ff860669617cd6a8cfc4c69cc14270f4cc19e968bb`; those earlier PDF bytes were not available for direct comparison. The published checksum above identifies the actual delivered file.

The unchanged bundled LaTeX and build script were rebuilt locally without dependency downloads. The rebuilt PDF's extracted text and all three 100-dpi rendered pages matched the delivered addendum exactly, pixel for pixel. All three pages were visually inspected. The final LaTeX pass had no warnings, missing-character messages, undefined references, or overfull/underfull box messages. This comparison validates paper content and presentation; it does not recheck the mathematical proof.

PDF metadata and Content Credentials can change file hashes without changing a paper's rendered content. The public checksum manifests identify the bytes actually distributed in this release.
