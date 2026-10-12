# Publication and preservation notes

These notes record the collection's preservation and publication rules. Repository changes require the owner's authorization.

## Layout

Each mathematical problem is grouped in its own numbered folder. The quadratic/APN materials are in `01-quadratic-apn/`. The new proof's 136-module dependency closure plus endpoint-inspection module is independent of the archived package. The LaTeX/PDF and verification records belong alongside that proof.

The earlier 1,954-file quadratic-family package is copied into `01-quadratic-apn/archive-known-extremal-family/`, retaining its complete internal relative layout and every file's latest published bytes. The remote README and root checksum file supersede the initial local archive copies; all 1,953 entries in the latest remote checksum manifest were verified against the staged archive. Nothing is deleted from the original working directories. The archive's own checksums remain valid. Fonts and PDFs already present in that archive are intentional document assets, not proof caches or executable binaries.

## History-preserving publication

An eventual authorized repository update must use the then-current remote HEAD as its parent and retain existing commit history. Do not force-push, reset, or replace the repository's history. The old working package has no local Git commit history; its `.git` directory is therefore not a substitute for the remote's history and is not copied into this deliverable. Existing remote content must be compared with this manifest before applying moves. In particular, the current remote root README is newer than the archived family README; its prior version remains in Git history.

## Scope and checks

The collection adds no CI configuration or project-wide license. External publication requires the owner's authorization. Prior-art status is separate from proof correctness. The old family's construction remains established; it is not relabelled as a novel APN result. The new lower bound does not prove sharpness or an attaining construction.

The package excludes internal research notes, abandoned experiments, compiled Lean objects, dependency checkouts, credentials, and machine-specific build paths. Only the actual imported proof closure is copied into the new proof tree. Source bytes are frozen by a separate source manifest. A root `SHA256SUMS` covers the final staged files except itself; regenerate it whenever reviewed assets change.

## Order-ten frameproof classification

`03-order-ten-frameproof/` contains the 15-module dependency closure of the completed classification theorem, four saved LRAT certificates, pinned Lean/mathlib configuration, portable verification scripts, the mathematical paper, and reviewed verification and prior-art records. The final theorem uses standard compiled `bv_check` evaluation; its four generated evaluation axioms are disclosed alongside the ordinary Lean axioms. Optional separately checked CNF proofs are included as corroboration and are not imports of the main theorem.

The owner authorized this addition on 10 October 2026. It is added to the current remote history without changing either existing problem package or the research-only WIP list. The publication contains no abandoned experiments, dependency checkout, compiled proof objects, credentials, or machine-specific build paths. Prior-art coverage remains qualified and separate from the successful formal proof.

## Short-interval square-difference masks

`04-short-interval-square-difference/` contains an analytic proof that modulus 144 minimizes worst-case interval survivor counts for every positive length among moduli at most 256 in a raw one-bit-per-residue representation. Exact finite comparisons, density certificates, and a second implementation support the computer-assisted lemmas. The central all-length theorem, strict comparison from length 148, and supporting discrepancy bounds are formalized in Lean 4.19.0 with pinned mathlib dependencies. The finite computations use standard native evaluation; the final theorem's `Lean.ofReduceBool` dependency is disclosed. The paper and README distinguish these formalized results from the analytic envelope formula and original numerical tables.

The owner authorized public release on 10 October 2026. Historical novelty remains unestablished, and the collection makes no priority or factorization-performance claim for this result. The addition includes the matching LaTeX source and PDF, nine local Lean proof modules, portable verification scripts, reproducible Python code, certificates, and reviewed records. The owner explicitly authorized the Lean verification and update to folder 04. Every local Lean module was rebuilt from the publication sources in a relocated copy, with pinned dependency caches reused. The original research protocol is retained byte-for-byte as historical provenance; its research-stage no-publication boundary was superseded by this later release authorization. The existing numbered packages, research-only WIP list, and repository history are preserved. No CI configuration or license is added.

## Elliptic-curve translation recurrences

`06-elliptic-curve-recurrences/` contains the verified Lean formalization, portable reproduction instructions, reviewed verification records, and a dated `FORMAL_VERIFICATION.md` addendum. The original 24 research assets formerly in `#6/` are retained byte-for-byte under `original-research/`, including their internal checksum manifest. Their research-stage statements about formal verification are historical; the new top-level README and dated addendum provide the current verification status and precise theorem scope.

The owner authorized publication after disclosure that historical novelty remains unestablished. This release makes no claim to a faster ECDLP solver, a general computational lower bound, or historical priority. It preserves the preceding numbered projects and current research queue, retains remote commit history, and refreshes the root checksum manifest. No CI configuration or project-wide license is added. Existing Apache-2.0 attribution for adapted divisor foundations is retained in the formalization. No dependency checkout, compiled Lean object, credential, or abandoned experiment is added.

## Scoped shifted-binomial irreducibility

`07-scoped-binomial-irreducibility/` preserves the original prime-inner-exponent paper and its immediate composite-inner-exponent addendum, unchanged mathematical Lean/LaTeX/PDF content, upstream source/license copies, pinned dependency configuration and source hashes, public reproduction instructions, and a concise verification report. The owner authorized this release on 12 October 2026.

Both exact roots compiled under Lean 4.32.2 and passed independent requested-type and referenced-definition comparison, patched official Lean 4.34.1 full-closure replay, and nanoda 0.4.19 checking. Only `propext`, `Classical.choice`, and `Quot.sound` occur as production axioms. The original sources also passed a clean all-local rebuild using pinned upstream caches and byte-identical export correspondence; no new whole-source clean rebuild is claimed for the extension. The non-isolated adapter, absence of external human peer review, and untested fresh-network installation recipe remain explicit.

The publication packages are newly assembled public ZIPs, distinct from the historical sealed archives identified in the unchanged papers. Historical machine-specific source origins, execution records, environment inventories and raw verification metadata are omitted. The public manifests retain source identities and public package-relative dependency hashes. Two read-only manifest readers were adapted for this public layout; the Lean sources and sequential original builder are unchanged. Source-integrity/import preflight and Python syntax checks passed after adaptation; no new complete Lean build or checker run is claimed for this packaging change.

The original PDF is the canonical byte-for-byte archived copy. The addendum is the delivered Content Credentials-bearing PDF. Actual hashes and the unchanged-source LaTeX rebuild comparison are documented in `PUBLICATION_FORMAT.md`; all three addendum pages and extracted text matched the rebuild. No credentials, private execution metadata, research notes, prebuilt proof objects, dependency checkout, admitted comparison fixture, or large serialized proof export is included.

These are scoped auxiliary irreducibility results, not a full Pillai solution, full Koala solution, or novelty claim. The earlier six numbered projects and unrelated research queue are preserved, remote commit history is retained, and the root checksum manifest is refreshed. No CI configuration or project-wide license is added.
