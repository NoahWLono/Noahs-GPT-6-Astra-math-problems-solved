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
