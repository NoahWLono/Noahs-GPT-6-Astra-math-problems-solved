# Extremal quadratic maps in dimensions divisible by four

Lean 4 proofs, mathematical reports, and reproducible finite checks. Research date: 9 October 2026.

> **Prior-art and novelty warning:** The underlying family is established: a fixed congruence identifies its pencil with a hyperbolic binary plane plus a Jha–Johnson cyclic-semifield core. The precise component-count result is a short determinant-fibre corollary. Its novelty is **unestablished**. This repository does not claim a new underlying construction, a solved unknown problem, or an APN result. The numerical existence cases n = 4 and n = 8 were already known.

## Result

For every integer e > 0, let n = 4e. There exists a homogeneous quadratic map F: F₂ⁿ → F₂ⁿ of degree exactly two with precisely

**3 · 2^(n/2 − 1) − 1 nonzero nonbent component masks.**

This attains the cited non-MNBC lower bound of Deryck in these equal-dimensional cases. That universal lower bound is **not formalized here**. Dimensions n ≡ 2 (mod 4) are not settled here.

The uniform Lean theorem is `FamilyAlgebra.uniform_nonaffine_quadratic`. It proves a squarefree quadratic representation, nonaffineness, and the exact count using actual integer Walsh sums. It uses classical choices and is not an efficient coefficient-extraction algorithm. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`.

The separate explicit twelve-bit theorem is `N12.exists_exactly_quadratic_with_ninety_five_nonbent_components`: 95 nonbent nonzero masks, hence 4000 bent masks by complement arithmetic. Its axioms are `propext` and `Quot.sound`. The uniform e = 3 witness is not identified byte-for-byte with this concrete map. The trace-formula identity for the concrete map has a human proof and an independent all-input check, not a separate Lean field-identification theorem.

## Read the papers

- [LaTeX edition (PDF)](papers/extremal_quadratic_maps_latex.pdf)
- [Canonical report (PDF)](proof/output/pdf/gpt6_astra_extremal_quadratic_family.pdf)
- [Editable LaTeX and build notes](latex/README.txt)
- [Complete proof-package guide and references](proof/source/README.txt)
- [Cyclic-semifield correspondence and prior art](proof/source/family/CYCLIC_SEMIFIELD_CORRESPONDENCE.txt)
- [Exact verification scope](proof/source/certificate_status.json)

“GPT-6 Astra” is a project label used in the reports, not a claim of runtime model attribution, affiliation, or peer review.

## Reproduce the Lean proofs from source

The repository includes **956 local proof modules**: 26 uniform modules and 930 concrete certificate modules. Both have recorded successful independent source-only replays. It ships no compiled `.olean` files, mathlib checkout, or proof cache. The Lean toolchain is pinned to 4.19.0.

### Uniform theorem

With an official Lean/elan installation:

```sh
cd proof/source/lean/uniform
lake update
lake exe cache get
lake env python3 replay.py --clean
```

Mathlib is pinned to commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. These commands also passed in a fresh-archive bootstrap with freshly downloaded official dependencies and isolated home/cache/git settings; the official Lean toolchain and Std were reused. See [bootstrap evidence](proof/source/lean/uniform/bootstrap/BOOTSTRAP_RESULT.json).

### Concrete twelve-bit certificate

```sh
cd proof/source/lean/concrete
LEAN="$(command -v lean)" python3 build.py --clean
```

This uses Lean 4.19.0 and bundled Std only. The recorded replay took about 43 minutes of summed module compilation time on Linux x86-64, with one Lean thread and a 3-GiB address-space cap. Successful per-module logs, source manifests, and final axiom reports are included. Source hashes are preserved.

## Independent finite checks

Python 3.10 or later, no dependencies or network needed for these commands:

```sh
cd proof/source
python3 verify_all.py
python3 family/verify_family.py
python3 family/verify_correspondence.py
```

The first command verifies the concrete coefficients, all 4096 input values, 1,048,576 effective Walsh coefficients, and 1536 independently summed raw Walsh coefficients. The family checks cover e = 1,…,6; the arbitrary-e theorem does not rely on extrapolation. A separate NumPy-based implementation and reference results are also included under `independent/`.

## Integrity and publication hygiene

[PUBLICATION.md](PUBLICATION.md) describes packaging changes and the boundary between previously recorded proof replays and publication-time checks. `SHA256SUMS` at the repository root covers every published file except itself. Original proof source bytes and their frozen manifests have been retained. No CI is installed; proof execution is explicit and local.

## License

No project-wide license has been specified. Publication alone does not grant a new license. Bundled DejaVu fonts retain their [existing license](proof/source/fonts/LICENSE.txt). Lean, Std, mathlib, Python, LaTeX, and other external dependencies remain governed by their respective upstream licenses; their source trees are not vendored here.
