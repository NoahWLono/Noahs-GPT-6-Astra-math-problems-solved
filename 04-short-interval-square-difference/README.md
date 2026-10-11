# 04: A uniform optimum for short-interval square-difference masks

**Status: The central all-length theorem is formally verified in Lean 4, with compiled finite checks. Historical novelty remains unestablished.** Paper attribution: GPT-6 astra.

Fermat's factorization method looks for `N = a² − b²`. A modular filter rejects a candidate `a` if `a² − N` is not a square modulo a chosen modulus `m`. Its decisions repeat, so a raw table can store one bit for each residue. This paper asks which modulus gives the smallest worst-case number of surviving candidates when that table is limited to 256 bits.

For each modulus, take the worst case over inputs coprime to it and every starting position of an interval containing `h` consecutive integers. Write the resulting maximum count as `F_m(h)`. The theorem is

```text
F_144(h) ≤ F_m(h)  for every integer h ≥ 1 and every integer 1 ≤ m ≤ 256.
```

Thus one modulus is optimal simultaneously for all interval lengths. Ties occur at some lengths. The theorem concerns this raw table model and candidate counts; it does not establish a faster factorization algorithm, optimal compressed storage, or a weakness in deployed cryptography.

- [Mathematical paper (PDF)](paper.pdf)
- [Editable LaTeX source](paper.tex)
- [Lean theorem and reproduction instructions](lean/README.md)
- [Fresh Lean rebuild and axiom audit](lean/verification.json)
- [Verification and PDF build record](parent_verification.json)
- [Prior-art sources and search limits](sources.json)
- [Package checksums](SHA256SUMS)

## Proof and verification

The analytic proof classifies the residue patterns modulo 144 and derives an exact formula for `F_144`. It proves the sharp inequality `F_144(h) ≤ h/12 + 7/4`. Exact finite enumeration gives density `1/12` for the worst mask at 144 and at least `2/21` for the worst mask at every competing modulus through 256. Averaging over interval starts then proves dominance for every `h ≥ 147`.

Finite checks cover the remaining lengths. The two implementations construct masks differently and agree on all 16,384 original entries for `h ≤ 64`. For lengths 65–146, the independent verifier checks the 144 envelope directly and uses density lower bounds for the 20,910 competing cells. It also checks all 37,376 extended attaining witnesses. It does not independently recompute competing upper bounds beyond 64; those bounds are not needed for the optimality proof.

The Lean proof independently establishes the bounds needed for the central theorem directly from the residue model. It checks the finite prefix and complete-period/remainder certificates, then proves the comparison for every natural interval length. It also proves strict optimality from length 148 onward. A semantic bridge identifies the executable count with the mathematical congruence predicate. Python-generated witnesses are treated as untrusted data and checked in Lean.

The final theorem uses the ordinary logical axioms `propext`, `Classical.choice`, and `Quot.sound`, plus `Lean.ofReduceBool` for standard `native_decide` evaluation. That finite computation trusts Lean's compiler and runtime as well as its kernel. There are no `sorry` placeholders or custom mathematical axioms. The exact all-length envelope formula, its sharpness examples, and the budget table retain their analytic/Python verification; they are outside the Lean formalization. Agent-assisted review does not constitute independent human peer review.

## Reproduce

For the formal theorem, install elan and run:

```bash
cd lean
lake exe cache get
bash verify.sh
```

The project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. The script rechecks all nine local proof modules and prints the theorem statements and axiom dependencies. Its [verification record](lean/verification.json) reports the fresh rebuild and measured resource use. Lean is not subject to the Python resource limits below.

For the original computational verification, use Linux with Python 3.10 or later. No third-party Python packages are required. The recorded runtime was Python 3.14.8. Python 3.10 compatibility was checked statically rather than with a separate interpreter run. Each exhaustive verifier and certificate checker enforces 120 CPU seconds and 256 MiB of address space; a sufficiently slow machine can reach the time limit.

Run from this numbered folder in a disposable copy of the checkout:

```bash
sha256sum -c SHA256SUMS
python3 -B wave2_b/test_minimax.py
python3 -B wave2_b/test_minimax_146.py
python3 -B wave2_b/generate_minimax_146.py
python3 -B wave2_b/check_all_h_constants.py
python3 -B wave2_c/verify_minimax.py
python3 -B wave2_c/verify_peer.py
python3 -B wave2_c/extend_optimality.py
python3 -B wave2_c/verify_extended_peer.py
```

`wave2_b` contains the construction; `wave2_c` contains the independent verifier. These directory names are retained so that the reviewed scripts and certificates keep their original bytes. The optional `python3 -B wave2_b/generate_minimax.py` regenerates the original 64-length table.

Replay overwrites result files. Mathematical outputs and certificates should retain their hashes; telemetry changes with the machine and run. Check `SHA256SUMS` before replay, then compare the mathematical output hashes with those recorded in `parent_verification.json`. A whole-package checksum comparison after replay will also see the expected telemetry changes.

The [original protocol](protocol.json) froze the 64-length domain before experiments. The [supplemental scope](wave2_b/extension_146_scope.json) records the extension used for the all-length proof. The protocol's prohibition on publication is a historical research-stage boundary. The owner subsequently authorized this public release on 10 October 2026; the frozen protocol remains unchanged to preserve its recorded hash.

## Build the paper

The source is standalone LaTeX. The included PDF was built from these exact source bytes with Tectonic 0.17.0 and visually checked on all pages. To rebuild it with Tectonic:

```bash
mkdir -p build
tectonic --untrusted --outdir build paper.tex
```

The publisher also checked compilation with the desktop editor's LaTeX compiler. PDF byte identity is not guaranteed across TeX distributions or timestamps; the included PDF's hash identifies the reviewed document.

## Prior art and release scope

Modular filtering, prime-power counts, finite modulus optimization, and the use of modulus 144 have prior art. The paper discusses Bower, Evans, Luo, and Miller; Hittmeir; and Hewitt's explicit 2022 modulus search. The exact all-length statement under this raw 256-bit model was not located in the bounded public search. That absence does not establish historical priority.

This is a public reproducibility release of a verified result with novelty unestablished. The package contains the proof, its finite certificates, the required verification code, and reviewed provenance records. It excludes internal research notes, abandoned experiments, caches, downloaded toolchains, and machine-specific build paths. No project-wide license or CI workflow is added. The paper attribution follows the owner's project label; it does not attest to runtime model identity or affiliation.
