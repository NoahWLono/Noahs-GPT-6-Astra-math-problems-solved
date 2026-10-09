GPT-6 Astra
Extremal quadratic maps in dimensions divisible by four
Research date: 9 October 2026

MAIN RESULT
-----------
For every integer e > 0 and n = 4e, there exists a homogeneous quadratic map
F: F2^n -> F2^n of degree exactly two with precisely

    3 * 2^(n/2 - 1) - 1

nonzero nonbent component masks. This attains Deryck's non-MNBC lower bound
for every equal-dimensional case m=n divisible by four. The universal lower
bound is cited externally; it is not formalized by this package. Dimensions
n = 2 modulo 4 are not settled, and no APN result is claimed.

Both formal projects passed independent source-only replay:
- Uniform theorem: all 26 local modules; Lean 4.19.0 with pinned mathlib.
- Explicit twelve-bit instance: all 930 local modules; Lean 4.19.0 and Std only.

The underlying family is established: a fixed congruence identifies the entire
pencil as a hyperbolic binary plane plus a Jha-Johnson cyclic-semifield core.
The exact extremal count is a short determinant-fibre corollary. No prior
publication of that precise component-count consequence was located, but
novelty is unestablished. Any contribution is at most a potentially new
application/corollary and its formal verification, not a new underlying
construction. The n=4 and n=8 numerical existence cases are already known.
See Appendix E of the PDF and family/CYCLIC_SEMIFIELD_CORRESPONDENCE.txt.
GPT-6 Astra is the requested project label, not runtime model attribution.

TWO FORMAL PROJECTS
-------------------
lean/uniform contains the uniform theorem
FamilyAlgebra.uniform_nonaffine_quadratic.
For each e>0 it proves a valid squarefree quadratic coefficient representation,
explicit nonaffineness, and the exact count using actual integer Walsh sums.
It makes classical choices of finite fields, generators, bases and coordinate
equivalences; it is not an efficient coefficient-extraction algorithm.
Final axioms: propext, Classical.choice, Quot.sound.

lean/concrete contains the separate explicit twelve-bit certificate
N12.exists_exactly_quadratic_with_ninety_five_nonbent_components.
The concrete 66-coefficient map has eight independent quadratic coordinates
and four zero coordinates, with 4000 bent and 95 nonbent nonzero masks.
Lean proves exact quadraticity/nonaffineness and the complete duplicate-free
95-mask classification. The number 4000 follows by complement arithmetic.
Final axioms: propext, Quot.sound.

The uniform e=3 witness is not identified byte-for-byte with the concrete map.
The F8 trace formula equals the concrete binary coefficient map by the human
proof and the independent check at all 4096 inputs. This concrete identity is
not a separate Lean field-identification theorem.

REPRODUCE THE UNIFORM LEAN PROOF
-------------------------------
From lean/uniform, with an official Lean/elan installation available:

    lake update
    lake exe cache get
    lake env python3 replay.py --clean

The project pins Lean 4.19.0 and mathlib commit
c44e0c8ee63ca166450922a373c7409c5d26b00b.
The portable replay.py is the exact tested runner. All three commands above
also passed from a fresh extraction of the source archive, with freshly
obtained official upstream dependencies and an isolated HOME, cache and git
configuration. No old mathlib or project path was used. Only the official
Lean 4.19.0 toolchain and Std were reused. The initial download launcher timed
out; resuming lake update with its newly downloaded files succeeded, followed
by a successful cache get and all 26 local module compilations. No proof
source changed. See lean/uniform/bootstrap/ for sanitized evidence and exact
scope. The earlier source-only replay is retained as a separate verification.

REPRODUCE THE CONCRETE LEAN PROOF
--------------------------------
From lean/concrete, with Lean 4.19.0 selected:

    LEAN="$(command -v lean)" python3 build.py --clean

No mathlib dependency is needed. The tested platform is Linux x86-64 with one
Lean thread and a 3-GiB address-space cap. The recorded independent replay took
about 43 minutes of summed module compilation time. Source manifests, successful
per-module logs, a full run log and the final axiom report are included. No
compiled .olean files or successful-build cache are supplied in this archive.

REPRODUCE THE INDEPENDENT FINITE CHECK
------------------------------------
From this source directory, using Python 3.10 or later:

    python3 verify_all.py

No third-party package or network access is required. The script checks:
- all 66 coefficients against the field construction;
- all 256 field/binary ranks and Pfaffians;
- all 4096 inputs against both trace and coefficient formulas;
- all 1,048,576 effective Walsh coefficients;
- 1536 independently summed raw Walsh coefficients.

It writes results/reproduced.json and prints the expected 4000/95 counts.
The separate NumPy implementation and its reference output are in independent/.
Original scripts in construction/ and independent/ preserve their original
relative paths for provenance; verify_all.py is the portable entry point.

REPRODUCE THE FAMILY FINITE CHECKS
---------------------------------
    python3 family/verify_family.py

This exhaustively checks the singular-mask statement for e=1,...,6, corresponding
to n=4,8,12,16,20,24. The proof for arbitrary e is mathematical and also formalized
in the separate uniform Lean project; it does not rely on extrapolating these
finite checks.

REBUILD THE PDF
---------------
Install requirements-pdf.txt in an isolated Python environment, then run:

    python3 build_report.py

Output: ../output/pdf/gpt6_astra_extremal_quadratic_family.pdf
The bundled fonts are distributed under fonts/LICENSE.txt. The requested report
label does not add any author affiliation or claim of peer review. The build
status file records the exact verification scope. Source hashes are listed in
SHA256SUMS; seal_bundle.py packages only source and the final PDF after checking
the certification metadata.

CONTENTS
--------
construction/         Explicit field formula, all coefficient masks/matrices,
                      original search/verifier and coefficient CSV
independent/          Independent truth table, full spectra and NumPy verifier
family/               Family proof, cyclic-semifield correspondence and checks
lean/uniform/         26-source uniform proof, runner, pins, manifests and log
lean/concrete/        930-source concrete certificate, builder and successful logs
results/              Portable-verifier results and runtime metadata
build_report.py       Complete PDF authoring source
requirements-pdf.txt  Pinned ReportLab version used for rendering
certificate_status.json  Exact final certificate scope and trust boundaries
SHA256SUMS            Checksums of every packaged source file

The optional mathematical variant replaces the four zero output coordinates
by x0,x1,x2,x3. It has no identically zero nonzero-mask component and preserves
signed Walsh spectra by frequency shifts. It does not change the quadratic
polar ranks or derivative fiber sizes. This variant and the full signed
spectral multiplicities are not separately exported Lean claims.

ENCODING OF THE CONCRETE MAP
---------------------------
F8 = F2[alpha]/(alpha^3 + alpha + 1), using basis 1,alpha,alpha^2.
Input: four three-bit field coordinates, least significant coordinate first.
Parameters: u,v,w,z,s,t,p,q, least significant bit first.
Coefficient pairs: (0,1),(0,2),...,(0,11),(1,2),...,(10,11).
Coefficient bit k: coefficient of x_i*x_j in output coordinate k.
Walsh convention: W_F(b,a) = sum_x (-1)^(<b,F(x)> + <a,x>).
Bent convention for n=12: every Walsh coefficient squared equals 4096.
A nonzero mask selecting the zero Boolean function is still counted as nonbent.
Effective nonbent masks: 0,4,8,13,14,15.

SHA-256 of the ordered 4096 truth-table output bytes:
ae7383fd45347cbcf32eefec5a6750434967dd727fe6751a388f3ba6ff72bce3
This is not the SHA-256 of the JSON encoding.

REFERENCES
----------
Maxime Deryck, Cryptography meets Finite Geometry, master's thesis,
Ghent University, academic year 2025-2026. Definition 5.1.4, printed p. 67;
Theorem 5.4.15, printed p. 87; higher-dimensional discussion, printed p. 88.
https://maximederyck.be/assets/Cryptography%20meets%20Finite%20Geometry.pdf

Rod Gow, Rank-related dimension bounds for subspaces of bilinear forms over
finite fields, arXiv:1703.07266v1, 21 March 2017. Trace descent appears in the
proof of Theorem 6.
https://arxiv.org/abs/1703.07266

Christof Beierle, Philippe Langevin, Gregor Leander, Alexandr Polujan and
Shahram Rasoolzadeh, Millions of inequivalent quadratic APN functions in eight
variables, arXiv:2508.04644v1, 6 August 2025, Definition 4.1 and Table 4.1.
The profiles imply (8,6) maps with 58 bent components. Padding gives 232 bent
and 23 nonbent nonzero masks, so the n=8 existence count is not new.
https://arxiv.org/html/2508.04644v1

Guglielmo Lunardon, 50 Years of translation structures, Journal of Geometry
113, article 35 (2022), Section 3.3.3 and Theorem 16. Related geometry of linear
sets outside hyperbolic quadrics and additive semifield spread sets.
https://link.springer.com/article/10.1007/s00022-022-00643-5

William M. Kantor and Robert A. Liebler, Semifields arising from irreducible
semilinear transformations, J. Aust. Math. Soc. 85 (2008), 333-339, section 2,
printed p. 334. Jha-Johnson irreducible-semilinear construction.
https://pages.uoregon.edu/kantor/PAPERS/IrreducibleSemilinear.pdf

Norman L. Johnson, Giuseppe Marino, Olga Polverino and Rocco Trombetti,
On a generalization of cyclic semifields, J. Algebr. Comb. 29 (2009), 1-34,
Theorem 1(2), pp. 10-11. Odd-degree norm/power-basis specialization.
https://emis.de/ft/43764
