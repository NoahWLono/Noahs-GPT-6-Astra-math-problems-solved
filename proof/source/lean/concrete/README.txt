EXPLICIT TWELVE-BIT QUADRATIC CERTIFICATE

Strongest theorem:
N12.exists_exactly_quadratic_with_ninety_five_nonbent_components

The explicit 66-coefficient map F: BitVec 12 -> BitVec 12 has a valid squarefree
homogeneous quadratic representation, is not affine, and has exactly 95 nonzero
nonbent masks. N12.exact_nonbent_masks classifies every mask using a duplicate-free
list of length 95. The effective bad masks are 0,4,8,13,14,15; their 16 padding
lifts, excluding the full zero mask, give that list.

Bentness uses actual integer Walsh sums over all 4096 inputs and every one of
the 4096 frequencies. No unproved rank test replaces this definition. Exact
nonaffineness is witnessed by F(0)=F(1)=F(8)=0 and F(9)=3.

REPLAY
Install the official Lean 4.19.0 toolchain. From this directory run:

    LEAN="$(command -v lean)" python3 build.py --clean

Alternatively set LEAN to the absolute path of that version's lean executable.
Only the bundled Lean Std library is required; there is no mathlib dependency.
Python uses only its standard library. The tested platform is Linux x86-64.
The script uses one Lean thread and a 3-GiB address-space cap. Its default shared
lock can be overridden with LEAN_COMPILE_LOCK.

A successful full build ends with REQUESTED_TARGETS_COMPLETE and the final
axiom report. Running without --clean resumes only hash-matching checked modules.
Changing a frozen source requires review and explicit --accept-source-update;
recursive source fingerprints then invalidate affected descendants.

CHECKED EVIDENCE
All 930 local modules were independently compiled from an initially source-only
tree, with no copied local objects or previous successful-build cache. All
modules and all 256 effective component certificates passed. The strongest
existence theorem and exact classification use exactly propext and Quot.sound.
No custom axioms, admitted proofs, native_decide, unsafe replacements or external
oracles are used. Proposed inverse columns and integer constants are checked
inside the kernel and are not trusted premises.

SOURCE-MANIFEST.json          Frozen hashes of all 930 Lean source files
SOURCE-SHA256SUMS            Same local source identity in standard hash format
independent-clean-build.log  Complete successful independent build summary
logs/Main.log               Successful final theorem, axiom and resource report
logs/toolchain.txt           Exact compiler identification
verification.json           Structured verification facts and scope

Main.lean SHA-256:
84d10536b997e10263c3c0297d4360f34bfc7651b5cc0a806e7673bd58709aff

PROOF OUTLINE
Definitions.lean gives the coefficient map and exact degree-two evidence.
Basis/ and Inputs/ certify all component input signs. Data/ contains shared
constant sign subtrees. QuadraticWalshShift.lean proves the actual quadratic
translation, complete-domain XOR reindexing and Walsh-shift identities.
Certificates/ checks inverse-alignment data and a zero-frequency sum for every
bent effective mask; the six bad masks have exact Walsh counterexamples.
Extension.lean and OutputExtension.lean prove the four zero-output extension.
MaskLists.lean, Membership/ and Main.lean give the exact nonzero mask count.

SCOPE
This project certifies the concrete binary coefficient map. It does not identify
it with an abstract Lean F8 object, or with the uniform theorem's classically
chosen e=3 witness. The displayed trace formula is linked to the coefficients
by the mathematical proof and the independent 4096-input check.
The value 4000 follows by complement arithmetic, not a separate exported count.
Exact signed-spectrum multiplicities and the optional linear-coordinate variant
are mathematical results in the PDF. Historical novelty and the cited universal
lower bound are not formal theorems of this project.
