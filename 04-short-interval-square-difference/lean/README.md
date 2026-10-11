# Lean proof of uniform interval optimality

The endpoint is `Astra.uniform_optimal` in [MainTheorem.lean](MainTheorem.lean):

```lean
theorem uniform_optimal (m h : ℕ) (hm1 : 1 ≤ m) (hm256 : m ≤ 256) :
    F 144 h ≤ F m h
```

Its hypotheses specify the modulus budget. The interval length is arbitrary, including zero. Finite enumeration is used to prove the supporting bounds, and the periodic-window argument extends them to every length.

The same file proves `Astra.strict_optimal_from_148`, which gives strict inequality for every competing modulus when `h ≥ 148`, and the two bounds used in the infinite tail:

```text
12 * F 144 h ≤ h + 21
2 * h ≤ 21 * F m h        (1 ≤ m ≤ 256, m ≠ 144)
```

## Mathematical meaning

[Model.lean](Model.lean) defines the mask by the equation `a*a % m = (n + b*b) % m` for some `b < m`. This includes zero among the square residues and avoids truncated subtraction on natural numbers. Unit inputs satisfy `n < m` and `Nat.gcd n m = 1`; at modulus 1 this includes the paper's input residue 0. The definition of `F` takes the maximum over every unit input and every start less than the modulus. Windows count repeated positions when their length exceeds a period.

[SemanticBridge.lean](SemanticBridge.lean) proves that the executable count equals the sum of this mathematical predicate and that `F` equals the corresponding supremum. It also checks concrete boundary examples by ordinary kernel reduction: modulus 1, a zero square difference, a case where natural subtraction would be incorrect, the density-ranking reversal between moduli 4 and 9, and a window longer than its period.

## How the proof uses computation

Three finite checks establish the facts needed by the infinite argument:

1. For every unit input and start modulo 144, the complete period and all remainders obey the upper discrepancy bound. Counts through length 146 also obey the explicit finite target.
2. For each competing modulus from 1 through 256, a valid unit input has sufficiently many passing positions in a period. Every remainder has a valid start witnessing the required lower bound.
3. For every competing modulus and each length from 1 through 146, a valid input and start attain at least the finite upper target for modulus 144.

The third check groups witnesses by input residue to reuse masks. It explicitly verifies that every required witness belongs to a checked group. All checks validate input and start bounds and recompute the actual mask counts in Lean.

[WindowScan.lean](WindowScan.lean) proves that a cumulative scan produces exactly the same Boolean checks as recomputing every prefix count. This equality permits faster evaluation of the upper certificate while preserving its original specification.

[WitnessData.lean](WitnessData.lean) contains untrusted encoded witness data. Parsing defaults cannot create a proof: the resulting values must still pass all validity and count checks. The converter uses the existing Python certificate to propose witnesses. The theorem never assumes that Python computed a correct answer. [LowerSoundness.lean](LowerSoundness.lean) and [CertificateBounds.lean](CertificateBounds.lean) prove that the checked Boolean statements imply the mathematical bounds consumed by the endpoint.

[GenericWindow.lean](GenericWindow.lean) proves the period/remainder identity and its upper and lower bound consequences. The endpoint combines the finite prefix with these consequences at length 147; their separation is strict from length 148.

## Trust and formal scope

The finite checks use Lean's standard `native_decide` facility. The final axiom inspection is saved with the verification record. Native evaluation relies on the correctness of Lean's compiler and runtime in addition to its logical kernel; it is not a computation performed entirely by kernel reduction. The proof sources contain no `sorry`, `admit`, custom axiom declaration, external implementation, or unsafe replacement for a mathematical definition.

The formalized results are the central all-length optimality theorem, strict optimality from length 148, the discrepancy upper bound, the competitor lower bound, and the semantic bridge to the residue definition. The paper's exact all-length envelope formula, sharpness examples, budget table, and historical claims are outside this formalization. Their analytic proofs and original Python evidence remain in the surrounding package. Successful formal verification does not establish historical novelty or human peer review.

## Reproduce

The project pins Lean 4.19.0 and mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. `lake-manifest.json` pins the transitive packages. Install Lean through elan, then run from this directory:

```bash
lake exe cache get
bash verify.sh
```

Dependency setup downloads mathlib and its compiled dependency cache. The verification script rechecks every local proof source in dependency order, reruns all native finite checks, and prints the endpoint statements and axiom lists. Project proof objects are generated locally and are not distributed. A failed command stops the script. The measured time and memory are recorded in `verification.json`; the Python verifier's 120-second and 256-MiB limits do not apply to Lean or dependency installation.

To regenerate the untrusted data in a disposable copy of the numbered folder:

```bash
python3 -B generate_witness_data.py
sha256sum -c SOURCE_SHA256SUMS
bash verify.sh
```

The converter accepts no arguments and reads the fixed sibling `wave2_b` certificate. Its provenance JSON records the source and generated-data hashes. Hash agreement identifies source bytes; Lean must still verify their mathematical consequences.
