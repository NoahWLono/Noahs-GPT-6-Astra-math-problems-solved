# Verification and trust boundary

The theorem applies to the original Boolean code predicate on all 128 cube vertices. Its final source is unconditional. The mathematical scope and all major reduction interfaces are reviewed in [SPEC.md](SPEC.md).

The custom proof sources and compiler-quoted data are frozen by SHA-256 manifests. A hash checks identity, not truth. The portable verifier builds all custom modules freshly, checks their successful compiler exits, requires the designated named axiom reports, and checks the fully qualified final theorem through an explicit type ascription.

Allowed logical foundations are the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. No external SAT answer, Python witness result, textual receipt or manifest hash is used as a new logical axiom. Quoted JSON is input to proof-producing or kernel-checked computations. The final theorem has a checked proof body in its defining module.

Lean's new module system may expose a body-hidden imported public theorem as `.axiomInfo`. The audit deliberately observes this interface. That observation alone proves nothing about the underlying body: the defining module must also be freshly compiled and its own standard-axiom audit accepted. The fresh full-closure verifier is designed to prevent stale/mixed custom objects from substituting for that check.

The trusted computing base still includes the official Lean compiler/kernel and standard library, the pinned Mathlib/dependency objects or their reproducible source builds, the operating system/hardware, and correct input handling. The Python orchestration and log parser can themselves be reviewed; they are not a formal proof of the build's integrity. No claim is made to have independently audited Lean, Mathlib, every finite enumeration by hand, or hardware correctness.

Current evidence distinctions:

- Initial coherent final composition: passed, original predicate and standard named axioms reported.
- Complete independent source closure: passed, including all 3,046 modules and 162 required named theorem audits; see INDEPENDENT_VERIFICATION.md.
- Public portable verifier: static checks and a 12-module compiler smoke test passed; full run not performed.
- Independent direct witness check: passed for all vertices and all adjacent pairs.

These statements must be updated only from completed, reviewed receipts. No success should be inferred from a running process or a partial build.
