# Composite inner exponents addendum

This immediate corollary replaces the original inner prime exponent by any natural `m > 1` whose prime divisors exceed the outer prime `p >= 5`, under the same integer and valuation assumptions. Repeated prime factors and common factors of `m` and `k` are allowed. No novelty or priority is claimed; the full fixed-gap Pillai conjecture remains unresolved.

The [paper](composite-inner-addendum.pdf), [LaTeX source](composite-inner-addendum.tex), [proof](proof/CompositeInnerPillai.lean), [audit](proof/CompositeInnerPillaiAudit.lean), and [exact theorem map](THEOREM_MAP.md) are unchanged. The pinned upstream odd-binomial criterion and its license are in `proof/upstream/`. The exact new root is `PillaiScoped.irreducible_composition_of_inner_prime_factors_gt`.

## Inherited prerequisite

This is additive to the [original Lean package](../original/lean/README.md). It is not a standalone dependency distribution. First rebuild the original package with Lean 4.32.2 and Mathlib revision `905b95818eb32af7874a58b427f50c1711a5e96c`. Then compile the pinned upstream `Mathlib.FieldTheory.KummerExtension`, the wrapper and its audit in that same complete dependency environment.

For example, from the top-level `07-scoped-binomial-irreducibility` folder after the original clean-local build:

```sh
ROOT="$PWD"
cd original/lean
lake build '+Mathlib.FieldTheory.KummerExtension:olean'
lake env python3 -c 'import os; print(os.pathsep.join(p for p in os.environ["LEAN_PATH"].split(os.pathsep) if os.path.isdir(p)))' > dependency-path.txt
LEAN_BIN="$(lake env which lean)"
UPSTREAM="$(cat dependency-path.txt)"
mkdir "$ROOT/addendum-build"
export LEAN_PATH="$ROOT/addendum-build:$ROOT/original/lean/fresh-build/objects:$UPSTREAM"
export LEAN_NUM_THREADS=1
unset LEAN_SRC_PATH
cd "$ROOT/addendum/proof"
"$LEAN_BIN" -M 3500 -j 1 -o "$ROOT/addendum-build/CompositeInnerPillai.olean" CompositeInnerPillai.lean
"$LEAN_BIN" -M 3500 -j 1 -o "$ROOT/addendum-build/CompositeInnerPillaiAudit.olean" CompositeInnerPillaiAudit.lean
```

Use a fresh `addendum-build` directory. The commands use one job and a 3,500 MB Lean limit; monitor available RAM and disk separately. Do not add the partial upstream source-copy directory to `LEAN_PATH`. Preserve the inherited rational-algebra instance in the exact proof source. These portable commands document the intended reproduction, and have not been run as a new complete Lean build in the publication environment.

## Verification and document reproduction

The new root and audit compiled, the requested-type comparison passed, and the 45,387-declaration closure passed patched official Lean 4.34.1 and independent nanoda 0.4.19 checking. Only `propext`, `Classical.choice`, and `Quot.sound` occur in production. See [the public verification report](../VERIFICATION.md) for the exact boundary, including the non-isolated adapter and absence of a new whole-source clean rebuild.

Run `bash build_pdf.sh` from this directory to rebuild the paper with installed TeX and Poppler. During publication preparation, the unchanged source rebuilt without dependency downloads; all three rendered pages and extracted text matched the delivered PDF. The delivered Content Credentials-bearing PDF is retained. See [publication format and integrity](../PUBLICATION_FORMAT.md) for its actual checksum and the distinction from historical PDF hashes.

The newly assembled public source ZIP omits historical machine-specific execution metadata. It does not replace the historical sealed archive identity cited by the unchanged paper; all mathematical sources are identical.
