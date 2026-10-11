#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"

# Dependency setup is documented in README.md. Every project module is
# re-elaborated here, including all three native finite checks.
lake env lean --version
mkdir -p .lake/build/lib/lean
for module in GenericWindow WindowScan Model SemanticBridge WitnessData FiniteChecks LowerSoundness CertificateBounds MainTheorem; do
  printf 'Checking %s.lean\n' "$module"
  lake env lean -o ".lake/build/lib/lean/$module.olean" "$module.lean"
done
