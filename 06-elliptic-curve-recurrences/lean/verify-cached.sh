#!/usr/bin/env bash
# Direct source rebuild using already-provisioned compiler/dependency caches.
# No network requests, downloads, installation, or Lake dependency resolution.
set -euo pipefail
cd -- "$(dirname -- "$0")"
: "${LEAN_BIN:?Set LEAN_BIN to the pinned Lean 4.32.2 executable}"
: "${CACHE_PACKAGES:?Set CACHE_PACKAGES to the directory containing cached dependency packages}"
if [[ "$($LEAN_BIN --short-version)" != "4.32.2" ]]; then
  echo "This project requires Lean 4.32.2." >&2
  exit 1
fi
sha256sum -c SOURCE_SHA256SUMS
objects="$(mktemp -d "${TMPDIR:-/tmp}/astra01-lean-objects.XXXXXX")"
cache_paths="$(find "$CACHE_PACKAGES" -type d -path '*/.lake/build/lib/lean' -print | paste -sd: -)"
if [[ -z "$cache_paths" ]]; then
  echo "No compiled dependency directories found." >&2
  exit 1
fi
export LEAN_PATH="$objects${EXTRA_LEAN_PATH:+:$EXTRA_LEAN_PATH}:$cache_paths"
mkdir -p verification-output
for file in PrimeOrbit PolynomialIdentities SharpnessCertificate FiniteFieldAction ProjectiveFieldCondition ExtensionDegree PrimeFieldArithmetic ProjectiveOrder CyclicFieldTheorem InvariantDivisor ProjectiveFixedPoint DedekindDivisor RationalFunctionDivisor EllipticAffineDivisor EllipticFinitePlaces FractionalDivisorDegree SeparablePrimeNorm SeparableIdealNorm FunctionFieldPlaces FunctionFieldProductFormula EllipticFunctionField EllipticInfinity EllipticPlaceDictionary EllipticPointDivisor EllipticFiberDegree EllipticTranslation FunctionFieldIntrinsicPlace FunctionFieldPlaceEquiv FunctionFieldPlaceAction EllipticAutomorphismDivisor EllipticCompositionDegree EllipticDegreePositive GlobalDegreeObstruction EllipticPointResidues ValuationResidueArithmetic EllipticTranslationLocal EllipticAuxiliaryPoints TranslationActionRigidity EllipticTranslationCovariance LinearFractionFixedFiber EllipticFixedFiber GlobalRecurrenceObstruction EllipticCoincidenceDivisor EllipticProjectiveValue FiniteAgreementObstruction FiniteMenuObstruction RationalProjectiveComposition ProjectiveRecurrenceBounds GlobalProjectiveRecurrence EllipticCoordinatePoleDegree EllipticXYDegrees ShortCurveYSemiconjugacy CharacteristicSevenExample SharpnessActualGroup SharpnessActualOrbit LinearFractionProjective SharpnessProjectiveAgreements EllipticXProjectiveValue SharpnessBaseChange LinearFractionBaseChange SharpnessCoverMinimum SharpnessGeometricAgreements SharpnessMenuEndpoint RationalProjectiveBaseChange SharpnessBaseFieldMinimum EllipticDuplicationPolynomials EllipticProjectiveDoubling EllipticDoublingIteration DoublingEvaluationCost DivisorClassCriterion EllipticAffineClassCriterion AdicRingEquiv EllipticAffineDivisorCoefficients EllipticPrincipalFiniteCoefficients EllipticPrincipalCriterion EllipticWeilFunction EllipticWeilConstantRatio EllipticXDifferenceDivisor EllipticAddSubAlgebra EllipticAddSubCompatibility EllipticAddSubAllPoints EllipticAddSubValuation EllipticAddSubMaxValuation EllipticProjectiveHeightDivisor EllipticHeightScaling ValuationSymmetricSquare EllipticSymmetricHeight EllipticHeightParallelogram EllipticHeightNormalization IntegerQuadraticHeight EllipticHeightCauchySchwarz EllipticFrobenius EllipticHeightPowers EllipticFrobeniusHeight EllipticChordExpansion EllipticChordValuation EllipticFrobeniusGeneric EllipticChordPole EllipticCoordinateInfinityValuation EllipticFrobeniusInfinity EllipticFrobeniusRationalPoles EllipticFrobeniusOrbitBound EllipticHasseUpper EllipticFiniteFieldUpper EllipticQuadraticFibers EllipticCharacterCount EllipticQuadraticTwist EllipticTwistCount EllipticHasseOdd PrimeFullGroupObstruction ProjectiveQuotientAction ProjectiveQuotientRecurrence PrimeFullGroupPGLObstruction; do
  sha256sum "$file.lean" > "verification-output/$file.log"
  "$LEAN_BIN" -M "${LEAN_MEMORY_MB:-3500}" -o "$objects/$file.olean" "$file.lean" \
    >> "verification-output/$file.log" 2>&1
  cat "verification-output/$file.log"
  if grep -Eq 'sorryAx|Lean.ofReduceBool|Lean.trustCompiler|error:' "verification-output/$file.log"; then
    echo "Unacceptable verification output for $file" >&2
    exit 1
  fi
done
printf 'All 113 modules checked from source. Fresh objects: %s\n' "$objects"
