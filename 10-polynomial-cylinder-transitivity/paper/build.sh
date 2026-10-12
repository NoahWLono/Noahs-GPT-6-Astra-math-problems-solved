#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Requires a working TeX Live or equivalent installation and standard packages.
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error polynomial-cylinder-transitivity.tex > "build-pass${pass}.log" 2>&1
done
# Optional local rendering for visual review when Poppler is available.
if command -v pdftoppm >/dev/null && command -v pdfinfo >/dev/null; then
  mkdir -p rendered
  pdfinfo polynomial-cylinder-transitivity.pdf > rendered/pdfinfo.txt
  pdftoppm -r 115 -png polynomial-cylinder-transitivity.pdf rendered/page >/dev/null 2>&1
fi
