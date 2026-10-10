#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p build
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build short-private-pools.tex
done
printf 'PDF: paper/build/short-private-pools.pdf\n'
