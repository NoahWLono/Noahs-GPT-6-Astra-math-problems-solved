#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
mkdir -p build
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build euler-critical-limit.tex
done
cp build/euler-critical-limit.pdf euler-critical-limit.pdf
