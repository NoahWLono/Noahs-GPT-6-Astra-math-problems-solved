#!/usr/bin/env bash
set -euo pipefail
paper_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
mkdir -p "$paper_dir/build"
cd "$paper_dir"
if command -v tectonic >/dev/null 2>&1; then
  tectonic --keep-logs --outdir build order_ten_frameproof.tex
elif command -v pdflatex >/dev/null 2>&1; then
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build order_ten_frameproof.tex
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=build order_ten_frameproof.tex
else
  printf '%s\n' 'Install Tectonic or a standard LaTeX distribution providing pdflatex.' >&2
  exit 127
fi
printf 'Built %s/build/order_ten_frameproof.pdf\n' "$paper_dir"
