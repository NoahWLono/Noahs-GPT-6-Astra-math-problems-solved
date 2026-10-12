#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p output/pdf tmp/pdfs/texmf-var tmp/pdfs/texmf-config
# This machine has installed TeX sources but no generated filename database or
# pdflatex format. Keep every generated support file in this document tree.
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texmf,/usr/share/texlive/texmf-dist}"
fi
export TEXMFVAR="$PWD/tmp/pdfs/texmf-var"
export TEXMFCONFIG="$PWD/tmp/pdfs/texmf-config"
export TEXFORMATS="$PWD/tmp/pdfs//:"
export TEXFONTMAPS="$PWD/tmp/pdfs//:/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd tmp/pdfs && pdftex -etex -ini -interaction=nonstopmode -halt-on-error \
    -jobname=pdflatex -progname=pdflatex pdflatex.ini > init-format.log 2>&1)
fi
if [[ ! -f tmp/pdfs/pdftex.map ]]; then
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map > tmp/pdfs/pdftex.map
fi
for pass in 1 2; do
  pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf \
    homogeneous-operator-addendum.tex > "tmp/pdfs/pdflatex-pass${pass}.log" 2>&1
done
pdfinfo output/pdf/homogeneous-operator-addendum.pdf > tmp/pdfs/pdfinfo.txt
pdftotext -layout output/pdf/homogeneous-operator-addendum.pdf tmp/pdfs/extracted.txt
pdftoppm -r 100 -png output/pdf/homogeneous-operator-addendum.pdf tmp/pdfs/page >/dev/null 2>&1
