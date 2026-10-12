#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
mkdir -p output/pdf tmp/pdfs/texmf-var tmp/pdfs/texmf-config
if ! kpsewhich article.cls >/dev/null 2>&1; then
  export TEXMF="{/usr/share/texmf,/usr/share/texlive/texmf-dist}"
fi
export TEXMFVAR="$PWD/tmp/pdfs/texmf-var"
export TEXMFCONFIG="$PWD/tmp/pdfs/texmf-config"
export TEXFORMATS="$PWD/tmp/pdfs//:"
export TEXFONTMAPS="$PWD/tmp/pdfs//:/usr/share/texmf/fonts/map//:/usr/share/texlive/texmf-dist/fonts/map//:"
if ! kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  (cd tmp/pdfs && timeout 20 pdftex -etex -ini -interaction=nonstopmode -halt-on-error \
    -jobname=pdflatex -progname=pdflatex pdflatex.ini > init-format.log 2>&1)
fi
if [[ ! -f tmp/pdfs/pdftex.map && -f /usr/share/texmf/fonts/map/dvips/lm/lm.map ]]; then
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/*.map > tmp/pdfs/pdftex.map
fi
for pass in 1 2; do
  timeout 20 pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf \
    nakai-quartic-certificate.tex > "tmp/pdfs/pdflatex-pass${pass}.log" 2>&1
done
pdfinfo output/pdf/nakai-quartic-certificate.pdf > tmp/pdfs/pdfinfo.txt
pdftotext -layout output/pdf/nakai-quartic-certificate.pdf tmp/pdfs/extracted.txt
pdftoppm -r 90 -png output/pdf/nakai-quartic-certificate.pdf tmp/pdfs/page >/dev/null 2>&1
