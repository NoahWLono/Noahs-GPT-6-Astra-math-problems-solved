#!/usr/bin/env bash
# Typeset only. Does not invoke Lean, install software, or access the network.
set -euo pipefail
cd "$(dirname "$0")"
export SOURCE_DATE_EPOCH=1791849600
export FORCE_SOURCE_DATE=1
export TZ=UTC
mkdir -p output/pdf qa
# A normal TeX Live installation uses its existing format and font maps.
# The supplied cloud image has broken system cache symlinks, so use a local
# format/cache and search the installed source trees when no format is found.
if ! kpsewhich --progname=pdflatex pdflatex.fmt >/dev/null 2>&1; then
  if [[ ! -d /usr/share/texlive/texmf-dist ]]; then
    echo 'A complete TeX Live installation with pdfLaTeX and BibTeX is required.' >&2
    exit 1
  fi
  export TEXMF="{$PWD/qa/texmf-var,/usr/share/texmf,/usr/share/texlive/texmf-dist,/etc/texmf}"
  export TEXMFVAR="$PWD/qa/texmf-var" TEXMFCONFIG="$PWD/qa/texmf-config"
  export TEXFORMATS="$PWD/qa/texmf-var/web2c/pdftex:"
  if [[ ! -f "$TEXMFVAR/web2c/pdftex/pdflatex.fmt" ]]; then
    mkdir -p "$TEXMFVAR/web2c/pdftex"
    (cd "$TEXMFVAR/web2c/pdftex" && pdftex -ini -etex -interaction=nonstopmode -halt-on-error \
      -jobname=pdflatex '\input pdflatex.ini') > qa/format-build.log 2>&1
  fi
fi
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf q7-local-identifying-draft.tex
(cd output/pdf && BIBINPUTS=../../: bibtex q7-local-identifying-draft)
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf q7-local-identifying-draft.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=output/pdf q7-local-identifying-draft.tex
