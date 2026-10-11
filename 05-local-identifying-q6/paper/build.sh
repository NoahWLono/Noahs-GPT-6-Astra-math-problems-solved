#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
# Ordinary TeX Live installations need only these two pdflatex invocations.
# This container has unpacked TeX files but no usable format/map database.
if kpsewhich pdflatex.fmt >/dev/null 2>&1; then
  engine=(pdflatex)
else
  cache="${Q6_TEX_CACHE:-/tmp/q6-paper-tex}"
  mkdir -p "$cache/config" "$cache/var/fonts/map/pdftex"
  export TEXMF="{$cache/config,$cache/var,/usr/share/texlive/texmf-dist,/usr/share/texmf,/etc/texmf}"
  export TEXMFVAR="$cache/var" TEXMFCONFIG="$cache/config"
  if [[ ! -f "$cache/var/pdflatex.fmt" ]]; then
    (cd "$cache/var" && pdftex -ini -etex -jobname=pdflatex \
      -interaction=nonstopmode '\input pdflatex.ini' > format-build.log)
  fi
  cat /usr/share/texmf/fonts/map/dvips/lm/lm.map \
    /usr/share/texlive/texmf-dist/fonts/map/dvips/amsfonts/{cm,cmextra,latxfont,symbols}.map \
    > "$cache/var/fonts/map/pdftex/pdftex.map"
  engine=(pdftex "-fmt=$cache/var/pdflatex.fmt")
fi
"${engine[@]}" -interaction=nonstopmode -halt-on-error main.tex > build.log
"${engine[@]}" -interaction=nonstopmode -halt-on-error main.tex >> build.log
if grep -Eq 'Overfull|undefined references|undefined citations' main.log; then
  echo 'Layout or reference issue requires review.' >&2
  exit 1
fi
pdfinfo main.pdf | grep Pages
