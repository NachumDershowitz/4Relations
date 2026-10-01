#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ -n "${PDFLATEX:-}" ]; then
  tex_engine=$PDFLATEX
elif [ -x /Library/TeX/texbin/pdflatex ]; then
  tex_engine=/Library/TeX/texbin/pdflatex
else
  tex_engine=pdflatex
fi
mkdir -p build
for pass in 1 2; do
  "$tex_engine" -interaction=nonstopmode -halt-on-error \
    -output-directory=build Four_Well_Founded_Relations.tex
done
cp build/Four_Well_Founded_Relations.pdf Four_Well_Founded_Relations.pdf
