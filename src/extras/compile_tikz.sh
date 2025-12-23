#!/bin/bash
# Compile a .tikz file to PNG
# Usage: ./compile_tikz.sh input.tikz [output.png]

set -e

if [ -z "$1" ]; then
    echo "Usage: $0 input.tikz [output.png]"
    exit 1
fi

INPUT="$1"
BASENAME="${INPUT%.tikz}"
OUTPUT="${2:-${BASENAME}.png}"

# Create temporary tex file
TMPDIR=$(mktemp -d)
TMPFILE="${TMPDIR}/diagram.tex"

# Copy quiver.sty if available
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
if [ -f "${SCRIPT_DIR}/quiver.sty" ]; then
    cp "${SCRIPT_DIR}/quiver.sty" "${TMPDIR}/"
fi

cat > "$TMPFILE" << 'HEADER'
\documentclass{article}
\usepackage{tikz-cd}
\usepackage{amssymb}
\usetikzlibrary{decorations.pathmorphing}
\usetikzlibrary{nfold}
\usepackage{quiver}
\usepackage[active,tightpage]{preview}
\PreviewEnvironment{tikzcd}
\setlength\PreviewBorder{10pt}
\begin{document}
HEADER

# Strip the comment line and append tikz content
grep -v '^%' "$INPUT" >> "$TMPFILE"

cat >> "$TMPFILE" << 'FOOTER'
\end{document}
FOOTER

# Compile (may return non-zero on warnings, so check for PDF)
cd "$TMPDIR"
pdflatex -interaction=nonstopmode diagram.tex || true
if [ ! -f diagram.pdf ]; then
    echo "Failed to create PDF"
    exit 1
fi

# Convert PDF to PNG (try different tools)
if command -v pdftoppm &> /dev/null; then
    pdftoppm -png -r 300 -singlefile diagram.pdf diagram
    mv diagram.png "$OUTPUT"
elif command -v convert &> /dev/null; then
    convert -density 300 diagram.pdf -quality 90 "$OUTPUT"
elif command -v sips &> /dev/null; then
    # macOS: sips can't convert PDF directly, need intermediate step
    echo "sips cannot convert PDF to PNG directly. Install poppler (brew install poppler) for pdftoppm."
    exit 1
else
    echo "No PDF to PNG converter found. Install poppler or imagemagick."
    exit 1
fi
rm -rf "$TMPDIR"

echo "Created: $OUTPUT"
