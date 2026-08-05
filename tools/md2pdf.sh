#!/usr/bin/env bash
# Render a repo markdown doc to PDF. Usage: tools/md2pdf.sh <in.md> [out.pdf]
# Engine: pandoc + tectonic (self-contained LaTeX; no TeX Live install needed).
set -euo pipefail

IN=${1:?usage: tools/md2pdf.sh <in.md> [out.pdf]}
OUT=${2:-${IN%.md}.pdf}

command -v pandoc   >/dev/null || { echo "need pandoc (brew install pandoc)"; exit 1; }
command -v tectonic >/dev/null || { echo "need tectonic (brew install tectonic)"; exit 1; }

# Title/date come from the H1 and the "Review date" line so the body stays
# readable as plain markdown; strip the H1 so it is not typeset twice.
TITLE=$(sed -n '1s/^# //p' "$IN")

HEADER=$(mktemp /tmp/md2pdf-header.XXXXXX.tex)
trap 'rm -f "$HEADER"' EXIT
cat > "$HEADER" <<'TEX'
\usepackage{booktabs}
\usepackage{microtype}
% Wide result tables: shrink and allow ragged-right cells so columns stop
% wrapping mid-number.
\let\oldlongtable\longtable
\def\longtable{\footnotesize\oldlongtable}
\usepackage{ragged2e}
\AtBeginDocument{\RaggedRight}
\setlength{\emergencystretch}{3em}
\usepackage{sectsty}
\allsectionsfont{\normalfont\sffamily\bfseries}
TEX

sed '1{/^# /d;}' "$IN" | pandoc \
  --from=markdown+pipe_tables \
  --pdf-engine=tectonic \
  --metadata title="$TITLE" \
  --metadata date="$(date +%Y-%m-%d)" \
  --include-in-header="$HEADER" \
  -V geometry:margin=0.9in \
  -V fontsize=10pt \
  -V linkcolor=black \
  -V colorlinks=true \
  -o "$OUT"

echo "wrote $OUT"
