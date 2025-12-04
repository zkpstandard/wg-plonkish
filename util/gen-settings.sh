#!/bin/bash
#
# Generates `.vscode/settings.json` from `src/macros.txt`.

set -efuo pipefail

function main
{
  cat <<'EOF' >$2
// This file is generated from `src/macros.txt` by `util/gen-settings.sh`.
{
    "markdown.extension.katex.macros": {
EOF
  sed -e 's/[\\]COL:/\\COL:\\hspace\{0.9em\}/;s/[\\]/\\\\/g;s/\([^:]*\):\(.*\)/        "\1": "\2"/;$ ! s/\(..*\)/\1,/' <$1 >>$2
  cat <<'EOF' >>$2

    }
}
EOF
}

main src/macros.txt .vscode/settings.json
