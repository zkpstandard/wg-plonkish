#!/bin/bash
#
# Print out any md files within `./src` which aren't linked from SUMMARY.
#
# If there are any, exit with non-zero status

set -efuo pipefail

function main
{
  # Move to src dir regardless of `pwd`:
  cd "$(dirname "$(readlink -f "$0")")/../src"

  local DATADIR="$(mktemp --directory)"
  local LINKED="${DATADIR}/linked"
  local ACTUAL="${DATADIR}/actual"
  local DIFF="${DATADIR}/diff"

  parse-linked-files < './SUMMARY.md' > "$LINKED"
  find-actual-files > "$ACTUAL"

  set +o pipefail # It's ok for this pipeline to fail:
  diff -u "$LINKED" "$ACTUAL" | grep -Eve '^(\+\+\+|---)' | grep '^[+-]' | tee "$DIFF"

  if [ "$(wc -l < "$DIFF")" -eq 0 ]
  then exit 0
  else exit 1
  fi
}

function parse-linked-files
{
  grep '(' | sed 's/^.*(//; s/)$//' | grep -v '^$' | sort
}

function find-actual-files
{
  find . -type f -not -name 'SUMMARY.md' -name '*.md' | sort
}

main "$@"
