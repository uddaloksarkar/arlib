#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if rg -n '^import ArlibCommunity(?:\.|$)' Arlib Arlib.lean; then
  echo 'error: Arlib must not import ArlibCommunity' >&2
  exit 1
fi

if rg -n '^namespace ArlibCommunity(?:\.|$)' Arlib Arlib.lean; then
  echo 'error: Arlib must not declare in the ArlibCommunity namespace' >&2
  exit 1
fi

if test -f BOUNDARY_MANIFEST.tsv && rg -n $'\tunclassified\t' BOUNDARY_MANIFEST.tsv; then
  echo 'error: boundary manifest contains unclassified modules' >&2
  exit 1
fi

if test -f BOUNDARY_MANIFEST.tsv; then
  declare -A owner_by_path=()
  while IFS=$'\t' read -r path owner _reason; do
    test "$path" = module && continue
    owner_by_path["$path"]="$owner"
  done < BOUNDARY_MANIFEST.tsv

  violations=0
  while IFS=: read -r source _line import_line; do
    test "${owner_by_path[$source]:-}" = core || continue
    module="${import_line#import }"
    target="${module//./\/}.lean"
    if test "${owner_by_path[$target]:-}" = community; then
      printf 'error: core module %s imports community module %s\n' "$source" "$target" >&2
      violations=$((violations + 1))
    fi
  done < <(rg -n --with-filename '^import Arlib(?:\.|$)' Arlib -g '*.lean' || true)
  if test "$violations" -ne 0; then
    exit 1
  fi
fi

echo 'Arlib boundary audit passed'
