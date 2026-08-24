#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

# This intentionally records source declarations rather than environment
# internals, so it remains useful while modules are being renamed across the two
# packages.  The final audit compares normalized declaration names and source
# hashes against this baseline.
rg -n --with-filename \
  '^(?:noncomputable )?(?:abbrev|def|structure|class|inductive|theorem|lemma|instance)\b' \
  Arlib -g '*.lean' | sort

