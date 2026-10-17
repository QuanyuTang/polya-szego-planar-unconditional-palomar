#!/usr/bin/env bash
set -euo pipefail
repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
python3 scripts/check-release-inputs.py
lake exe cache get
# Reject incomplete canonical cache/traces instead of silently building Mathlib.
lake build --no-build --no-cache @mathlib/+Mathlib
while IFS= read -r target || [ -n "$target" ]; do
  case "$target" in
    ''|'#'*) continue ;;
    @/+*|@EllipticPdes/+*) ;;
    *) echo "error: unexpected reviewed Lake target: $target" >&2; exit 1 ;;
  esac
  printf 'Building %s\n' "$target"
  lake build "$target"
done < verification/build-targets.txt
# Confirm the actual submission targets remain up-to-date before replay.
lake build --no-build --no-cache @/+PlanarBucklingChallenge @/+PlanarBucklingSolution
