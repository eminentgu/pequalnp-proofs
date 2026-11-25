#!/bin/sh
set -eu
src_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
project=$(CDPATH= cd -- "$src_dir/../../../lean" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT
cd "$project"
lake build PEqualNP.Defs
LEAN_PATH="$build_dir:$(lake env printenv LEAN_PATH)"
export LEAN_PATH
lean_bin=$(elan which lean)
"$lean_bin" -j1 -R "$src_dir/.." -o "$build_dir/SharedMask.olean" "$src_dir/../SharedMask.lean"
for module in Guarded Shannon GuardedTree GuardedCycle AuditGuarded; do
  "$lean_bin" -j1 -R "$src_dir" -o "$build_dir/$module.olean" "$src_dir/$module.lean"
done
