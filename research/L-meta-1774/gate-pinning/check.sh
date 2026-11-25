#!/bin/sh
set -eu
src_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
readers_dir="$src_dir/../shared-readers"
project=$(CDPATH= cd -- "$src_dir/../../../lean" && pwd)
build_dir=$(mktemp -d)
trap 'rm -rf -- "$build_dir"' EXIT
cd "$project"
lake build PEqualNP.Outside.L_meta_2573 PEqualNP.Outside.L_meta_4846 PEqualNP.Outside.L_meta_5465 PEqualNP.Outside.L_meta_2668
LEAN_PATH="$build_dir:$(lake env printenv LEAN_PATH)"
export LEAN_PATH
lean_bin=$(elan which lean)
"$lean_bin" -j1 -R "$src_dir/.." -o "$build_dir/SharedMask.olean" "$src_dir/../SharedMask.lean"
for module in Guarded Shannon Opposite Omit; do
  "$lean_bin" -j1 -R "$readers_dir" -o "$build_dir/$module.olean" "$readers_dir/$module.lean"
done
for module in Pin StarPin PinDescent PinDesk PinTree CriticalCases CriticalTree Sensitive LocalRigidity CriticalOr CriticalPairOr CriticalPairTree GroupedStar CriticalOrTree GroupedStarTree PrivateParents MatchingRigidity AuditPin; do
  "$lean_bin" -j1 -R "$src_dir" -o "$build_dir/$module.olean" "$src_dir/$module.lean"
done
