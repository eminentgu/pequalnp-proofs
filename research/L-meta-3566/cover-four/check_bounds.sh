#!/bin/sh
# Compile the named bounds and print their kernel axioms from any working directory.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
research=$(dirname "$here")
repo=$(cd "$research/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
cd "$repo/lean"
lake build PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.Outside.L_meta_579 \
  PEqualNP.Outside.L_meta_615 PEqualNP.Outside.L_meta_8493 PEqualNP.Outside.L_meta_550 \
  PEqualNP.Outside.L_meta_1007 PEqualNP.Outside.L_meta_723
build() {
  src=$1
  module=$2
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -j1 -R "$2" -o "$1/$3.olean" "$2/$3.lean"' \
    sh "$scratch" "$src" "$module"
}
build "$research" Equivalence
for module in ResidualGraphs ResidualRuns ResidualThetas ResidualExplicit ResidualBounds; do
  build "$here" "$module"
done
for module in SideReaders ZeroFold SidePeel PendantCross; do
  build "$research" "$module"
done
build "$here" ResidualPartner
build "$here" ResidualPrivateReaders
