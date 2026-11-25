#!/bin/sh
# Compile the named bounds and print their kernel axioms from any working directory.
set -eu
here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
research=$(dirname "$here")
repo=$(cd "$research/../.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
project=${PEQUALNP_LEAN_PROJECT:-"$repo/lean"}
cd "$project"
lake build PEqualNP.MetaComplexity.Helpers.PermInputs PEqualNP.Outside.L_meta_579 \
  PEqualNP.Outside.L_meta_615 PEqualNP.Outside.L_meta_8493 PEqualNP.Outside.L_meta_550 \
  PEqualNP.Outside.L_meta_1007 PEqualNP.Outside.L_meta_723 PEqualNP.Outside.L_meta_4342 \
  PEqualNP.Research.L_meta_1774.CoveredOwnership
build() {
  src=$1
  module=$2
  lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean -j1 -R "$2" -o "$1/$3.olean" "$2/$3.lean"' \
    sh "$scratch" "$src" "$module"
}
python3 "$here/partial15/verify.py" --project "$project" --build-dir "$scratch" --jobs 2
for module in SideReaders ZeroFold SidePeel PendantCross RowFold Descent; do
  build "$research" "$module"
done
for module in ResidualRuns ResidualExplicit ResidualPartner ResidualPrivateReaders ResidualFifteen ResidualBounds; do
  build "$here" "$module"
done
