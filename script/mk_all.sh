#!/usr/bin/env bash
# Usage: ./script/mk_all.sh [subdirectory]
#
# Examples:
#   ./script/mk_all.sh
#   ./script/mk_all.sh data/
#
# Makes a ./library/$directory/all.lean importing all files inside $directory.
# If $directory is omitted, creates `./library/all.lean`.

cd "$( dirname "${BASH_SOURCE[0]}" )"/../library
if [[ $# = 1 ]]; then
  dir="$1"
else
  dir="."
fi

find "$dir" -name \*.lean -not -name all.lean \
  | sed 's,^\./,,;s,\.lean$,,;s,/,.,g;s,^,import ,' \
  | sort >"$dir"/all.lean
