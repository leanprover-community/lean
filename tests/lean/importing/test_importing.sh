#!/usr/bin/env bash
if [ $# -ne 1 ]; then
    echo "Usage: test_importing.sh [lean-executable-path]"
    exit 1
fi
ulimit -s 8192
LEAN=$1
export LEAN_PATH=../../../library:.

cat <<EOF > foo.lean
run_cmd tactic.trace "foo"
EOF
rm -f foo.olean

out=$($LEAN --make ./foo.lean 2>&1)
if [[ $out != "foo" ]]; then
    echo "-- Lean isn't building foo: got $out , expected foo"
    exit 1
fi

touch foo.lean
out=$($LEAN --make ./foo.lean 2>&1)
if [[ $out != "" ]]; then
    echo "-- Lean rebuilds foo on timestamp change: got $out , expected no output"
    exit 1
fi

cat <<EOF > x.lean
def x := 0
run_cmd tactic.trace "x"
EOF
cat <<EOF > y.lean
import x
def y := x
run_cmd tactic.trace "y"
EOF
cat <<EOF > z.lean
import y
def z := y
run_cmd tactic.trace "z"
EOF
rm -f x.olean y.olean z.olean

out=$($LEAN --make z.lean 2>&1 | tr -d '\n')
if [[ "$out" != "xyz" ]]; then
    echo "-- Wrong modules built: got $out , expected xyz"
    exit 1
fi

cat <<EOF > y.lean
def y := 1
run_cmd tactic.trace "y"
EOF

out=$($LEAN --make z.lean 2>&1 | tr -d '\n')
if [[ "$out" != "yz" ]]; then
    echo "-- Wrong modules built: got $out , expected yz"
    exit 1
fi

cat <<EOF > y.lean
import x
def y := x
run_cmd tactic.trace "y"
EOF

out=$($LEAN --make z.lean 2>&1 | tr -d '\n')
if [[ "$out" != "yz" ]]; then
    echo "-- Wrong modules built: got $out , expected yz"
    exit 1
fi

touch x.lean
out=$($LEAN --make z.lean 2>&1 | tr -d '\n')
if [[ "$out" != "" ]]; then
    echo "-- Wrong modules built: got $out , expected no output"
    exit 1
fi

rm -f foo.lean foo.olean x.lean x.olean y.lean y.olean z.lean z.olean
