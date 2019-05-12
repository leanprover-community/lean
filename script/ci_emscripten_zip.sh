#!/bin/bash
set -e
# can't run build/shell/lean directly since the path in it is set by the docker container
LEAN_VERSION_DIGITS=$(node build/shell/lean.js -v | sed 's/Lean (version \([^,]*\),.*/\1/')
echo "tracing"
echo "- " $LEAN_VERSION_DIGITS
echo "- " lean-$LEAN_VERSION_DIGITS-$LEAN_VERSION_STRING-browser.zip
ls build/
zip build/lean-$LEAN_VERSION_DIGITS-$LEAN_VERSION_STRING-browser.zip build/shell/lean_js_*
