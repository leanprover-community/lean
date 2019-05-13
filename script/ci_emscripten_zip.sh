#!/bin/bash
set -e
# can't run build/shell/lean directly since the path in it is set by the docker container
# LEAN_VERSION_DIGITS=$(node build/shell/lean.js -v | sed 's/Lean (version \([^,]*\),.*/\1/')
echo "tracing"
# echo "- " $LEAN_VERSION_DIGITS
echo "- " lean-browser.zip
ls build/shell/lean_js_*
zip build/lean-browser.zip build/shell/lean_js_*
ls build/
NODE_DEBUG=fs node build/shell/lean.js -v
