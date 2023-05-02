#!/bin/bash
set -Eeo pipefail
# can't run build/shell/lean directly since the path in it is set by the docker container
LEAN_VERSION_DIGITS=$(node build/shell/lean.js -v | sed 's/Lean (version \([^,]*\),.*/\1/')
zip build/lean-$LEAN_VERSION_DIGITS-$LEAN_VERSION_STRING-browser.zip build/shell/lean_js_*
