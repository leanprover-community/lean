#!/bin/bash
set -exu
apt-get update
apt-get install -y m4
cd build
emconfigure cmake ../src $OPTIONS
NODE_OPTIONS="--max-old-space-size=4096" emmake make # -j2 leads to intermittent build errors
# TODO: fix emscripten tests
# ctest -j2 --output-on-failure
cd ..
