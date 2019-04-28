#!/bin/bash
set -e
apt-get update
apt-get install -y m4
mkdir build
cd build
emconfigure cmake ../src -DCMAKE_BUILD_TYPE=Emscripten
NODE_OPTIONS="--max-old-space-size=4096" emmake make # -j2 leads to intermittent build errors
ctest -j2 --output-on-failure
cd ..
