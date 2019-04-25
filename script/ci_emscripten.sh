#!/bin/bash
set -e
mkdir build
cd build
emconfigure cmake ../src/ -DCMAKE_BUILD_TYPE=Emscripten
emmake make # -j2 doesn't work here because libgmp has to be built
travis_wait 60 ctest -j2 --output-on-failure
cd ..
