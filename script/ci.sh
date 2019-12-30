#!/usr/bin/env bash
set -e
mkdir -p build
cd build
# eval cmake ../src $CMAKE_OPTIONS
eval cmake -DCMAKE_BUILD_TYPE=$CMAKE_BUILD_TYPE \
                -DCMAKE_CXX_COMPILER=$CXX_FAMILY \
                -DTESTCOV=$TESTCOV \
                -DTCMALLOC=$TCMALLOC \
                -DMULTI_THREAD=$MULTI_THREAD \
                # -DSTATIC=OFF \
                -DSTATIC=$STATIC \
                -DLEAN_EXTRA_MAKE_OPTS=$LEAN_EXTRA_MAKE_OPTS \
                $OPTIONS \
                ../src
cmake --build . -j4
cpack
