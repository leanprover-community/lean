#!/usr/bin/env bash
set -e
mkdir -p build
cd build

if [ $CFG == 'MINGW64' ]; then
    OPTIONS=''
    cmake ../src -DINCLUDE_MSYS2_DLLS=ON -DCMAKE_BUILD_TYPE=Release $OPTIONS -G 'Unix Makefiles'
else
    cmake ../src -DCMAKE_BUILD_TYPE=Release
              -DCMAKE_TOOLCHAIN_FILE=c:/tools/vcpkg/scripts/buildsystems/vcpkg.cmake
              -DLEAN_EXTRA_CXX_FLAGS=/GL-
              -DLEAN_EXTRA_LINKER_FLAGS_MSVC=/LTCG:OFF
              -G "NMake Makefiles"
fi

cmake --build . -j4
cpack
