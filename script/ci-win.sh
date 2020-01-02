#!/usr/bin/env bash
set -e
mkdir -p build
cd build
            # CMAKE_OPTIONS: -DCMAKE_BUILD_TYPE=Release -G "Unix Makefiles" -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++

if [ $CFG == 'MINGW64' ]; then
    OPTIONS=''
    cmake ../src -DINCLUDE_MSYS2_DLLS=ON -DCMAKE_BUILD_TYPE=Release $OPTIONS -G 'Unix Makefiles'
              -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
else
    cmake ../src -DCMAKE_BUILD_TYPE=Release
              -DCMAKE_TOOLCHAIN_FILE=c:/tools/vcpkg/scripts/buildsystems/vcpkg.cmake
              -DLEAN_EXTRA_C_FLAGS=/GL-
              -DLEAN_EXTRA_CXX_FLAGS=/GL-
              -DLEAN_EXTRA_LINKER_FLAGS_MSVC=/LTCG:OFF
              -G "Unix Makefiles"
              -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++
              # -G "NMake Makefiles"
fi

cmake --build . -j4
cpack
