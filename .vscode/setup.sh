#! /bin/bash

WORKDIR=$(pwd)

mkdir -p ./build/debug
mkdir -p ./build/release
mkdir -p ./build/emscripten

# make ccache

cd $WORKDIR/build/debug
cmake -DCMAKE_BUILD_TYPE=Debug -DCMAKE_CXX_COMPILER=$WORKDIR/.vscode/ccache.sh $WORKDIR/src

cd $WORKDIR/build/release
cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_CXX_COMPILER=$WORKDIR/.vscode/ccache.sh $WORKDIR/src

cd $WORKDIR/build/emscripten
emconfigure cmake $WORKDIR/src -DCMAKE_BUILD_TYPE=Emscripten -DLEAN_EMSCRIPTEN_BUILD=Main -DCMAKE_CXX_COMPILER=$WORKDIR/.vscode/ccache.sh

