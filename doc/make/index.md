Requirements
------------

- C++11 compatible compiler
- [CMake](http://www.cmake.org)
- [GMP (GNU multiprecision library)](http://gmplib.org/)

Platform-Specific Setup
-----------------------

- [Linux (Ubuntu)](ubuntu-16.04.md)
- [Windows (msys2)](msys2.md)
- [Windows (Visual Studio)](msvc.md)
- [macOS](osx-10.9.md)

Generic Build Instructions
--------------------------

Setting up a basic release build using `make`:

```bash
git clone https://github.com/leanprover/lean
cd lean
mkdir -p build/release
cd build/release
cmake ../../src
make
```

Setting up a basic debug build using `make`:

```bash
git clone https://github.com/leanprover/lean
cd lean
mkdir -p build/debug
cd build/debug
cmake -D CMAKE_BUILD_TYPE=DEBUG ../../src
make
```

Building JS / wasm binaries with Emscripten
------------------------

- Install Emscripten, following the instructions [here](https://emscripten.org/docs/getting_started/downloads.html). Before building, be sure to set up the environment using something like `source ./emsdk_env.sh` in your terminal.

Setting up a basic release build using `make`:

```bash
git clone https://github.com/leanprover/lean
cd lean
mkdir -p build/emscripten
cd build/emscripten
emconfigure cmake ../../src/ -DCMAKE_BUILD_TYPE=Emscripten
NODE_OPTIONS="--max-old-space-size=4096" emmake make
```

Here's a brief description of the build output. The paths given below are relative to the `build/emscripten` directory:

- `shell/lean.js` and `shell/lean.wasm` constitute a JS / wasm version of the main `lean` executable. Similarly, `checker/leanchecker.js` and `checker/leanchecker.wasm` are the JS / wasm version of `leanchecker`. There are also various testing binaries in the subdirectories `test`. All of these are primarily meant for use with `ctest`, though they can also be run from the command-line using `node` as in the shell script placed at `shell/lean`.

- `shell/lean_js.js` is an obsolete browser version of the `lean_js` server which seems to be tricky to build. It is not built by default; you can try building it by running `NODE_OPTIONS="--max-old-space-size=4096" emmake make lean_js`. This file can be quite large as it contains an uncompressed bundle of lean's core library `.olean` files. The file `shell/lean_js.html` demonstrates its use.

- The files `shell/lean_js_js.js`, `shell/lean_js_wasm.js`, and `shell/lean_js_wasm.wasm` are browser versions of the lean server, suitable for use with the [lean-web-editor](https://github.com/leanprover/lean-web-editor). To use, copy these three files to the `dist/` subdirectory of your `lean-web-editor` directory.

Useful CMake Configuration Settings
-----------------------------------

Pass these along with the `cmake ../../src` command.

* `-G Ninja`
  CMake 2.8.11 supports the [Ninja](https://ninja-build.org/) build system.
  [Some people report][ninja_work] that using
  Ninja can reduce the build time, esp when a build is
  incremental. Call `ninja` instead of `make` to build the project.

  [ninja_work]: https://web.archive.org/web/20120509074955/https://plus.google.com/108996039294665965197/posts/SfhrFAhRyyd

* `-D CMAKE_BUILD_TYPE=`
  Select the build type. Valid values are `RELEASE` (default), `DEBUG`,
  `RELWITHDEBINFO`, and `MINSIZEREL`.

* `-D CMAKE_CXX_COMPILER=`
  Select the C++ compiler to use.

* `-D LEAN_IGNORE_OLEAN_VERSION`
  The `.olean` files are tagged with the Lean version they were produced with.
  This means that by default, the core library has to be recompiled after e.g.
  every `git commit`. Use this option to avoid the version check. The `.olean`
  files can be removed manually by invoking `make/ninja clean-olean`.

Incremental Builds
------------------
To speed up interactive development, you can use `make -j<nthreads> bin_lean` or `ninja shell/bin_lean`, which will build the Lean executable (into `bin/`), but not all the tests.

Further Information
-------------------

- [Using CCache](ccache.md) to avoid recompilation
- [Measuring Code Coverage](coverage.md)
- [Compiling Lean with Split Stacks](split-stack.md)
