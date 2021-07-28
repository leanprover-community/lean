[msys2]: http://msys2.github.io
[pacman]: https://wiki.archlinux.org/index.php/pacman

Lean for Windows
----------------

A native Lean binary for Windows can be generated using [msys2].
It is easy to install all dependencies, it produces native
64/32-binaries, and supports a C++11 compiler.


## Installing dependencies

[The official webpage of msys2][msys2] provides one-click installers.
We assume that you install [msys2][msys2] at `c:\msys64`.
It has a package management system, [pacman][pacman], which is used in Arch Linux - you must use this to update `msys2` and install all of Lean's dependencies. The Lean build that's used in CI currently uses this set of commands (in any of the many installed `msys` shells):

```bash
pacman -Syu
```

And then, after restarting the shell:

```bash
pacman -Su
pacman -S --needed --overwrite * base-devel mingw-w64-x86_64-gcc mingw-w64-x86_64-gmp make mingw-w64-x86_64-cmake cmake git
```

Then follow the [generic build instructions](index.md) in the `msys mingw` shell, but make sure to append `-DINCLUDE_MSYS2_DLLS=ON -G Unix\ Makefiles` to the `cmake` commands.

## Install lean

You can use the `install` ninja/make target to install Lean into, by, default,
`C:\\User Programs (x86)\\LEAN`. To change this, add `-DCMAKE_INSTALL_PREFIX=path/you/want`
to your cmake invocation.
