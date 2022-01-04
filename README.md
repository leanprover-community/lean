<p align=center><a href="https://leanprover-community.github.io"><img src="https://leanprover.github.io/images/lean_logo.svg" alt="logo" width="300px"/></a></p>
<table>
  <tr>
    <th>License</th><th>Continuous integration</th><th>Chat</th>
  </tr>
  <tr>
    <td><a href="LICENSE"><img src="https://img.shields.io/badge/license-APACHE_2-green.svg?dummy" title="License"/></a></td>
    <td>
      <a href="https://github.com/leanprover-community/lean/actions"><img src="https://github.com/leanprover-community/lean/workflows/lean%20core%20build/badge.svg?branch=master" alt="github actions"/></a>
      <a href="https://app.bors.tech/repositories/24760"><img src="https://bors.tech/images/badge_small.svg" alt="Bors enabled"/></a>
    </td>
    <td><a href="https://leanprover.zulipchat.com"><img src="https://img.shields.io/badge/zulip-join_chat-brightgreen.svg" alt="Join the Zulip chat"/></a></td>
  </tr>
</table>

About
-----

- **Important**: This is Lean 3.36.0c, a fork of Lean 3 maintained and updated by the Lean community. The last official release of Lean 3.x was Lean 3.4.2, which can be found [here](https://github.com/leanprover/lean). The Lean developers are currently developing [Lean 4](https://github.com/leanprover/lean4).
- [Lean Homepage](http://leanprover.github.io)
- [Lean Prover Community Homepage](https://leanprover-community.github.io)
- [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/index.html)
- [Change Log](doc/changes.md)
- [Lean 3.4.2 FAQ](doc/faq.md)
- For HoTT mode, please use [Lean2](https://github.com/leanprover/lean2).

Installation
------------

If you want to use Lean, the recommended way to install Lean is following [these instructions under Regular install](https://leanprover-community.github.io/get_started.html#regular-install).

If you want to modify the code of Lean or the core library, the recommended way is to [build Lean from source](doc/make/index.md).

If you want to modify *a single file* in the core library (not the C++ source), then instead of building Lean from scratch, you can run (in your local `lean/` directory)
```
git checkout v3.xx.x
git checkout -b my-branch-name
elan override set leanprover-community/lean:3.xx.x
```
You can now build the core library with `lean --make library` or open any Lean file is VSCode / Emacs and it will use the version of Lean you specified. You might have to restart Lean (in VScode: `ctrl+shift+P Lean: Restart`). Warning: all imported Lean files will be from the downloaded community version, *not* the version of the files in this repository. Therefore, this setup is not recommended if you modify more than one file. Moreover, editor features like `Go to Definition` will not behave correctly with this setup. For the best experience, [build Lean from source](doc/make/index.md).

Stable binary releases of Lean are available on the [release page](https://github.com/leanprover-community/lean/releases).

Miscellaneous
-------------

- Building Doxygen Documentation: `doxygen src/Doxyfile`
- [Coding Style](doc/coding_style.md)
- [Library Style Conventions](doc/lean/library_style.org)
- [Git Commit Conventions](doc/commit_convention.md)
- [Syntax Highlight Lean Code in LaTeX](doc/syntax_highlight_in_latex.md)
- [Exporting, and reference type-checkers](doc/export_format.md)
