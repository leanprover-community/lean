{ llvmPackages, bash, cmake, ccache, python, gmp, gcc, stdenv }:

llvmPackages.stdenv.mkDerivation rec {
  name = "lean-${version}";
  version = "local";

  # I have way too many untracked files in my checkout
  src = if builtins.pathExists ../.git then builtins.fetchGit { url = ../.; } else ../.;

  nativeBuildInputs = [ bash cmake ccache python ];
  buildInputs = [ gmp llvmPackages.llvm stdenv.cc.cc.lib ];
  enableParallelBuilding = true;

  preConfigure = ''
    cd src
  '';
  postConfigure = ''
    patchShebangs ../../bin
  '';

  meta = with llvmPackages.stdenv.lib; {
    description = "Automatic and interactive theorem prover";
    homepage    = https://leanprover.github.io/;
    license     = licenses.asl20;
    platforms   = platforms.unix;
  };
}