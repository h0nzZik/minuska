{ pkgs, coqMinuskaFun, src }:
{ coqPackages }:

let coqMinuska = coqMinuskaFun { inherit coqPackages; }; in
pkgs.stdenv.mkDerivation {
  name = "libminuska-src";
  src = (pkgs.lib.fileset.toSource {
    root = src;
    fileset = src;
  });
  buildPhase = ''
    mkdir -p $out
    mkdir -p $out/bin
    mkdir -p $out/lib
    cp dune-project $out/
    cp bin/* $out/bin
    cp lib/* $out/lib
    cp ${coqMinuska}/share/coq-minuska/Dsm.mli $out/lib/
    printf "open Stdlib\n" >> $out/lib/Dsm.ml
    cat ${coqMinuska}/share/coq-minuska/Dsm.ml >> $out/lib/Dsm.ml
    ls -R $out
 '';

 passthru = {
   inherit coqMinuska;
   coqPackages  = coqMinuska.coqPackages;
   coqLibraries = coqMinuska.coqLibraries;
   coqPlugins   = coqMinuska.coqPlugins;
 };
}
