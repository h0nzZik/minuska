{ pkgs, src }:
{ coqPackages }:

let
  coqVersion = coqPackages.coq.coq-version;
in
let
  stdpp = coqPackages.stdpp;
in
let
  coqLibraries = [
    stdpp
  ];
in
let
  coqPlugins = [
    coqPackages.equations
    coqPackages.QuickChick
  ];
in
let
  bothNativeAndOtherInputs = [
    coqPackages.coq
  ]
  ++ coqLibraries
  ++ coqPlugins;
in
let
  wrapped = coqPackages.callPackage (
    { coq, stdenv }:
    coqPackages.mkCoqDerivation {
      useDune = true;
      pname = "minuska";
      version = "0.6.0";
      duneVersion = "3";

      inherit src;

      nativeBuildInputs = [
        pkgs.dune_3
        pkgs.time # for QuickChick
      ]
      ++ bothNativeAndOtherInputs;

      passthru = {
        inherit coqPackages;
        inherit coqLibraries;
        inherit coqPlugins;
      };

      buildPhase = ''
        runHook preBuild
        dune build @all theories/Minuska.html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
        runHook postBuild
      '';

      #installFlags = [ "COQLIB=$(out)/lib/coq/${coqPackages.coq.coq-version}/" ];

    }
  ) { };
in
(pkgs.enableDebugging wrapped)
