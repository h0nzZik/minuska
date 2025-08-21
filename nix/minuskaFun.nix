{ pkgs, libminuskaSrcFun }:
{ coqPackages, ocamlPackages }:

let
  coqVersion = coqPackages.coq.coq-version;
in
let
  minuskaSrc = libminuskaSrcFun { inherit coqPackages; };
in
let
  ocamlLibraries = with pkgs.ocamlPackages; [
    findlib
    zarith
    core
    core_unix
    ppx_jane
    ppx_sexp_conv
    base_quickcheck
    benchmark
  ];
in
let
  bothNativeAndOtherInputs = with pkgs; [
    ocaml
  ];
in
let
  wrapped = ocamlPackages.buildDunePackage {
    pname = "minuska";
    version = "0.6.0";
    src = minuskaSrc;
    dontStrip = true;
    propagatedBuildInputs = ocamlLibraries;

    nativeBuildInputs = [
      coqPackages.coq
      ocamlPackages.menhir
    ];

    buildInputs =
      minuskaSrc.coqMinuska.coqLibraries
      ++ minuskaSrc.coqMinuska.coqPlugins
      ++ [
        ocamlPackages.ocaml
        pkgs.makeWrapper
        pkgs.dune_3
      ]
      ++ bothNativeAndOtherInputs;

    meta.mainProgram = "minuska";

    postPatch = ''
      substituteInPlace bin/main.ml \
        --replace-fail \
          "\"/usr/lib/coq/user-contrib/Minuska\"" \
           "\"${minuskaSrc.coqMinuska}/lib/coq/${coqVersion}/user-contrib/Minuska\"" \
        --replace-fail \
          "\"/usr/lib/coq/user-contrib/stdpp\"" \
          "\"${minuskaSrc.coqMinuska.coqPackages.stdpp}/lib/coq/${coqVersion}/user-contrib/stdpp\"" \
        --replace-fail \
          "\"/usr/lib/coq/user-contrib/Equations\"" \
          "\"${minuskaSrc.coqMinuska.coqPackages.equations}/lib/coq/${coqVersion}/user-contrib/Equations\"" \
        --replace-fail \
          "\"coqc\"" \
          "\"${coqPackages.coq}/bin/coqc\""
    '';

    buildPhase = ''
      runHook preBuild
      dune build @all ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
      runHook postBuild
    '';

    postInstall = ''
      dune install --prefix $out
      wrapProgram $out/bin/minuska \
        --set OCAMLFIND_DESTDIR $OCAMLFIND_DESTDIR \
        --set OCAMLPATH $OCAMLPATH \
        --set COQPATH $COQPATH \
        --set PATH $PATH \
        --set CAML_LD_LIBRARY_PATH $CAML_LD_LIBRARY_PATH
    '';

    passthru = {
      inherit coqPackages;
      inherit ocamlPackages;
      coqLibraries = minuskaSrc.coqLibraries;
      coqPlugins = minuskaSrc.coqPlugins;
    };
  };
in
wrapped
