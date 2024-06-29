{
  description = "Minuska - an experimental semantic framework";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    nix-appimage.url = "github:ralismark/nix-appimage";
    nix-appimage.inputs.nixpkgs.follows = "nixpkgs";
    nix-appimage.inputs.flake-utils.follows = "flake-utils";
   };

  outputs = { self, nixpkgs, flake-utils, nix-appimage }: (
    flake-utils.lib.eachDefaultSystem (system:
      let

        pkgs = nixpkgs.legacyPackages.${system};

        runtime = pkgs.runCommand "appimage-runtime" {} ''
            mkdir -p $out/bin/
            mkdir -p $out/libexec/
            ln -s ${nix-appimage.outputs.packages.${system}.runtime} $out/libexec/appimage-runtime
          ''
        ;
        appimage-wrapper = pkgs.writeShellScriptBin "appimagetool" ''
          ${pkgs.appimagekit}/bin/appimagetool --runtime-file "${runtime}/libexec/appimage-runtime" $@
        '';

        minuskaFun = { coqPackages }: (
           let coqVersion = coqPackages.coq.coq-version; in
           let stdpp = coqPackages.stdpp; in
           let coqLibraries = [
              coqPackages.equations
              coqPackages.QuickChick
              stdpp
           ]; in
           let bothNativeAndOtherInputs = [
              coqPackages.coq

              coqPackages.coq.ocaml
              coqPackages.coq.ocamlPackages.findlib
              coqPackages.coq.ocamlPackages.zarith
              coqPackages.coq.ocamlPackages.core
              coqPackages.coq.ocamlPackages.core_unix
              coqPackages.coq.ocamlPackages.ppx_jane
              coqPackages.coq.ocamlPackages.ppx_sexp_conv
              coqPackages.coq.ocamlPackages.benchmark
           ] ++ coqLibraries ; in
           let wrapped = coqPackages.callPackage  ( { coq, stdenv }: coqPackages.mkCoqDerivation {

            useDune = true; 
            pname = "minuska";
            version = "0.2";
            src = ./minuska;
            duneVersion = "3";
 
            nativeBuildInputs = [
              pkgs.makeWrapper
              pkgs.dune_3
              appimage-wrapper
              #pkgs.appimagekit
              coqPackages.coq.ocamlPackages.menhir
              coqPackages.coq.ocamlPackages.odoc
            ] ++ bothNativeAndOtherInputs;

            #buildInputs = [] ++ bothNativeAndOtherInputs;

            #propagatedBuildInputs = [ coqPackages.coq ] ++ coqLibraries;

            passthru = {
              inherit coqPackages;
              inherit coqLibraries;
	    };

            postPatch = ''
              substituteInPlace bin/main.ml \
                --replace-fail "/coq/user-contrib/Minuska" "/coq/${coqVersion}/user-contrib/Minuska" \
                --replace-fail "ocamlfind" "${coqPackages.coq.ocamlPackages.findlib}/bin/ocamlfind" \
                --replace-fail "coqc" "${coqPackages.coq}/bin/coqc"
            '';


            buildPhase = ''
              runHook preBuild
              dune build @all theories/Minuska.html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
              runHook postBuild
            '';

            postInstall = ''
              wrapProgram $out/bin/minuska \
                --set OCAMLFIND_DESTDIR $OCAMLFIND_DESTDIR \
                --set OCAMLPATH $OCAMLPATH \
                --set COQPATH $COQPATH \
                --set PATH $PATH \
                --set CAML_LD_LIBRARY_PATH $CAML_LD_LIBRARY_PATH
            '';
          } ) { };  in
          wrapped
       );

      in {
        packages.minuska = minuskaFun { coqPackages = pkgs.coqPackages_8_19; } ;

        packages.examples-coq
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "examples-coq";
          src = ./examples-coq;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            #coq.ocamlPackages.menhir
          ] ++ [self.outputs.packages.${system}.minuska.coqPackages.coq]
           ++ self.outputs.packages.${system}.minuska.coqLibraries ;

          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { coqPackages = pkgs.coqPackages_8_19; };
        } ) { } ;


        packages.examples-standalone
        = pkgs.stdenv.mkDerivation {
          name = "examples-standalone";
          src = ./examples-standalone;
          nativeBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.time
            pkgs.ocaml
            pkgs.dune_3
            pkgs.ocamlPackages.menhir
            pkgs.ocamlPackages.findlib
            pkgs.ocamlPackages.core
            pkgs.ocamlPackages.core_unix
            pkgs.ocamlPackages.ppx_jane
          ];
          #buildInputs = [
          #  pkgs.fuse
          #  pkgs.strace
          #];
        };

        packages.examples-hybrid
        = pkgs.stdenv.mkDerivation {
          name = "examples-hybrid";
          src = ./examples-hybrid;
          nativeBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.time
          ] ++ [self.outputs.packages.${system}.minuska.coqPackages.coq]
           ++ self.outputs.packages.${system}.minuska.coqLibraries ;
        };

        packages.minuska-bench
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska-bench";
          src = ./minuska-bench;

          propagatedBuildInputs = [
            pkgs.time
            pkgs.python312
            self.outputs.packages.${system}.examples-coq
            #self.outputs.packages.${system}.examples-coq.coqPackages.coq
          ];
          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { coqPackages = pkgs.coqPackages_8_19; };
        } ) { } ;


        packages.minuska-docker
        = pkgs.dockerTools.buildImage {
          name = "minuska-docker";
          config = {
            Cmd = [ "${self.outputs.packages.${system}.minuska}/bin/minuska" ];
          };
        };


        packages.default = self.outputs.packages.${system}.minuska;
        
        devShells = {
          
          # For developing Minuska
          minuska =
            let
              minuska = self.outputs.packages.${system}.minuska;
            in
              pkgs.mkShell {
                inputsFrom = [minuska];
                packages = [
                  minuska.coqPackages.coq-lsp 
                  minuska.coqPackages.coqide 
                ];
              };

          # For using Minuska
          with-minuska =
            let
              minuska = self.outputs.packages.${system}.minuska;
            in
              pkgs.mkShell {
                packages = [minuska minuska.coqPackages.coq-lsp minuska.coqPackages.coq];
              };

          examples-coq =
            let
              examples-coq = self.outputs.packages.${system}.examples-coq;
            in
              pkgs.mkShell {
                inputsFrom = [examples-coq];
                packages = [
                  examples-coq.coqPackages.coq-lsp
                ];
              };

          examples-standalone =
            let
              examples-standalone = self.outputs.packages.${system}.examples-standalone;
            in
              pkgs.mkShell {
                inputsFrom = [examples-standalone];
                packages = [];
              };

          minuska-bench =
            let
              minuska-bench = self.outputs.packages.${system}.minuska-bench;
            in
              pkgs.mkShell {
                inputsFrom = [minuska-bench];
                packages = [
                  minuska-bench.coqPackages.coq-lsp
                  #benchexec
                ];
              };

        };
      }
    )
  );
}
