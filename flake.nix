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
              coqPackages.coq.ocamlPackages.base_quickcheck
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
              pkgs.appimagekit
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

            #installFlags = [ "COQLIB=$(out)/lib/coq/${coqPackages.coq.coq-version}/" ];

            #installPhase = ''
            #  mkdir -p $out
            #  runHook preInstall
            #  dune install --prefix $out
            #  runHook postInstall
            #'';

            postInstall = ''
              dune install --prefix $out libminuska
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

        packages.languages-in-coq
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "languages-in-coq";
          src = ./languages-in-coq;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            #coq.ocamlPackages.menhir
          ] ++ [self.outputs.packages.${system}.minuska.coqPackages.coq]
           ++ self.outputs.packages.${system}.minuska.coqLibraries ;

          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { coqPackages = pkgs.coqPackages_8_19; };
        } ) { } ;


        packages.bench-standalone
        = pkgs.stdenv.mkDerivation {
          name = "bench-standalone";
          src = ./bench-standalone;
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

        packages.bench-hybrid
        = pkgs.stdenv.mkDerivation {
          name = "bench-hybrid";
          src = ./bench-hybrid;
          nativeBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.time
          ] ++ [self.outputs.packages.${system}.minuska.coqPackages.coq]
           ++ self.outputs.packages.${system}.minuska.coqLibraries ;
        };

        packages.bench-coq
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "bench-coq";
          src = ./bench-coq;

          propagatedBuildInputs = [
            pkgs.time
            pkgs.python312
            self.outputs.packages.${system}.languages-in-coq
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

          languages-in-coq =
            let
              languages-in-coq = self.outputs.packages.${system}.languages-in-coq;
            in
              pkgs.mkShell {
                inputsFrom = [languages-in-coq];
                packages = [
                  languages-in-coq.coqPackages.coq-lsp
                ];
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

          bench-standalone =
            let
              bench-standalone = self.outputs.packages.${system}.bench-standalone;
            in
              pkgs.mkShell {
                inputsFrom = [bench-standalone];
                packages = [];
              };

          bench-coq =
            let
              bench-coq = self.outputs.packages.${system}.bench-coq;
            in
              pkgs.mkShell {
                inputsFrom = [bench-coq];
                packages = [
                  bench-coq.coqPackages.coq-lsp
                  #benchexec
                ];
              };

        };
      }
    )
  );
}
