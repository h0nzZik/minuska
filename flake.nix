{
  description = "Minuska - an experimental semantic framework";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    vscoq.url = "github:coq-community/vscoq";
    vscoq.inputs.nixpkgs.follows = "nixpkgs";
   };

  outputs = { self, nixpkgs, flake-utils, vscoq }: (
    flake-utils.lib.eachDefaultSystem (system:
      let

        pkgs = nixpkgs.legacyPackages.${system};

        minuskaFun = { coqPackages }: (
           let coqVersion = coqPackages.coq.coq-version; in
           let stdpp = coqPackages.stdpp; in
           let coqLibraries = [
              coqPackages.equations
              coqPackages.QuickChick
              # TODO remove, we will not use this
              #coqPackages.CoLoR
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
              coqPackages.coq.ocamlPackages.menhir
              coqPackages.coq.ocamlPackages.odoc
            ] ++ bothNativeAndOtherInputs;

            buildInputs = [] ++ bothNativeAndOtherInputs;

            propagatedBuildInputs = [ coqPackages.coq ] ++ coqLibraries;

            passthru = { inherit coqPackages; };

            postPatch = ''
              substituteInPlace bin/main.ml \
                --replace "/coq/user-contrib/Minuska" "/coq/${coqVersion}/user-contrib/Minuska" \
                --replace "ocamlfind" "${coqPackages.coq.ocamlPackages.findlib}/bin/ocamlfind" \
                --replace "coqc" "${coqPackages.coq}/bin/coqc"
            '';


            buildPhase = ''
              runHook preBuild
              dune build @all theories/Minuska.html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
              runHook postBuild
            '';

            postInstall = ''
              wrapProgram $out/bin/minuska \
                --prefix OCAMLPATH : $OCAMLPATH \
                --prefix COQPATH : $COQPATH \
                --prefix PATH : $PATH \
                --prefix CAML_LD_LIBRARY_PATH : $CAML_LD_LIBRARY_PATH
            '';
          } ) { };  in
          wrapped
          #pkgs.symlinkJoin {
          #  name = wrapped.name;
          #  paths = [
          #    wrapped
          #    coqPackages.coq
          #  ];
          #  postInstall = ''
          #    wrapProgram $out/bin/coqc
          #  '';
          #}
        );

      in {

        packages.minuska-coq_8_19 = minuskaFun { coqPackages = pkgs.coqPackages_8_19; } ;

        packages.minuska = self.outputs.packages.${system}.minuska-coq_8_19;

        packages.examples-coq
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "examples-coq";
          src = ./examples-coq;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.coqPackages_8_19.dpdgraph
            coq.ocamlPackages.menhir
          ];
          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { coqPackages = pkgs.coqPackages_8_19; };
        } ) { } ;


        packages.examples-standalone
        = pkgs.stdenv.mkDerivation {
          name = "examples-standalone";
          src = ./examples-standalone;
          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.time
            pkgs.dune_3
            pkgs.ocamlPackages.menhir
            #pkgs.ocamlPackages.findlib
            pkgs.ocamlPackages.core
            pkgs.ocamlPackages.core_unix
            pkgs.ocamlPackages.ppx_jane

          ];
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


        # TODO remove this
        packages.minuska-symbolic
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska-symbolic";
          src = ./minuska-symbolic;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.coqPackages_8_19.CoLoR
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
                  vscoq.packages.${system}.vscoq-language-server-coq-8-19
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

          minuska-symbolic =
            let
              minuska-symbolic = self.outputs.packages.${system}.minuska-symbolic;
            in
              pkgs.mkShell {
                inputsFrom = [minuska-symbolic];
                packages = [minuska-symbolic.coqPackages.coq-lsp minuska-symbolic.coqPackages.coqide];
              };

        };
      }
    )
  );
}
