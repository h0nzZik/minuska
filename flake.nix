{
  description = "Minuska - an experimental semantic framework";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
   };

  outputs = { self, nixpkgs, flake-utils }: (
    flake-utils.lib.eachDefaultSystem (system:
      let

        pkgs = nixpkgs.legacyPackages.${system};

        minuskaFun = { coqPackages }: (
           let coqVersion = coqPackages.coq.coq-version; in
           let stdpp = coqPackages.stdpp; in
           let coqLibraries = [
              coqPackages.equations
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

            # I do not know how to populate the environment variables (OCAMLPATH, COQPATH) with the stuff coming out of Equations and stdpp.
            # It should be possible to do it with setuphooks, but I do not know how.
            # Therefore, I just hard-code the paths to the libraries into all invocations of `coqc` done inside the `minuska` binary.
            postPatch = ''
              substituteInPlace bin/main.ml \
                --replace "/coq/user-contrib/Minuska" "/coq/${coqVersion}/user-contrib/Minuska" \
                --replace "ocamlfind" "${coqPackages.coq.ocamlPackages.findlib}/bin/ocamlfind" \
                --replace "coqc" "${coqPackages.coq}/bin/coqc"
            '';


            buildPhase = ''
              dune build @all theories/Minuska.html
            '';

            postInstall = ''
              wrapProgram $out/bin/minuska \
                --prefix OCAMLPATH : $OCAMLPATH \
                --prefix COQPATH : $COQPATH \
                --prefix PATH : $PATH \
                --prefix CAML_LD_LIBRARY_PATH : $CAML_LD_LIBRARY_PATH
            '';



            #setupHook = pkgs.writeText "setupHook.sh" ''
            #  source ${coqPackages.coq}/nix-support/setup-hook
            #'';

          } ) { };  in
          wrapped
          #pkgs.symlinkJoin {
          #  name = wrapped.name;
          #  paths = [
          #    wrapped
          #    coqPackages.coq
          #    coqPackages.coq.ocamlPackages.findlib
          #    coqPackages.coq.ocamlPackages.zarith
          #  ] ++ bothNativeAndOtherInputs;
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

        packages.default = self.outputs.packages.${system}.minuska;
        
        devShells = {
          minuska =
            let
              minuska = self.outputs.packages.${system}.minuska;
            in
              pkgs.mkShell {
                inputsFrom = [minuska];
                packages = [minuska.coqPackages.coq-lsp minuska.coqPackages.coqide];
              };


          minuska-coq_8_19 =
            let
              minuska = self.outputs.packages.${system}.minuska-coq_8_19;
            in
              pkgs.mkShell {
                inputsFrom = [minuska];
                packages = [minuska.coqPackages.coq-lsp minuska.coqPackages.coqide ];
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
