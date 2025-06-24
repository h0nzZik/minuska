{
  description = "Minuska - an experimental semantic framework";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    bundlers.url = "github:NixOS/bundlers";
    bundlers.inputs.nixpkgs.follows = "nixpkgs";
   };

  outputs = { self, nixpkgs, flake-utils, bundlers }: (
    flake-utils.lib.eachDefaultSystem (system:
      let

        pkgs = nixpkgs.legacyPackages.${system};
        
        coqMinuskaFun = { coqPackages }: (
           let coqVersion = coqPackages.coq.coq-version; in
           let stdpp = coqPackages.stdpp; in
           let coqLibraries = [
             stdpp
           ]; in
           let coqPlugins = [
              coqPackages.equations
              coqPackages.QuickChick 
           ]; in
           let bothNativeAndOtherInputs = [
              coqPackages.coq
           ] ++ coqLibraries ++ coqPlugins ; in
           let wrapped = coqPackages.callPackage  ( { coq, stdenv }: coqPackages.mkCoqDerivation {

            useDune = true; 
            pname = "minuska";
            version = "0.6.0";
            src = ./coq-minuska;
            duneVersion = "3";
 
            nativeBuildInputs = [
              pkgs.dune_3
            ] ++ bothNativeAndOtherInputs;

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

          } ) { };  in
          wrapped
       );

      # OCaml sources
      libminuskaSrcFun = { coqPackages }: (
      let
        coqMinuska = (coqMinuskaFun { inherit coqPackages; } );
      in
        pkgs.stdenv.mkDerivation {
          name = "libminuska-src";
          src =
            (pkgs.lib.fileset.toSource {
              root = ./minuska;
              fileset = ./minuska;
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
            inherit coqPackages;
            inherit coqMinuska;
            coqLibraries = coqMinuska.coqLibraries;
            coqPlugins = coqMinuska.coqPlugins;

          };
        }
       );

       minuskaFun = { coqPackages, ocamlPackages }: (
        let coqVersion = coqPackages.coq.coq-version; in
        let minuskaSrc = libminuskaSrcFun { inherit coqPackages; }; in
        let ocamlLibraries = with pkgs.ocamlPackages; [
          findlib
          zarith
          core
          core_unix
          ppx_jane
          ppx_sexp_conv
          base_quickcheck
          benchmark
        ]; in

        let bothNativeAndOtherInputs = with pkgs; [
          ocaml
        ]; in
        
        let wrapped = ocamlPackages.buildDunePackage {
          pname = "minuska";
          version = "0.6.0";
          src = minuskaSrc;
          #duneVersion = "3";

          propagatedBuildInputs = ocamlLibraries;

          nativeBuildInputs = [
            coqPackages.coq
            ocamlPackages.menhir
          ];

          buildInputs =
            minuskaSrc.coqMinuska.coqLibraries ++
            minuskaSrc.coqMinuska.coqPlugins ++
          [
            ocamlPackages.ocaml
            pkgs.makeWrapper
            pkgs.dune_3
          ] ++ bothNativeAndOtherInputs;

          meta.mainProgram = "minuska";

          postPatch = ''
            substituteInPlace bin/main.ml \
              --replace-fail "\"/usr/lib/coq/user-contrib/Minuska\"" "\"${minuskaSrc.coqMinuska}/lib/coq/${coqVersion}/user-contrib/Minuska\"" \
              --replace-fail "\"/usr/lib/coq/user-contrib/stdpp\"" "\"${minuskaSrc.coqMinuska.coqPackages.stdpp}/lib/coq/${coqVersion}/user-contrib/stdpp\"" \
              --replace-fail "\"/usr/lib/coq/user-contrib/Equations\"" "\"${minuskaSrc.coqMinuska.coqPackages.equations}/lib/coq/${coqVersion}/user-contrib/Equations\"" \
              --replace-fail "\"coqc\"" "\"${coqPackages.coq}/bin/coqc\""
          '';


          buildPhase = ''
            runHook preBuild
            dune build @all ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
            runHook postBuild
          '';

          #installFlags = [ "COQLIB=$(out)/lib/coq/${coqPackages.coq.coq-version}/" ];

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
        }; in
        wrapped
       );

       # The parsers in `languages/*` depend on these.
       example_languages_parser_deps = [
            pkgs.dune_3
            pkgs.ocamlPackages.menhir
            pkgs.ocamlPackages.findlib
            pkgs.ocamlPackages.core
            pkgs.ocamlPackages.core_unix
            pkgs.ocamlPackages.ppx_jane
            pkgs.ocaml
        ];

      in {
        # Contains compiled Coq sources of Minuska
        packages.coq-minuska = coqMinuskaFun {
          coqPackages = pkgs.coqPackages_8_20;
        };
        
        # Contains OCaml sources of Minuska,
        # including those extracted from Coq
        packages.libminuska-src = libminuskaSrcFun {
          coqPackages = pkgs.coqPackages_8_20;
        };

        # Contains compiled Minuska executable
        packages.minuska = minuskaFun { 
          coqPackages = pkgs.coqPackages_8_20;
          ocamlPackages = pkgs.ocamlPackages;
        };


        packages.bench-standalone
        = pkgs.stdenv.mkDerivation {
          name = "bench-standalone";
          src = ./bench-standalone;
          nativeBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.dune_3
            pkgs.time
            pkgs.coqPackages_8_20.coqide # for user builtins
            pkgs.coqPackages_8_20.coq
          ] ++ example_languages_parser_deps;
          buildInputs = [
            self.outputs.packages.${system}.coq-minuska
          ];
        };

        packages.bench-hybrid
        = pkgs.stdenv.mkDerivation {
          name = "bench-hybrid";
          src = ./bench-hybrid;
          nativeBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.dune_3
            pkgs.time
          ] ++ example_languages_parser_deps;
        };

        packages.minuska-docker
        = pkgs.dockerTools.buildImage {
          name = "minuska-docker";
          config = {
            Cmd = [ "${self.outputs.packages.${system}.minuska}/bin/minuska" ];
          };
        };

        packages.minuska-bundle-rpm
        = bundlers.bundlers.${system}.toRPM self.outputs.packages.${system}.minuska;

        packages.minuska-bundle-deb
        = bundlers.bundlers.${system}.toDEB self.outputs.packages.${system}.minuska;

        packages.default = self.outputs.packages.${system}.minuska;
        
        devShells = {
          
          # For developing Minuska
          coq-minuska =
            let
              coq-minuska = self.outputs.packages.${system}.coq-minuska;
            in
              pkgs.mkShell {
                inputsFrom = [coq-minuska];
                packages = [
                  coq-minuska.coqPackages.coq-lsp 
                  coq-minuska.coqPackages.coqide 
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


          # For developing bench-standalone
          bench-standalone =
           let
             bench-standalone = self.outputs.packages.${system}.bench-standalone;
             coq-minuska = self.outputs.packages.${system}.coq-minuska;
           in
             pkgs.mkShell {
               inputsFrom = [bench-standalone];
               packages = [coq-minuska.coqPackages.coq-lsp coq-minuska.coqPackages.coqide];
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

        };
      }
    )
  );
}
