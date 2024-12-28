{
  description = "Minuska - an experimental semantic framework";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    nix-appimage.url = "github:ralismark/nix-appimage";
    # We cannot use newer nixpkgs because nix-appimage uses `lzma` instead of `xz`.
    #nix-appimage.inputs.nixpkgs.follows = "nixpkgs";
    #nix-appimage.inputs.flake-utils.follows = "flake-utils";
    bundlers.url = "github:NixOS/bundlers";
    bundlers.inputs.nixpkgs.follows = "nixpkgs";
   };

  outputs = { self, nixpkgs, flake-utils, nix-appimage, bundlers }: (
    flake-utils.lib.eachDefaultSystem (system:
      let

        pkgs = nixpkgs.legacyPackages.${system};
        
        # The appimagetool-wrapper is there to ensure that invocations of `appimagetool` from the `minuska` exacutable,
        # when building an interpreter from a parser and extracted Coq/OCaml Minuska interpreter,
        # use a runtime that does not depend on Nix paths (to /nix/store) for FUSE, but looks it up in some standard paths.
        runtime = pkgs.runCommand "appimage-runtime" {} ''
            mkdir -p $out/bin/
            mkdir -p $out/libexec/
            ln -s ${nix-appimage.outputs.packages.${system}.appimage-runtimes.appimage-type2-runtime} $out/libexec/appimage-runtime
          ''
        ;
        appimagetool-wrapper = pkgs.writeShellScriptBin "appimagetool" ''
	      export PATH="${pkgs.appimagekit}/bin:$PATH"
          ${pkgs.appimagekit}/bin/appimagetool --runtime-file "${runtime}/libexec/appimage-runtime" $@
        '';

        coqMinuskaFun = { coqPackages }: (
           let coqVersion = coqPackages.coq.coq-version; in
           let stdpp = coqPackages.stdpp; in
           let coqLibraries = [
              coqPackages.equations
              coqPackages.QuickChick
              stdpp
           ]; in
           let bothNativeAndOtherInputs = [
              coqPackages.coq
           ] ++ coqLibraries ; in
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
	          };

            buildPhase = ''
              runHook preBuild
              dune build @all theories/Minuska.html ''${enableParallelBuilding:+-j $NIX_BUILD_CORES}
              runHook postBuild
            '';

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
            cp ${coqMinuska}/share/coq-minuska/Dsm.ml ${coqMinuska}/share/coq-minuska/Dsm.mli $out/lib/
            ls -R $out
          '';

          passthru = {
            inherit coqPackages;
            inherit coqMinuska;
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

          buildInputs = [
            minuskaSrc.coqMinuska.coqLibraries
            ocamlPackages.ocaml
            pkgs.makeWrapper
            pkgs.dune_3
            appimagetool-wrapper
            #pkgs.appimagekit
          ] ++ bothNativeAndOtherInputs;

          meta.mainProgram = "minuska";

          postPatch = ''
            substituteInPlace bin/main.ml \
              --replace-fail "\"/usr/lib/coq/user-contrib/Minuska\"" "\"${minuskaSrc.coqMinuska}/lib/coq/${coqVersion}/user-contrib/Minuska\"" \
              --replace-fail "\"ocamlfind\"" "\"${coqPackages.coq.ocamlPackages.findlib}/bin/ocamlfind\"" \
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
          coqPackages = pkgs.coqPackages_8_19;
        };
        
        # Contains OCaml sources of Minuska,
        # including those extracted from Coq
        packages.libminuska-src = libminuskaSrcFun {
          coqPackages = pkgs.coqPackages_8_19;
        };

        # Contains compiled Minuska executable
        packages.minuska = minuskaFun { 
          coqPackages = pkgs.coqPackages_8_19;
          ocamlPackages = pkgs.ocamlPackages;
        };

        packages.languages-in-coq
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "languages-in-coq";
          src = ./languages-in-coq;

          buildInputs = [
            self.outputs.packages.${system}.coq-minuska
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
            pkgs.dune_3
            pkgs.time
          ] ++ example_languages_parser_deps;
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

        packages.minuska-bundle-rpm
        = bundlers.bundlers.${system}.toRPM self.outputs.packages.${system}.minuska;

        packages.minuska-bundle-deb
        = bundlers.bundlers.${system}.toDEB self.outputs.packages.${system}.minuska;

        packages.minuska-bundle-appimage
        = nix-appimage.bundlers.${system}.default self.outputs.packages.${system}.minuska;

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
