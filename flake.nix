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

        # Coq project
        # { coqPackages } -> derivation
        coqMinuskaFun = import ./nix/coqMinuskaFun.nix { 
          inherit pkgs;
          src = ./coq-minuska;
        }; 

        # OCaml sources
        # { coqPackages } -> derivation
        libminuskaSrcFun = import ./nix/libminuskaSrcFun.nix {
          inherit pkgs;
          inherit coqMinuskaFun;
          src = ./minuska;
        };

       # OCaml frontend
       # { coqPackages, ocamlPackages } -> derivation
       minuskaFun = import ./nix/minuskaFun.nix {
         inherit pkgs;
         inherit libminuskaSrcFun;
       };

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
