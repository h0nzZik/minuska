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


       groupFun = { pkgs, coqPackages, ocamlPackages  }: (
       let
         coq-minuska = coqMinuskaFun { inherit coqPackages; };
         libminuska-src = libminuskaSrcFun { inherit coqPackages; };
         minuska = minuskaFun { inherit coqPackages; inherit ocamlPackages; };

         # The parsers in `languages/*` depend on these.
         example_languages_parser_deps = [
            pkgs.dune_3
            ocamlPackages.menhir
            ocamlPackages.findlib
            ocamlPackages.core
            ocamlPackages.core_unix
            ocamlPackages.ppx_jane
            ocamlPackages.ocaml
         ];

         bench-standalone = pkgs.stdenv.mkDerivation {
           name = "bench-standalone";
           src = ./bench-standalone;
           nativeBuildInputs = [
             minuska
             pkgs.dune_3
             pkgs.time
             coqPackages.coqide # for user builtins
             coqPackages.coq
            ] ++ example_languages_parser_deps;
            buildInputs = [
              coq-minuska
            ];
           };

         # Does not work these days
         bench-hybrid = pkgs.stdenv.mkDerivation {
           name = "bench-hybrid";
           src = ./bench-hybrid;
           nativeBuildInputs = [
             minuska
             pkgs.dune_3
             pkgs.time
           ] ++ example_languages_parser_deps;
         };

         minuska-docker = pkgs.dockerTools.buildImage {
           name = "minuska-docker";
           config = {
             Cmd = [ "${minuska}/bin/minuska" ];
            };
         };

         minuska-bundle-rpm = bundlers.bundlers.${system}.toRPM minuska;
         minuska-bundle-deb = bundlers.bundlers.${system}.toDEB minuska;
       in
       {
         inherit coq-minuska;
         inherit libminuska-src;
         inherit minuska;
         inherit bench-standalone;
         inherit bench-hybrid;
         inherit minuska-docker;
         inherit minuska-bundle-rpm;
         inherit minuska-bundle-deb;

         default = minuska;

         devShells = { 
           # For developing Minuska
           coq-minuska = pkgs.mkShell {
             inputsFrom = [coq-minuska];
             packages = [
               coq-minuska.coqPackages.coq-lsp 
               coq-minuska.coqPackages.coqide 
             ];
           };
           # For using Minuska
           with-minuska = pkgs.mkShell {
             packages = [minuska minuska.coqPackages.coq-lsp minuska.coqPackages.coq];
           };
           # For developing bench-standalone
           bench-standalone = pkgs.mkShell {
             inputsFrom = [bench-standalone];
             packages = [coq-minuska.coqPackages.coq-lsp coq-minuska.coqPackages.coqide];
           };
         };
       });


      in {
        legacyPackages.minuskaGroupCoq_8_20 = groupFun {
          inherit pkgs;
          coqPackages = pkgs.coqPackages_8_20;
          ocamlPackages = pkgs.ocamlPackages;
        };

        legacyPackages.minuskaGroupDefault = self.outputs.legacyPackages.${system}.minuskaGroupCoq_8_20;
        packages.coq-minuska        = self.outputs.legacyPackages.${system}.minuskaGroupDefault.coq-minuska;
        packages.libminuska-src        = self.outputs.legacyPackages.${system}.minuskaGroupDefault.libminuska-src;
        packages.minuska        = self.outputs.legacyPackages.${system}.minuskaGroupDefault.minuska;



        packages.bench-standalone   = self.outputs.legacyPackages.${system}.minuskaGroupDefault.bench-standalone;
        packages.bench-hybrid       = self.outputs.legacyPackages.${system}.minuskaGroupDefault.bench-hybrid;
        packages.minuska-docker     = self.outputs.legacyPackages.${system}.minuskaGroupDefault.minuska-docker;
        packages.minuska-bundle-rpm = self.outputs.legacyPackages.${system}.minuskaGroupDefault.minuska-bundle-rpm;
        packages.minuska-bundle-deb = self.outputs.legacyPackages.${system}.minuskaGroupDefault.minuska-bundle-deb;
        packages.default            = self.outputs.legacyPackages.${system}.minuskaGroupDefault.default;
        devShells                   = self.outputs.legacyPackages.${system}.minuskaGroupDefault.devShells;
      }
    )
  );
}
