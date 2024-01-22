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
          coqPackages.callPackage 
          ( { coq, stdenv }:
          stdenv.mkDerivation {
            name = "minuska";
            src = ./minuska;

            propagatedBuildInputs = [
              coq
              #coqPackages.equations
              coqPackages.stdpp
              coq.ocaml
              coq.ocamlPackages.zarith
            ];
            enableParallelBuilding = true;
            installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

            passthru = { inherit coqPackages; };
          } ) { } 
        );

        coqPackages = pkgs.coqPackages_8_18;

      in {

        packages.minuska-coq_8_19 = minuskaFun { coqPackages = pkgs.coqPackages_8_19; } ;
        packages.minuska-coq_8_18 = minuskaFun { coqPackages = pkgs.coqPackages_8_18; } ;
        packages.minuska-coq_8_17 = minuskaFun { coqPackages = pkgs.coqPackages_8_17; } ;

        packages.minuska = self.outputs.packages.${system}.minuska-coq_8_18;

        packages.minuska-symbolic
        = coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska-symbolic";
          src = ./minuska-symbolic;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            coqPackages.CoLoR
          ];
          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { inherit coqPackages; };
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
