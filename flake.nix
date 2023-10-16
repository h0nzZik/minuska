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
        coqPackages = pkgs.coqPackages_8_18;

      in {

        # The 'matching logic in Coq' library
        packages.minuska
        = coqPackages.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska";
          src = ./minuska;

          propagatedBuildInputs = [
            coq
            coqPackages.equations
            coqPackages.stdpp
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
                packages = [minuska.coqPackages.coq-lsp];
              };
        };
      }
    )
  );
}
