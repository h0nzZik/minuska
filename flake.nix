{
  description = "Minuska - an experimental semantic framework";

  inputs = {
    nixpkgs.url = "github:NixOs/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
    benchexec-nixpkgs.url = "github:lorenzleutgeb/nixpkgs/benchexec";
   };

  outputs = { self, nixpkgs, flake-utils, benchexec-nixpkgs }: (
    flake-utils.lib.eachDefaultSystem (system:
      let

        #overlay-benchexec = final: prev: {
        #   benchexec = nixpkgs-unstable.legacyPackages.${prev.system};
        #};

        pkgs = nixpkgs.legacyPackages.${system};
	      be-pkgs = benchexec-nixpkgs.legacyPackages.${system};

        stdppFun = { lib, mkCoqDerivation, coq }: (
          mkCoqDerivation rec {
            pname = "stdpp";
            domain = "gitlab.mpi-sws.org";
            owner = "iris";
            defaultVersion = with lib.versions; lib.switch coq.coq-version [
              { case = range "8.19" "8.19"; out = "a91260bd12710952c407622f6174eb53eafebf8b"; }
              { case = range "8.16" "8.18"; out = "coq-stdpp-1.9.0"; }
              { case = range "8.13" "8.17"; out = "coq-stdpp-1.8.0"; }
              { case = range "8.12" "8.14"; out = "coq-stdpp-1.6.0"; }
              { case = range "8.11" "8.13"; out = "coq-stdpp-1.5.0"; }
              { case = range "8.8" "8.10";  out = "coq-stdpp-1.4.0"; }
            ] null;
            release."a91260bd12710952c407622f6174eb53eafebf8b".sha256 = "sha256-7kOtz69Bu3/8tDZGLFgsafOJZJa6VjjMxk8nGcRf8Dk=";
            release."coq-stdpp-1.9.0".sha256 = "sha256-OXeB+XhdyzWMp5Karsz8obp0rTeMKrtG7fu/tmc9aeI=";
            release."coq-stdpp-1.8.0".sha256 = "sha256-VkIGBPHevHeHCo/Q759Q7y9WyhSF/4SMht4cOPuAXHU=";
            release."coq-stdpp-1.7.0".sha256 = "sha256:0447wbzm23f9rl8byqf6vglasfn6c1wy6cxrrwagqjwsh3i5lx8y";
            release."coq-stdpp-1.6.0".sha256 = "1l1w6srzydjg0h3f4krrfgvz455h56shyy2lbcnwdbzjkahibl7v";
            release."coq-stdpp-1.5.0".sha256 = "1ym0fy620imah89p8b6rii8clx2vmnwcrbwxl3630h24k42092nf";
            release."coq-stdpp-1.4.0".sha256 = "1m6c7ibwc99jd4cv14v3r327spnfvdf3x2mnq51f9rz99rffk68r";
            releaseRev = v: "${v}";

            preBuild = ''
              if [[ -f coq-lint.sh ]]
              then patchShebangs coq-lint.sh
              fi
            '';

            meta = with lib; {
              description = "An extended “Standard Library” for Coq";
              license = licenses.bsd3;
              maintainers = [ maintainers.vbgl maintainers.ineol ];
            };
          }
        );

        minuskaFun = { coqPackages }: (
          coqPackages.callPackage 
          ( { coq, stdenv }:
          stdenv.mkDerivation {
            name = "minuska";
            src = ./minuska;

            propagatedBuildInputs = [
              coq
              coqPackages.equations
              # (
              #   coqPackages.lib.overrideCoqDerivation {
              #     inherit coq;
              #     defaultVersion = "1.9.0"; 
              #   } pkgs.coqPackages_8_18.stdpp
              # )
              (stdppFun {lib = coqPackages.lib; mkCoqDerivation = coqPackages.mkCoqDerivation; inherit coq; })
              coq.ocaml
              coq.ocamlPackages.zarith
            ];
            enableParallelBuilding = true;
            installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

            passthru = { inherit coqPackages; };
          } ) { } 
        );

      in {

        packages.minuska-coq_8_19 = minuskaFun { coqPackages = pkgs.coqPackages_8_19; } ;

        packages.minuska = self.outputs.packages.${system}.minuska-coq_8_19;

        packages.minuska-examples
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska-examples";
          src = ./minuska-examples;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            coq.ocamlPackages.menhir
          ];
          enableParallelBuilding = true;
          installFlags = [ "COQLIB=$(out)/lib/coq/${coq.coq-version}/" ];

          passthru = { coqPackages = pkgs.coqPackages_8_19; };
        } ) { } ;



        packages.minuska-bench
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska-bench";
          src = ./minuska-bench;

          propagatedBuildInputs = [
            pkgs.time
            pkgs.python312
            self.outputs.packages.${system}.minuska-examples
            #self.outputs.packages.${system}.minuska-examples.coqPackages.coq
            be-pkgs.benchexec            
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


          minuska-examples =
            let
              minuska-examples = self.outputs.packages.${system}.minuska-examples;
            in
              pkgs.mkShell {
                inputsFrom = [minuska-examples];
                packages = [
                  minuska-examples.coqPackages.coq-lsp
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
