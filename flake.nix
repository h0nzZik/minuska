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
           let coqVersion = coqPackages.coq.coq-version; in
           let stdpp = (stdppFun {lib = coqPackages.lib; mkCoqDerivation = coqPackages.mkCoqDerivation; coq = coqPackages.coq; }); in
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
            version = "0.1";
            src = ./minuska;
            duneVersion = "3";
 
            nativeBuildInputs = [
              pkgs.makeWrapper
              pkgs.dune_3
              coqPackages.coq.ocamlPackages.menhir
              coqPackages.coq.ocamlPackages.odoc
            ] ++ bothNativeAndOtherInputs;

            buildInputs = [] ++ bothNativeAndOtherInputs;

            propagatedBuildInputs = [];

            passthru = { inherit coqPackages; };

            # I do not know how to populate the environment variables (OCAMLPATH, COQPATH) with the stuff coming out of Equations and stdpp.
            # It should be possible to do it with setuphooks, but I do not know how.
            # Therefore, I just hard-code the paths to the libraries into all invocations of `coqc` done inside the `minuska` binary.
            postPatch = ''
              substituteInPlace bin/main.ml \
                --replace "/coq/user-contrib/Minuska" "/coq/${coqVersion}/user-contrib/Minuska" \
                --replace "coqc" "${coqPackages.coq}/bin/coqc -R ${stdpp}/lib/coq/${coqVersion}/user-contrib/stdpp stdpp -R ${coqPackages.equations}/lib/coq/${coqVersion}/user-contrib/Equations Equations -I ${coqPackages.equations}/lib/ocaml/${coqPackages.coq.ocaml.version}/site-lib/coq-equations" \
                --replace "ocamlfind" "${coqPackages.coq.ocamlPackages.findlib}/bin/ocamlfind" \
            '';
             #                --replace "env OCAMLPATH=" "env OCAMLPATH=${coqPackages.coq.ocamlPackages.zarith}/lib/ocaml/${coqPackages.coq.ocaml.version}/site-lib:"


            buildPhase = ''
              dune build @all theories/Minuska.html
            '';

            postInstall = ''
              wrapProgram $out/bin/minuska --prefix OCAMLPATH : $OCAMLPATH
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

        packages.minuska-examples
        = pkgs.coqPackages_8_19.callPackage 
        ( { coq, stdenv }:
        stdenv.mkDerivation {
          name = "minuska-examples";
          src = ./minuska-examples;

          propagatedBuildInputs = [
            self.outputs.packages.${system}.minuska
            pkgs.coqPackages_8_19.dpdgraph
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
