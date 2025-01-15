{
  description = "Yet another category theory library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.11";
    utils.url = "github:numtide/flake-utils";
    agda = {
      url = "github:agda/agda/v2.7.0.1";
      flake = false;
    };
    std-lib = {
      url = "github:agda/agda-stdlib/v2.1.1";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, utils, ... }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.${system}.default ];
        };
        agdaWithLibraries = pkgs.agda.withPackages (p: [
          p.standard-library
        ]);

      in {
        checks.whitespace = pkgs.stdenvNoCC.mkDerivation {
          name = "check-whitespace";
          dontBuild = true;
          src = ./.;
          doCheck = true;
          checkPhase = ''
            ${pkgs.haskellPackages.fix-whitespace}/bin/fix-whitespace --check
          '';
          installPhase = ''mkdir "$out"'';
        };

        overlays = rec {
          agda = final: prev: {
            haskellPackages = prev.haskellPackages.override {
              overrides = hfinal: hprev:
                let inherit (final.haskell.lib.compose)
                  addBuildDepends enableCabalFlag overrideSrc;
                in {
                  Agda = final.lib.pipe hprev.Agda [
                    (overrideSrc {
                      src = inputs.agda;
                      version = "2.7.0.1";
                    })
                    (addBuildDepends (with hfinal; [pqueue text-icu]))
                    (enableCabalFlag "enable-cluster-counting")
                  ];
                };
            };
          };

          standard-library = final: prev: {
            agdaPackages = prev.agdaPackages.overrideScope (
              finalAgda: prevAgda: {
                standard-library = prevAgda.standard-library.overrideAttrs {
                  version = "2.1";
                  src = inputs.std-lib;
                };
              }
            );
          };

          # pkgs.lib.composeExtensions, but how to get it without infinte recursion?
          default = final: prev:
            let agda' = agda final prev;
                prev' = prev // agda';
            in agda' // standard-library final prev';
        };

        devShells.default = pkgs.mkShell {
          buildInputs = [
            agdaWithLibraries
            pkgs.haskellPackages.fix-whitespace
          ];
        };

        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "cheshire";
          version = "0.0.1";
          src = ./.;

          everythingFile = "./src/Everything.agda";

          buildInputs = with pkgs.agdaPackages; [
            standard-library
          ];

          meta = with pkgs.lib; {
            description = "Yet another category theory library";
            homepage = "https://github.com/Perspicuous-Computing/cheshire";
          };
        };
      }
    );
}
