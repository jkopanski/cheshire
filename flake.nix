{
  description = "Yet another category theory library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-25.11";
    utils.url = "github:numtide/flake-utils";
    stdlib-classes = {
      url = "github:agda/agda-stdlib-classes/v2.3";
      flake = false;
    };
    stdlib-meta = {
      url = "github:agda/agda-stdlib-meta/v2.3";
      flake = false;
    };
  };

  outputs = inputs@{ self, nixpkgs, utils, ... }:
    (utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ self.overlays.default ];
        };
        agdaWithLibraries = pkgs.agda.withPackages (p: [
          p.standard-library p.standard-library-classes p.standard-library-meta
        ]);

      in {
        checks.whitespace = pkgs.stdenvNoCC.mkDerivation {
          name = "check-whitespace";
          dontBuild = true;
          src = ./.;
          doCheck = true;
          checkPhase = ''
            ${pkgs.haskellPackages.fix-whitespace.bin}/bin/fix-whitespace --check
          '';
          installPhase = ''mkdir "$out"'';
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
            standard-library standard-library-classes standard-library-meta
          ];

          meta = {
            description = "Yet another category theory library";
            homepage = "https://github.com/Perspicuous-Computing/cheshire";
          };
        };
      }
    )) // {
      overlays = rec {
        packages = final: prev: {
          agdaPackages = prev.agdaPackages.overrideScope (
            finalAgda: prevAgda: {
              standard-library-classes = final.agdaPackages.mkDerivation {
                pname = "standard-library-classes";
                version = "2.3";
                src = inputs.stdlib-classes;

                everythingFile = "./standard-library-classes.agda";
                libraryFile = "agda-stdlib-classes.agda-lib";

                buildInputs = with final.agdaPackages; [
                  standard-library
                ];

                meta = with final.lib; {
                  description = "Type-classes for the Agda standard library";
                  homepage = "https://github.com/agda/agda-stdlib-classes";
                  license = licenses.mit;
                };
              };

              standard-library-meta = final.agdaPackages.mkDerivation {
                pname = "standard-library-meta";
                version = "2.3";
                src = inputs.stdlib-meta;

                everythingFile = "standard-library-meta.agda";
                libraryFile = "agda-stdlib-meta.agda-lib";

                buildInputs = with final.agdaPackages; [
                  standard-library standard-library-classes
                ];

                meta = with final.lib; {
                  description = "Meta-programming utilities for Agda";
                  homepage = "https://github.com/agda/agda-stdlib-meta";
                  license = licenses.mit;
                };
              };
            }
          );
        };

        default = packages;
      };
    };
}
