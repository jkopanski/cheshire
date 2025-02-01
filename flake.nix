{
  description = "Yet another category theory library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/release-24.11";
    utils.url = "github:numtide/flake-utils";
    agda = {
      url = "github:agda/agda/v2.7.0.1";
      flake = false;
    };
    stdlib = {
      url = "github:agda/agda-stdlib/v2.2";
      flake = false;
    };
    stdlib-classes = {
      url = "github:agda/agda-stdlib-classes/v2.1.1";
      flake = false;
    };
    stdlib-meta = {
      url = "github:agda/agda-stdlib-meta/v2.1.1";
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
            ${pkgs.haskellPackages.fix-whitespace}/bin/fix-whitespace --check
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

          meta = with pkgs.lib; {
            description = "Yet another category theory library";
            homepage = "https://github.com/Perspicuous-Computing/cheshire";
          };
        };
      }
    )) // {
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

        packages = final: prev: {
          agdaPackages = prev.agdaPackages.overrideScope (
            finalAgda: prevAgda: {
              standard-library = prevAgda.standard-library.overrideAttrs {
                version = "2.2";
                src = inputs.stdlib;
              };

              standard-library-classes = final.agdaPackages.mkDerivation {
                pname = "standard-library-classes";
                version = "2.1.1";
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
                version = "2.1.1";
                src = inputs.stdlib-meta;

                # next release
                # everythingFile = "standard-library-meta.agda";
                everythingFile = "./Main.agda";
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

        # pkgs.lib.composeExtensions, but how to get it without infinte recursion?
        default = final: prev:
          let agda' = agda final prev;
              prev' = prev // agda';
          in agda' // packages final prev';
      };
    };
}
