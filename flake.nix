{
  description = "Yet another category theory library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/24.05";
    utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, utils }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        agdaWithLibraries = pkgs.agda.withPackages (p: [
          p.agda-categories
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
            agda-categories
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
