{
  description = "Yet another category theory library";

  inputs = {
    overture.url = "sourcehut:~madnat/overture";
    nixpkgs.follows = "overture/nixpkgs";
    utils.follows = "overture/utils";
  };

  outputs = inputs@{ self, nixpkgs, utils, ... }:
    (utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ inputs.overture.overlays.default ];
        };
        agdaWithLibraries = pkgs.agda.withPackages (p: [
          p.standard-library
          inputs.overture.packages.${system}.default
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
            standard-library
            inputs.overture.outputs.packages.${system}.default
          ];

          meta = {
            description = "Yet another category theory library";
            homepage = "https://github.com/Perspicuous-Computing/cheshire";
          };
        };
      }
    ));
}
