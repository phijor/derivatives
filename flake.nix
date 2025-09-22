{
  description = "An Agda Library set up with Nix Flakes";
  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    cornelis.url = "github:agda/cornelis";
    cornelis.inputs.nixpkgs.follows = "nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs =
    {
      nixpkgs,
      cornelis,
      flake-utils,
      ...
    }:
    let
      inherit (flake-utils.lib) eachDefaultSystem;
    in
    eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        lib = pkgs.lib;
        cubical = pkgs.agdaPackages.cubical;

        derivative = pkgs.agdaPackages.mkDerivation {
          pname = "derivative";
          version = "0.1.0";

          src = builtins.path {
            name = "derivative-source";
            path = lib.sources.cleanSource ./.;
          };

          buildInputs = [ cubical ];

          meta = {
            description = "Derivatives of containers in UF";
            platforms = lib.platforms.all;
          };
        };
      in
      {
        packages.default = derivative;
        devShells.default = pkgs.mkShell {
          inputsFrom = [ derivative ];
          packages = [
            cornelis.packages.${system}.cornelis
            pkgs.cornelis
          ];
        };
      }
    );
}
