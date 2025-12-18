{
  perSystem =
    {
      config,
      pkgs,
      lib,
      inputs',
      ...
    }:
    let
      cubical = pkgs.agdaPackages.cubical;

      derivative = pkgs.agdaPackages.mkDerivation {
        pname = "derivative";
        version = "0.1.0";

        src = with lib.fileset; toSource {
          root = ./.;
          fileset = unions [
            ./derivative.agda-lib
            ./Derivative
          ];
        };

        buildInputs = [ cubical ];

        meta = {
          description = "Derivatives of containers in UF";
          platforms = lib.platforms.all;
          license = lib.licenses.mit;
        };
      };
    in
    {
      packages.derivative = derivative;
      packages.default = config.packages.derivative;

      make-shells.default = {
        inputsFrom = [ config.packages.derivative ];
        packages = [
          inputs'.cornelis.packages.cornelis
        ];
      };
    };
}
