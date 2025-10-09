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

        src = builtins.path {
          name = "derivative-source";
          path = lib.sources.cleanSourceWith {
            src = ./.;
            filter = path: type: type != "directory" || baseNameOf path != "doc";
          };
        };

        buildInputs = [ cubical ];

        meta = {
          description = "Derivatives of containers in UF";
          platforms = lib.platforms.all;
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
