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

      src =
        with lib.fileset;
        toSource {
          root = ./.;
          fileset = unions [
            ./derivative.agda-lib
            ./agda
          ];
        };

      derivative = pkgs.agdaPackages.mkDerivation {
        pname = "derivative";
        version = "0.1.0";

        inherit src;

        outputs = [ "out" "html" ];

        buildInputs = [ cubical ];

        postInstall = ''
          mkdir -p $html
          agda --html --html-dir=$html --html-highlight=code agda/README.lagda.md
        '';

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
      packages.mkdocs-env = (
        pkgs.python314.withPackages (p: [
          p.mkdocs
          p.mkdocs-awesome-nav
          p.mkdocs-gen-files
          p.mkdocs-material

          p.black
        ])
      );

      packages.site = pkgs.stdenvNoCC.mkDerivation {
        pname = "site";
        version = "0.1.0";

        meta.license = lib.licenses.mit;

        src =
          with lib.fileset;
          toSource {
            root = ./.;
            fileset = unions [
              ./docs/stylesheets
              ./docs/.nav.yml
              ./mkdocs.yml
              ./scripts/gen_agda_pages.py
            ];
          };

        nativeBuildInputs = [
          config.packages.mkdocs-env
        ];

        buildPhase = ''
          AGDA_HTML_DIR="${config.packages.derivative.html}" mkdocs -v build
        '';

        installPhase = ''
          mkdir -p $out
          cp -vr site $out
        '';
      };

      make-shells.default = {
        inputsFrom = [ config.packages.derivative ];
        packages = [
          inputs'.cornelis.packages.cornelis

          config.packages.mkdocs-env
        ];
      };
    };
}
