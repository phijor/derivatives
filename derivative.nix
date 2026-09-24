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
      inherit (pkgs.haskell.lib.compose) justStaticExecutables;
      # This derivation pollutes $PATH with binaries of its dependencies
      # (in particular, Agda) if used as a build input.  This messes with
      # which version of Agda is picked up.  This is fixed by only keeping
      # the static `blindhuhn` executable.
      blindhuhn = justStaticExecutables inputs'.blindhuhn.packages.default;

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

        nativeBuildInputs = [
          blindhuhn
        ];

        postInstall = ''
          mkdir -p $html
          blindhuhn --html --html-dir=$html --html-highlight=code \
            --library-file=${pkgs.agdaPackages.mkLibraryFile [ cubical ]} \
            --blindhuhn-index derivative \
            agda/README.lagda.md
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
              ./docs/javascript
              ./docs/stylesheets
              ./docs/.nav.yml
              ./mkdocs.yml
              ./scripts/gen_agda_pages.py
              ./scripts/merge_search_index.py
            ];
          };

        nativeBuildInputs = [
          config.packages.mkdocs-env
        ];

        buildPhase = ''
          AGDA_HTML_DIR="${config.packages.derivative.html}" \
          AGDA_SEARCH_INDEX_FILE="${config.packages.derivative.html}/index.json" \
          mkdocs -v build
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
