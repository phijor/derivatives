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
            ];
          };

        nativeBuildInputs = [
          (pkgs.python3.withPackages (p: [
            p.mkdocs
            p.mkdocs-awesome-nav
            p.mkdocs-material
          ]))
          pkgs.sd
        ];

        # configurePhase = ''
        #   cp -vrT ${config.packages.derivative.html} docs
        # '';

        buildPhase = ''
          mkdir -p docs

          echo "Copying hightlighted Markdown files..."
          cp -v ${config.packages.derivative.html}/*.md docs/

          echo "Wrapping raw HTML files as Markdown..."
          for raw in ${config.packages.derivative.html}/*.html; do
            base="''${raw##*/}"
            md="docs/''${base%.html}.md"
            echo "Preparing $raw → $md..."
            cp -v $raw $md
            sd '\A' '<pre class="Agda">' $md
            sd '\z' '</pre>' $md
          done

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

          pkgs.gnumake
          pkgs.sd
          (pkgs.python3.withPackages (p: [
            p.mkdocs
            p.mkdocs-awesome-nav
            p.mkdocs-material
          ]))
        ];
      };
    };
}
