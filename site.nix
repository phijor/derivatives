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
      # Assets the site otherwise pulls from a CDN.  Vendored so that the
      # offline build is self-contained: Nix builds have no network, so the
      # `privacy` plugin (which mkdocs-material recommends for this) cannot run.
      #
      # Pinned to the exact versions the online site serves today, so the
      # archived copy renders identically to what reviewers saw.  MathJax's
      # CHTML output lazy-loads webfonts from the script's own directory, so the
      # whole `es5/` tree is needed, not just the bundle.
      mathjax = pkgs.fetchzip {
        name = "mathjax-3.2.2";
        url = "https://registry.npmjs.org/mathjax/-/mathjax-3.2.2.tgz";
        hash = "sha256-KFtCOTH1/4xgDOz/Xr0F8pteCtRg0TmAsjn9Wzv0M/M=";
      };

      # Injected by the `offline` plugin itself, to let the search Web Worker
      # start from a `file://` URL.
      iframe-worker-shim = pkgs.fetchurl {
        name = "iframe-worker-shim.js";
        url = "https://unpkg.com/iframe-worker@1.0.4/shim/index.js";
        hash = "sha256-6OQS28/qm34xtf+iiNe2A1kV5xTFQvQXagzb4mL8lgk=";
      };

      siteSrc =
        with lib.fileset;
        toSource {
          root = ./.;
          fileset = unions [
            ./docs/javascript
            ./docs/stylesheets
            ./docs/.nav.yml
            ./mkdocs.yml
            ./scripts/check_internal_links.py
            ./scripts/gen_agda_pages.py
            ./scripts/merge_search_index.py
          ];
        };

      mkSite =
        { offline }:
        pkgs.stdenvNoCC.mkDerivation {
          pname = if offline then "site-offline" else "site";
          version = "0.1.0";

          meta.license = lib.licenses.mit;

          src = siteSrc;

          nativeBuildInputs = [ config.packages.mkdocs-env ];

          # Declarative and reviewable, and `patch` fails loudly if `mkdocs.yml`
          # drifts away from the context lines -- which is what we want: a
          # silently unapplied hunk would yield an artifact needing a server.
          patches = lib.optional offline ./mkdocs-offline.patch;

          # MathJax is vendored for *both* variants: `mkdocs.yml` points at the
          # local copy, so the deployed site no longer hits a CDN either.
          postPatch = ''
            cp -r --no-preserve=mode,ownership ${mathjax}/es5 docs/javascript/mathjax
          '';

          # `runHook` is load-bearing: a custom buildPhase replaces stdenv's,
          # which is what would otherwise call postBuild.  Without these the
          # offline fix-ups below are silently skipped.
          buildPhase = ''
            runHook preBuild
            AGDA_HTML_DIR="${config.packages.derivative.html}" \
            AGDA_SEARCH_INDEX_FILE="${config.packages.derivative.html}/index.json" \
            mkdocs -v build
            runHook postBuild
          '';

          # The shim URL is baked into the offline plugin's template, so it can
          # only be replaced after the fact.  Every page sits at the site root
          # (`use_directory_urls: false`, and the Agda pages are flat), so one
          # relative path works everywhere.
          postBuild =
            lib.optionalString offline ''
              install -D ${iframe-worker-shim} site/assets/javascripts/iframe-worker-shim.js
              substituteInPlace site/*.html \
                --replace-fail \
                  'https://unpkg.com/iframe-worker/shim' \
                  'assets/javascripts/iframe-worker-shim.js'

              # Nothing may reach for the network.  `404.html` is exempt: it keeps
              # absolute paths by design, and is never opened from disk.
              if remaining=$(grep -rlE 'https?://(unpkg\.com|fonts\.(googleapis|gstatic)\.com)' \
                    site --include='*.html' | grep -v '404\.html$'); then
                echo "offline build still references external hosts:" >&2
                echo "$remaining" >&2
                exit 1
              fi
            ''
            # Both variants: no page may link to a file we do not ship.
            + ''
              python3 scripts/check_internal_links.py site
            '';

          installPhase = ''
            runHook preInstall
            mkdir -p $out
            cp -r site $out
            runHook postInstall
          '';
        };
    in
    {
      packages.mkdocs-env = (
        pkgs.python314.withPackages (p: [
          p.mkdocs
          p.mkdocs-awesome-nav
          p.mkdocs-gen-files
          p.mkdocs-material

          p.black
        ])
      );

      packages.site = config.packages.site-online;

      # The deployed site, and an offline variant for archival.  They differ
      # only by `mkdocs-offline.patch`.
      packages.site-online = mkSite { offline = false; };
      packages.site-offline = mkSite { offline = true; };
    };
}
