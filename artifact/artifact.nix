{
  perSystem =
    {
      config,
      pkgs,
      lib,
      ...
    }:
    {
      packages.artifact = pkgs.stdenvNoCC.mkDerivation {
        pname = "artifact";
        version = config.packages.derivative.version;

        meta.license = lib.licenses.mit;

        nativeBuildInputs = [
          pkgs.gnutar
          pkgs.gzip
        ];

        dontUnpack = true;
        dontConfigure = true;

        buildPhase = ''
          runHook preBuild

          # Stage a trees under the directory name it should unpack into.
          # Drop the Nix store `read-only permissions so the extracted copies are editable.
          stage() {
            cp --recursive --no-preserve=mode,ownership "$1" "stage/$2"
          }

          mkdir -p stage
          # Stage the MkDocs-based site we build
          # The offline variant, not `packages.site`: the deployed site uses
          # absolute URLs and CDN assets, so it only renders behind a server.
          stage ${config.packages.site-offline}/site documentation
          # Stage everything that is tracked by git.
          # To avoid including files from a dirty tree, run `nix build --no-allow-dirty .#artifact`.
          stage ${../.} source

          # Reproducible archives: fixed member order, zeroed timestamps and
          # ownership, and `gzip --no-name` so the gzip header carries neither a
          # file name nor an mtime.
          archive() {
            tar --create \
                --directory=stage \
                --sort=name \
                --mtime='@0' \
                --owner=0 \
                --group=0 \
                --numeric-owner \
                --format=gnu \
                "$1" \
              | gzip --best --no-name > "$2.tar.gz"
          }

          archive documentation documentation
          archive source source

          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall
          mkdir -p $out
          cp documentation.tar.gz source.tar.gz $out/
          # Describe the archives for whoever downloads them from Zenodo.
          cp ${./README.md} $out/README.md
          runHook postInstall
        '';
      };
    };
}
