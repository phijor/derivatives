{
  perSystem =
    {
      config,
      pkgs,
      lib,
      inputs',
      ...
    }:
    {
      packages.serve = pkgs.writeShellScriptBin "serve" ''
        AGDA_SITE_DIR='${config.packages.site}/site' python ${./serve.py}
      '';
    };
}
