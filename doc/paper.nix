{
  perSystem =
    {
      pkgs,
      lib,
      config,
      ...
    }:
    let
      inherit (pkgs) texlive;
      inherit (lib) fileset;
    in
    {
      packages.texlive = texlive.combine {
        inherit (texlive)
          scheme-medium

          bussproofs
          csquotes
          tikz-cd
          todonotes
          translations
          ;
      };
      packages.paper = pkgs.stdenvNoCC.mkDerivation {
        pname = "derivatives-paper";
        version = config.packages.derivative.version;
        src =
          with fileset;
          toSource {
            root = ./.;
            fileset = unions [
              ./latexmkrc
              (fileFilter (f: f.hasExt "tex") ./.)
            ];
          };

        nativeBuildInputs = [ config.packages.texlive ];

        buildPhase = ''
          runHook preBuild
          mkdir _target
          latexmk -interaction=batchmode -halt-on-error -cd
          runHook postBuild
        '';

        installPhase = ''
          runHook preInstall
          mkdir -p $out
          cp _target/main.pdf $out/
          runHook postInstall
        '';
      };
      make-shells.latex = {
        inputsFrom = [ config.packages.paper ];
      };
    };

}
