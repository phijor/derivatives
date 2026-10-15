{
  perSystem =
    {
      pkgs,
      lib,
      config,
      ...
    }:
    let
      inherit (lib) fileset;

      src = fileset.toSource {
        root = ./.;
        fileset = fileset.unions [
          ./latexmkrc
          (fileset.fileFilter (f: f.hasExt "tex") ./.)
          ./bibliography.bib
          ./LICENSE
        ];
      };
    in
    {
      packages.texlive = pkgs.texliveMedium.withPackages (
        ps: with ps; [
          biber
          latex-bin
          latexmk

          biblatex
          bussproofs
          cmll
          csquotes
          enumitem
          preprint # For authblk
          stmaryrd
          tcolorbox
          tikz-cd
          todonotes
          translations
          scheme-medium
        ]
      );
      packages.paper = pkgs.stdenvNoCC.mkDerivation {
        pname = "derivatives-paper";
        version = config.packages.derivative.version;

        inherit src;
        meta.license = lib.licenses.cc-by-40;

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
          cp main.pdf $out/
          runHook postInstall
        '';
      };
      packages.arxiv = pkgs.stdenvNoCC.mkDerivation {
        pname = "derivative-arxiv";
        version = config.packages.derivative.version;

        inherit src;
        meta.license = lib.licenses.cc-by-40;

        nativeBuildInputs = [ pkgs.gnutar ];

        installPhase = ''
          mkdir -p $out
          tar --create --gzip --file "$out/arxiv.tar.gz" latexmkrc *.tex bibliography.bib LICENSE
        '';
      };
      make-shells.latex = {
        inputsFrom = [
          config.packages.paper
        ];
        packages = [
          pkgs.tinymist
          pkgs.typst
          pkgs.typstyle
          pkgs.websocat
        ];
      };
    };

}
