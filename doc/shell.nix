{
  mkShell,
  texlive,
}:
let
  tex = texlive.combine {
    inherit (texlive)
      scheme-medium

      csquotes
      tikz-cd
      todonotes
      translations
      ;
  };
in
mkShell {
  packages = [ tex ];
}
