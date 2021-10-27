{ chan ? "7e9b0dff974c89e070da1ad85713ff3c20b0ca97"
, pkgs ? import (builtins.fetchTarball { url = "https://github.com/NixOS/nixpkgs/archive/${chan}.tar.gz"; }) {}
}:
# Style sheets https://github.com/citation-style-language/styles/
with pkgs;
let deps = [
      (texlive.combine
        { inherit (texlive)
        scheme-small thmtools datetime xpatch fmtcount;
        }
      )
      haskellPackages.pandoc
    ];
in
  stdenv.mkDerivation {
    name = "render_companion_guide";
    src = ./.;
    buildInputs = deps;
    buildPhase = ''
      export FONTCONFIG_PATH=src
      echo rendering...
      pandoc \
             --from markdown \
             --to latex \
             --template template.tex \
             --out companion-solver-implementation-reference.pdf \
             --pdf-engine xelatex \
             companion.md
      echo rendered.
    '';
    installPhase = ''
      mkdir -p $out
      cp companion-solver-implementation-reference.pdf $out/companion-solver-implementation-reference.pdf
      '';
  }
