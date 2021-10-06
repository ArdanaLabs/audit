{ chan ? "7e9b0dff974c89e070da1ad85713ff3c20b0ca97"
, pkgs ? import (builtins.fetchTarball { url = "https://github.com/NixOS/nixpkgs/archive/${chan}.tar.gz"; }) {}
}:
# Style sheets https://github.com/citation-style-language/styles/
with pkgs;
let deps = [
      (texlive.combine
        { inherit (texlive)
        scheme-small datetime xpatch fmtcount;
        }
      )
      haskellPackages.pandoc
    ];
in
  stdenv.mkDerivation {
    name = "render_audit";
    src = ./.;
    buildInputs = deps;
    buildPhase = ''
      export FONTCONFIG_PATH=src
      echo rendering...
      pandoc \
             --from markdown+citations \
             --to latex \
             --template src/template.tex \
             --bibliography src/biblio.bib \
             --out audit.pdf \
             --pdf-engine xelatex \
             $(cat src/index.txt) \
             --citeproc
      echo rendered.
    '';
    installPhase = ''
      mkdir -p $out
      cp audit.pdf $out/audit.pdf
      '';
  }
