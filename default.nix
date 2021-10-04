{ chan ? "7e9b0dff974c89e070da1ad85713ff3c20b0ca97"
, pkgs ? import (builtins.fetchTarball { url = "https://github.com/NixOS/nixpkgs/archive/${chan}.tar.gz"; }) {}
}:
with pkgs;
let deps = [
      (texlive.combine
        { inherit (texlive)
        scheme-small biblatex xpatch datetime fmtcount amsmath graphics hyperref xetex;
        }
      )
      haskellPackages.pandoc
    ];
in
  stdenv.mkDerivation {
    name = "render_audit";
    src = ./.;
    buildInputs = deps;
    buildPhase = ''pandoc \
      --from markdown \
      --to latex \
      --template src/template.tex \
      --out audit.pdf \
      --bibliography src/biblio.bib \
      --pdf-engine xelatex \
      --csl src/acm-sig-proceedigns.csl \
      $(cat src/index.txt)
    '';
    installPhase = ''
      mkdir -p $out
      cp audit.pdf $out/audit.pdf
      '';
  }
