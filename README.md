# Ardana Audit

# Build instructions

Render `audit.pdf` to the `result` directory. 
``` sh
nix-build
```

Note, **realistically you can dodge this because it happens in a github action and gets automatically pushed to `main` branch**. 

If you have `xdg-open` to open files (i.e. like in ubuntu), the `Makefile` will build it then open it. 

``` sh
make 
```

# Developer setup instructions

[Install `nix`](https://nixos.org/download.html). You can technically skip this because rendering happens in github action. 

# Developer workflow instructions

After you push you have (wait like under a minute) to 

``` sh
git fetch origin
git pull origin main
```

To pull down the action-rendered `audit.pdf`, so that your later pushes aren't rejected. 

Edit source files with markdown in latex, you can use `nix-build` to verify that nothing in the render is broken. 

[Here](https://garrettgman.github.io/rmarkdown/authoring_pandoc_markdown.html) is a resource on pandoc markdown. It does differ from github markdown in a few places. 

# Directory structure explanation

## `src/`: everything concerning the render

Subdirectories `preamble`, `considerations`, `attacks`, `postamble`, `appendices` correspond to _chapters_, which are roman-numeral'd in the pdf render. 

`src/` also has files like `cover.tex`, `biblio.bib`, and `template.tex` specifying all cover page, bibliography, and `TeX` metadata respectively. 

When a new `.md` file is added in `src` one must add it's path in `src/index.txt`. The order in which things appear in `index.txt` is the order in which they'll be rendered. Links, table of contents, and bibliography are all rather intelligent. 

Besides the contents of the `/preamble` subdirectory, you shouldn't have to worry about (roman-numeral'd) chapter names.

## `longreports/`: research that might not go into the major public facing documents

This includes
- A coq theory of the eutxo model, that was mostly for my own educational benefit (`dune` build configured and available, for the curious). 
- Jupyter notebooks analyzing rootfinding solver behavior (I think the `nix-shell` is a little busted, but there's a `Dockerfile` in there).
- Some mathematical notes about the invariant function (also jupyter notebooks, just for latex reasons).
- `companion` matrix failed proof of concept (`cabal` build configured and available, for the curious). 

# Core branches meaning explanation 

I only work on `main`, and I push directly to it from `local`. 

April should work from branches with names like `copywrite-<sectionname>` and file pull requests to `main`.
