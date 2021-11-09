# Ardana Audit

## Repo usage

Please file ideas- threat models, attack vectors, or overall just considerations for the audit -as issues. Issue templates self-explanatory.

## To render PDF

A job renders it and pushes it to github, so just look at that one. 

But if you want to render it locally, 
```sh
nix-build
```

A `Makefile` is here that will build then open with `xdg-open`.

```sh
make
```

### When a new `.md` file is added in `src`
One must add it's path in `src/index.txt`. 

**Please make sure** that the first file per subdirectory listed in `index.txt` has a `\chapter{ChapterName}` at the top. The order listed in `index.txt` is the part that matters here. 
