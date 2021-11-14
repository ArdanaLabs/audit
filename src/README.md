# `src/`

In this subdirectory go the *actual draft/final* documents. They are assembled into a `.pdf` with `pandoc` in `../default.nix` according to the listing in `index.txt`. 

Note the first section of each chapter (with respect to the ordering in `index.txt`) **must** have `\chapter{ChapterName}` at the top. 

**They are not meant for reading on github. Latex markup will not render if you're reading on github. Please read in `../audit.pdf`**

## `.csl` sheets

You can get [`.csl` sheets here](https://github.com/citation-style-language/styles/) which in theory style up the bibliography, but we're not currently using _any_ in the render because of what is either a pandoc bug or improper usage. 

## On appendices

I have removed `invariant derivations` from `index.txt`, and since that was the only appendix **we currently have no appendices**. I'm saving the contents of `invariant.md` for a future publication on rootfinding. 
