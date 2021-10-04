##
# Pandoc render
# # LEGACY: use `nix-build` instead
#
# Courtesy of https://github.com/lauritzsh/pandoc-markdown-template/tree/master/report-bib
# Style sheets https://github.com/citation-style-language/styles/
# @file
# @version 0.1

.PHONY: typeset

FILES=`cat index.txt`

typeset:
	pandoc                          \
	  --from         markdown       \
	  --to           latex          \
	  --template     template.tex   \
	  --out          audit.pdf      \
	  --pdf-engine   xelatex        \
	  --bibliography src/biblio.bib \
	  --csl acm-sig-proceedings.csl \
	  $(FILES) -V block-headings
# end
