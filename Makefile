##
# Pandoc render
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
	  --bibliography biblio.bib     \
	  --csl acm-sig-proceedings.csl \
      --biblatex                    \
	  $(FILES)
# end
