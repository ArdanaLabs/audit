##
# Pandoc render
#
# @file
# @version 0.1

.PHONY: typeset

FILES=`cat index.txt`

typeset:
	pandoc                          \
	  --from         markdown       \
	  --to           latex          \
	  --template     template.tex   \
	  --out          audit.pdf 		\
	  --pdf-engine   xelatex        \
	  --bibliography biblio.bib     \
	  --csl style.csl               \
	  $(FILES)

# end
