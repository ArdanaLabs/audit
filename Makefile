##
# nix-build render and open
#
# @file
# @version 0.1

.PHONY: typeset

typeset:
	nix-build
	xdg-open result/audit.pdf
# end
