##
# Alectryon Tarski1955
#
# @file
# @version 0.1

Fixpoint.v.html:
	alectryon ../src/Fixpoint.v -o Fixpoint.rst
	alectryon --frontend coq+rst --backend rst ../theories/Fixpoint.v -o Fixpoint.rst
	alectryon Fixpoint.v.rst
	alectryon --frontend rst --backend webpage Fixpoint.rst -o Fixpoint.html

open: Fixpoint.html
	xdg-open Fixpoint.html

clean:
	rm *.css *.js *.rst *.html

# end
