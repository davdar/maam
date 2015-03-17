.PHONY: open clean update dependencies tidy

GHC_FLAGS = -package-db=$(wildcard .cabal-sandbox/*-packages.conf.d)

oopsla2015.pdf: oopsla2015.tex tmp/autogen/paper.markdown.tex tmp/dvanhorn.bib tmp/davdar.bib
	mkdir -p tmp/latex-out/include
	xelatex --output-directory=tmp/latex-out oopsla2015.tex 
	cp tmp/davdar.bib tmp/latex-out/
	cp tmp/dvanhorn.bib tmp/latex-out/
	cd tmp/latex-out ; bibtex oopsla2015
	xelatex --output-directory=tmp/latex-out oopsla2015.tex 
	xelatex --output-directory=tmp/latex-out oopsla2015.tex 
	cp tmp/latex-out/oopsla2015.pdf ./

init:
	cabal sandbox init
	cabal install --dependencies-only

reinit:
	rm -rf .cabal-sandbox
	make init

tmp/autogen/paper.markdown.tex: paper.markdown Process.hs *.tbl
	runhaskell $(GHC_FLAGS) Process.hs

tmp/davdar.bib:
	mkdir -p tmp
	curl -o tmp/davdar.bib "http://www.citeulike.org/bibtex/user/davdar?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=abstract:x-abstract&fieldmap=pages:xpages&fieldmap=volume:x-volume&fieldmap=editor:x-editor&fieldmap=number:x-number"

open:
	open oopsla2015.pdf

update:
	cabal update

dependencies:
	cabal install --only-dependencies

setup: update dependencies

clean:
	rm -rf dist
	rm -rf tmp

tidy:
	runhaskell $(GHC_FLAGS) Tidy.hs

tmp/dvanhorn.bib:
	mkdir -p tmp
	curl -o tmp/dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=abstract:x-abstract&fieldmap=pages:xpages&fieldmap=volume:x-volume&fieldmap=editor:x-editor&fieldmap=number:x-number"
