.PHONY: open clean update dependencies tidy

pldi15.pdf: pldi15.tex tmp/autogen/pldi15.markdown.tex tmp/dvanhorn.bib tmp/davdar.bib
	mkdir -p tmp/latex-out/include
	xelatex --output-directory=tmp/latex-out pldi15.tex 
	cp tmp/davdar.bib tmp/latex-out/
	cp tmp/dvanhorn.bib tmp/latex-out/
	cd tmp/latex-out ; bibtex pldi15
	xelatex --output-directory=tmp/latex-out pldi15.tex 
	xelatex --output-directory=tmp/latex-out pldi15.tex 
	cp tmp/latex-out/pldi15.pdf ./

tmp/autogen/pldi15.markdown.tex: pldi15.markdown Process.hs *.tbl
	runhaskell Process.hs

tmp/davdar.bib:
	mkdir -p tmp
	curl -o tmp/davdar.bib "http://www.citeulike.org/bibtex/user/davdar?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:booktitle&fieldmap=booktitle:x-booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:xpages&fieldmap=volume:x-volume&fieldmap=editor:x-editor&fieldmap=number:x-number"

open:
	open pldi15.pdf

update:
	cabal update

dependencies:
	cabal install --only-dependencies

setup: update dependencies

clean:
	rm -rf dist
	rm -rf tmp

tidy:
	runhaskell Tidy.hs

tmp/dvanhorn.bib:
	mkdir -p tmp
	curl -o tmp/dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:booktitle&fieldmap=booktitle:x-booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:xpages&fieldmap=volume:x-volume&fieldmap=editor:x-editor&fieldmap=number:x-number"
