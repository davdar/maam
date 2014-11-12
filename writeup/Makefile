.PHONY: open clean update dependencies tidy

pldi15.pdf: pldi15.tex tmp/autogen/pldi15.markdown.tex
	mkdir -p tmp/latex-out
	xelatex --output-directory=tmp/latex-out pldi15.tex && mv tmp/latex-out/pldi15.pdf ./

tmp/autogen/pldi15.markdown.tex: pldi15.markdown Process.hs *.tbl
	runhaskell Process.hs

davdar.bib:
	mkdir -p tmp
	curl http://www.citeulike.org/bibtex/user/davdar > tmp/davdar.bib

open:
	open pldi15.pdf

update:
	cabal update

dependencies:
	cabal install --only-dependencies

setup: update dependencies

clean:
	rm -rf tmp

tidy:
	runhaskell Tidy.hs

WGETDVANHORNBIB=curl -o dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:xpages&fieldmap=volume:x-volume&fieldmap=editor:x-editor&fieldmap=number:x-number&fieldmap=booktitle:x-booktitle&fieldmap=publisher:x-publisher"

getbib:
	$(WGETDVANHORNBIB)


# -- The old build system: passing to sed and then pandoc command line
#
# tmp/autogen/pldi15.markdown.tex: tmp/autogen/pldi15.markdown
# 	pandoc tmp/autogen/pldi15.markdown -t latex -o tmp/autogen/pldi15.markdown.tex

# tmp/autogen/pldi15.markdown: pldi15.markdown
# 	mkdir -p tmp/autogen
# 	# removes lines that start with -- (and any number of spaces before --)
# 	cat pldi15.markdown > tmp/autogen/pldi15.markdown
# 	sed -i .bak '/^ *--.*$$/d' tmp/autogen/pldi15.markdown

