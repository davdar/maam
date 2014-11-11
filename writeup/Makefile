.PHONY: open clean update dependencies tidy

pldi15.pdf: pldi15.tex tmp/autogen/pldi15.markdown.tex
	mkdir -p tmp/latex-out
	xelatex --output-directory=tmp/latex-out pldi15.tex && mv tmp/latex-out/pldi15.pdf ./

tmp/autogen/pldi15.markdown.tex: pldi15.markdown Process.hs Process_macros.tbl Process_mathttNames.tbl Process_mathitNames.tbl
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

# -- The old build system: passing to sed and then pandoc command line
#
# tmp/autogen/pldi15.markdown.tex: tmp/autogen/pldi15.markdown
# 	pandoc tmp/autogen/pldi15.markdown -t latex -o tmp/autogen/pldi15.markdown.tex

# tmp/autogen/pldi15.markdown: pldi15.markdown
# 	mkdir -p tmp/autogen
# 	# removes lines that start with -- (and any number of spaces before --)
# 	cat pldi15.markdown > tmp/autogen/pldi15.markdown
# 	sed -i .bak '/^ *--.*$$/d' tmp/autogen/pldi15.markdown

