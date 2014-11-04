.PHONY: clean

tmp/latex-out/pldi15.pdf: pldi15.tex tmp/autogen/pldi15.markdown.tex
	mkdir -p tmp/latex-out
	xelatex --output-directory=tmp/latex-out pldi15.tex && mv tmp/latex-out/pldi15.pdf ./

tmp/autogen/pldi15.markdown.tex: tmp/autogen/pldi15.markdown
	pandoc tmp/autogen/pldi15.markdown -t latex -o tmp/autogen/pldi15.markdown.tex

tmp/autogen/pldi15.markdown: pldi15.markdown
	mkdir -p tmp/autogen
	# removes lines that start with -- (and any number of spaces before --)
	cat pldi15.markdown > tmp/autogen/pldi15.markdown
	sed -i .bak '/^ *--.*$$/d' tmp/autogen/pldi15.markdown

davdar.bib:
	mkdir -p tmp
	curl http://www.citeulike.org/bibtex/user/davdar > tmp/davdar.bib

clean:
	rm -rf tmp
