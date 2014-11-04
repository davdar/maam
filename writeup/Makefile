pldi15.pdf: pldi15.tex pldi15.markdown.tex
	xelatex pldi15.tex

pldi15.markdown.tex: pldi15.markdown
	pandoc pldi15.markdown -t latex -o pldi15.autogen.tex

davdar.bib:
	curl http://www.citeulike.org/bibtex/user/davdar > davdar.bib

clean:
	rm *.log *.aux *.out pldi15.pdf davdar.bib *.autogen.tex
