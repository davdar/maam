.PHONY: pdf touch bib dobib clean

pdf: darais-quals.pdf
touch:
	touch darais-quals.tex
bib: pdf dobib touch pdf
dobib:
	bibtex darais-quals

darais-quals.pdf: darais-quals.tex setup.tex davdar.bib $(wildcard diagrams/*.tikz) $(wildcard snips/*.tex)
	xelatex -shell-escape darais-quals.tex

davdar.bib:
	curl http://www.citeulike.org/bibtex/user/davdar > davdar.bib

clean:
	rm -f *.aux *.log *.bbl *.blg *.bib *.pyg *.toc darais-quals.pdf diagrams/*.aux
