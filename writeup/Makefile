pdf: darais-quals.pdf

darais-quals.pdf: darais-quals.tex setup.tex diagrams/AI.tikz diagrams/AIGC.tikz
	xelatex -shell-escape darais-quals.tex

toc.pdf: darais-quals.toc toc.tex
	xelatex -shell-escape toc.tex

darais-quals.bbl: darais-quals.tex davdar.bib
	xelatex -shell-escape darais-quals.tex
	bibtex darais-quals
	xelatex -shell-escape darais-quals.tex

davdar.bib:
	curl http://www.citeulike.org/bibtex/user/davdar > davdar.bib

open: darais-quals.pdf
	open ./darais-quals.pdf

clean:
	rm *.aux *.log *.bbl *.blg *.bib *.pyg darais-quals.pdf

touch:
	touch darais-quals.tex

.PHONY: pdf open clean touch

