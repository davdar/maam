PACKAGE = galois

.PHONY:help
help:
	@echo '******************************************'
	@echo 'make [help]       : this help'
	@echo 'make documentation: create ${PACKAGE}.pdf'
	@echo 'make distribution : create ${PACKAGE}.tar.gz'
	@echo 'make cleanup      : delete auxiliary files'
	@echo '******************************************'

.PHONY:documentation
documentation:
	@echo '******************************************'
	@echo 'Make documentation of ${PACKAGE} package...'
	latex ${PACKAGE}.ins
	latex ${PACKAGE}.dtx
	makeindex -s gind.ist ${PACKAGE}
	makeindex -s gglo.ist -o ${PACKAGE}.gls ${PACKAGE}.glo
	latex ${PACKAGE}.dtx
	latex ${PACKAGE}.dtx
	dvips -Ppdf ${PACKAGE}.dvi
	ps2pdf ${PACKAGE}.ps
	@echo '******************************************'

distribution:
	@echo '******************************************'
	@echo 'Make distribution of ${PACKAGE} package...'
	mkdir $(PACKAGE)
	cp -p README Makefile $(PACKAGE)
	cp -p $(PACKAGE).dtx $(PACKAGE).ins $(PACKAGE).pdf $(PACKAGE)
	tar -cvf $(PACKAGE).tar ./$(PACKAGE) 
	rm -rf $(PACKAGE)
	gzip -9 $(PACKAGE).tar
	@echo '******************************************'

.PHONY:cleanup
cleanup:
	@echo '******************************************'
	@echo 'Clean up...'
	rm -f ${PACKAGE}.{aux,dvi,glo,gls,idx,ilg,ind,log,ps,sty,gz}
	rm -f ${PACKAGE}.dtx~ ${PACKAGE}.ins~ Makefile~ README~
	@echo '******************************************'

