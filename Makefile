all: src tex

src:
	cabal configure && cabal build

tex:
	make -C tex

toc:
	make -C tex toc.pdf

clean:
	make -C code clean
	make -C tex clean

.PHONY: all src tex toc clean
