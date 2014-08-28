all: src

src:
	cabal configure --enable-library-profiling --enable-executable-profiling && cabal build

tex:
	make -C tex

toc:
	make -C tex toc.pdf

clean:
	cabal clean
	make -C tex clean

.PHONY: all src tex toc clean
