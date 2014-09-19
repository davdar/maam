all: writeup

src:
	cabal configure --enable-library-profiling --enable-executable-profiling && cabal build

writeup:
	make -C writeup

toc:
	make -C writeup toc.pdf

clean:
	cabal clean
	make -C writeup clean

.PHONY: all src writeup toc clean
