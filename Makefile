.PHONY: all init src writeup toc clean

all: src

init:
	runhaskell EnvSetup.hs

src:
	cabal configure --disable-library-profiling && cabal build

writeup:
	make -C writeup

toc:
	make -C writeup toc.pdf

clean:
	cabal clean
	make -C writeup clean
	rm .extensions*
	rm .options*
