.PHONY: all init configure build writeup toc docs clean

all: build

init:
	runhaskell EnvSetup.hs

configure:
	cabal configure --disable-library-profiling

build:
	cabal build

writeup:
	make -C writeup

toc:
	make -C writeup toc.pdf

docs:
	pandoc --ascii -f markdown -t html README > README.html

clean:
	cabal clean
	make -C writeup clean
	rm .extensions*
	rm .options*
	rm README.html
