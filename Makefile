.PHONY: all init configure build pconfigure pbuild writeup toc docs clean

all: build

init:
	runhaskell EnvSetup.hs

configure:
	cabal configure

build:
	cabal build

pconfigure:
	cabal configure --enable-library-profiling --enable-executable-profiling

pbuild:
	cabal build

writeup:
	make -C writeup

toc:
	make -C writeup toc.pdf

docs:
	pandoc --ascii -f markdown -t html README > README.html

clean:
	cabal clean
	rm -f .extensions*
	rm -f .ghc_options*
	rm -f README.html
	rm -f js-prof.hp
	rm -f js-prof.prof
	rm -f js-prof.ps
