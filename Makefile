.PHONY: all init configure build run pconfigure pbuild prun writeup toc docs clean

all: build

init:
	runhaskell EnvSetup.hs

configure:
	cabal configure

build:
	cabal build

run:
	cabal run js

pconfigure:
	cabal configure --enable-library-profiling --enable-executable-profiling

prun:
	cabal run js-prof && hp2ps -e8in -c js-prof.hp 

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
