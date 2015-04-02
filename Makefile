.PHONY: default sandbox clean init-flags all run

default: all

sandbox:
	cabal sandbox init
	cabal install --dependencies-only

clean:
	rm -f .extensions*
	rm -f .ghc_options*
	cabal clean

init-flags:
	rm -f .extension*
	rm -f .ghc_options*
	runhaskell EnvSetup.hs

all:
	cabal build

run:
	cabal run maam

html:
	pandoc -f markdown -t html --self-contained -o README.html README.md

