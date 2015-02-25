.PHONY: all clean init fp maam maam-lam-if

all: maam-lam-if

clean:
	rm -f .extensions*
	rm -f .ghc_options*
	cabal clean

init:
	runhaskell EnvSetup.hs

fp:
	rm -f maam.cabal
	ln -s cabal_files/fp.cabal maam.cabal
	- cabal build

maam:
	rm -f maam.cabal
	ln -s cabal_files/maam.cabal maam.cabal
	- cabal build

maam-lam-if:
	rm -f maam.cabal
	ln -s cabal_files/maam-lam-if.cabal maam.cabal
	- cabal build
