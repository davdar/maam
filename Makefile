.PHONY: default clean init fp darkdown maam maam-lam-if maam-hask build-all

default: all

clean:
	rm -f .extensions*
	rm -f .ghc_options*
	cabal clean
	- hdevtools --stop-server

init:
	runhaskell EnvSetup.hs

fp:
	rm -f maam.cabal
	ln -s cabal_files/fp.cabal maam.cabal
	cabal build

darkdown:
	rm -f maam.cabal
	ln -s cabal_files/darkdown.cabal maam.cabal
	cabal build

maam:
	rm -f maam.cabal
	ln -s cabal_files/maam.cabal maam.cabal
	cabal build

maam-lam-if:
	rm -f maam.cabal
	ln -s cabal_files/maam-lam-if.cabal maam.cabal
	cabal build

maam-hask:
	rm -f maam.cabal
	ln -s cabal_files/maam-hask.cabal maam.cabal
	cabal build

all:
	rm -f maam.cabal
	ln -s cabal_files/all.cabal maam.cabal
	cabal build
