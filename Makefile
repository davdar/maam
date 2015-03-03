.PHONY: default clean init fp darkdown maam maam-lam-if maam-hask build-all

default: maam-hask

clean:
	rm -f .extensions*
	rm -f .ghc_options*
	cabal clean

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

build-all:
	make clean fp
	make clean maam
	make clean maam-lam-if
	make clean maam-hask
	@echo "ALL BUILDS SUCCEED"
