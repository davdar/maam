.PHONY: all init configure build run clean

all: build

init:
	runhaskell EnvSetup.hs

configure:
	cabal configure

build:
	cabal build

run:
	cabal run maam

clean:
	cabal clean
	rm -f .extensions*
	rm -f .ghc_options*
