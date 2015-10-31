.PHONY: default sandbox sandbox-clean build clean html

default: build

sandbox:
	cabal sandbox init
	cabal install --dependencies-only

sandbox-clean:
	rm -rf .cabal-sandbox cabal.sandbox.config

build:
	cabal build

clean:
	cabal clean

html:
	pandoc -f markdown -t html --self-contained -o README.html README.md
