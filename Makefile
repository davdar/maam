.PHONY: default sandbox-init sandbox-clean ghci-init ghc-clean setup-init setup-clean build clean html

default: build

sandbox-init:
	cabal sandbox init
	cabal install --dependencies-only

sandbox-clean:
	rm -rf .cabal-sandbox cabal.sandbox.config

ghci-init:
	runhaskell env-setup/EnvSetup.hs

ghci-clean:
	rm -f .extensions*
	rm -f .ghc_options*

setup-init: sandbox-init ghci-init
setup-clean: sandbox-clean ghci-clean

build:
	cabal build

clean:
	cabal clean

html:
	pandoc -f markdown -t html --self-contained -o README.html README.md
