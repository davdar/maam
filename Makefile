.PHONY: all init src ghci writeup docs toc clean

all: writeup

init:
	runhaskell EnvSetup.hs

configure:
	cabal configure --disable-library-profiling

build:
	cabal build

writeup:
	make -C writeup

docs:
	pandoc --ascii -f markdown -t html README > README.html

clean:
	cabal clean
	make -C writeup clean
	rm .extensions*
	rm .options*
	rm README.html
