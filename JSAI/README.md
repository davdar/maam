### JSAI Instructions

This package contains all the supplementary materials mentioned in our paper: our formalisms for the concrete interpreter, abstract interpreter, their implementation, and proof sketch for the abstract object domain. 

There are two folders in this package: `base` and `error`. The `base` folder has a `README.md` that explains how to use our tool. The `error` folder has the error client used in the paper (which is built on top of `base`).

To check how we got the performance numbers were gathered in the paper, `cd` into the `base` folder and run:

```
$ sbt "run-main notjs.abstracted.interpreter.notJS 
  src/test/resources/FSE_benchmarks/XXX.js --prune --lightgc --trace=YYY"
```

where `XXX` is the filename of the benchmark taken from the folder `src/test/resources/FSE_benchmarks/`, and `YYY` is the trace name. `YYY` can be one of the following (`N`, `N1`, `N2` stand for numbers), for the appropriate trace:

1. Context-insensitive, default: `fs` 
2. Stack CFA: `stack-N1-N2`
3. Acyclic CFA: `acyclic-N`
4. Object-sensitive CFA: `ofull-N` 
5. Signature CFA: `sig-N1-N2`
6. Mixed CFA: `cno-N1-N2`

An example run, thus, would be:
```
$ sbt "run-main notjs.abstracted.interpreter.notJS 
  src/test/resources/FSE_benchmarks/opn-aes.js --prune --lightgc --trace=stack-1-0"
```

In order to obtain the precision numbers based on the error client, switch to the `error` folder, and run everything else exactly the same way, but add `--stats` as an option at the end of the command.
