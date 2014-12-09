# JSAI: JavaScript Abstract Interpreter

The document notjs.pdf contains the formal specification of the notJS IR, its concrete and abstract semantics. This document references builtin.pdf. The document translation.pdf contains formalisms for translation from JavaScript to notJS and the document proof-sketches.pdf contains proof sketches for the object abstract domain.

## Installation

In order to install and run the analysis, you will need:

1. [sbt version 0.12.1](http://www.scala-sbt.org/0.12.1/docs/home.html).
2. Scala version 2.10.1. 

## Building

To build the project:

1. Do a clean
```console
$ sbt clean
```

2. Do a build
```console
$ sbt compile
```     

## Running

To run the concrete interpreter:
```console
$ sbt "run-main notjs.concrete.interpreter.notJS <JavaScript file name> <options>"
```

The different options to the concrete interpreter are:

1. `--print`: This will print out the argument provided to the `print()` calls in the provided JavaScript file. 
2. `--testing`: This is used for testing concrete interpreter with the abstract interpreter. 
3. `--catchexc`: This will reduce clutter in output produced due to exceptions thrown.
4. `--printid`: This will print out the argument provided to the `print` calls, along with the ids of the print statements, helpful to debug along with abstract interpreter output. 

To run the abstract interpreter:
```console
$ sbt "run-main notjs.abstracted.interpreter.notJS <JavaScript file name> <options>"
```

The different options to the abstract interpreter are:

1. `--lightgc`: Perform lightweight gc. 
2. `--fullgc`: Perform full gc. 
3. `--prune`: Perform store pruning. 
4. `--testing`: To be provided when tested against the concrete interpreter. 
5. `--print`: This will print out the argument provided to the `print()` calls in the provided JavaScript file. 
6. `--catchexc`: This will reduce clutter in output produced due to exceptions thrown.
7.  `--timeout=`: This is used to provide a timeout (in seconds), if the abstract interpreter takes more than the specified timeout, an exception is thrown.
8. `--trace=`: This is used to provide various traces. Consult `src/main/scala/abstract/interpreter.scala` for available traces. 

More options can be seen from `src/main/scala/abstract/interpreter.scala`. 

Note: if the JavaScript file has `with` construct, please use the with rewriter in `lib/WithRewriter.jar` (`java -jar WithRewriter.jar [inputfile name] [outputfile name]`). All credits to the rewriter go to Programming Language Research Group @KAIST (http://plrg.kaist.ac.kr/research/software). 

## Running the tests

To run the simple abstract tests:
```console
$ sbt "test-only notjs.tester.abstracted.SimpleTests"
```

To run the simple abstract tests with various options:
```console
$ sbt "test-only notjs.tester.abstracted.SimpleTestsWithOptions"
```

To run the simple abstract tests with various traces:
```console
$ sbt "test-only notjs.tester.abstracted.SimpleTestsWithTraces"
```

To run the Sun Spider tests (by default, the options are `--prune` and `trace=stack-1-0`: 
```console
$ sbt "test-only notjs.tester.abstracted.SunSpiderTests"
```

## Running pretty printers

To run the text pretty printer:
```console
$ sbt "run-main notjs.syntax.TextPrint <js file> <output file> --debug"
```    

To run the code pretty printer:
```console
$ sbt "run-main notjs.syntax.CodePrint <js file> <output file> --debug"
```    

To run the dotty pretty printer:
```console
$ sbt "run-main notjs.syntax.DotPrint <js file> <output file> --debug"
```    

Each of these can also be run without the `--debug` flag, that does not treat calls to `print` specially. 
