## Building and Running

I recommend building with a cabal sandbox. To initialize a cabal sandbox and
install needed dependencies, run:

    make sandbox

I have not included dependency bounds in my cabal file. Should you have trouble
finding appropriate bounds, here are the versions of ghc and cabal packages
that I am using.

    base=4.7.0.2
    Cabal=1.18.1.5
    containers=0.5.5.1
    directory=1.2.1.0
    ghc=7.8.4
    template-haskell=2.9.0.0
    text=1.2.0.4

## Running

To run the project, displaying an analysis of various lambda-if examples, run:

    make run

Example output is included at the end of this readme.

## Interactive (GHCI)

To support my custom (well-formatted and colored) pretty printing in ghci, you
need to first initialize some ghc flag files:

    make init-flags

Then just run:

    ./ghci.sh

to run Main, or:

    ./ghci.sh Lang.LamIf.Examples

to run another module, like `LamIf.Examples`.


## Source Code

All code is in `/src`.

### FP

`FP` is a core functional programming library which replaces the standard
Prelude. `FP` fixes some oddities of the Prelude which exist only for backward
compatability. `FP` includes more batteries for things like functors, monads,
monad transformers, lenses, pretty printing, parsing, deriving, and more. On
the downside, it is non-idiomatic at parts and isn't as mature (i.e. debugged
and stable).

### MAAM

`MAAM` is a semantics-independent package for implement path, flow, context and object
sensitivity in program analysis. `MAAM` only contains types and definitions
which are _analysis specific_. Because the monad transformers that capture path
and flow sensitivity are fully general purpose, they are defined in
`FP.Monads`, not here. The same goes for lattice structures, which are mostly
all defined in `FP.Core`.

The only parts that are specific to analysis are:

- Mapping monadic actions to state space transition systems, which is defined
  in `MAAM.MonadStep`.
- Implementations for abstract time to infinite-k (concrete), finite-k, and
  zero-k, which are defined in `MAAM.Time`.

### LamIf

`Lang.LamIf` implements the following for a small applied lambda calculus with
booleans and if-statements:

- Direct-style syntax (`Lang.LamIf.Syntax`)
- Continuation passing style (CPS) syntax (`Lang.LamIf.CPS`)
- Parsing (`Lang.LamIf.Parser`) and pretty printing (`Lang.LamIf.Pretty`)
- CPS conversion (`Lang.LamIf.Passes`)
- Semantics state-space (`Lang.LamIf.StateSpace`)
- Monadic semantics (`Lang.LamIf.Semantics`)
- Concrete and abstract value domains (`Lang.LamIf.Val`)
- Instantiations of language-independent monads from `MAAM` (`Lang.LamIf.Monads`)
- Orthogonal analysis parameters (`Lang.LamIf.Analyses`)
- Example analyses (`Lang.LamIf.Examples`)

### Hask

A semantics for GHC core is implemented in `Lang.Hask`:

- CPS syntax and conversion (`Lang.Hask.CPS`)
- Pretty printing (`Lang.Hask.Pretty`)
- Monadic semantics (`Lang.Hask.Semantics`)
- Execution semantics (`Lang.Hask.Execution`)
- Instantiations of language-independent monads from `MAAM` (`Lang.Hask.Monads`)
- Concrete value domain (`Lang.Hask.ValConcrete`)
- Lifting of an arbitrary value domain to a sum-of-products lattice (`Lang.Hask.SumOfProdVal`)

While the core semantics for core GHC is implemented, we haven't implemented
any GHC primitives yet, but you should be able to get a feel for the semantics
without the primitives. (More coming soon.)

## Example Output

If you execute the project it will compute an abstract interpretation of some
very small LamIf programs.

The output includes results for the heap when it reaches any `HALT` state:

The current output of `make run` is:

    ...
