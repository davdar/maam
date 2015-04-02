## Building and Running

I recommend building with a cabal sandbox. To initialize a cabal sandbox (that
will live in the current directory) and install needed dependencies, run:

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

to run another module, like `Lang.LamIf.Examples`.

## Source Code

All code is in `/src`.

### FP

`FP` is a core functional programming library which replaces the standard
Prelude. `FP` includes more batteries for things like functors, monads, monad
transformers, lenses, pretty printing, parsing, deriving, and more. On the
downside, it is non-idiomatic at parts and isn't as mature (i.e. debugged and
stable).

### MAAM

`MAAM` is a semantics-independent package for implement path, flow, context and object
sensitivity in program analysis. `MAAM` only contains types and definitions
which are _analysis specific_. Because the monad transformers that capture path
and flow sensitivity are fully general purpose, they are defined in
`FP.Monads`, not here. The same goes for lattice structures, which are mostly
all defined in `FP.Core`. If I were to port `MAAM` to use GHC's Prelude, I
would need to rip out maybe 50% of `FP` to be packaged alongside it.

The only code that ends up being specific to analysis is:

- Mapping monadic actions to state space transition systems, which is defined
  in `MAAM.MonadStep`.
- Implementations for abstract time to infinite-k (concrete), finite-k and
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
without the primitives. (More on this coming soon.)

## Example Output

If you execute the project it will compute an abstract interpretation of some
very small `LamIf` programs.

The output includes results for the heap when it reaches any `HALT` state:

Below is a copy of the (normally ANSI-terminal-color-coded) output of `make
run`. For 0CFA results the state space will contain `∙` values and abstract
environments mapping variables to themselves, which are degenerate encodings of
(unused) call-site sensitivity. The abstract heap will come last, mapping
variables to the values they take on. This is also the example from the Galois
Transformers paper. More examples programs can be found in `/data/lamif-src`,
with example configurations found in `/src/Lang/LamIf/Examples.hs`.
    
    Source
    let b := 1 - 1 >= 0 in
    let v := if b
        then if b then 1 else 2
        else if b then 3 else 4
    in
    let w := if b then 5 else 6 in <v,w>
    Stamped
    0:let 0:b := 1:(2:(3:1) - (4:1)) >= (5:0) in
    6:let 1:v := 7:if 8:0:b
        then 9:if 10:0:b then 11:1 else 12:2
        else 13:if 14:0:b then 15:3 else 16:4
    in
    17:let 2:w := 18:if 19:0:b then 20:5 else 21:6 in
    22:<23:1:v,24:2:w>
    CPS
    25:3:a#0 := 2:1 - 1
    0:0:b := 1:(3:a#0) >= 0
    33:8:k#5 := 32:λ 4:x#1 ->
      6:1:v := 7:4:x#1
      29:7:k#4 := 28:λ 5:x#2 ->
        17:2:w := 18:5:x#2
        26:6:a#3 := 22:<1:v,2:w>
        27:HALT (6:a#3)
      18:if 0:b then 30:(7:k#4) 5 else 31:(7:k#4) 6
    7:if 0:b
      then
        9:if 0:b then 34:(8:k#5) 1 else 35:(8:k#5) 2
      else
        13:if 0:b then 36:(8:k#5) 3 else 37:(8:k#5) 4
    LT=0 DT=0 V=abstract M=fi G=yes C=link LF=app DF=app
    ( { ( 27:HALT (6:a#3)
        , ( ∙
          , ∙
          , { 0:b => <x=0:b,lτ=∙,dτ=∙>
            , 1:v => <x=1:v,lτ=∙,dτ=∙>
            , 2:w => <x=2:w,lτ=∙,dτ=∙>
            , 3:a#0 => <x=3:a#0,lτ=∙,dτ=∙>
            , 4:x#1 => <x=4:x#1,lτ=∙,dτ=∙>
            , 5:x#2 => <x=5:x#2,lτ=∙,dτ=∙>
            , 6:a#3 => <x=6:a#3,lτ=∙,dτ=∙>
            }
          )
        )
      }
    , { <x=1:v,lτ=∙,dτ=∙> => {1,2,3,4}
      , <x=2:w,lτ=∙,dτ=∙> => {5,6}
      , <x=6:a#3,lτ=∙,dτ=∙> =>
          {<<x=1:v,lτ=∙,dτ=∙>,<x=2:w,lτ=∙,dτ=∙>>}
      }
    )
    LT=0 DT=0 V=abstract M=fs G=yes C=link LF=app DF=app
    { 27:HALT (6:a#3) =>
        ( { ( ∙
            , ∙
            , { 0:b => <x=0:b,lτ=∙,dτ=∙>
              , 1:v => <x=1:v,lτ=∙,dτ=∙>
              , 2:w => <x=2:w,lτ=∙,dτ=∙>
              , 3:a#0 => <x=3:a#0,lτ=∙,dτ=∙>
              , 4:x#1 => <x=4:x#1,lτ=∙,dτ=∙>
              , 5:x#2 => <x=5:x#2,lτ=∙,dτ=∙>
              , 6:a#3 => <x=6:a#3,lτ=∙,dτ=∙>
              }
            )
          }
        , { <x=1:v,lτ=∙,dτ=∙> => {1,4}
          , <x=2:w,lτ=∙,dτ=∙> => {5,6}
          , <x=6:a#3,lτ=∙,dτ=∙> =>
              {<<x=1:v,lτ=∙,dτ=∙>,<x=2:w,lτ=∙,dτ=∙>>}
          }
        )
    }
    LT=0 DT=0 V=abstract M=ps G=yes C=link LF=app DF=app
    { ( 27:HALT (6:a#3)
      , ( ( ∙
          , ∙
          , { 0:b => <x=0:b,lτ=∙,dτ=∙>
            , 1:v => <x=1:v,lτ=∙,dτ=∙>
            , 2:w => <x=2:w,lτ=∙,dτ=∙>
            , 3:a#0 => <x=3:a#0,lτ=∙,dτ=∙>
            , 4:x#1 => <x=4:x#1,lτ=∙,dτ=∙>
            , 5:x#2 => <x=5:x#2,lτ=∙,dτ=∙>
            , 6:a#3 => <x=6:a#3,lτ=∙,dτ=∙>
            }
          )
        , { <x=1:v,lτ=∙,dτ=∙> => {1}
          , <x=2:w,lτ=∙,dτ=∙> => {5}
          , <x=6:a#3,lτ=∙,dτ=∙> =>
              {<<x=1:v,lτ=∙,dτ=∙>,<x=2:w,lτ=∙,dτ=∙>>}
          }
        )
      )
    , ( 27:HALT (6:a#3)
      , ( ( ∙
          , ∙
          , { 0:b => <x=0:b,lτ=∙,dτ=∙>
            , 1:v => <x=1:v,lτ=∙,dτ=∙>
            , 2:w => <x=2:w,lτ=∙,dτ=∙>
            , 3:a#0 => <x=3:a#0,lτ=∙,dτ=∙>
            , 4:x#1 => <x=4:x#1,lτ=∙,dτ=∙>
            , 5:x#2 => <x=5:x#2,lτ=∙,dτ=∙>
            , 6:a#3 => <x=6:a#3,lτ=∙,dτ=∙>
            }
          )
        , { <x=1:v,lτ=∙,dτ=∙> => {4}
          , <x=2:w,lτ=∙,dτ=∙> => {6}
          , <x=6:a#3,lτ=∙,dτ=∙> =>
              {<<x=1:v,lτ=∙,dτ=∙>,<x=2:w,lτ=∙,dτ=∙>>}
          }
        )
      )
    }
