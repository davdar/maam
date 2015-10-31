## Building and Running

I recommend building with a cabal sandbox. To initialize a cabal sandbox (that
will live in the current directory) and install needed dependencies, run:

    make sandbox

I have not included dependency bounds in my cabal file. Should you have trouble
finding appropriate bounds, here are the versions of ghc and cabal packages
that I am using.

    base=4.8.1.0
    containers=0.5.6.2
    template-haskell=2.10.0.0
    text=1.2.1.3
    vector=0.11.0.0

## Running

To run the project, displaying three different sets of analysis results for a
small example, run:

    cabal run

Example output is included at the end of this README.

## Source Code

All code is in `src/`.

DISCLAIMERS:

- The analyses implemented in Lang.LamIf are not optimized for efficiency but
  their performance is reasonable. However, the pretty printing of results can
  be very expensive due to a naive pretty printing algorithm that I'm using.
- The prelude replacement that I'm using is non-standard, and also uses lots of
  unicode. I plan on writting an ASCII compatibility layer at some point.

### FP

`FP` is a core functional programming library which replaces the standard
Prelude. `FP` includes more batteries for things like functors, monads, monad
transformers, lenses, pretty printing, parsing, deriving, and more. On the
downside, it is non-idiomatic at parts and isn't as mature (i.e. debugged and
stable).

### MAAM

`MAAM` is a semantics-independent library for building abstract interpreters,
while also making it easy to change the path and flow sensitivity of the
interpreter.

`MAAM` only contains types and definitions which are _specific to analysis in
general_. Because the monad transformers that capture path and flow sensitivity
are fully general purpose, they are defined in `FP.Prelude.Monads` and
`FP.Prelude.Effects`, not here. The same goes for lattice structures, which are
mostly all defined in `FP.Prelude.Lattice`. If I were to port `MAAM` to use
the standard Prelude, I would need to rip out maybe 50% of `FP.Prelude` to be
packaged alongside it.

The only code that ends up being specific to analysis is the mapping from
monadic actions to state space transition systems, which is defined in
`MAAM.GaloisTransformer`.

### LamIf

`Lang.LamIf` implements the following for a small applied lambda calculus with
booleans and if-statements:

- Syntax syntax (`Lang.LamIf.Syntax`)
- Parsing (`Lang.LamIf.Parser`)
- Syntax annotations (`Lang.LamIf.Stamp`)
- Semantic values (`Lang.LamIf.Values`)
- Abstract time  (`Lang.LamIf.Time`)
- Monadic semantics (`Lang.LamIf.Semantics`)
- Concrete and abstract value domains (`Lang.LamIf.Domains`)
- Instantiations of language-independent monads from `MAAM` (`Lang.LamIf.Monads`)
- Execution of analyses (`Lang.LamIf.Execution`)
- Example analyses (`Lang.LamIf.Examples`)

## Example Output

If you execute the project it will compute three different abstract
interpretations of a very small program. The variations in path and flow
sensitivity are implemented by rearranging the monad transformers used to
construct the analysis monad.

    program
      0: let x := (1 + 1) - 1 in
      1: let n := (if0 x then x else 1) in
      2: let m := (if0 x then x else 1) in
      3: let r := (if0 x then n + m else 0) in r
    zcfa flow insensitive
    { x ↦ {AInt 0,ANotZero,AAnyInt,ABot}
    , n ↦ {AInt 0,AInt 1,ANotZero,AAnyInt,ABot}
    , m ↦ {AInt 0,AInt 1,ANotZero,AAnyInt,ABot}
    , r ↦ {AInt 0,APos,AZero,ANotZero,AAnyInt,ABot}
    }
    zcfa flow sensitive
    { x ↦ {AInt 0,ANotZero,AAnyInt}
    , n ↦ {AInt 0,AInt 1}
    , m ↦ {AInt 0}
    , r ↦ {APos,AZero}
    }
    zcfa path sensitive
    { x ↦ {AInt 0,ANotZero,AAnyInt}
    , n ↦ {AInt 0,AInt 1}
    , m ↦ {AInt 0}
    , r ↦ {AZero}
    }
