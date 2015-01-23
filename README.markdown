# Building

    make build

# Running

    make run

# Code organization

FP is a core functional programming library which replaces the standard
Prelude. FP fixes some oddities of the Prelude which must remain for backward
compatability, includes more batteries for things like functors, monads, pretty
printing, parsing, deriving, and more. On the downside, it is non-idiomatic at
parts and isn't as mature (i.e. debugged and stable).

MAAM is a semantics-independent package for monadic AAM. AAM-style time (see
Time.hs) and Galois Transformers (see MonadStep.hs) are defined.

Lang.Lam is a simple applied lambda calculus with a parser.

Lang.CPS is a core CPS representation of Lang.Lam with a desugarer and pretty printer.

The demonstration analysis is for Lang.CPS, and is found in:

- Lang.CPS.Val
    - The abstract domain interface and instances for CPS
- Lang.CPS.StateSpace
    - The AAM style state space for CPS
- Lang.CPS.Semantics
    - The monadic semantics for CPS
- Lang.CPS.Monads
    - Instantiations of the semantics-independent monads to analyze CPS
- Lang.CPS.Analyses
    - Choices for each independent axis of analysis

# Coming soon

- More examples and demonstrations of the framework
- More documentation in the README and framework code

# Example Output

If you execute the project it will compute a concrete and abstract
interpretation of a very small simple program.

The output is verbose and contains the entire state space.

The output of `make run` is:

    Source
    let b := -1 0 in
    let id := λ x . x in if >=0? b then id 1 else id 2
    Stamped
    let b := -1 0 in
    let id := λ x . x in if >=0? b then id 1 else id 2
    CPS
    b := -1 0
    id := λ x k#0 . k#0 x
    a#1 := >=0? b
    k#3 := λ x#2 . HALT x#2
    if a#1 then id 1 k#3 else id 2 k#3
    LT=* DT=* V=concrete M=ps G=no C=link LF=* DF=*
    { ( k#3 := λ x#2 . HALT x#2
        if a#1 then id 1 k#3 else id 2 k#3
      , ( []
        , [16,3,0]
        , { b => <x=b,lτ=[],dτ=[0]>
          , id => <x=id,lτ=[],dτ=[3,0]>
          , a#1 => <x=a#1,lτ=[],dτ=[16,3,0]>
          }
        , { <x=b,lτ=[],dτ=[0]> => {-1}
          , <x=id,lτ=[],dτ=[3,0]> => {<λ=4,lτ=[]>}
          , <x=a#1,lτ=[],dτ=[16,3,0]> => {False}
          }
        )
      )
    , ( HALT x#2
      , ( [18]
        , [15,12,6,19,16,3,0]
        , { b => <x=b,lτ=[],dτ=[0]>
          , id => <x=id,lτ=[],dτ=[3,0]>
          , a#1 => <x=a#1,lτ=[],dτ=[16,3,0]>
          , x#2 => <x=x#2,lτ=[4],dτ=[15,12,6,19,16,3,0]>
          }
        , { <x=b,lτ=[],dτ=[0]> => {-1}
          , <x=x,lτ=[],dτ=[12,6,19,16,3,0]> => {2}
          , <x=id,lτ=[],dτ=[3,0]> => {<λ=4,lτ=[]>}
          , <x=k#0,lτ=[],dτ=[12,6,19,16,3,0]> => {<λ=18,lτ=[]>}
          , <x=a#1,lτ=[],dτ=[16,3,0]> => {False}
          , <x=x#2,lτ=[4],dτ=[15,12,6,19,16,3,0]> => {2}
          , <x=k#3,lτ=[],dτ=[19,16,3,0]> => {<λ=18,lτ=[]>}
          }
        )
      )
    , ( a#1 := >=0? b
        k#3 := λ x#2 . HALT x#2
        if a#1 then id 1 k#3 else id 2 k#3
      , ( []
        , [3,0]
        , {b => <x=b,lτ=[],dτ=[0]>,id => <x=id,lτ=[],dτ=[3,0]>}
        , { <x=b,lτ=[],dτ=[0]> => {-1}
          , <x=id,lτ=[],dτ=[3,0]> => {<λ=4,lτ=[]>}
          }
        )
      )
    , ( k#0 x
      , ( [4]
        , [12,6,19,16,3,0]
        , { b => <x=b,lτ=[],dτ=[0]>
          , x => <x=x,lτ=[],dτ=[12,6,19,16,3,0]>
          , k#0 => <x=k#0,lτ=[],dτ=[12,6,19,16,3,0]>
          }
        , { <x=b,lτ=[],dτ=[0]> => {-1}
          , <x=x,lτ=[],dτ=[12,6,19,16,3,0]> => {2}
          , <x=id,lτ=[],dτ=[3,0]> => {<λ=4,lτ=[]>}
          , <x=k#0,lτ=[],dτ=[12,6,19,16,3,0]> => {<λ=18,lτ=[]>}
          , <x=a#1,lτ=[],dτ=[16,3,0]> => {False}
          , <x=k#3,lτ=[],dτ=[19,16,3,0]> => {<λ=18,lτ=[]>}
          }
        )
      )
    , ( id 2 k#3
      , ( []
        , [6,19,16,3,0]
        , { b => <x=b,lτ=[],dτ=[0]>
          , id => <x=id,lτ=[],dτ=[3,0]>
          , a#1 => <x=a#1,lτ=[],dτ=[16,3,0]>
          , k#3 => <x=k#3,lτ=[],dτ=[19,16,3,0]>
          }
        , { <x=b,lτ=[],dτ=[0]> => {-1}
          , <x=id,lτ=[],dτ=[3,0]> => {<λ=4,lτ=[]>}
          , <x=a#1,lτ=[],dτ=[16,3,0]> => {False}
          , <x=k#3,lτ=[],dτ=[19,16,3,0]> => {<λ=18,lτ=[]>}
          }
        )
      )
    , ( if a#1 then id 1 k#3 else id 2 k#3
      , ( []
        , [19,16,3,0]
        , { b => <x=b,lτ=[],dτ=[0]>
          , id => <x=id,lτ=[],dτ=[3,0]>
          , a#1 => <x=a#1,lτ=[],dτ=[16,3,0]>
          , k#3 => <x=k#3,lτ=[],dτ=[19,16,3,0]>
          }
        , { <x=b,lτ=[],dτ=[0]> => {-1}
          , <x=id,lτ=[],dτ=[3,0]> => {<λ=4,lτ=[]>}
          , <x=a#1,lτ=[],dτ=[16,3,0]> => {False}
          , <x=k#3,lτ=[],dτ=[19,16,3,0]> => {<λ=18,lτ=[]>}
          }
        )
      )
    , ( id := λ x k#0 . k#0 x
        a#1 := >=0? b
        k#3 := λ x#2 . HALT x#2
        if a#1 then id 1 k#3 else id 2 k#3
      , ([],[0],{b => <x=b,lτ=[],dτ=[0]>},{<x=b,lτ=[],dτ=[0]> => {-1}})
      )
    , ( b := -1 0
        id := λ x k#0 . k#0 x
        a#1 := >=0? b
        k#3 := λ x#2 . HALT x#2
        if a#1 then id 1 k#3 else id 2 k#3
      , ([],[],{},{})
      )
    }
    LT=0 DT=0 V=abstract M=fi G=no C=link LF=* DF=*
    ( { ( k#3 := λ x#2 . HALT x#2
          if a#1 then id 1 k#3 else id 2 k#3
        , ( ∙
          , ∙
          , { b => <x=b,lτ=∙,dτ=∙>
            , id => <x=id,lτ=∙,dτ=∙>
            , a#1 => <x=a#1,lτ=∙,dτ=∙>
            }
          )
        )
      , ( HALT x#2
        , ( ∙
          , ∙
          , { b => <x=b,lτ=∙,dτ=∙>
            , id => <x=id,lτ=∙,dτ=∙>
            , a#1 => <x=a#1,lτ=∙,dτ=∙>
            , x#2 => <x=x#2,lτ=∙,dτ=∙>
            }
          )
        )
      , ( a#1 := >=0? b
          k#3 := λ x#2 . HALT x#2
          if a#1 then id 1 k#3 else id 2 k#3
        , (∙,∙,{b => <x=b,lτ=∙,dτ=∙>,id => <x=id,lτ=∙,dτ=∙>})
        )
      , ( k#0 x
        , ( ∙
          , ∙
          , { b => <x=b,lτ=∙,dτ=∙>
            , x => <x=x,lτ=∙,dτ=∙>
            , k#0 => <x=k#0,lτ=∙,dτ=∙>
            }
          )
        )
      , ( id 2 k#3
        , ( ∙
          , ∙
          , { b => <x=b,lτ=∙,dτ=∙>
            , id => <x=id,lτ=∙,dτ=∙>
            , a#1 => <x=a#1,lτ=∙,dτ=∙>
            , k#3 => <x=k#3,lτ=∙,dτ=∙>
            }
          )
        )
      , ( id 1 k#3
        , ( ∙
          , ∙
          , { b => <x=b,lτ=∙,dτ=∙>
            , id => <x=id,lτ=∙,dτ=∙>
            , a#1 => <x=a#1,lτ=∙,dτ=∙>
            , k#3 => <x=k#3,lτ=∙,dτ=∙>
            }
          )
        )
      , ( if a#1 then id 1 k#3 else id 2 k#3
        , ( ∙
          , ∙
          , { b => <x=b,lτ=∙,dτ=∙>
            , id => <x=id,lτ=∙,dτ=∙>
            , a#1 => <x=a#1,lτ=∙,dτ=∙>
            , k#3 => <x=k#3,lτ=∙,dτ=∙>
            }
          )
        )
      , ( id := λ x k#0 . k#0 x
          a#1 := >=0? b
          k#3 := λ x#2 . HALT x#2
          if a#1 then id 1 k#3 else id 2 k#3
        , (∙,∙,{b => <x=b,lτ=∙,dτ=∙>})
        )
      , ( b := -1 0
          id := λ x k#0 . k#0 x
          a#1 := >=0? b
          k#3 := λ x#2 . HALT x#2
          if a#1 then id 1 k#3 else id 2 k#3
        , (∙,∙,{})
        )
      }
    , { <x=b,lτ=∙,dτ=∙> => {INT}
      , <x=x,lτ=∙,dτ=∙> => {2,1}
      , <x=id,lτ=∙,dτ=∙> => {<λ=4,lτ=∙>}
      , <x=k#0,lτ=∙,dτ=∙> => {<λ=18,lτ=∙>}
      , <x=a#1,lτ=∙,dτ=∙> => {BOOL}
      , <x=x#2,lτ=∙,dτ=∙> => {2,1}
      , <x=k#3,lτ=∙,dτ=∙> => {<λ=18,lτ=∙>}
      }
    )
