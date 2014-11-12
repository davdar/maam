# Introduction

Traditional practice in the program analysis literature, be it for
points-to, flow, shape analysis or others, is to fix a language and
its abstraction (a computable, sound approximation to the "concrete"
semantics of the language) and investigate its effectiveness [CITE
overload].  These one-off abstractions require effort to design and
prove sound.  Consequently later work has focused on endowing the
abstraction with a number of knobs, levers, and dials to tune
precision and compute efficiently [CITE overload].  These parameters
come in various forms with overloaded meanings such as
object`~\cite{dvanhorn:Milanova2005Parameterized}`{.raw}, context [CITE],
path [CITE], and heap [CITE] sensitivities, or some combination
thereof [CITE].  These efforts develop families of analyses for a
specific language and prove the framework sound.

But even this framework approach suffers from many of the same drawbacks as the
one-off analyzers.  They are language specific, preventing reuse across
languages and thus requiring similar abstraction implementations and soundness
proofs.  This process is difficult and error prone.  It results in a cottage
industry of research papers on varying frameworks for varying languages.  It
prevents fruitful insights and results developed in one paradigm from being
applied to others [PLDI'10].

In this paper, we propose an alternative approach to structuring and
implementing program analysis.  We propose to use concrete interpreters in
monadic style.  As we show, classical program abstractions can be embodied as
language-independent monads.  Moveover, these abstractions can be written as
monad transformers, thereby allowing their composition to achieve new forms of
analysis.  Most significantly, these monad transformers can be proved sound
once and for all.  Abstract interpreters, which take the form of monad
transformer stacks coupled together with a monadic interpreter, inherit the
soundness properties of each element in the stack.  This approach enables reuse
of abstractions across languages and lays the foundation for a modular
metatheory of program analysis.

## Contributions

Our contributions are:

- A compositional meta-theory framework for building correct-by-construction abstract interpreters.
  This framework is built using a restricted class of monad transformers.
- An isolated understanding of flow and path sensitivity for static analysis.
  We understand this spectrum as mere variations in the order of monad transformer composition in our framework.

## Outline

We will demonstrate our framework by example, walking the reader through the design and implementation of an abstract interpreter.
Section [2][Semantics] gives the concrete semantics for a small functional language.
Section [3][Flow Properties in Analysis] gives a brief tutorial on the path and flow sensitivity in the setting of our example language.
Section [4][Analysis Parameters] describes the parameters of our analysis, one of which is the interpreter monad.
Section [5][The Interpreter] shows the full definition of a highly parameterized monadic interpreter.
Section [6][Recovering Analyses] shows how to recover concrete and abstract interpreters.
Section [7][Varying Path and Flow Sensitivity] 
  shows how to manipulate the path and flow sensitivity of the interpreter through varyations in the monad.
Section [8][A Compositional Monadic Framework] demonstrates our compositional meta-theory framework built on monad transformers.
Section [9][Implementation] briefly discusses our implementation of the framework in Haskell.
Section [10][Related Word] discusses related work and Section [11][Conclusion] concludes.

# Semantics

To demonsrate our framework we design an abstract interpreter for `λIF` a simple applied lambda calculus, 
  which is shown in Figure \ref{Syntax}.
`\begin{figure}`{.raw}
`````align````````````````````````````````````````
  i ∈  ℤ
  x ∈  Var
  a ∈  Atom  ::= i | x | [λ](x).e
  ⊕ ∈  IOp   ::= [+] | [-]
  ⊙ ∈  Op    ::= ⊕ | @ 
  e ∈  Exp   ::= a | e ⊙ e | if0(e){e}{e}
``````````````````````````````````````````````````
`\caption{`{.raw}
`λIF`
`} \label{Syntax} \end{figure}`{.raw}
`λIF` extends traditional lambda calculus with integers, addition, subtration and conditionals.
We use the operator `@` as explicit syntax for function application.
This allows for `Op` to be a single syntactic class for all operators and simplifies the presentation.

Before designing an abstract interpreter we first specify a formal semantics for `λIF`.
Our semantics makes allocation explicit and separates values and continuations into separate stores.
Our approach to analysis will be to design a configurable interpreter that is capable of mirroring these semantics.

The state space `Σ` for `λIF` is a standard CESK machine augmented with a separate store for continuation values:
`````align````````````````````````````````````````
 τ ∈  Time    := ℤ
 l ∈  Addr    := Var × Time
 ρ ∈  Env     := Var ⇀ Addr
 σ ∈  Store   := Addr ⇀ Val
 c ∈  Clo     ::= ⟨[λ](x).e,ρ⟩ 
 v ∈  Val     ::= i | c
κl ∈  KAddr   := Time
κσ ∈  KStore  := KAddr ⇀ Frame × KAddr
fr ∈  Frame   ::= ⟨□ ⊙ e⟩ | ⟨v ⊙ □⟩ | ⟨if0(□){e}{e}⟩
 ς ∈  Σ       ::= Exp × Env × Store × KAddr × KStore
``````````````````````````````````````````````````

Atomic expressions are given meaning through the denotation function `A⟦_,_,_⟧`:
`````indent```````````````````````````````````````
A⟦_,_,_⟧ ∈ Env × Store × Atom ⇀ Val
A⟦ρ,σ,i⟧ := i
A⟦ρ,σ,x⟧ := σ(ρ(x))
A⟦ρ,σ,[λ](x).e⟧ := ⟨[λ](x).e,ρ⟩ 
``````````````````````````````````````````````````
Primitive operations are given meaning through the denotation function `δ⟦_,_,_⟧`:
`````indent```````````````````````````````````````
δ⟦_,_,_⟧ ∈ IOp × ℤ × ℤ → ℤ
δ⟦[+],i₁,i₂⟧ := i₁ + i₂
δ⟦[-],i₁,i₂⟧ := i₁ - i₂
``````````````````````````````````````````````````

The semantics of compound expressions are given relationally via the step relation `_~~>_`:
`````indent```````````````````````````````````````
_~~>_ ∈ 𝒫(Σ × Σ)
⟨e₁ ⊙ e₂,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e₁,ρ,σ,τ,κσ',τ+1⟩
  where κσ' := κσ[τ ↦ ⟨□ ⊙ e₂⟩∷κl]
⟨a,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e,ρ,σ,τ,κσ',tick(τ)⟩
  where 
    ⟨□ ⊙ e⟩∷κl' := κσ(κl)
    κσ' := κσ[τ ↦ ⟨A⟦ρ,σ,a⟧ ⊙ □⟩∷κl']
⟨a,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e,ρ'',σ',κl',κσ,τ+1⟩
  where 
    ⟨⟨[λ](x).e,ρ'⟩ @ □⟩∷κl':= κσ(κl)
    σ' := σ[(x,τ) ↦ A⟦ρ,σ,a⟧]
    ρ'' := ρ'[x ↦ (x,τ)]
⟨i₂,ρ,σ,κl,κσ,τ⟩ ~~> ⟨i,ρ,σ,κl',κσ,τ+1⟩
  where 
    ⟨i₁ ⊕ □⟩∷κl' := κσ(κl)
    i := δ⟦⊕,i₁,i₂⟧
⟨i,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e,ρ,σ,κl',κσ,τ+1⟩
  where 
    ⟨if0(□){e₁}{e₂}⟩∷κl' := κσ(κl)
    e := e₁ when i = 0
    e := e₂ when i ≠ 0
``````````````````````````````````````````````````

Our abstract intepreter will support abstract garbage collection [CITE], the concrete analogue of which is just standard garbage collection.
Garbage collection is defined with a reachability function `R` which computes the transitively reachable address from `(ρ,e)` in `σ`:
`````indent```````````````````````````````````````
R[_] ∈ Store → Env × Exp → 𝒫(Addr)
R[σ](ρ,e) := μ(X). 
  R₀(ρ,e) ∪ X ∪ {l' | l' ∈ R-Val(σ(l)) ; l ∈ X}
``````````````````````````````````````````````````
We write `μ(X). f(X)` as the least-fixed-point of a function `f`.
This definition uses two helper functions: `R₀` for computing the initial reachable set adn `R-Val` for computing addresses reachable from addresses.
`````indent```````````````````````````````````````
R₀ ∈ Env × Exp → 𝒫(Addr)
R₀(ρ,e) := {ρ(x) | x ∈ FV(e)}
R-Val ∈ Val → 𝒫(Addr)
R-Val(i) := {}
R-Val(⟨[λ](x).e,ρ⟩) := {ρ(x) | y ∈ FV([λ](x).e)}
``````````````````````````````````````````````````
`FV` is the standard recursive definition for computing free variables of an expression:
`````indent```````````````````````````````````````
FV ∈ Exp → 𝒫(Var)
FV(x) := {x}
FV(i) := {}
FV([λ](x).e) := FV(e) - {x}
FV(e₁ ⊙ e₂) := FV(e₁) ∪ FV(e₂)
FV(if0(e₁){e₂}{e₃}) := FV(e₁) ∪ FV(e₂) ∪ FV(e₃)
``````````````````````````````````````````````````

Analagously, `KR` is the set of transitively reachabel continuation addresses in `κσ`:
`````indent```````````````````````````````````````
KR[_] ∈ KStore → KAddr → 𝒫(KAddr)
KR[κσ](κl) := μ(kθ). κθ₀ ∪ κθ ∪ {π₂(κσ(κl)) | κl ∈ κθ}
``````````````````````````````````````````````````

Our final semantics is given via the step relation `_~~>ᵍᶜ_` which nondeterministically either takes a semantic step or performs garbage collection.
`````indent```````````````````````````````````````
_~~>ᵍᶜ_ ∈ 𝒫(Σ × Σ)
ς ~~>ᵍᶜ ς' 
  where ς ~~> ς'
⟨e,ρ,σ,κl,κσ,τ⟩ ~~>ᵍᶜ ⟨e,ρ,σ',κl,κσ,τ⟩
  where 
    σ' := {l ↦ σ(l) | l ∈ R[σ](ρ,e)}
    κσ' := {κl ↦ κσ(κl) | κl ∈ KR[κσ](κl)}
``````````````````````````````````````````````````

An execution of the semantics is states as the least-fixed-point of a collecting semantics:
`````indent```````````````````````````````````````
μ(X).{ς₀} ∪ X ∪ { ς' | ς ~~>ᵍᶜ ς' ; ς ∈ X }
``````````````````````````````````````````````````
The analyses we present in this paper will be proven correct by establishing a Galois connection with this concrete collecting semantics.

# Flow Properties in Analysis

One key property of a static analysis is the way it tracks _flow_.
The term "flow" is heavily overloaded in static analysis, for example CFA is literally the abbreviation of "control flow analysis".
We wish to draw a sharper distinction on what is a flow property.
First we identify three different types of flow in analysis:

1. Path sensitive and flow sensitive
2. Path insensitive and flow sensitive
3. Path insensitive and flow insensitive

Consider a simple if-statement in our example language `λIF` (extended with let-bindings) where an analysis cannot determine the value of `N`:
`````indent```````````````````````````````````````
1: let x := if0(N){1}{-1};
2: let y := if0(N){1}{-1};
3: e
``````````````````````````````````````````````````

\paragraph{Path Sensitive Flow Sensitive}
A path and flow sensitive analysis will track both control and data flow precisely.
At program point 2 the analysis considers separate worlds:
`````align````````````````````````````````````````
{N=0,,  x=   1}
{N≠0,,  x=-  1}
``````````````````````````````````````````````````
At program point 3 the analysis remains precise, resulting in environments:
`````align````````````````````````````````````````
{N=0,,  x=   1,,  y=   1} 
{N≠0,,  x=-  1,,  y=-  1}
``````````````````````````````````````````````````

\paragraph{Path Insensitive Flow Sensitive}
A path insensitive flow sensitive analysis will track control flow precisely but merge the heap after control flow branches.
At program point 2 the analysis considers separate worlds:
`````align````````````````````````````````````````
{N=ANY,,  x=   1}
{N=ANY,,  x=-  1}
``````````````````````````````````````````````````
At program point 3 the analysis is forced to again consider both branches, resulting in environments:
`````align````````````````````````````````````````
{N=ANY,,  x=   1,,  y=   1}
{N=ANY,,  x=   1,,  y=-  1}
{N=ANY,,  x=-  1,,  y=   1}
{N=ANY,,  x=-  1,,  y=-  1}
``````````````````````````````````````````````````

\paragraph{Path Insensitive Flow Insensitive}
A path insensitive flow insensitive analysis will compute a single global set of facts that must be true at all points of execution.
At program points 2 and 3 the analysis considers a single world with environment:
`````align````````````````````````````````````````
{N=ANY,, x={-1, 1}}
``````````````````````````````````````````````````
and 
`````align````````````````````````````````````````
{N=ANY,, x={-1, 1},, y={-1, 1}}
``````````````````````````````````````````````````
respectively.

In our framework we capture both path and flow sensitivity as orthogonal parameters to our interpreter.
Path sensitivity will arise from the order of monad transformers used to construct the analysis.
Flow sensitivity will arise from the Galois connection used to map interpreters to state space transition systems.
For brevity, and lack of better terms, we will abbreviate these analyses as "path sensitive", "flow sensitive" and "flow insensitive".
This is only ambiguous for "flow sensitive", as path sensitivity implies flow sensitivity, and flow insensitivity implies path insensitivity.

# Analysis Parameters

Before writing an abstract interpreter we first design its parameters.
The interpreter will be designed such that variations in these paramaters recover the concrete and a family of abstract interpretrs.
To do this we extend the ideas developed in AAM[CITE] with a new parameter for flow-sensitivity.
When finished, we will be able to recover a concrete interpreter--which respects the concrete semantics--and a family of abstract interpreters.

First we describe the parameters to the interpreter.
Then we conclude the section with an implementation which is generic to these parameters.

There will be three parameters to our abstract interpreter, one of which is novel in this work:

1. The monad, novel in this work.
   This is the execution engine of the interpreter and captures the flow-sensitivity of the analysis.
2. The abstract domain.
   For our language is merely an abstraction for integers.
3. The abstraction for time. 
   Abstract time captures the call-site sensitivity of the analysis, as introduced by [CITE].

We place each of these parameters behind an abstract interface and leave their implementations opaque for the generic monadic interpreter.
We will give each of these parameters reasoning principles as we introduce them.
These reasoning principles allow us to reason about the correctness of the generic interpreter independent of a particular instantiation.
The goal is to factor as much of the proof-effort into what we can say about the generic interpreter.
An instantiation of the interpreter need only justify that each parameter meets their local interface.

## The Monad

The monad for the interpreter is capturing the _effects_ of interpretation.
There are two effects we wish to model in the interpreter, state and nondeterminism.
The state effect will mediate how the interpreter interacts with state cells in the state space, like `Env` and `Store`.
The nondeterminism effect will mediate the branching of the execution from the interpreter.
Our result is that path and flow sensitivities can be recovered by altering how these effects interact in the monad.

We briefly review monad, state and nondeterminism operators and thier laws.

### Monad Properties
To be a monad, a type operator `M` must support the `bind` operation:
`````indent```````````````````````````````````````
bind : ∀ α β, M(α) → (α → M(β)) → M(β)
``````````````````````````````````````````````````
as well as a unit for `bind` called `return`:
`````indent```````````````````````````````````````
return : ∀ α, α → M(α)
``````````````````````````````````````````````````

We use the monad laws to reason about our implementation in the absence of a particular implementatino of `bind` and `return`:
`````indent```````````````````````````````````````
unit₁ : bind(return(a))(k) = k(a)
unit₂ : bind(m)(return) = m
assoc : bind(bind(m)(k₁))(k₂) = bind(m)(λ(a).bind(k₁(a))(k₂))
``````````````````````````````````````````````````
`bind` and `return` mean something different for each monadic effect class.
For state, `bind` is a sequencer of state and `return` is the "no change in state" effect.
For nondeterminism, `bind` implements a merging of multiple branches and `return` is the singleton branch.
These operators capture the essence of the combination of explicit state-passing and set comprehension in the interpreter.
Our interpreter will use these operators and avoid referencing an explicit configuration `ς` or explicit collections of results.

As is traditional with monadic programming, we use `do` and semicolon notation as syntactic sugar for `bind`.
For example:
`````indent```````````````````````````````````````
do 
  a ← m 
  k(a)
``````````````````````````````````````````````````
and
`````indent```````````````````````````````````````
a ← m ; k(a)
``````````````````````````````````````````````````
are both just sugar for
`````indent``````````````````````````````````````` 
bind(m)(k)
``````````````````````````````````````````````````

### Monad State Properties
Interacting with a state component like `Env` is achieved through `get-Env` and `put-Env` effects:
`````indent``````````````````````````````````````` 
get-Env : M(Env)
put-Env : Env → M(1)
``````````````````````````````````````````````````

We use the state monad laws to reason about state effects:
`````indent``````````````````````````````````````` 
put-put : put(s₁) ; put(s₂) = put(s₂)
put-get : put(s) ; get = return(s)
get-put : s ← get ; put(s) = return(1)
get-get : s₁ ← get ; s₂ ← get ; k(s₁,s₂) = s ← get ; k(s,s)
``````````````````````````````````````````````````
The effects for `get-Store`, `get-KAddr` and `get-KStore` are identical.

### Monad Nondeterminism Properties

Nondeterminism is achieved through operators `mzero` and `⟨+⟩`:
`````indent``````````````````````````````````````` 
mzero : ∀ α, M(α)
_⟨+⟩_ : ∀ α, M(α) × M(α) → M(α)
`````````````````````````````````````````````````` 

We use the nondeterminism laws to reason about nondeterminism effects:
`````indent```````````````````````````````````````
⊥-zero₁ : bind(mzero)(k) = mzero
⊥-zero₂ : bind(m)(λ(a).mzero) = mzero
⊥-unit₁ : mzero ⟨+⟩ m = m
⊥-unit₂ : m ⟨+⟩ mzero = m 
+-assoc : m₁ ⟨+⟩ (m₂ ⟨+⟩ m₃) = (m₁ ⟨+⟩ m₂) ⟨+⟩ m₃
+-comm : m₁ ⟨+⟩ m₂ = m₂ ⟨+⟩ m₁
+-dist : bind(m₁ ⟨+⟩ m₂)(k) = bind(m₁)(k) ⟨+⟩ bind(m₂)(k)
``````````````````````````````````````````````````

## The Abstract Domain

The abstract domain is encapsulated by the `Val` type in the semantics.
To parameterize over it, we make `Val` opaque but require it support various operations.
There is a constraint on `Val` its-self: it must be a join-semilattice with `⊥` and `⊔` respecting the usual laws.
We require `Val` to be a join-semilattice so it can be merged in the `Store`.

The interface for integers consists of introduction and elimiation rules:
`````indent```````````````````````````````````````
int-I : ℤ → Val
int-if0-E : Val → 𝒫(Bool)
``````````````````````````````````````````````````

The laws for this interface are designed to induce a Galois connection between `ℤ` and `Val`:
`````indent```````````````````````````````````````
{true}  ⊑ int-if0-E(int-I(i))     if i = 0
{false} ⊑ int-if0-E(int-I(i))     if i ≠ 0
v ⊒ ⨆⸤b ∈ int-if0-E(v)⸥ θ(b)
  where 
    θ(true)  = int-I(0)
    θ(false) = ⨆⸤i ∈ ℤ | i ≠ 0⸥ int-I(i)
``````````````````````````````````````````````````

Additionally we must abstract closures:
`````indent```````````````````````````````````````
clo-I : Clo → Val
clo-E : Val → 𝒫(Clo)
``````````````````````````````````````````````````
which follow similar laws:
`````indent```````````````````````````````````````
{c} ⊑ clo-E(cloI(c))
v ⊑ ⨆⸤c ∈ clo-E(v)⸥ clo-I(c)
``````````````````````````````````````````````````

The denotation for primitive operations `δ` must also be opaque:
`````indent```````````````````````````````````````
δ⟦_,_,_⟧ : IOp × Val × Val → Val
``````````````````````````````````````````````````

We can also give soundness laws for `δ` using int-I and int-if0-E:
`````indent```````````````````````````````````````
int-I(i₁ + i₂) ⊑ δ⟦[+],int-I(i₁),int-I(i₂)⟧
int-I(i₁ - i₂) ⊑ δ⟦[-],int-I(i₁),int-I(i₂)⟧ 
``````````````````````````````````````````````````

Supporting additional primitive types like booleans, lists, or arbitrary inductive datatypes is analagous.
Introduction functions inject the type into `Val`.
Elimination functions project a finite set of discrete observations.
Introduction and elimination operators must follow a Galois connection discipline.

Of note is our restraint from allowing operations over `Val` to have monadic effects.
We set things up specifically in this way so that `Val` and the monad `M` can be varied independent of each other.

## Abstract Time 

The interface for abstract time is familiar from the AAM literature:
`````indent```````````````````````````````````````
tick : Exp × KAddr × Time → Time
``````````````````````````````````````````````````

In traditional AAM, `tick` is defined to have access to all of `Σ`.
This comes from the generality of the framework--to account for all possibile `tick` functions.
We only discuss instantiating `Addr` to support k-CFA, so we specialize the `Σ` parameter to `Exp × KAddr`.
Also in AAM is the opaque function `alloc : Var × Time → Addr`.
Because we will only ever use the identity function for `alloc`, we omit its abstraction and instantiation in our development.

Remarkably, we need not state laws for `tick`.
Our interpreter will always merge values which reside at the same address to achieve soundness.
Therefore, any supplied implementations of `tick` is valid.

# The Interpreter

We now present a generic monadic interpreter for `λIF` paramaterized over `M`, `Val` and `Time`.

In moving our semantics to an analysis, we will need to reuse addresses in the state space.
This induces `Store` and `KStore` to join when binding new values to in-use addresses.
The state space for our interpreter will therefore use the following domain for `Store` and `KStore`:
`````indent```````````````````````````````````````
σ  ∈ Store  : Addr → Val
κσ ∈ KStore : KAddr → 𝒫(Frame × KAddr)
``````````````````````````````````````````````````

We have already established a join-semilattice structure for `Val`.
Developing a custom join-semilattice for continuations is possible, and is the key component of recent developments in pushdown abstraction.
For this presentation we use `𝒫(Frame × KAddr)` as an abstraction for continuations for simplicity.

Before defining the interpreter we define some helper functions which interact with the underlying monad `M`.

First, values in `𝒫(α)` can be lifted to monadic values `M(α)` using `return` and `mzero`, which we name `↑ₚ`:
`````indent```````````````````````````````````````
↑ₚ : ∀ α, 𝒫(α) → M(α)
↑ₚ({a₁ .. aₙ}) := return(a₁) ⟨+⟩ .. ⟨+⟩ return(aₙ)
``````````````````````````````````````````````````

Allocating addresses and updating time can be implemented using monadic state effects:
`````indent```````````````````````````````````````
allocM : Var → M(Addr)
allocM(x) := do
  τ ← get-Time
  return(x,τ)
κallocM : M(KAddr)
κallocM := do
  τ ← get-Time
  return(τ)
tickM : Exp → M(1)
tickM(e) = do
  τ ← get-Time
  κl ← get-KAddr
  put-Time(tick(e,κl,τ))
``````````````````````````````````````````````````

Finally, we introduce helper functions for manipulating stack frames:
`````indent```````````````````````````````````````
push : Frame → M(1)
push(fr) := do
  κl ← get-KAddr
  κσ ← get-KStore
  κl' ← κallocM
  put-KStore(κσ ⊔ [κl' ↦ {fr∷κl}])
  put-KAddr(κl')
pop : M(Frame)
pop := do
  κl ← get-KAddr
  κσ ← get-KStore
  fr∷κl' ← ↑ₚ(κσ(κl))
  put-KAddr(κl')
  return(fr)
``````````````````````````````````````````````````

To implement our interpreter we define a denotation function for atomic expressions and a step function for compound expressions.
The denotation for atomic expressions is written as a monadic computation from atomic expresssions to values.
`````indent```````````````````````````````````````
A⟦_⟧ ∈ Atom → M(Val)
A⟦i⟧ := return(int-I(i))
A⟦x⟧ := do
  ρ ← get-Env
  σ ← get-Store
  l ← ↑ₚ(ρ(x))
  return(σ(x))
A⟦[λ](x).e⟧ := do
  ρ ← get-Env
  return(clo-I(⟨[λ](x).e,ρ⟩))
``````````````````````````````````````````````````
The step function is written as a small-step monadic computation from expressions to the next expression to evaluate, and is shown in 
Figure \ref{Interpreter}.
Interpreting compound expressions is simple, the interpreter pushes a stack frame and continues with the first operand.
Interpreting atomic expressions must pop and inspect the stack and perform the denotation of the operation:
`\begin{figure}`{.raw}
`````indent```````````````````````````````````````
step : Exp → M(Exp)
step(e₁ ⊙ e₂) := do
  tickM(e₁ ⊙ e₂)
  push(⟨□ ⊙ e₂⟩)
  return(e₁)
step(a) := do
  tickM(a)
  fr ← pop
  v ← A⟦a⟧
  case fr of
    ⟨□ ⊙ e⟩ → do
      push(⟨v ⊙ □⟩)
      return(e)
    ⟨v' @ □⟩ → do
      ⟨[λ](x).e,ρ'⟩ ← ↑ₚ(clo-E(v'))
      l ← alloc(x)
      σ ← get-Store
      put-Env(ρ'[x↦l])
      put-Store(σ[l↦v])
      return(e)
    ⟨v' ⊕ □⟩ → do
      return(δ(⊕,v',v))
    ⟨if0(□){e₁}{e₂}⟩ → do
      b ← ↑ₚ(int-if0-E(v))
      if(b) then return(e₁) else return(e₂)
``````````````````````````````````````````````````
\caption{The Generic Monadic Interpreter}
\label{Interpreter}
`\end{figure}`{.raw}

We can also implement abstract garbage collection in a fully general away against the monadic effect interface:
`````indent```````````````````````````````````````
gc : Exp → M(1)
gc(e) := do
  ρ ← get-Env
  σ ← get-Store
  κσ ← get-KStore
  l*₀ ← R₀(ρ,e)
  κl₀ ← get-KAddr
  let l*' := μ(θ). l*₀ ∪ θ ∪ R[σ](θ)
  let κl*' := μ(κθ). {κl₀} ∪ κθ ∪ KR[κσ](κθ)
  put-Store({l ↦ σ(l) | l ∈ l*'})
  put-KStore({κl ↦ κσ(κl) | κl ∈ κl*'})
``````````````````````````````````````````````````
where `R₀` is defined as before and `R`, `KR` and `R-Clo` are defined:
`````indent```````````````````````````````````````
R : Store → 𝒫(Addr) → 𝒫(Addr)
R[σ](θ) := { l' | l' ∈ R-Clo(c) ; c ∈ clo-E(v) ; v ∈ σ(l) ; l ∈ θ }
R-Clo : Clo → 𝒫(Addr)
R-Clo(⟨[λ](x).e,ρ⟩) := { ρ(x) | x ∈ FV([λ](x).e) }
KR : KStore → 𝒫(KAddr) → 𝒫(KAddr)
KR[σ](κθ) := { π₂(fr) | fr ∈ κσ(κl) ; κl ∈ θ }
``````````````````````````````````````````````````

To execute the interpreter we must introduce one more parameter.
In the concrete semantics, execution takes the form of a least-fixed-point computation over the collecting semantics
This in general requires a join-semilattice structure for some `Σ` and a transition function `Σ → Σ`.
We bridge this gap between monadic interpreters and transition functions with an extra constraint on the monad `M`.
We require that monadic actions `α → M(β)` form a Galois connection with a transition system `Σ → Σ`.

There is one last parameter to our development: a connection between our monadic interpreter and a state space transition system.
We state this connection formally as a Galois connection `(Σ → Σ)α⇄γ(Exp → M(Exp))`.
This Galois connection serves two purposes.
First, it allows us to implement the analysis by converting our interpreter to the transition system `Σ → Σ` through `γ`.
Second, this Galois connection serves to _transport other Galois connections_.
For example, given concrete and abstract versions of `Val`, we carry `CVal α⇄γ AVal` through the Galois connection to establish `CΣ α⇄γ AΣ`.

A collecting-semantics execution of our interpreter is defined as the least-fixed-point of `step` transported through the Galois connection.
`````indent```````````````````````````````````````
μ(X). ς₀ ⊔ X ⊔ γ(step)(X)
``````````````````````````````````````````````````
where `ς₀` is the injection of the initial program `e₀` into `Σ `.

# Recovering Analyses

To recover concrete and abstract interpreters we need only instantiate our generic monadic interpreter with concrete and abstract components.

## Recovering a Concrete Interpreter

For the concrete value space we instantiate `Val` to `CVal`, a powerset of values:
`````indent```````````````````````````````````````
v ∈ CVal := 𝒫(Clo + ℤ)
``````````````````````````````````````````````````

The concrete value space `CVal` has straightforward introduction and elimination rules:
`````indent```````````````````````````````````````
int-I : ℤ → CVal
int-I(i) := {i}
int-if0-E : CVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | i ∈ v ∧ i ≠ 0 }
``````````````````````````````````````````````````
and the concrete `δ` you would expect:
`````indent```````````````````````````````````````
δ⟦_,_,_⟧ : IOp × CVal × CVal → CVal
δ⟦[+],v₁,v₂⟧ := { i₁ + i₂ | i₁ ∈ v₁ ; i₂ ∈ v₂ }
δ⟦[-],v₁,v₂⟧ := { i₁ - i₂ | i₁ ∈ v₁ ; i₂ ∈ v₂ }
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`CVal` satisfies the abstract domain laws from section [X][The Abstract Domain].
`\end{proposition}`{.raw}

Concrete time `CTime` captures program contours as a product of `Exp` and `KAddr`:
`````indent```````````````````````````````````````
τ ∈ CTime := (Exp × KAddr)⋆
``````````````````````````````````````````````````
and `tick` is just a cons operator:
`````indent```````````````````````````````````````
tick : Exp × KAddr × CTime → CTime
tick (e,κl,τ) := (e,κl)∷τ
``````````````````````````````````````````````````

For the concrete monad we instantiate `M` to a path-sensitive `CM` which contains a powerset of concrete state space components.
`````indent```````````````````````````````````````
ψ ∈ Ψ := Env × CStore × KAddr × KStore × CTime
m ∈ CM(α) := Ψ → 𝒫(α × Ψ)
``````````````````````````````````````````````````

Monadic operators `bind` and `return` encapsulate both state-passing and set-flattening:
`````indent```````````````````````````````````````
bind : ∀ α, CM(α) → (α → CM(β)) → CM(β)
bind(m)(f)(ψ) := 
  {(y,ψ'') | (y,ψ'') ∈ f(a)(ψ') ; (a,ψ') ∈ m(ψ)}
return : ∀ α, α → CM(α)
return(a)(ψ) := {(a,ψ)}
``````````````````````````````````````````````````

State effects merely return singleton sets:
`````indent```````````````````````````````````````
get-Env : CM(Env)
get-Env(⟨ρ,σ,κ,τ⟩) := {(ρ,⟨ρ,σ,κ,τ⟩)}
put-Env : Env → 𝒫(1)
put-Env(ρ')(⟨ρ,σ,κ,τ⟩) := {(1,⟨ρ',σ,κ,τ⟩)}
``````````````````````````````````````````````````

Nondeterminism effects are implemented with set union:
`````indent```````````````````````````````````````
mzero : ∀ α, CM(α)
mzero(ψ) := {}
_⟨+⟩_ : ∀ α, CM(α) × CM(α) → CM(α)
(m₁ ⟨+⟩ m₂)(ψ) := m₁(ψ) ∪ m₂(ψ)
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`CM` satisfies monad, state, and nondeterminism laws.
`\end{proposition}`{.raw}

Finally, we must establish a Galois connection between `Exp → CM(Exp)` and `CΣ → CΣ` for some choice of `CΣ`.
For the path sensitive monad `CM` instantiate with `CVal` and `CTime`, , `CΣ` is defined:
`````indent```````````````````````````````````````
CΣ := 𝒫(Exp × Ψ)
``````````````````````````````````````````````````

The Galois connection between `CM` and `CΣ` is straightforward:
`````indent```````````````````````````````````````
γ : (Exp → CM(Exp)) → (CΣ → CΣ)
γ(f)(eψ*) := {(e,ψ') | (e,ψ') ∈ f(e)(ψ) ; (e,ψ) ∈ eψ*}
α : (CΣ → CΣ) → (Exp → CM(Exp))
α(f)(e)(ψ) := f({(e,ψ)})
``````````````````````````````````````````````````

The injection `ς⸢CM⸣₀` for a program `e₀` is:
`````indent```````````````````````````````````````
ς₀ := {⟨e,⊥,⊥,∙,⊥,∙⟩}
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`γ` and `α` form an isomorphism.
`\end{proposition}`{.raw}

`\begin{corollary}`{.raw}
`γ` and `α` form a Galois connection.
``\end{corollary}`{.raw}`{.raw}

## Recovering an Abstract Interpreter

We pick a simple abstraction for integers, `{[-],0,[+]}`, although our technique scales seamlessly to other domains.
`````indent```````````````````````````````````````
AVal := 𝒫(Clo + {[-],0,[+]})
``````````````````````````````````````````````````

Introduction and elimination functions for `AVal` are defined:
`````indent```````````````````````````````````````
int-I : ℤ → AVal
int-I(i) := [-] if i < 0
int-I(i) := 0   if i = 0
int-I(i) := [+] if i > 0
int-if0-E : AVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | [-] ∈ v ∨ [+] ∈ v }
``````````````````````````````````````````````````
Introduction and elmination for `Clo` is identical to the concrete domain.

The abstract `δ` operator is defined:
`````indent```````````````````````````````````````
δ : IOp × AVal × AVal → AVal 
δ(+,v₁,v₂) := 
    { i     | 0 ∈ v₁ ∧ i ∈ v₂ }
  ∪ { i     | i ∈ v₁ ∧ 0 ∈ v₂ }
  ∪ { [+]     | [+] ∈ v₁ ∧ [+] ∈ v₂ } 
  ∪ { [-]     | [-] ∈ v₁ ∧ [-] ∈ v₂ } 
  ∪ { [-],0,[+] | [+] ∈ v₁ ∧ [-] ∈ v₂ }
  ∪ { [-],0,[+] | [-] ∈ v₁ ∧ [+] ∈ v₂ }
``````````````````````````````````````````````````
The definition for `δ(-,v₁,v₂)` is analagous.

`\begin{proposition}`{.raw}
`AVal` satisfies the abstract domain laws from section [X][The Abstract Domain].
`\end{proposition}`{.raw}

`\begin{proposition}`{.raw}
`CVal α⇄γ AVal` and their operations `int-I`, `int-if0-E` and `δ` are ordered `⊑` respectively through the Galois connection.
`\end{proposition}`{.raw}

Next we abstract `Time` to `ATime` as the finite domain of k-truncated lists of execution contexts:
`````indent```````````````````````````````````````
ATime := (Exp × KAddr)⋆ₖ
``````````````````````````````````````````````````
The `tick` operator becomes cons followed by k-truncation:
`````indent```````````````````````````````````````
tick : Exp × KAddr × ATime → ATime
tick(e,κl,τ) = ⌊(e,κl)∷τ⌋ₖ
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`CTime α⇄γ ATime` and `tick` is ordered `⊑` through the Galois connection.
`\end{proposition}`{.raw}

The monad `AM` need not change in implementation from `CM`; they are identical up to choices for `AStore` (which maps to `AVal`) and `ATime`.
`````indent```````````````````````````````````````
ψ ∈ Ψ := Env × AStore × KAddr × KStore × ATime
``````````````````````````````````````````````````

The resulting state space `AΣ` is finite, and its least-fixed-point iteration will give a sound and computable analysis.

# Varying Path and Flow Sensitivity

We are able to recover a flow-insensitivity in the analysis through a new definition for `AM`: `AMᶠⁱ`.
To do this we pull `AStore` out of the powerset, exploiting its join-semilattice structure:
`````indent```````````````````````````````````````
Ψ := Env × KAddr × KStore × ATime
AMᶠⁱ(α) := Ψ × AStore → 𝒫(α × Ψ) × AStore
``````````````````````````````````````````````````

The monad operator `bind` performs the store merging needed to capture a flow-insensitive analysis.
`````indent```````````````````````````````````````
bind : ∀ α β, AMᶠⁱ(α) → (α → AMᶠⁱ(β)) → AMᶠⁱ(β)
bind(m)(f)(ψ,σ) := ({bs₁₁ .. bsₙ₁ .. bsₙₘ},σ₁ ⊔ .. ⊔ σₙ)
  where
    ({(a₁,ψ₁) .. (aₙ,ψₙ)},σ') := m(ψ,σ)
    ({bψᵢ₁ .. bψᵢₘ},σᵢ) := f(aᵢ)(ψᵢ,σ')
``````````````````````````````````````````````````
The unit for `bind` returns one nondeterminism branch and a single store:
`````indent```````````````````````````````````````
return : ∀ α, α → AM(α)
return(a)(ψ,σ) := ({a,ψ},σ)
``````````````````````````````````````````````````

State effects `get-Env` and `put-Env` are also straightforward, returning one branch of nondeterminism:
`````indent```````````````````````````````````````
get-Env : AMᶠⁱ(Env)
get-Env(⟨ρ,κ,τ⟩,σ) := ({(ρ,⟨ρ,κ,τ⟩)},σ)
put-Env : Env → AMᶠⁱ(1)
put-Env(ρ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ',κ,τ⟩)},σ)
``````````````````````````````````````````````````

State effects `get-Store` and `put-Store` are analagous to `get-Env` and `put-Env`:
`````indent```````````````````````````````````````
get-Store : AMᶠⁱ(Env)
get-Store(⟨ρ,κ,τ⟩,σ) := ({(σ,⟨ρ,κ,τ⟩},σ)
put-Store : AStore → AMᶠⁱ(1)
put-Store(σ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ,κ,τ⟩)},σ')
``````````````````````````````````````````````````

Nondeterminism operations will union the powerset and join the store pairwise:
`````indent```````````````````````````````````````
mzero : ∀ α, M(α)
mzero(ψ,σ) := ({}, ⊥)
_⟨+⟩_ : ∀ α, M(α) × M(α) → M α 
(m₁ ⟨+⟩ m₂)(ψ,σ) := (aψ*₁ ∪ aψ*₂,σ₁ ⊔ σ₂)
  where (aψ*ᵢ,σᵢ) := mᵢ(ψ,σ)
``````````````````````````````````````````````````

Finally, the Galois connection relating `AMᶠⁱ` to a state space transition over `AΣᶠⁱ` must also compute set unions and store joins:
`````indent```````````````````````````````````````
AΣᶠⁱ := 𝒫(Exp × Ψ) × AStore
γ : (Exp → AMᶠⁱ(Exp)) → (Σᶠⁱ → Σᶠⁱ)
γ(f)(eψ*,σ) := ({eψ₁₁ .. eψₙ₁ .. eψₙₘ}, σ₁ ⊔ .. ⊔ σₙ)
  where 
    {(e₁,ψ₁) .. (eₙ,ψₙ)} := eψ*
    ({eψᵢ₁ .. eψᵢₘ},σᵢ) := f(eᵢ)(ψᵢ,σ)
α  : (Σᶠⁱ → Σᶠⁱ) → (Exp → AMᶠⁱ(Exp))
α(f)(e)(ψ,σ) := f({(e,ψ)},σ)
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`γ` and `α` form an isomorphism.
`\end{proposition}`{.raw}

`\begin{corollary}`{.raw}
`γ` and `α` form a Galois connection.
`\end{corollary}`{.raw}

`\begin{proposition}`{.raw}
There exists Galois connection `CΣ α₁⇄γ₁ AΣ α₂⇄γ₂ AΣᶠⁱ` and `α₁ ∘ Cγ(step) ∘ γ₁ ⊑ Aγ(step) ⊑ γ₂ ∘ Aγᶠⁱ(step) ∘ α₂`.
`\end{proposition}`{.raw}

The first Galois connection `CΣ α₁⇄γ₁ AΣ` is justified by the Galois connections between `CVal α⇄γ AVal` and `CTime α⇄γ ATime`.
The second Galois connection `AΣ α₂⇄γ₂ AΣᶠⁱ` is justified by first calculating the Galois connection between monads `AM` and `CM`,
  and then transporting it through their respective Galois connections to `AΣ` and `AΣᶠⁱ`.
These proofs are tedious calculations over the definitions which we do not repeat here.
However, we will recover these proof in a later section through our compositional framework which greatly reduces the proof burden.

We note that the implementation for our interpreter and abstract garbage collector remain the same.
They both scale seamlessly to flow-sensitive and flow-insensitive variants when instantiated with the appropriate monad.

# A Compositional Monadic Framework

In our development thus far, any modification to the interpreter requires redesigning the monad `AM` and constructing new proofs.
We want to avoid reconstructing complicated monads for our interpreters, especially as languages and analyses grow and change.
Even more, we want to avoid reconstructing complicated _proofs_ that such changes will necessarily alter.
Toward this goal we introduce a compositional framework for constructing monads which are correct-by-construction.
To do this we build upon the well-known structure of monad transformer.

There are two types of monadic effects used in our monadic interprer: state and nondeterminism.
Each of these effects have corresponding monad transformers.
Monad transformers for state effects were described by Jones in [CITE].
Our definition of a monad transformer for nondeterminism is novel in this work.

## State Monad Transformer

Briefly we review the state monad transformer, `Sₜ[s]`:
`````indent```````````````````````````````````````
Sₜ[_] : (Type → Type) → (Type → Type)
Sₜ[s](m)(α) := s → m(α × s)
``````````````````````````````````````````````````

For monad transformers, `bind` and `return` will use monad operations from the underlying `m`, which we notate `bindₘ` and `returnₘ`.
When writing in do-notation, we write `doₘ` and `←ₘ` for clarity.

The state monad transformer can transport monadic operations from `m` to `Sₜ[s](m)`:
`````indent```````````````````````````````````````
bind : ∀ α β, Sₜ[s](m)(α) → (α → Sₜ[s](m)(β)) → Sₜ[s](m)(β)
bind(m)(f)(s) := doₘ
  (x,s') ←ₘ m(s)
  f(x)(s')
return : ∀ α m, α → Sₜ[s](m)(α)
return(x)(s) := returnₘ(x,s)
``````````````````````````````````````````````````

The state monad transformer can also transport nondeterminism effects from `m` to `Sₜ[s](m)`:
`````indent```````````````````````````````````````
mzero : ∀ α, Sₜ[s](m)(α)
mzero(s) := mzeroₘ 
_⟨+⟩_ : ∀ α, Sₜ[s](m)(α) x Sₜ[s](m)(α) → Sₜ[s](m)(α)
(m₁ ⟨+⟩ m₂)(s) := m₁(s) ⟨+⟩ₘ m₂(s) 
``````````````````````````````````````````````````

Finally, the state monad transformer exposes `get` and `put` operations given that `m` is a monad:
`````indent```````````````````````````````````````
get : Sₜ[s](m)(s)
get(s) := returnₘ(s,s)
put : s → Sₜ[s](m)(1)
put(s')(s) := returnₘ(1,s')
``````````````````````````````````````````````````

## Nondeterminism Monad Transformer

We have developed a new monad transformer for nondeterminism which can compose with state in both directions.
Previous attempts to define a monad transformer for nondeterminism have resulted in monad operations which do not respect monad laws.

Our nondeterminism monad transformer shares the "expected" type, embedding `𝒫` inside `m`:
`````indent```````````````````````````````````````
𝒫ₜ : (Type → Type) → (Type → Type)
𝒫ₜ(m)(α) := m(𝒫(α))
``````````````````````````````````````````````````

The nondeterminism monad transformer can transport monadic operations from `m` to `𝒫ₜ` _provided that `m` is also a join-semilattice functor_:
`````indent```````````````````````````````````````
bind : ∀ α β, 𝒫ₜ(m)(α) → (α → 𝒫ₜ(m)(β)) → 𝒫ₜ(m)(β)
bind(m)(f) := doₘ
  {x₁ .. xₙ} ←ₘ m
  f(x₁) ⊔ₘ .. ⊔ₘ f(xₙ)
return : ∀ α, α → 𝒫ₜ(m)(α)
return(x) := returnₘ({x})
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`bind` and `return` satisfy the monad laws.
`\end{proposition}`{.raw}

The key lemma in this proof is the functorality of `m`, namely that:
`````align````````````````````````````````````````
returnₘ(x ⊔ y) = returnₘ(x) ⊔ returnₘ(y)
``````````````````````````````````````````````````

The nondeterminism monad transformer can transport state effects from `m` to `𝒫ₜ`:
`````indent```````````````````````````````````````
get : 𝒫ₜ(m)(s)
get = mapₘ(λ(s).{s})(getₘ)
put : s → 𝒫ₜ(m)(s)
put(s) = mapₘ(λ(1).{1})(putₘ(s))
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`get` and `put` satisfy the state monad laws.
`\end{proposition}`{.raw}

The proof is by simpl calculation.

Finally, our nondeterminism monad transformer expses nondeterminism effects as a trivial applciation of the underlying monad's join-semilattice functorality:
`````indent```````````````````````````````````````
mzero : ∀ α, 𝒫ₜ(m)(α)
mzero := ⊥ᵐ
_⟨+⟩_ : ∀ α, 𝒫ₜ(m)(α) x 𝒫ₜ(m)(α) → 𝒫ₜ(m)(α)
m₁ ⟨+⟩ m₂ := m₁ ⊔ₘ m₂
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
`mzero` and `⟨+⟩` satisfy the nondterminism monad laws.
`\end{proposition}`{.raw}

The proof is trivial as a consequence of the underlying monad being a join-semilattice functor.

## Mapping to State Spaces

Both our execution and correctness frameworks requires that monadic actions in `M` map to some state space transitions `Σ`.
We extend the earlier statement of Galois connection to the transformer setting:
`````indent```````````````````````````````````````
mstep : ∀ α β, (α → M(β)) α⇄γ (Σ(α) → Σ(β))
``````````````````````````````````````````````````
Here `M` must map _arbitrary_ monadic actions `α → M(β)` to state space transitions for a state space _functor_ `Σ(_)`
We only show the `γ` sides of the mappings in this section, which allow one to execute the analyses.

For the state monad transformer `Sₜ[s]` mstep is defined:
`````indent```````````````````````````````````````
mstep-γ : ∀ α β m, (α → Sₜ[s](m)(β)) → (Σₘ(α × s) → Σₘ(β × s))
mstep-γ(f) := mstepₘ-γ(λ(a,s). f(a)(s))
``````````````````````````````````````````````````

For the nondeterminism transformer `𝒫ₜ`, mstep has two possible definitions.
One where `Σ` is `Σᵐ ∘ 𝒫`:
`````indent```````````````````````````````````````
mstep₁-γ : ∀ α β m, (α → 𝒫ₜ(m)(β)) → (Σₘ(𝒫(α)) → Σₘ(𝒫(β)))
mstep₁-γ(f) := mstepₘ-γ(λ({x₁ .. xₙ}). f(x₁) ⟨+⟩ .. ⟨+⟩ f(xₙ))
``````````````````````````````````````````````````
and one where `Σ` is `𝒫 ∘ Σᵐ`:
`````indent```````````````````````````````````````
mstep₂-γ : ∀ α β m, (α → 𝒫ₜ(m)(β)) → (𝒫(Σₘ(α)) → 𝒫(Σₘ(β)))
mstep₂-γ(f)({ς₁ .. ςₙ}) := aΣP₁ ∪ .. ∪ aΣPₙ
  where 
    commuteP-γ : ∀ α, Σₘ(𝒫(α)) → 𝒫(Σₘ(α))
    aΣPᵢ := commuteP-γ(mstepₘ-γ(f)(ςᵢ)) 
``````````````````````````````````````````````````
The operation `computeP-γ` must be defined for the underlying `Σᵐ`.
In general, `commuteP` must form a Galois connection.
However, this property exists for the identity monad, and is preserverd by `Sₜ[s]`, the only monad we will compose `𝒫ₜ` with in this work.
`````indent```````````````````````````````````````
commuteP-γ : ∀ α, Σₘ(𝒫(α) × s) → 𝒫(Σₘ(α × s))
commuteP-γ := commutePₘ ∘ map(λ({α₁ .. αₙ},s). {(α₁,s) .. (αₙ,s)})
``````````````````````````````````````````````````
Of all the `γ` mappings defined, the `γ` side of `commuteP` is the only mapping that loses information in the `α` direction.
Therefore, `mstep⸤Sₜ[s]⸥` and `mstep⸤𝒫ₜ1⸥` are really isomorphism transformers, and `mstep⸤𝒫ₜ2⸥` is the only Galois connection transformer.
The Galois connections for `mstep` for both `Sₜ[s]` or `Pₜ` rely crucially on `mstepₘ-γ` and `mstepₘ-α` to be functorial (i.e., homomorphic).

For convenience, we name the pairing of `𝒫ₜ` with `mstep₁` `FIₜ`, and with `mstep₂` `FSₜ` for flow insensitive and flow sensitive respectively.

`\begin{proposition}`{.raw}
`Σ⸤FSₜ⸥ α⇄γ Σ⸤FIₜ⸥`.
`\end{proposition}`{.raw}

The proof is by consequence of `commuteP`.

`\begin{proposition}`{.raw}
`Sₜ[s] ∘ 𝒫ₜ α⇄γ 𝒫ₜ ∘ Sₜ[s]`.
`\end{proposition}`{.raw}

We can now build monad transformer stacks from combinations of `Sₜ[s]`, `FIₜ` and `FSₜ` that have the following properties:

- The resulting monad has the combined effects of all pieces of the transformer stack.
- Actions in the resulting monad map to a state space transition system `Σ → Σ` for some `Σ`.
-- - Galois connections between states `s₁` and `s₂` are transported along the Galois connection between 
--   `(α → Sₜ[s₁](m)(β)) α⇄γ (Σ[s₁](α) → Σ[s₁](β))` and `(α → Sₜ[s₂](m)(β)) α⇄γ (Σ[s₂](α) → Σ[s₂](β))`
--   resulting in `(Σ[s₁](α) → Σ[s₁](β)) α⇄β (Σ[s₂](α) → Σ[s₂](β))`.

We can now instantiate our interpreter to the following monad stacks in decreasing order of precision:
`````align````````````````````````````````````````
Sₜ[Env] ∘ Sₜ[KAddr] ∘ Sₜ[KStore] ∘ Sₜ[ATime] ∘ Sₜ[AStore] ∘ FSₜ
``````````````````````````````````````````````````
which yields a path-sensitive flow-sensitive analysis,
`````align````````````````````````````````````````
Sₜ[Env] ∘ Sₜ[KAddr] ∘ Sₜ[KStore] ∘ Sₜ[ATime] ∘ FSₜ ∘ Sₜ[AStore]
``````````````````````````````````````````````````
which yeilds a path-insensitive flow-sensitive analysis, and
`````align````````````````````````````````````````
Sₜ[Env] ∘ Sₜ[KAddr] ∘ Sₜ[KStore] ∘ Sₜ[ATime] ∘ FIₜ ∘ Sₜ[AStore]
``````````````````````````````````````````````````
which yields a path-insensitive flow-insensitive analysis.
Furthermore, the Galois connections for our interpreter instantiated to each state space `Σ` is justified fully by construction.


# Implementation

We have implemented our framework in Haskell and applied it to compute analyses for `λIF`.
Our implementation provides path sensitivity, flow sensitivity, and flow insensitivity as a semantics-independent monad library.
The code shares a striking resemblance with the math.

Our interpreter for `λIF` is paramaterized as discussed in Section [4][Analysis Parameters].
We express a valid analysis with the following Haskell constraint:
`````indent```````````````````````````````````````
type Analysis(δ,μ,m) ∷ Constraint = 
  (AAM(μ),Delta(δ),AnalysisMonad(δ,μ,m))
``````````````````````````````````````````````````
Constraints `AAM(μ)` and `Delta(δ)` are interfaces for abstract time and the abstract domain.
The constraint `AnalysisMonad(m)` requires only that `m` has the required effects[^1]:
`````indent```````````````````````````````````````
type AnalysisMonad(δ,μ,m) ∷ Constraint = (
   Monad(m(δ,μ)), 
   MonadNondeterminism(m(δ,μ)),
   MonadState(Env(μ))(m(δ,μ)),
   MonadState(Store(δ,μ))(m(δ,μ)),
   MonadState(Time(μ,Call))(m(δ,μ)))
``````````````````````````````````````````````````
Our interpreter is implemented against this interface and concrete and abstract interpreters are recovered by instantiating `δ`, `μ` and `m`.

[^1]: 
    We use a CPS representation and a single store in our implementation.
    This requires `Time`, which is generic to the language, to take `Call` as a paramter rather than `Exp × KAddr`.

Our implementation is publically available and can be installed as a cabal package by executing:
`````align````````````````````````````````````````
cabal install maam
``````````````````````````````````````````````````

# Related Work

The most directly related work is the development of Monadic Abstract Interpreters (MAI) by \citet{davdar:Sergey:2013:Monalysis}.
In MAI, interpreters are also written in monadic style and variations in analysis are recovered through new monad implementations.
However, each monad in MAI is designed from scratch for a specific language to have specific analysis properties.
Our work extends the ideas in MAI in a way that isolates each parameter to be independent of others.
We factor out the monad as a truly semantics independent feature.
This factorization reveals an orthogonal tuning knob for path and flow sensitivity
Even more, we give the user building blocks for constructing monads that are correct and give the desired properties by construction.
Our framework is also motivated by the needs of reasoning formally about abstract interpreters, no mention of which is made in MAI.

We build directly on the work of Abstracting Abstract Machines (AAM) by \citet{davdar:van-horn:2010:aam}
  in our parameterization of abstract time and call-site sensitivity.
More notably, we follow the AAM philosophy of instrumenting a concrete semantics _first_ and performing a systematic abstraction _second_.
This greatly simplifies the Galois connection arguments during systematic abstraction.
However, this is at the cost of proving that the instrumented semantics simulate the original concrete semantics.

# Conclusion
