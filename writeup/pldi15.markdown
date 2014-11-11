# Introduction

Writing abstract interpreters is hard.
Writing proofs about abstract interpreters is extra hard.
Modern practice in whole-program analysis requires multiple iterations in the design space of possible analyses.
As we explore the design space of abstract interpreters, it would be nice if we didn't need to reprove all the properties we care about.
What we lack is a reusable meta-theory for exploring the design space of _correct-by-construction_ abstract interpreters.

We propose a compositional meta-theory framework for general purpose static analysis.
Our framework gives the analysis designer building blocks for building correct-by-construction abstract interpreters.
These building blocks are compositional, and they carry both computational and correctness properties of an analysis.
For example, we are able to tune the flow and path sensitivities of an analysis in our framework with no extra proof burden.
We do this by capturing the essential properties of flow and path sensitivities into plug-and-play components.
Comparably, we show how to design an analysis to be correct for all possible instantiations to flow and path sensitivity.

To achieve compositionality, our framework leverages monad transformers as the fundamental building blocks for an abstract interpreter.
Monad transformers snap together to form a single monad which drives interpreter execution.
Each piece of the monad transformer stack corresponds to either an element of the semantics' state space or a nondeterminism effect.
Variations in the transformer stack to give rise to different path and flow sensitivities for the analysis.
Interpreters written in our framework are proven correct w.r.t. all possible monads, and therefore to each choice of path and flow sensitivity.

The monad abstraction provides the computational and proof properties for our interpreters, from the monad operators and laws respectively.
Monad transformers are monad composition function; they consume and produce monads.
We strengthen the monad transformer interface to require that the resulting monad have a relationship to a state machine transition space.
We prove that a small set of monads transformers that meet this stronger interface can be used to write monadic abstract interpreters.

## Contributions:

Our contributions are:

- A compositional meta-theory framework for building correct-by-construction abstract interpreters.
  This framework is built using a restricted class of monad transformers.
- An isolated understanding of flow and path sensitivity for static analysis.
  We understand this spectrum as mere variations in the order of monad transformer composition in our framework.

## Outline

We will demonstrate our framework by example, walking the reader through the design and implementation of an abstract interpreter.
Section [X][Semantics] gives the concrete semantics for a small functional language.
Section [X][Monadic Interpreter] shows the full definition of a highly parameterized monadic interpreter.
Section [X][Recovering Concrete and Abstract Interpreters] shows how to recover concrete and abstract interpreters.
Section [X][Varying Path and Flow Sensitivity] shows how to manipulate the path and flow sensitivity of the interpreter through varyations in the monad.
Section [X][A Compositional Monadic Framework] demonstrates our compositional meta-theory framework built on monad transformers.

# Semantics

To demonsrate our framework we design an abstract interpreter for a simple applied lambda calculus: `λIF`.
`````align````````````````````````````````````````
  i ∈  ℤ
  x ∈  Var
  a ∈  Atom  ::= i | x | [λ](x).e
  ⊕ ∈  IOp   ::= [+] | [-]
  ⊙ ∈  Op    ::= ⊕ | @ 
  e ∈  Exp   ::= a | e ⊙ e | if0(e){e}{e}
``````````````````````````````````````````````````
`λIF` extends traditional lambda calculus with integers, addition, subtration and conditionals.
We use the  operator `@` as explicit syntax for function application.
This allows for `Op` to be a single syntactic class for all operators and simplifies the presentation.

Before designing an abstract interpreter we first specify a formal semantics for `λIF`.
Our semantics makes allocation explicit and separates values and continuations into separate stores.
Our approach to analysis will be to design a configurable interpreter that is capable of mirroring these semantics.

The state space `Σ` for `λIF` is a standard CESK machine augmented with a separate store for continuation values:
`````align````````````````````````````````````````
 τ ∈  Time    := ℤ
 l ∈  Addr   := Var × Time
 ρ ∈  Env     := Var ⇀ Addr
 σ ∈  Store   := Addr ⇀ Val
 c ∈  Clo     ::= ⟨[λ](x).e,ρ⟩ 
 v ∈  Val     ::= i | c
κl ∈  KAddr   := Time
κσ ∈  KStore  := KAddr ⇀ Frame × KAddr
fr ∈  Frame   ::= ⟨□ ⊙ e⟩ | ⟨v ⊙ □⟩ | ⟨if0(□){e}{e}⟩
 ς ∈  Σ       ::= Exp × Env × Store × KAddr × KStore
``````````````````````````````````````````````````

The semantics of atomic terms is given denotationally with the denotation function `A⟦_,_,_⟧`:
`````align````````````````````````````````````````
       A⟦_,_,_⟧  ∈ Env × Store × Atom ⇀ Val
       A⟦ρ,σ,i⟧  := i
       A⟦ρ,σ,x⟧  := σ(ρ(x))
A⟦ρ,σ,[λ](x).e⟧  := ⟨[λ](x).e,ρ⟩ 
       δ⟦_,_,_⟧  ∈ IOp × ℤ × ℤ → ℤ
   δ⟦[+],i₁,i₂⟧  := i₁ + i₂
   δ⟦[-],i₁,i₂⟧  := i₁ - i₂
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
We will justify our analyses as sound approximations of this collecting semantics.

# Monadic Interpreter

In this section we design a monadic interpreter for the `λIF` language which is also parameterizedin AAM[CITE] style.
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
bind-unit₁ : bind(return(a))(k) = k(a)
bind-unit₂ : bind(m)(return) = m
bind-assoc : bind(bind(m)(k₁))(k₂) = bind(m)(λ(a).bind(k₁(a))(k₂))
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
put-put : put-Env(s₁) ; put-Env(s₂) = put-Env(s₂)
put-get : put-Env(s) ; get-Env = return(s)
get-put : s ← get-Env ; put-Env(s) = return(1)
get-get : s₁ ← get-Env ; s₂ ← get-Env ; k(s₁,s₂) = s ← get-Env ; k(s,s)
``````````````````````````````````````````````````
The effects for `get-Store`, `get-KAddr` and `get-KStore` are identical.

### Monad Nondeterminism Properties

Nondeterminism is achieved through operators `<0>` and `<+>`:
`````align```````````````````````````````````````` 
  <0> :  ∀ α, M(α)
_<+>_ :  ∀ α, M(α) × M(α) → M(α)
`````````````````````````````````````````````````` 

We use the nondeterminism laws to reason about nondeterminism effects:
`````indent```````````````````````````````````````
⊥-zero₁ : bind(<0>)(k) = <0>
⊥-zero₂ : bind(m)(λ(a).<0>) = <0>
⊥-unit₁ : <0> <+> m = m
⊥-unit₂ : m <+> <0> = m 
+-assoc : m₁ <+> (m₂ <+> m₃) = (m₁ <+> m₂) <+> m₃
+-comm : m₁ <+> m₂ = m₂ <+> m₁
+-dist : bind(m₁ <+> m₂)(k) = bind(m₁)(k) <+> bind(m₂)(k)
``````````````````````````````````````````````````

## The Abstract Domain

The abstract domain is encapsulated by the `Val` type in the semantics.
To parameterize over it, we leave `Val` opaque but require it support various operations.
There is a constraint on `Val` its-self: it must be a join-semilattice with `⊥` and `⊔` respecting the usual laws.
We require `Val` to be a join-semilattice so it can be merged in the `Store`.

The interface for integers consists of introduction and elimiation rules:
`````align````````````````````````````````````````
    int-I :  ℤ → Val
int-if0-E :  Val → 𝒫(Bool)
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
`````align````````````````````````````````````````
clo-I :  Clo → Val
clo-E :  Val → 𝒫(Clo)
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

## The Interpreter

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

First, values in `𝒫(α)` can be lifted to monadic values `M(α)` using `return` and `<0>`, which we name `↑ₚ`:
`````indent```````````````````````````````````````
↑ₚ : ∀ α, 𝒫(α) → M(α)
↑ₚ({a₁ .. aₙ}) := return(a₁) <+> .. <+> return(aₙ)
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
The step function is written as a monadic computation from expressions to the next expression to evaluate, in small step style.
The definition for operators is simple: it merely pushes a stack from and returns the first operand:
`````indent```````````````````````````````````````
step : Exp → M(Exp)
step(e₁ ⊙ e₂) := do
  tickM(e₁ ⊙ e₂)
  push(⟨□ ⊙ e₂⟩)
  return(e₁)
``````````````````````````````````````````````````
The definition for atomic expressions must pop and inspect the stack and perform the denotation of the operation:
`````indent```````````````````````````````````````
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

A collecting-semantics execution of our interpreter is defined as:
`````indent```````````````````````````````````````
μ(X). ς₀ ⊔ X ⊔ γ(step)(X)
``````````````````````````````````````````````````
where `ς₀` is the injection of the initial program `e₀` into `Σ `.

# Recovering Interpreters

## Recovering a Concrete Interpreter

For the concrete value space we instantiate `CVal` to a powerset of `Val`.
`````indent```````````````````````````````````````
v ∈ CVal := 𝒫(Val)
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

\begin{proposition}
`CVal` satisfies the abstract domain laws from section [X][The Abstract Domain].
\end{proposition}

Concrete time `CTime` captures program contours as a product of `Exp` and `KAddr`:
`````indent```````````````````````````````````````
τ  ∈ CTime  := (Exp × KAddr)*
``````````````````````````````````````````````````
and `tick` is just a cons operator:
`````indent```````````````````````````````````````
tick : Exp × KAddr × Time → Time
tick (e,κl,τ) := (e,κl)∷τ
``````````````````````````````````````````````````

For the concrete monad we instantiate `M` to a path-sensitive `CM` which contains a powerset of concrete state space components.
`````indent```````````````````````````````````````
ψ ∈ Ψᶜᵐ := Env × Store × KAddr × KStore × Time
m ∈ CM(α) := Ψᶜᵐ → 𝒫(α × Ψᶜᵐ)
``````````````````````````````````````````````````

Monadic operators `bindᶜᵐ` and `returnᶜᵐ` encapsulate both state-passing and set-flattening:
`````indent```````````````````````````````````````
bindᶜᵐ : ∀ α, CM(α) → (α → CM(β)) → CM(β)
bindᶜᵐ(m)(f)(ψ) := {(y,ψ'') | (y,ψ'') ∈ f(a)(ψ') ; (a,ψ') ∈ m(ψ)}
returnᶜᵐ : ∀ α, α → CM(α)
returnᶜᵐ(a)(ψ) := {(a,ψ)}
``````````````````````````````````````````````````

State effects merely return singleton sets:
`````indent```````````````````````````````````````
get-Envᶜᵐ : CM(Env)
get-Envᶜᵐ(⟨ρ,σ,κ,τ⟩) := {(ρ,⟨ρ,σ,κ,τ⟩)}
put-Envᶜᵐ : Env → 𝒫(1)
put-Envᶜᵐ(ρ')(⟨ρ,σ,κ,τ⟩) := {(1,⟨ρ',σ,κ,τ⟩)}
``````````````````````````````````````````````````

Nondeterminism effects are implemented with set union:
`````indent```````````````````````````````````````
<0>ᶜᵐ : ∀ α, CM(α)
<0>ᶜᵐ(ψ) := {}
_<+>ᶜᵐ_ : ∀ α, CM(α) × CM(α) → CM(α)
(m₁ <+>ᶜᵐ m₂)(ψ) := m₁(ψ) ∪ m₂(ψ)
``````````````````````````````````````````````````

\begin{proposition}
`CM` satisfies monad, state, and nondeterminism laws.
\end{proposition}

Finally, we must establish a Galois connection between `Exp → CM(Exp)` and `CΣ → CΣ` for some choice of `CΣ`.
For the path sensitive monad `CM` instantiate with `CVal` and `CTime`, , `CΣ` is defined:
`````indent```````````````````````````````````````
CΣ := 𝒫(Exp × Ψᶜᵐ)
``````````````````````````````````````````````````

The Galois connection between `CM` and `CΣ` is straightforward:
`````indent```````````````````````````````````````
γᶜᵐ : (Exp → CM(Exp)) → CΣ → CΣ
γᶜᵐ(f)(eψ*) := {(e,ψ') | (e,ψ') ∈ f(e)(ψ) ; (e,ψ) ∈ eψ*}
αᶜᵐ : (CΣ → CΣ) → Exp → CM(Exp)
αᶜᵐ(f)(e)(ψ) := f({(e,ψ)})
``````````````````````````````````````````````````

The injection `ςᶜᵐ₀` for a program `e₀` is:
`````indent```````````````````````````````````````
ςᶜᵐ₀ := {⟨e,⊥,⊥,∙,⊥,∙⟩}
``````````````````````````````````````````````````

\begin{proposition} 
`γᶜᵐ` and `αᶜᵐ` form an isomorphism.
\end{proposition}

\begin{corollary}
`γᶜᵐ ` and `αᶜᵐ` form a Galois connection.
\end{corollary}

## Recovering an Abstract Interpreter

To arrive at an abstract interpreter we need seek only seek a monad `AM` that has a Galois connection to a finite state space `AΣ`.

We pick a simple abstraction for integers, `{[-],0,[+]}`, although our technique scales seamlessly to other domains.
As a consequence, the value type `AVal` turns into a powerset of abstract values:
`````indent```````````````````````````````````````
AVal := 𝒫(Clo + {[-],0,[+]})
``````````````````````````````````````````````````

Introduction and elimination functions for `AVal` are defined:
`````indent```````````````````````````````````````
int-I : ℤ → AVal
int-I(i) := 
  [-] if i < 0
  0 if i = 0
  [+] if i > 0
int-if0-E : AVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | [-] ∈ v ∨ [+] ∈ v }
``````````````````````````````````````````````````
Introduction and elmination for `Clo` is identical to the concrete domain.

The abstract `Aδ` operator is defined:
`````indent```````````````````````````````````````
Aδ : IOp × AVal × AVal → AVal 
Aδ(+,v₁,v₂) := { i     | 0 ∈ v₁ ∧ i ∈ v₂ }
             ∪ { i     | i ∈ v₁ ∧ 0 ∈ v₂ }
             ∪ { [+]     | [+] ∈ v₁ ∧ [+] ∈ v₂ } 
             ∪ { [-]     | [-] ∈ v₁ ∧ [-] ∈ v₂ } 
             ∪ { [-],0,[+] | [+] ∈ v₁ ∧ [-] ∈ v₂ }
             ∪ { [-],0,[+] | [-] ∈ v₁ ∧ [+] ∈ v₂ }
``````````````````````````````````````````````````
The definition for `Aδ(-,v₁,v₂)` is analagous.

Next we abstract `Time` to the finite domain of k-truncated lists of execution contexts:
`````indent```````````````````````````````````````
Time := (Exp × KAddr)*ₖ
``````````````````````````````````````````````````
The `tick` operator becomes cons followed by k-truncation:
`````indent```````````````````````````````````````
tick : Exp × KAddr × Time → Time
tick(e,κl,τ) = ⌊(e,κl)∷τ⌋ₖ
``````````````````````````````````````````````````

The monad `AM` need not change in implementation from `CM`; they are identical up to choices for `AStore` (which maps to `AVal`) and `ATime`.
`````indent```````````````````````````````````````
ψ ∈ Ψᵃᵐ := Env × AStore × KAddr × KStore × ATime
``````````````````````````````````````````````````

The resulting state space `AΣ` is finite, and its least-fixed-point iteration will give a sound and computable analysis.

# Varying Path and Flow Sensitivity

We are able to recover a flow-insensitivity in the analysis through a new definition for `M`: `AMᶠⁱ`.
To do this we pull `Store` out of the powerset and exploit its join-semilattice structure:
`````indent```````````````````````````````````````
Ψᶠⁱ := Env × KAddr × KStore × Time
AMᶠⁱ(α) := Ψᶠⁱ × Store × 𝒫(α × Ψᶠⁱ) × Store
``````````````````````````````````````````````````

The monad operator `bindᶠⁱ` performs the store merging needed to capture a flow-insensitive analysis.
`````indent```````````````````````````````````````
bindᶠⁱ : ∀ α β, AMᶠⁱ(α) → (α → AMᶠⁱ(β)) → AMᶠⁱ(β)
bindᶠⁱ(m)(f)(ψ,σ) := ({bs₁₁ .. bsₙ₁ .. bsₙₘ},σ₁ ⊔ .. ⊔ σₙ)
  where
    ({(a₁,ψ₁) .. (aₙ,ψₙ)},σ') := m(ψ,σ)
    ({bψᵢ₁ .. bψᵢₘ},σᵢ) := f(aᵢ)(ψᵢ,σ')
``````````````````````````````````````````````````
The unit for `bindᶠⁱ` returns one nondeterminism branch and a single store:
`````indent```````````````````````````````````````
returnᶠⁱ : ∀ α, α → AMᶠⁱ(α)
returnᶠⁱ(a)(ψ,σ) := ({a,ψ},σ)
``````````````````````````````````````````````````

State effects `get-Env` and `put-Env` are also straightforward, returning one branch of nondeterminism:
`````indent```````````````````````````````````````
get-Envᶠⁱ : AMᶠⁱ(Env)
get-Envᶠⁱ(⟨ρ,κ,τ⟩,σ) := ({(ρ,⟨ρ,κ,τ⟩)},σ)
put-Envᶠⁱ : Env → AMᶠⁱ(1)
put-Envᶠⁱ(ρ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ',κ,τ⟩)},σ)
``````````````````````````````````````````````````

State effects `get-Store` and `put-Store` are analagous to `get-Env` and `put-Env`:
`````indent```````````````````````````````````````
get-Storeᶠⁱ : AMᶠⁱ(Env)
get-Storeᶠⁱ(⟨ρ,κ,τ⟩,σ) := ({(σ,⟨ρ,κ,τ⟩},σ)
put-Storeᶠⁱ : Store → AMᶠⁱ(1)
put-Storeᶠⁱ(σ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ,κ,τ⟩)},σ')
``````````````````````````````````````````````````

Nondeterminism operations union the powerset and join the store pairwise:
`````indent```````````````````````````````````````
<0>ᶠⁱ : ∀ α, M(α)
<0>ᶠⁱ(ψ,σ) := ({}, ⊥)
_<+>_ : ∀ α, M(α) × M(α) → M α 
(m₁ <+> m₂)(ψ,σ) := (aψ*₁ ∪ aψ*₂,σ₁ ⊔ σ₂)  
  where (aψ*ᵢ,σᵢ) := mᵢ(ψ,σ)
``````````````````````````````````````````````````

Finally, the Galois connection relating `AMᶠⁱ` to a state space transition over `AΣᶠⁱ` must also compute nondeterminism unions and store joins:
`````indent```````````````````````````````````````
AΣᶠⁱ := 𝒫(Exp × Ψᶠⁱ) × Store
γᶠⁱ : (Exp → AMᶠⁱ(Exp)) → (Σᶠⁱ → Σᶠⁱ)
γᶠⁱ(f)(eψ*,σ) := ({eψ₁₁ .. eψₙ₁  .. eψₙₘ}, σ₁ ⊔ .. ⊔ σₙ)
  where 
    {(e₁,ψ₁) .. (eₙ,ψₙ)} := eψ*
    ({eψᵢ₁ .. eψᵢₘ},σᵢ) := f(eᵢ)(ψᵢ,σ)
αᶠⁱ  : (Σᶠⁱ → Σᶠⁱ) → (Exp → AMᶠⁱ(Exp))
αᶠⁱ(f)(e)(ψ,σ) := f({(e,ψ)},σ)
``````````````````````````````````````````````````

\begin{proposition}
`γᶠⁱ` and `αᶠⁱ` form an isomorphism.
\end{proposition}

\begin{corollary}
`γᶠⁱ` and `αᶠⁱ` form a Galois connection.
\end{corollary}

\begin{proposition}
There exists Galois connection `CΣ α₁⇄γ₁ AΣ α₂⇄γ₂ AΣᶠⁱ` and `α₁ ∘ Cγ(step) ∘ γ₁ ⊑  Aγ(step) ⊑ γ₂ ∘ Aγᶠⁱ(step) ∘ α₂`
\end{proposition}

The first Galois connection `CΣ α₁⇄γ₁ AΣ` is justified by the Galois connections between `CVal α⇄γ AVal` and `CTime α⇄γ ATime`.
The second Galois connection `AΣ α₂⇄γ₂ AΣᶠⁱ` is justified by first calculating the Galois connection between monads `AM` and `CM`,
  and then transporting it through their respective Galois connections to `AΣ` and `AΣᶠⁱ`.
These proofs are tedious calculations over the definitions which we do not repeat here.
However, we will recover these proof in a later section through our compositional framework which greatly reduces the proof burden.

We note that the implementation for our interpreter and abstract garbage collector remain the same.
They both scale seamlessly to flow-sensitive and flow-insensitive variants when instantiated with the appropriate monad.

# A Compositional Monadic Framework

In our framework thus far, any modification to the interpreter requires redesigning the monad `M`.
However, we want to avoid reconstructing complicated monads for our interpreters.
Even more, we want to avoid reconstructing _proofs_ about monads for our interpreters.
Toward this goal we introduce a compositional framework for constructing monads using a restricted class of monad transformer.

There are two types of monadic effects used in the monadic interprer: state and nondeterminism.
There is a monad transformer for adding state effects to existing monads, called the state monad tranformer:

`````indent```````````````````````````````````````
Sₜ[_] : (Type → Type) → (Type → Type)
Sₜ[s](m)(α) := s → m(α × s)
``````````````````````````````````````````````````

Monadic actions `bind` and `return` (and their laws) use the underlying monad:

`````indent```````````````````````````````````````
bindₛ : ∀ α β, Sₜ[s](m)(α) → (α → Sₜ[s](m)(β)) → Sₜ[s](m)(β)
bindₛ(m)(f)(s) := do
  (x,s') ←ₘ m(s)
  f(x)(s')
returnₛ : ∀ α m, α → Sₜ[s](m)(α)
returnₛ(x)(s) := returnₘ(x,s)
``````````````````````````````````````````````````

State actions `get` and `put` expose the cell of state while interacting with the underlying monad `m`:

`````indent```````````````````````````````````````
getₛ : Sₜ[s](m)(s)
getₛ(s) := returnₘ(s,s)
putₛ : s → Sₜ[s](m)(1)
putₛ(s')(s) := returnₘ(1,s')
``````````````````````````````````````````````````

and the state monad transformer is able to transport nondeterminism effects from the underlying monad:
`````indent```````````````````````````````````````
<0>ₛ : ∀ α, Sₜ[s](m)(α)
<0>ₛ(s) := <0>ₘ 
_<+>ₛ_ : ∀ α, Sₜ[s](m)(α) x Sₜ[s](m)(α) → Sₜ[s](m)(α)
(m₁ <+>ₛ m₂)(s) := m₁(s) <+>ₘ m₂(s) 
``````````````````````````````````````````````````

The state monad transformer was introduced by Mark P. Jones in [[X](http://web.cecs.pdx.edu/~mpj/pubs/springschool95.pdf)].

We develop a new monad transformer for nondeterminism which can compose with state in both directions.

`````indent```````````````````````````````````````
𝒫ₜ : (Type → Type) → (Type → Type)
𝒫ₜ(m)(α) := m(𝒫(α))
``````````````````````````````````````````````````

Monadic actions `bind` and `return` require that the underlying monad be a join-semilattice functor:

`````indent```````````````````````````````````````
bindₚ : ∀ α β, 𝒫ₜ(m)(α) → (α → 𝒫ₜ(m)(β)) → 𝒫ₜ(m)(β)
bindₚ(m)(f) := do
  {x₁ .. xₙ} ←ₘ m
  f(x₁) ⊔ₘ .. ⊔ₘ f(xₙ)
returnₚ : ∀ α, α → 𝒫ₜ(m)(α)
returnₚ(x) := returnₘ({x})
``````````````````````````````````````````````````

Nondterminism actions `<0> and `<+> interact with the join-semilattice functorality of the underlying monad `m`:

`````indent```````````````````````````````````````
<0>ₚ : ∀ α, 𝒫ₜ(m)(α)
<0>ₚ := ⊥ᵐ
_<+>ₚ_ : ∀ α, 𝒫ₜ(m)(α) x 𝒫ₜ(m)(α) → 𝒫ₜ(m)(α)
m₁ <+>ₚ m₂ := m₁ ⊔ₘ m₂
``````````````````````````````````````````````````

and the nondeterminism monad transformer is able to transport state effects from the underlying monad:

`````indent```````````````````````````````````````
getₚ : 𝒫ₜ(m)(s)
getₚ = mapₘ(λ(s).{s})(getₘ)
putₚ : s → 𝒫ₜ(m)(s)
putₚ(s) = mapₘ(λ(1).{1})(putₘ(s))
``````````````````````````````````````````````````

_Proposition: `𝒫ₜ` is a transformer for monads which are also join semi-lattice functors._

Our correctness framework requires that monadic actions in `M` map to state space transitions in `Σ`.
We establish this property in addition to monadic actions and effects for state and nondeterminism monad transformers.
We call this property `MonadStep`, where monadic acations in `M` admit a Galois connection to transitions in `Σ`:

`````indent```````````````````````````````````````
mstep : ∀ α β, (α → M(β)) α⇄γ (Σ(α) → Σ(β))
``````````````````````````````````````````````````

We now show that the monad transformers for state and nondeterminism transport this property in addition to monadic operations.

For the state monad transformer `Sₜ[s]` mstep is defined:

`````indent```````````````````````````````````````
mstepₛ-γ : ∀ α β m, (α → Sₜ[s](m)(β)) → (Σₘ(α × s) → Σₘ(β × s))
mstepₛ-γ(f) := mstepₘ-γ(λ(a,s). f(a)(s))
``````````````````````````````````````````````````

For the nondeterminism transformer `𝒫ₜ`, mstep has two possible definitions.
One where `Σ` is `Σᵐ ∘ P`:

`````indent```````````````````````````````````````
mstepₚ₁-γ : ∀ α β m, (α → 𝒫ₜ(m)(β)) → (Σₘ(𝒫(α)) → Σₘ(𝒫(β)))
mstepₚ₁-γ(f) := mstepₘ-γ(λ({x₁ .. xₙ}). f(x₁) <+> .. <+> f(xₙ))
``````````````````````````````````````````````````

and one where `Σ` is `P ∘ Σᵐ`:

`````indent```````````````````````````````````````
mstepₚ₂-γ : ∀ α β m, (α → 𝒫ₜ(m)(β)) → (𝒫(Σₘ(α)) → 𝒫(Σₘ(β)))
mstepₚ₂-γ(f)({ς₁ .. ςₙ}) := aΣP₁ ∪ .. ∪ aΣPₙ
  where 
    commuteP : ∀ α, Σₘ(𝒫(α)) → 𝒫(Σₘ(α))
    aΣPᵢ := commuteP-γ(mstepₘ-γ(f)(ςᵢ)) 
``````````````````````````````````````````````````

The operation `computeP` must be defined for the underlying `Σᵐ`.
This property is true for the identiy monad, and is preserved by `Sₜ[s]` when `Σᵐ` is also a functor:

`````indent```````````````````````````````````````
commuteP-γ : ∀ α, Σₘ(𝒫(α) × s) → 𝒫(Σₘ(α × s))
commuteP-γ := commutePₘ ∘ map(λ({α₁ .. αₙ},s). {(α₁,s) .. (αₙ,s)})
``````````````````````````````````````````````````

The `γ` side of commuteP is the only Galois connection mapping that loses information in the `α` direction.
Therefore, `mstepₛ` and `mstepₚ₁` are really isomorphism transformers, and `mstepₚ₂` is the only Galois connection transformer.

[QUESTION: should I give the definitions for the `α` maps here? -DD]

For convenience, we name the pairing of `𝒫ₜ` with `mstepᵖ₁` `FIₜ`, and with `mstepₚ₂` `FSₜ` for flow insensitive and flow sensitive respectively.

We can now build monad transformer stacks from combinations of `Sₜ[s]`, `FIₜ` and `FSₜ` that have the following properties:

- The resulting monad has the combined effects of all pieces of the transformer stack.
- Actions in the resulting monad map to a state space transition system `Σ → Σ` for some `Σ`.
- Galois connections between states `s₁` and `s₂` are transported along the Galois connection between 
  `(α → Sₜ[s₁](m)(β)) α⇄γ (Σ[s₁](α) → Σ[s₁](β))` and `(α → Sₜ[s₂](m)(β)) α⇄γ (Σ[s₂](α) → Σ[s₂](β))`
  resulting in `(Σ[s₁](α) → Σ[s₁](β)) α⇄β (Σ[s₂](α) → Σ[s₂](β))`.

We can now instantiate our interpreter to the following monad stacks.

- `Sₜ[Env] ∘ Sₜ[Store] ∘ Sₜ[KAddr] ∘ Sₜ[KStore] ∘ Sₜ[Time] ∘ FSₜ`
    - This yields a path-sensitive flow-sensitive analysis.
- `Sₜ[Env] ∘ Sₜ[KAddr] ∘ Sₜ[KStore] ∘ Sₜ[Time] ∘ FSₜ ∘ Sₜ[Store]`
    - This yeilds a path-insensitive flow-sensitive analysis.
- `Sₜ[Env] ∘ Sₜ[KAddr] ∘ Sₜ[KStore] ∘ Sₜ[Time] ∘ FIₜ ∘ Sₜ[Store]`
    - This yields a path-insensitive flow-insensitive analysis.

Furthermore, the final Galois connection for each state space Σ is justified from individual Galois connections between state space components.
