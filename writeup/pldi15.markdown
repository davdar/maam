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

Our language of study is `λIF`:
`````align````````````````````````````````````````
  i ∈  ℤ
  x ∈  Var
  a ∈  Atom  ::= i | x | [λ](x).e
  ⊕ ∈  IOp   ::= [+] | [-]
  ⊙ ∈  Op    ::= ⊕ | @ 
  e ∈  Exp   ::= a | e ⊙ e | if0(e){e}{e}
``````````````````````````````````````````````````
`λIF` is a simple applied lambda calculus with integers and conditionals.
The operator `@` is explicit syntax for function application.
This allows for `Op` to be a single syntactic class for all operators and simplifies the presentation.

We begin with a concrete semantics for `λIF` which makes allocation explicit.
Allocation is made explicit to make the semantics more amenable to abstraction and abstract garbage collection.

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

Before defining the step relation we define metafunctions for evaluating atomic expressions and integer arithmatic:
`````align````````````````````````````````````````
       A⟦_,_,_⟧  ∈ Env × Store × Atom ⇀ Val
       A⟦ρ,σ,i⟧  := i
       A⟦ρ,σ,x⟧  := σ(ρ(x))
A⟦ρ,σ,[λ](x).e⟧  := ⟨[λ](x).e,ρ⟩ 
       δ⟦_,_,_⟧  ∈ IOp × ℤ × ℤ → ℤ
   δ⟦[+],i₁,i₂⟧  := i₁ + i₂
   δ⟦[-],i₁,i₂⟧  := i₁ - i₂
``````````````````````````````````````````````````

Our step relation is somewhat standard:
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

We also wish to employ abstract garbage collection, which adheres to the following specification:
`````indent```````````````````````````````````````
_~~>ᵍᶜ_ ∈ 𝒫(Σ × Σ)
ς ~~>ᵍᶜ ς' 
  where ς ~~> ς'
⟨e,ρ,σ,κl,κσ,τ⟩ ~~>ᵍᶜ ⟨e,ρ,σ',κl,κσ,τ⟩
  where 
    σ' := {l ↦ σ(l) | l ∈ R[σ](ρ,e)}
    κσ' := {κl ↦ κσ(κl) | κl ∈ KR[κσ](κl)}
``````````````````````````````````````````````````
where `R` is the set of addresses reachable from a given expression:
`````indent```````````````````````````````````````
R[_] ∈ Store → Env × Exp → 𝒫(Addr)
R[σ](ρ,e) := μ(θ). 
  R₀(ρ,e) ∪ θ ∪ {l' | l' ∈ R-Val(σ(l)) ; l ∈ θ}
R₀ ∈ Env × Exp → 𝒫(Addr)
R₀(ρ,e) := {ρ(x) | x ∈ FV(e)}
FV ∈ Exp → 𝒫(Var)
FV(x) := {x}
FV(i) := {}
FV([λ](x).e) := FV(e) - {x}
FV(e₁ ⊙ e₂) := FV(e₁) ∪ FV(e₂)
FV(if0(e₁){e₂}{e₃}) := FV(e₁) ∪ FV(e₂) ∪ FV(e₃)
R-Val ∈ Val → 𝒫(Addr)
R-Val(i) := {}
R-Val(⟨[λ](x).e,ρ⟩) := {ρ(x) | y ∈ FV([λ](x).e)}
``````````````````````````````````````````````````
`R[σ](ρ,e)` computes the transitively reachable addresses from `e` in `ρ` and `σ`.
(We write `μ(x). f(x)` as the least-fixed-point of a function `f`.)
`R₀(ρ,e)` computes the initial reachable address set for `e` under `ρ`.
`FV(e)` computes the free variables for an expression `e`.
`R-Val` computes the addresses reachable from a value.

Analagously, `KR` is the set of addresses reachable from a given continuation address:
`````indent```````````````````````````````````````
KR[_] ∈ KStore → KAddr → 𝒫(KAddr)
KR[κσ](κl) := μ(kθ). κθ₀ ∪ κθ ∪ {π₂(κσ(κl)) | κl ∈ κθ}
``````````````````````````````````````````````````

# Monadic Interpreter

We next design an interpreter for `λIF` as a monadic interpreter.
This interpreter will support both concrete and abstract executions.
To do this, there will be three parameters which the user can instantiate in any way they wish:

1. The monad, which captures the flow-sensitivity of the analysis.
2. The value space, which captures the abstract domain for integers and closures.
3. Abstract time, which captures the call-site sensitivity of the analysis.

We place each of these features behind an abstract interface and leave their implementations opaque.
We will recover specific concrete and abstract interpreters in a later section.

The goal is to implement as much of the interpreter as possible while leaving these things abstract.
The more we can prove about the interpreter independent of these variables, the more proof-work we'll get for free.

## The Monad Interface

The interpreter will use a monad `M` in two ways.
First, to manipulate components of the state space (like `Env` and `Store`).
Second, to exhibit nondeterministic behavior, which is inherent in computable analysis.
We capture these properties as monadic effects.

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

These operators capture the essence of the explicit state-passing and set comprehension aspects of the interpreter.
Our interpreter will use these operators and avoid referencing an explicit configuration `ς` or sets of results.

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

Interacting with `Env` is achieved through `get-Env` and `put-Env` effects:
`````indent``````````````````````````````````````` 
get-Env : M(Env)
put-Env : Env → M(1)
``````````````````````````````````````````````````
which have the following laws:
`````indent``````````````````````````````````````` 
put-put : put-Env(s₁) ; put-Env(s₂) = put-Env(s₂)
put-get : put-Env(s) ; get-Env = return(s)
get-put : s ← get-Env ; put-Env(s) = return(1)
get-get : s₁ ← get-Env ; s₂ ← get-Env ; k(s₁,s₂) = s ← get-Env ; k(s,s)
``````````````````````````````````````````````````
The effects for `get-Store`, `get-KAddr` and `get-Store` are identical.

Nondeterminism is achieved through operators `⟨0⟩` and `⟨+⟩`:
`````align```````````````````````````````````````` 
  ⟨0⟩ :  ∀ α, M(α)
_⟨+⟩_ :  ∀ α, M(α) × M(α) → M(α)
`````````````````````````````````````````````````` 
which have the following laws:
`````indent```````````````````````````````````````
⊥-zero₁ : bind(⟨0⟩)(k) = ⟨0⟩
⊥-zero₂ : bind(m)(λ(a).⟨0⟩) = ⟨0⟩
⊥-unit₁ : ⟨0⟩ ⟨+⟩ m = m
⊥-unit₂ : m ⟨+⟩ ⟨0⟩ = m 
+-assoc : m₁ ⟨+⟩ (m₂ ⟨+⟩ m₃) = (m₁ ⟨+⟩ m₂) ⟨+⟩ m₃
+-comm : m₁ ⟨+⟩ m₂ = m₂ ⟨+⟩ m₁
+-dist : bind(m₁ ⟨+⟩ m₂)(k) = bind(m₁)(k) ⟨+⟩ bind(m₂)(k)
``````````````````````````````````````````````````

The laws for monads, state and nondeterminism are important.
They enable us to argue that our interpreter is correct w.r.t. the concrete semantics in the absence of a particular choice of monad.

## The Value Space Interface

To abstract the value space we require the type `Val` be an opaque parameter
We need only require that `Val` is a join-semilattice:

`````align````````````````````````````````````````
⊥ : Val
_⊔_ : Val × Val → Val
``````````````````````````````````````````````````

The interface for integers consists of introduction and elimiation rules:

`````align````````````````````````````````````````
int-I : ℤ → Val
int-if0-E : Val → 𝒫(Bool)
``````````````````````````````````````````````````

The laws for this interface are designed to induce a Galois connection between `ℤ` and `Val`:

`````indent```````````````````````````````````````
{true}  ⊑ int-if0-E(int-I(i))     if i = 0
{false} ⊑ int-if0-E(int-I(i))     if i ≠ 0
v ⊒ ⨆⸤b ∈ int-if0-E(v)⸥ θ(b)
  where θ(true)  = int-I(0)                                      
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

## Interpreter Definition

We use the three interfaces from above as opaque parameters to out interpreter.
Before defining the interpreter we define some helper functions which interact with the underlying monad `M`.

First, values in `𝒫(α)` can be lifted to monadic values `M(α)` using `return` and `⟨0⟩`, which we name `↑ₚ`:

`````indent```````````````````````````````````````
↑ₚ : ∀ α, 𝒫(α) → M(α)
↑ₚ({a₁ .. aₙ}) := return(a₁) ⟨+⟩ .. ⟨+⟩ return(aₙ)
``````````````````````````````````````````````````

We introduce monadic helper functions for allocation and manipulating time:

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

Finally we introduce helper functions for manipulating stack frames:

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

We can now write a monadic interpreter for `λIF` using these monadic effects.

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

We also implement abstract garbage collection monadically:

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

There is one last parameter to our development: a connection between our monadic interpreter and a state space transition system.
We state this connection formally as a Galois connection `(Σ → Σ)α⇄γ(Exp → M(Exp))`.
This Galois connection serves two purposes.
First, it allows us to implement the analysis by converting our interpreter to the transition system `Σ → Σ` through `γ`.
Second, this Galois connection serves to _transport other Galois connections_.
For example, given concrete and abstract versions of `Val`, we carry `CVal α⇄γ AVal` through the Galois connection to establish `CΣ α⇄γ AΣ`.

A collecting-semantics execution of our interpreter is defined as:

`````indent```````````````````````````````````````
μ(ς). ς₀ ⊔ ς ⊔ γ(step)(ς)
``````````````````````````````````````````````````

where `ς₀` is the injection of the initial program `e` into `Σ `.

# Recovering Concrete and Abstract Interpreters

To recover a concrete interpreter we instantiate `M` to a path-sensitive monad: `Mᵖˢ`.
The path sensitive monad is a simple powerset of products:

`````indent```````````````````````````````````````
ψ ∈ Ψᵖˢ := Env × Store × KAddr × KStore × Time
m ∈ Mᵖˢ(α) := Ψᵖˢ → 𝒫(α × Ψᵖˢ)
``````````````````````````````````````````````````

Monadic operators `bindᵖˢ` and `returnᵖˢ` are defined to encapsulate both state-passing and set-flattening:

`````indent```````````````````````````````````````
bindᵖˢ : ∀ α, Mᵖˢ(α) → (α → Mᵖˢ(β)) → Mᵖˢ(β)
bindᵖˢ(m)(f)(ψ) := {(y,ψ'') | (y,ψ'') ∈ f(a)(ψ') ; (a,ψ') ∈ m(ψ)}
returnᵖˢ : ∀ α, α → Mᵖˢ(α)
returnᵖˢ(a)(ψ) := {(a,ψ)}
``````````````````````````````````````````````````

State effects merely return singleton sets:

`````indent```````````````````````````````````````
get-Envᵖˢ : Mᵖˢ(Env)
get-Envᵖˢ(⟨ρ,σ,κ,τ⟩) := {(ρ,⟨ρ,σ,κ,τ⟩)}
put-Envᵖˢ : Env → 𝒫(1)
put-Envᵖˢ(ρ')(⟨ρ,σ,κ,τ⟩) := {(1,⟨ρ',σ,κ,τ⟩)}
``````````````````````````````````````````````````

Nondeterminism effects are implemented with set union:

`````indent```````````````````````````````````````
⟨0⟩ᵖˢ : ∀ α, Mᵖˢ(α)
⟨0⟩ᵖˢ(ψ) := {}
_⟨+⟩ᵖˢ_ : ∀ α, Mᵖˢ(α) × Mᵖˢ(α) → Mᵖˢ(α)
(m₁ ⟨+⟩ᵖˢ m₂)(ψ) := m₁(ψ) ∪ m₂(ψ)
``````````````````````````````````````````````````

_Proposition: Mᵖˢ satisfies monad, state, and nondeterminism laws._

For the value space `CVal` we use a powerset of semantic values `Val`:

`````indent```````````````````````````````````````
v ∈ CVal := 𝒫(Val)
``````````````````````````````````````````````````

with introduction and elimination rules:

`````indent```````````````````````````````````````
int-I : ℤ → CVal
int-I(i) := {i}
int-if0-E : CVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | i ∈ v ∧ i ≠ 0 }
``````````````````````````````````````````````````

and `δ` to manipulate abstract values:

`````indent```````````````````````````````````````
δ⟦_,_,_⟧ : IOp × CVal × CVal → CVal
δ⟦[+],v₁,v₂⟧ := { i₁ + i₂ | i₁ ∈ v₁ ; i₂ ∈ v₂ }
δ⟦[-],v₁,v₂⟧ := { i₁ - i₂ | i₁ ∈ v₁ ; i₂ ∈ v₂ }
``````````````````````````````````````````````````

Abstract time and addresses are program contours in the concrete space:

`````indent```````````````````````````````````````
τ  ∈ Time  := (Exp × KAddr)*
l  ∈ Addr  := Var × Time
κl ∈ KAddr := Time
``````````````````````````````````````````````````

Operators `alloc` and `κalloc` are merely identity functions, and `tick` is just a cons operator.

Finally, we must establish a Galois connection between `Exp → Mᵖˢ(Exp)` and `Σ → Σ` for some `Σ`.
The state space `Σ` depends only on the monad `Mᵖˢ` and is independent of the choice for `CVal`, Addr or Time.
For the path sensitive monad `Mᵖˢ` , `Σᵖˢ` is defined:

`````indent```````````````````````````````````````
Σᵖˢ := 𝒫(Exp × Ψᵖˢ)
``````````````````````````````````````````````````

and the Galois connection is:

`````indent```````````````````````````````````````
γᵖˢ : (Exp → Mᵖˢ(Exp)) → Σᵖˢ → Σᵖˢ
γᵖˢ(f)(eψ*) := {(e,ψ') | (e,ψ') ∈ f(e)(ψ) ; (e,ψ) ∈ eψ*}
αᵖˢ : (Σᵖˢ → Σᵖˢ) → Exp → Mᵖˢ(Exp)
αᵖˢ(f)(e)(ψ) := f({(e,ψ)})
``````````````````````````````````````````````````

_Proposition: `γᵖˢ` and `αᵖˢ` form an isomorphism._

This implies Galois connnection.

The injection `ςᵖˢ₀` for a program `e` is:

`````indent```````````````````````````````````````
ςᵖˢ₀ := {⟨e,⊥,⊥,∙,⊥,∙⟩}
``````````````````````````````````````````````````

To arrive at an abstract interpreter we seek a finite state space.
First we abstract the value space `Val` as `AVal`, which only tracks integer parity:

`````indent```````````````````````````````````````
AVal := 𝒫(Clo + {-,0,+})
``````````````````````````````````````````````````

Introduction and elimination functions are defined:

`````indent```````````````````````````````````````
int-I : ℤ → AVal
int-I(i) := [-] if i < 0
            [0] if i = 0
            [+] if i > 0
int-if0-E : AVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | [-] ∈ v ∨ + ∈ v }
``````````````````````````````````````````````````

Introduction and elmination for `Clo` is identical to the concrete domain.

The abstract `δ` operator is defined:

`````indent```````````````````````````````````````
Aδ : IOp × AVal × AVal → AVal 
Aδ(+,v₁,v₂) := { p     | [0] ∈ v₁ ∧ p ∈ v₂ }
             ∪ { p     | p ∈ v₁ ∧ [0] ∈ v₂ }
             ∪ { [+]     | [+] ∈ v₁ ∧ [+] ∈ v₂ } 
             ∪ { [-]     | [-] ∈ v₁ ∧ [-] ∈ v₂ } 
             ∪ { [-],[0],[+] | [+] ∈ v₁ ∧ [-] ∈ v₂ }
             ∪ { [-],[0[,[+] | [-] ∈ v₁ ∧ [+] ∈ v₂ }
``````````````````````````````````````````````````

Next we abstract `Time` to the finite domain of a k-truncated list of execution contexts:

`````indent```````````````````````````````````````
Time := (Exp × KAddr)*ₖ
``````````````````````````````````````````````````

The `tick` operator becomes cons followed by k-truncation:

`````indent```````````````````````````````````````
tick : Exp × KAddr × Time → Time
tick(e,κl,τ) = ⌊(e,κl)∷τ⌋ₖ
``````````````````````````````````````````````````

After substituting abstract versions for `Val` and `Time`, the following state space for `Σᵖˢ` becomes finite:

`````indent```````````````````````````````````````
𝒫(Exp × AEnv × AStore × AKAddr × AKStore × ATime)
``````````````````````````````````````````````````

and the least-fixed-point iteration of the collecting semantics provides a sound and computable analysis.

# Varying Path and Flow Sensitivity

We are able to recover a flow-insensitive interpreter through a new definition for `M`: `Mᶠⁱ`.
To do this we pull `Store` out of the powerset and use its join-semilattice structure:

`````indent```````````````````````````````````````
Ψᶠⁱ := Env × KAddr × KStore × Time
Mᶠⁱ(α) := Ψᶠⁱ × Store × 𝒫(α × Ψᶠⁱ) × Store
``````````````````````````````````````````````````

The monad operator `bindᶠⁱ` must merge multiple stores back to one:
 
`````indent```````````````````````````````````````
bindᶠⁱ : ∀ α β, Mᶠⁱ(α) → (α → Mᶠⁱ(β)) → Mᶠⁱ(β)
bindᶠⁱ(m)(f)(ψ,σ) := ({bs₁₁ .. bsₙ₁ .. bsₙₘ},σ₁ ⊔ .. ⊔ σₙ)
  where
    ({(a₁,ψ₁) .. (aₙ,ψₙ)},σ') := m(ψ,σ)
    ({bψᵢ₁ .. bψᵢₘ},σᵢ) := f(aᵢ)(ψᵢ,σ')
``````````````````````````````````````````````````
 
The unit for `bindᶠⁱ`:

`````indent```````````````````````````````````````
returnᶠⁱ : ∀ α, α → Mᶠⁱ(α)
returnᶠⁱ(a)(ψ,σ) := ({a,ψ},σ)
``````````````````````````````````````````````````

State effects `get-Env` and `put-Env`:
 
`````indent```````````````````````````````````````
get-Envᶠⁱ : Mᶠⁱ(Env)
get-Envᶠⁱ(⟨ρ,κ,τ⟩,σ) := ({(ρ,⟨ρ,κ,τ⟩)},σ)
put-Envᶠⁱ : Env → Mᶠⁱ(1)
put-Envᶠⁱ(ρ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ',κ,τ⟩)},σ)
``````````````````````````````````````````````````

State effects `get-Store` and `put-Store`:

`````indent```````````````````````````````````````
get-Storeᶠⁱ : Mᶠⁱ(Env)
get-Storeᶠⁱ(⟨ρ,κ,τ⟩,σ) := ({(σ,⟨ρ,κ,τ⟩},σ)
put-Storeᶠⁱ : Store → Mᶠⁱ(1)
put-Storeᶠⁱ(σ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ,κ,τ⟩)},σ')
``````````````````````````````````````````````````

Nondeterminism operations:
 
`````indent```````````````````````````````````````
⟨0⟩ᶠⁱ : ∀ α, M(α)
⟨0⟩ᶠⁱ(ψ,σ) := ({}, ⊥)
_⟨+⟩_ : ∀ α, M(α) × M(α) → M α 
(m₁ ⟨+⟩ m₂)(ψ,σ) := (aψ*₁ ∪ aψ*₂,σ₁ ⊔ σ₂)  
  where (aψ*ᵢ,σᵢ) := mᵢ(ψ,σ)
``````````````````````````````````````````````````

Finally, the Galois connection for relating `Mᶠⁱ` to a state space transition over `Σᶠⁱ`:

`````indent```````````````````````````````````````
Σᶠⁱ := 𝒫(Exp × Ψᶠⁱ) × Store
γᶠⁱ : (Exp → Mᶠⁱ(Exp)) → (Σᶠⁱ → Σᶠⁱ)
γᶠⁱ(f)(eψ*,σ) := ({eψ₁₁ .. eψₙ₁  .. eψₙₘ}, σ₁ ⊔ .. ⊔ σₙ)
  where {(e₁,ψ₁) .. (eₙ,ψₙ)} := eψ*
        ({eψᵢ₁ .. eψᵢₘ},σᵢ) := f(eᵢ)(ψᵢ,σ)
αᶠⁱ  : (Σᶠⁱ → Σᶠⁱ) → (Exp → Mᶠⁱ(Exp))
αᶠⁱ(f)(e)(ψ,σ) := f({(e,ψ)},σ)
``````````````````````````````````````````````````

_Proposition: `γᶠⁱ` and `αᶠⁱ` form an isomorphism._

Like the concrete `γᶠⁱ` and `αᶠⁱ`, this implies Galois connection.

_Proposition: `Mᵖˢ α⇄γ Mᶠⁱ`._

This demonstrates that path sensitivity is more precise than flow insensitivity in a formal, language-independent setting.

We leave out the explicit definition for the flow-sensitive monad `Mᶠˢ`.
However, we will recover it through the compositional framework in Section [X][A Compositional Framework] using monad transformers.

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
bindˢ : ∀ α β, Sₜ[s](m)(α) → (α → Sₜ[s](m)(β)) → Sₜ[s](m)(β)
bindˢ(m)(f)(s) := do
  (x,s') ←ᵐ m(s)
  f(x)(s')
returnˢ : ∀ α m, α → Sₜ[s](m)(α)
returnˢ(x)(s) := returnᵐ(x,s)
``````````````````````````````````````````````````

State actions `get` and `put` expose the cell of state while interacting with the underlying monad `m`:

`````indent```````````````````````````````````````
getˢ : Sₜ[s](m)(s)
getˢ(s) := returnᵐ(s,s)
putˢ : s → Sₜ[s](m)(1)
putˢ(s')(s) := returnᵐ(1,s')
``````````````````````````````````````````````````

and the state monad transformer is able to transport nondeterminism effects from the underlying monad:

`````indent```````````````````````````````````````
⟨0⟩ : ∀ α, Sₜ[s](m)(α)
⟨0⟩(s) := ⟨0⟩ᵐ 
_⟨+⟩_ : ∀ α, Sₜ[s](m)(α) x Sₜ[s](m)(α) → Sₜ[s](m)(α)
(m₁ ⟨+⟩ m₂)(s) := m₁(s) ⟨+⟩ᵐ m₂(s) 
``````````````````````````````````````````````````

The state monad transformer was introduced by Mark P. Jones in [[X](http://web.cecs.pdx.edu/~mpj/pubs/springschool95.pdf)].

We develop a new monad transformer for nondeterminism which can compose with state in both directions.

`````indent```````````````````````````````````````
𝒫ₜ : (Type → Type) → (Type → Type)
𝒫ₜ(m)(α) := m(𝒫(α))
``````````````````````````````````````````````````

Monadic actions `bind` and `return` require that the underlying monad be a join-semilattice functor:

`````indent```````````````````````````````````````
bindᵖ : ∀ α β, 𝒫ₜ(m)(α) → (α → 𝒫ₜ(m)(β)) → 𝒫ₜ(m)(β)
bindᵖ(m)(f) := do
  {x₁ .. xₙ} ←ᵐ m
  f(x₁) ⊔ᵐ .. ⊔ᵐ f(xₙ)
returnᵖ : ∀ α, α → 𝒫ₜ(m)(α)
returnᵖ(x) := returnᵐ({x})
``````````````````````````````````````````````````

Nondterminism actions `⟨0⟩ᵐ and `⟨+⟩ᵐ interact with the join-semilattice functorality of the underlying monad `m`:

`````indent```````````````````````````````````````
⟨0⟩ᵖ : ∀ α, 𝒫ₜ(m)(α)
⟨0⟩ᵖ := ⊥ᵐ
_⟨+⟩_ : ∀ α, 𝒫ₜ(m)(α) x 𝒫ₜ(m)(α) → 𝒫ₜ(m)(α)
m₁ ⟨+⟩ᵖ m₂ := m₁ ⊔ᵐ m₂
``````````````````````````````````````````````````

and the nondeterminism monad transformer is able to transport state effects from the underlying monad:

`````indent```````````````````````````````````````
getᵖ : 𝒫ₜ(m)(s)
getᵖ = mapᵖ(λ(s).{s})(getᵐ)
putᵖ : s → 𝒫ₜ(m)(s)
putᵖ(s) = mapᵖ(λ(1).{1})(putᵐ(s))
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
mstepˢ-γ : ∀ α β m, (α → Sₜ[s](m)(β)) → (Σᵐ(α × s) → Σᵐ(β × s))
mstepˢ-γ(f) := mstepᵐ-γ(λ(a,s). f(a)(s))
``````````````````````````````````````````````````

For the nondeterminism transformer `𝒫ₜ`, mstep has two possible definitions.
One where `Σ` is `Σᵐ ∘ P`:

`````indent```````````````````````````````````````
mstepᵖ₁-γ : ∀ α β m, (α → 𝒫ₜ(m)(β)) → (Σᵐ(𝒫(α)) → Σᵐ(𝒫(β)))
mstepᵖ₁-γ(f) := mstepᵐ-γ(λ({x₁ .. xₙ}). f(x₁) ⟨+⟩ .. ⟨+⟩ f(xₙ))
``````````````````````````````````````````````````

and one where `Σ` is `P ∘ Σᵐ`:

`````indent```````````````````````````````````````
mstepᵖ₂-γ : ∀ α β m, (α → 𝒫ₜ(m)(β)) → (𝒫(Σₘ(α)) → 𝒫(Σₘ(β)))
mstepᵖ₂-γ(f)({ς₁ .. ςₙ}) := aΣP₁ ∪ .. ∪ aΣPₙ
  where 
    commuteP : ∀ α, Σᵐ(𝒫(α)) → 𝒫(Σᵐ(α))
    aΣPᵢ := commuteP-γ(mstepᵐ-γ(f)(ςᵢ)) 
``````````````````````````````````````````````````

The operation `computeP` must be defined for the underlying `Σᵐ`.
This property is true for the identiy monad, and is preserved by `Sₜ[s]` when `Σᵐ` is also a functor:

`````indent```````````````````````````````````````
commuteP-γ : ∀ α, Σᵐ(𝒫(α) × s) → 𝒫(Σᵐ(α × s))
commuteP-γ := commutePᵐ ∘ map(λ({α₁ .. αₙ},s). {(α₁,s) .. (αₙ,s)})
``````````````````````````````````````````````````

The `γ` side of commuteP is the only Galois connection mapping that loses information in the `α` direction.
Therefore, `mstepˢ` and `mstepᵖ₁` are really isomorphism transformers, and `mstepᵖ₂` is the only Galois connection transformer.

[QUESTION: should I give the definitions for the `α` maps here? -DD]

For convenience, we name the pairing of `𝒫ₜ` with `mstepᵖ₁` `FIₜ`, and with `mstepᵖ₂` `FSₜ` for flow insensitive and flow sensitive respectively.

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
