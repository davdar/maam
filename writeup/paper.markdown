# Introduction

Traditional practice in program analysis via abstract interpretation is to fix
a language (as a concrete semantics) and an abstraction (as an abstraction map,
concretization map or Galois connection) before constructing a static analyzer
that it sound with respect to both the abstraction and the concrete semantics.
Thus, each pairing of abstraction and semantics requires a one-off manual
derivation of the abstract semantics and construction of a proof of soundness.

Work has focused on endowing abstractions with knobs, levers, and dials to tune
precision and compute efficiently.  These parameters come with overloaded
meanings such as object, context, path, and heap sensitivities, or some
combination thereof.  These efforts develop families of analyses _for a
specific language_ and prove the framework sound.

But this framework approach suffers from many of the same drawbacks as the
one-off analyzers.  They are language-specific, preventing reuse of concepts
across languages and require similar re-implementations and soundness proofs.
This process is still manual, tedious, difficult and error-prone. And, changes
to the structure of the parameter-space require a completely new proof of
soundness.  And, it prevents fruitful insights and results developed in one
paradigm from being applied to others, e.g., functional to object-oriented and
_vice versa_.

We propose an automated alternative to structuring and implementing program
analysis.  Inspired by \citeauthor*{dvanhorn:Liang1995Monad}'s \emph{Monad
Transformers and Modular Interpreters} \cite{dvanhorn:Liang1995Monad}, we
propose to start with concrete interpreters written in a specific monadic
style. Changing the monad will change the interpreter from a concrete
interpreter into an abstract interpreter. As we show, classical program
abstractions can be embodied as language-independent monads.  Moreover, these
abstractions can be written as monad _transformers_, thereby allowing their
composition to achieve new forms of analysis.  We show that these monad
transformers obey the properties of \emph{Galois connections}
\cite{dvanhorn:Cousot1979Systematic} and introduce the concept of a
\emph{Galois transformer}, a monad transformer which transports (1) Galois
connections and (2) mappings to an executable transition system.

Most significantly, Galois transformers can be proved sound once and used
everywhere.  Abstract interpreters, which take the form of monad transformer
stacks coupled with a monadic interpreter, inherit the soundness properties of
each element in the stack.  This approach enables reuse of abstractions across
languages and lays the foundation for a modular metatheory of program analysis.

\paragraph{Setup}
We describe a simple language and a garbage-collecting allocating semantics as
the starting point of analysis design (Section \ref{semantics}). We then
briefly discuss three types of path and flow sensitivity and their
corresponding variations in analysis precision (Section
\ref{path-and-flow-sensitivity-in-analysis}).

\paragraph{Monadic Abstract Interpreters}
We develop an abstract interpreter for our example language as a monadic
function with parameters (Section \ref{analysis-parameters}), one of which is a
monadic effect interface combining state and nondeterminism effects (Section
\ref{the-analysis-monad}). These monadic effects, state and nondeterminism,
support arbitrary relational small-step state-machine semantics and correspond
to the state-machine components and relational nondeterminism respectively.

Interpreters written in this style can be reasoned about using various laws,
including monadic effect laws, and therefore verified correct independent of
any particular choice of parameters. Likewise, instantiations for these
parameters can be reasoned about in isolation from their instantiation. When
instantiated, our generic interpreter is capable of recovering the concrete
semantics and a family of abstract interpreters, with variations in abstract
domain, abstract garbage collection, mcfa, call-site sensitivity, object
sensitivity, and path and flow sensitivity (Section \ref{recovering-analyses}).

\paragraph{Isolating Path and Flow Sensitivity}
We give specific monads for instantiating the interpreter from Section
\ref{the-interpreter} to path-sensitive, flow-sensitive and flow-insensitive
analyses (Section \ref{varying-path-and-flow-sensitivity}). This leads to an
isolated understanding of path and flow sensitivity as mere variations in the
monad used for execution. Furthermore, these monads are language independent,
allowing one to reuse the same path and flow sensitivity machinery for any
language of interest, and compose seamlessly with other analysis parameters.

\paragraph{Galois Transformers}
To ease the construction of monads for building abstract interpreters and their
proofs of correctness, we develop a framework of Galois transformers (Section
\ref{a-compositional-monadic-framework}). Galois transformers are an extension
of monad transformers which transport (1) Galois connections and (2) mappings to
an executable transition system (Section \ref{galois-transformers-1}). Our
Galois transformer framework allows us to both execute and reason about the
correctness of an abstract interpreter piecewise for each transformer in a
stack. Galois transformers are language independent and they can be proven
correct one and for all in isolation from a particular semantics.

\paragraph{Implementation}
We have implemented our technique as a Haskell library and example client
analysis (Section \ref{implementation}). Developers are able to reuse our
language-independent framework for prototyping the design space of analysis
features for their language of choice. Our implementation is publicly available
on Hackage\footnote{
-- http://hackage.haskell.org/package/maam
http://...[redacted]...
}, Haskell's package manager.

\paragraph{Contributions}
We make the following contributions:

- A methodology for constructing monadic abstract interpreters based on
  _monadic effects_\footnote{
    This is in contrast to \citet{dvanhorn:Sergey2013Monadic} where monadic
    interpreters are constructed based on \emph{denotation functions}. See our
    Section \ref{related-work} for more details.}.
- A compositional, language-independent library for constructing monads with
  various analysis properties based on _monad transformers_.
- A compositional, language-independent proof framework for constructing Galois
  connections using _Galois transformers_, an extension of monad transformers
  which transport (1) Galois connections and (2) mappings to an executable
  transition system.
- Two new general purpose monad transformers for nondeterminism which are not
  present in any previous work on monad transformers (even outside static
  analysis literature). Although applicable to settings other than static
  analysis, these two transformers give rise naturally to variations in path
  and flow sensitivity when applied to abstract interpreters.
- An isolated understanding of path and flow sensitivity in 
  analysis as properties of the interpreter monad, which we develop
  independently of other analysis features.

# Semantics

To demonstrate our framework we design an abstract interpreter for `λIF`, a
simple applied lambda calculus shown in Figure`~\ref{SS}`{.raw}. `λIF` extends
traditional lambda calculus with integers, addition, subtraction and
conditionals. We write `[@]` as explicit abstract syntax for function
application. The state-space `Σ` for `λIF` makes allocation explicit using two
separate stores for values (`Store`) and for the stack (`KStore`).

Guided by the syntax and semantics of `λIF` defined in this section we develop
interpretation parameters in Section \ref{analysis-parameters}, a monadic
interpreter in Section \ref{the-interpreter}, and both concrete and abstract
instantiations for the interpretation parameters in Section
\ref{recovering-analyses}. The variations in path and flow sensitivity
developed in sections \ref{varying-path-and-flow-sensitivity} and
\ref{a-compositional-monadic-framework} are independent of this (or any other)
semantics.

`\begin{figure}`{.raw}
-- \vspace{-1em}
`````align````````````````````````````````````````
 i ∈  ℤ
 x ∈  Var
 a ∈  Atom    ::= i | x | [λ](x).e
 ⊕ ∈  IOp     ::= [+] | [-]
 ⊙ ∈  Op      ::= ⊕ | [@]
 e ∈  Exp     ::= a | e ⊙ e | [if0](e){e}{e}
<>
 τ ∈  Time    := ℤ
 l ∈  Addr    := Var × Time
 ρ ∈  Env     := Var ⇀ Addr
 σ ∈  Store   := Addr ⇀ Val
 c ∈  Clo     ::= ⟨[λ](x).e,ρ⟩ 
 v ∈  Val     ::= i | c
κl ∈  KAddr   := Time
κσ ∈  KStore  := KAddr ⇀ Frame × KAddr
fr ∈  Frame   ::= ⟨□ ⊙ e⟩ | ⟨v ⊙ □⟩ | ⟨[if0](□){e}{e}⟩
 ς ∈  Σ       ::= Exp × Env × Store × KAddr × KStore
``````````````````````````````````````````````````
`\caption{`{.raw} `λIF` Syntax and Concrete State Space `}`{.raw}
\label{SS} 
-- \vspace{-1em}
`\end{figure}`{.raw}

We give semantics to atomic expressions and primitive operators denotationally
through `A⟦_⟧` and `δ⟦_⟧`, and to compound expressions relationally through
`~~>`, as shown in Figure \ref{ConcreteSemantics}. We will recover these
semantics from a concrete instantiation of our generic abstract interpreter in
Section \ref{recovering-analyses}.

`\begin{figure}`{.raw}
-- \vspace{-1em}
`````indent```````````````````````````````````````
A⟦_⟧ ∈ Atom → (Env × Store ⇀ Val)
A⟦i⟧(ρ,σ) := i
A⟦x⟧(ρ,σ) := σ(ρ(x))
A⟦[λ](x).e⟧(ρ,σ) := ⟨[λ](x).e,ρ⟩ 
δ⟦_⟧ ∈ IOp → (ℤ × ℤ → ℤ)
δ⟦[+]⟧(i₁,i₂) := i₁ + i₂
δ⟦[-]⟧(i₁,i₂) := i₁ - i₂
<>
_[~~>]_ ∈ 𝒫(Σ × Σ)
⟨e₁ ⊙ e₂,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e₁,ρ,σ,τ,κσ',τ+1⟩ where 
  κσ' := κσ[τ ↦ (⟨□ ⊙ e₂⟩,κl)]
⟨a,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e,ρ,σ,τ,κσ',τ+1⟩ where
  ALIGNED< & (⟨□ ⊙ e⟩,κl') := κσ(κl) || & κσ' := κσ[τ ↦ (⟨A⟦a⟧(ρ,σ) ⊙ □⟩,κl')] ALIGNED>
⟨a,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e,ρ'',σ',κl',κσ,τ+1⟩ where 
  ALIGNED< & (⟨⟨[λ](x).e,ρ'⟩ [@] □⟩,κl') := κσ(κl) || & ρ'' := ρ'[x ↦ (x,τ)] || & σ' := σ[(x,τ) ↦ A⟦a⟧(ρ,σ)] ALIGNED>
⟨i₂,ρ,σ,κl,κσ,τ⟩ ~~> ⟨i,ρ,σ,κl',κσ,τ+1⟩ where 
  ALIGNED< & (⟨i₁ ⊕ □⟩,κl') := κσ(κl) || & i := δ⟦⊕⟧(i₁,i₂) ALIGNED>
⟨i,ρ,σ,κl,κσ,τ⟩ ~~> ⟨e,ρ,σ,κl',κσ,τ+1⟩ where 
  ALIGNED< & (⟨[if0](□){e₁}{e₂}⟩,κl') := κσ(κl) || & e := e₁ when i = 0 ; e₂ when i ≠ 0 ALIGNED>
``````````````````````````````````````````````````
\caption{Concrete Semantics}
\label{ConcreteSemantics} 
-- \vspace{-1em}
`\end{figure}`{.raw}

Our abstract interpreter will support abstract garbage
collection`~\cite{dvanhorn:Might:2006:GammaCFA}`{.raw}, the concrete analogue
of which is just standard garbage collection. We include abstract garbage
collection for two reasons. First, it is one of the few techniques that results
in both performance _and_ precision improvements for abstract interpreters.
Second, later we will systematically recover both concrete and abstract garbage
collectors through a single monadic garbage collector.

Garbage collection is defined using a reachability function `R` which computes
transitively reachable address in `σ`:
`````indent```````````````````````````````````````
R ∈ Store × Env × Exp → 𝒫(Addr)
R(σ,ρ,e) := μ(X). 
  X ∪ R₀(ρ,e) ∪ {l' | l' ∈ R-Val(σ(l)) ; l ∈ X}
``````````````````````````````````````````````````
We write `μ(X). f(X)` as the least-fixed-point of a function `f`. This
definition uses two helper functions: `R₀` for computing the initial reachable
set and `R-Val` for computing addresses reachable from values.
`````indent```````````````````````````````````````
R₀ ∈ Env × Exp → 𝒫(Addr)
R₀(ρ,e) := {ρ(x) | x ∈ FV(e)}
R-Val ∈ Val → 𝒫(Addr)
R-Val(i) := {}
R-Val(⟨[λ](x).e,ρ⟩) := {ρ(y) | y ∈ FV([λ](x).e)}
``````````````````````````````````````````````````
We omit the definition of `FV`, which is the standard recursive definition for
computing free variables of an expression. Analogously, `KR` is the set of
transitively reachable stack-frame addresses in
`κσ`:
`````indent```````````````````````````````````````
KR ∈ KStore × KAddr → 𝒫(KAddr)
KR(κσ,κl₀) := μ(X). X ∪ {κl₀} ∪ {π₂(κσ(κl)) | κl ∈ X}
``````````````````````````````````````````````````

Our final semantics is given via the step relation `_[~~>⸢gc⸣]_` which
nondeterministically either takes a semantic step or performs garbage
collection.
`````indent```````````````````````````````````````
_[~~>⸢gc⸣]_ ∈ 𝒫(Σ × Σ)
ς ~~>⸢gc⸣ ς' where ς ~~> ς'
⟨e,ρ,σ,κl,κσ,τ⟩ ~~>⸢gc⸣ ⟨e,ρ,σ',κl,κσ',τ⟩ where 
  ALIGNED< & σ' := {l ↦ σ(l) | l ∈ R(σ,ρ,e)} || & κσ' := {κl ↦ κσ(κl) | κl ∈ KR(κσ,κl)} ALIGNED>
``````````````````````````````````````````````````
An execution of the semantics is the least-fixed-point of a collecting
semantics:
`````indent```````````````````````````````````````
Analysis := μ(X).X ∪ {ς₀} ∪ { ς' | ς ~~>⸢gc⸣ ς' ; ς ∈ X }
``````````````````````````````````````````````````
where `ς₀` is the injection of the initial program `e₀`:
`````indent```````````````````````````````````````
ς₀ := ⟨e₀,⊥,⊥,0,⊥,1⟩
``````````````````````````````````````````````````
The analyses we present in this paper will be proven correct in Section
\ref{recovering-analyses} by establishing a Galois connection with this
concrete collecting semantics.

# Path and Flow Sensitivity in Analysis

In this paper we identify three specific variants of path and flow sensitivity
in analysis: path-sensitive, flow-sensitive and flow-insensitive. Our framework
exposes the essence of path and flow sensitivity through a monadic effect
interface in Section \ref{analysis-parameters}, and we recover each of these
variations through specific monad instances in Sections
\ref{varying-path-and-flow-sensitivity} and
\ref{a-compositional-monadic-framework}.

Consider a combination of if-statements in our example language `λIF` (extended
with let-bindings) where an analysis cannot determine the value of `N`:
`\small\begin{alignat*}{3}`{.raw}
`````rawmacro````````````````````````````````````
& 1: [let] x :=           && ␣␣[in]                 \\
& ␣␣2: [if0](N){          && ␣␣5: [let] y :=        \\
& ␣␣␣␣3: [if0](N){1}{2}   && ␣␣␣␣6: [if0](N){5}{6}  \\
& ␣␣} [else] {            && ␣␣[in]                 \\
& ␣␣␣␣4: [if0](N){3}{4}   && ␣␣7: [exit](x, y)      \\
& ␣␣}                     && \\
``````````````````````````````````````````````````
`\end{alignat*}\normalsize`{.raw}
\paragraph{Path-Sensitive}
A path-sensitive analysis tracks both data and control flow precisely. At
program points 3 and 4 the analysis considers separate worlds:
`````align````````````````````````````````````````
3: {N=0} \quad 4: {N≠0}
``````````````````````````````````````````````````
At program points 5 and 6 the analysis continues in two separate, precise
worlds:
`````align````````````````````````````````````````
5,6: {N=0,, x=1} {N≠0,, x=4}
``````````````````````````````````````````````````
At program point 7 the analysis correctly corrolates the values for `x` and
`y`:
`````align````````````````````````````````````````
7: {N=0,, x=1,, y=5} {N≠0,, x=4,, y=6}
``````````````````````````````````````````````````

\paragraph{Flow-Sensitive}
A flow-sensitive analysis collects a _single_ set of facts for each
variable _at each program point_. At program points 3 and 4, the analysis
considers separate worlds:
`````align````````````````````````````````````````
3: {N=0} \quad 4: {N≠0}
``````````````````````````````````````````````````
Each nested if-statement then evaluates only one side of the branch, resulting
in values `1` and `4`. At program points 5 and 6 the analysis is only allowed
one set of facts, so it must merge the possible values that `x` and `N` could
take:
`````align````````````````````````````````````````
5,6: {N∈ℤ,, x∈{1,4}}
``````````````````````````````````````````````````
The analysis then explores both branches at program point 6 resulting in no
corrolation between values for `x` and `y`:
`````align````````````````````````````````````````
7: {N∈ℤ,, x∈{1,4},, y∈{5,6}}
``````````````````````````````````````````````````

\paragraph{Flow-Insensitive}
A flow-insensitive analysis collects a _single_ set of facts about each
variable which must hold true _for the entire program_. Because the value of
`N` is unknown at _some_ point in the program, the value of `x` must consider
both branches of the nested if-statement. This results in the global set of
facts giving four values to `x`.
`````align````````````````````````````````````````
{N∈ℤ,, x∈{1,2,3,4},, y∈{5,6}}
``````````````````````````````````````````````````

In our framework we capture the variation of path and flow sensitivity as a
purely orthogonal parameter to the abstract interpreter. Path and flow
sensitivity will then compose seamlessly with choices of call-site sensitivity,
object sensitivity, abstract garbage collection, mcfa a la
\citet{dvanhorn:Might2010Resolving}, shape analysis, abstract domain, etc. Most
importantly, we empower the analysis designer to compartmentalize the path and
flow sensitivity of each component in the abstract state space independently.
Constructing an analysis which is flow-sensitive in the data-store and
path-sensitive in the stack-store is just as easy as constructing a single path
or flow sensitivity across the board, and one can alternate between them for
free.

# Analysis Parameters

Before writing an abstract interpreter we first design its parameters. The
interpreter, which we develop in Section \ref{the-interpreter}, will be
designed such that variations in these parameters will recover both concrete
and a family of abstract interpreters, which we show in Section
\ref{recovering-analyses}. To do this we extend the ideas developed in
\citet{davdar:van-horn:2010:aam} with a new parameter for path and flow
sensitivity. 

There will be three parameters to our abstract interpreter, one of which is
novel in this work:

1. The monad, novel in this work, captures the state and control effects of the
   interpreter and gives rise to path and flow sensitivity.
2. The abstract domain, which for this language is merely an abstraction for
   integers.
3. Abstract Time, capturing call-site and object sensitivities.

We place each of these parameters behind an abstract interface and leave their
implementations opaque when defining the monadic interpreter in Section
\ref{the-interpreter}. Each of these parameters come with reasoning principles.
These principles allow us to reason about the correctness of the generic
interpreter independent of a particular instantiation of the parameters. The
goal is to factor as much of the proof effort into what we can say about the
generic interpreter independent of parameter instantiation. Then, an
instantiation of the interpreter need only justify that each parameter meets
its local interface.

## The Analysis Monad

The monad for the interpreter captures the _effects_ of interpretation. There
are two effects in the interpreter: state and nondeterminism. The state effect
will mediate how the interpreter interacts with state cells in the state space:
`Env`, `Store`, `KAddr` and `KStore`. The nondeterminism effect will mediate
branching in the execution of the interpreter. One of our results is that path
and flow sensitivity can be recovered by altering how these effects interact in
the monad.

We use monadic state and nondeterminism effects to abstract over arbitrary
_relational small-step state-machine semantics_. State effects correspond to
the components of the state-machine and nondeterminism effects correspond to
potential nondeterminism in the relation's definition.

We briefly review monad, state and nondeterminism operators and their laws. For
more details about monad transformers and monad laws we refer the reader to
\cite{dvanhorn:Liang1995Monad}.

\paragraph{Monadic Sequencing}
A type operator `M` is a monad if it supports `bind`, a sequencing operator,
and its unit `return`.
`````align```````````````````````````````````````` 
M        : Type → Type
bind     : ∀ α β, M(α) → (α → M(β)) → M(β)
return   : ∀ α, α → M(α)
``````````````````````````````````````````````````
We use monad laws (left and right units, and associativity) to reason about the
interpreter in the absence of a particular implementation of `bind` and
`return`. We use semicolon notation as syntactic sugar for `bind`; for example,
`a ← m ; k(a)` is sugar for `bind(m)(k)`. We replace semicolons with line
breaks headed by a `do` command for multiline monadic definitions.

\paragraph{State Effect}
A type operator `M` supports the monadic state effect for a type `s` if it
supports `get` and `put` actions over `s`.
`\small\begin{alignat*}{4}`{.raw}
`````rawmacro``````````````````````````````````````
  M & : Type → Type & ␣␣get & : M(s)       \\
  s & : Type        & ␣␣put & : s → M(1)
`````````````````````````````````````````````````
`\end{alignat*}\normalsize`{.raw}
We use the state monad laws (get-get, get-put, put-get, put-put) to reason
about state effects.

\paragraph{Nondeterminism Effect}
A type operator `M` support the monadic nondeterminism effect if it supports an
alternation operator `⟨+⟩` and its unit `mzero`.
`````align```````````````````````````````````````` 
M        : Type → Type
_[⟨+⟩]_  : ∀ α, M(α) × M(α) → M(α)
mzero    : ∀ α, M(α)
``````````````````````````````````````````````````
Nondeterminism laws state that `M(α)` must have a join-semilattice structure,
that `mzero` be a zero for `bind`, and that `bind` distributes through `⟨+⟩`.

\paragraph{Monad Examples}
The state monad `Stateₛ(α)` is defined as `s → (α × s)` and supports monadic
sequencing (`bind` and `return`) and state effects (`get` and `put`). The
nondeterminism monad `Nondet(α)` is defined as `𝒫(α)` and supports monadic
sequencing (`bind` and `return`) and nondeterminism effects (`_[⟨+⟩]_` and
`mzero`).

Our interpreter will be defined up to this effect interface and avoid
referencing an explicit configuration `ς` or explicit collections of results.
This level of indirection will then be exploited in Section
\ref{varying-path-and-flow-sensitivity}, where different monads will meet the
same effect interface but yield different analysis properties.

## The Abstract Domain

The abstract domain is the `Val` type in the semantics. To parameterize over
the abstract domain we make `Val` opaque, but require that it support various
operations.

`Val` must be a join-semilattice with `⊥` and `⊔` respecting the usual
laws. We require `Val` to be a join-semilattice so it can be merged in updates
to `Store` to preserve soundness. 
`````align````````````````````````````````````````
⊥ : Val  ␣␣_[⊔]_ : Val × Val → Val
``````````````````````````````````````````````````

`Val` must also support conversions to and from concrete values. These
conversions take the form of introduction and elimination rules. Introduction
rules inject concrete values into abstract values. Elimination rules project
abstract values into a _finite_ set of concrete observations. For example, we
do not require that abstract values support elimination to integers, only the
finite observation of comparison with zero.
`````align````````````````````````````````````````
int-I  : ℤ → Val    ␣␣int-if0-E  : Val → 𝒫(Bool)
clo-I  : Clo → Val      ␣␣clo-E  : Val → 𝒫(Clo)
``````````````````````````````````````````````````

The laws for the introduction and elmination rules induce a Galois connection
between `𝒫(ℤ)` and `Val`:
`````align````````````````````````````````````````
                                    {true}   ⊑ int-if0-E(int-I(i)) if i = 0
                                    {false}  ⊑ int-if0-E(int-I(i)) if i ≠ 0
 ⨆⸤⸤b ∈ int-if0-E(v) || i ∈ θ(b)⸥⸥ int-I(i)  ⊑ v
where ALIGNED< θ(true) || θ(false) ALIGNED>  ALIGNED< & := {0} || & := {i | i ∈ ℤ ; i ≠ 0} ALIGNED>
``````````````````````````````````````````````````
Closures must follow similar laws, inducing a Galois connection between
`𝒫(Clo)` and `Val`:
`````align````````````````````````````````````````
                       {c}  ⊑ clo-E(cloI(c))
⨆⸤⸤c ∈ clo-E(v)⸥⸥ clo-I(c)  ⊑ v
``````````````````````````````````````````````````
Finally, `δ` must be sound and complete w.r.t. the Galois connection between
concrete values and `Val`:
`````align````````````````````````````````````````
                                                        int-I(i₁ + i₂)  ⊑ δ⟦[+]⟧(int-I(i₁),int-I(i₂))
                                                        int-I(i₁ - i₂)  ⊑ δ⟦[-]⟧(int-I(i₁),int-I(i₂))
⨆⸤⸤b₁ ∈ int-if0-E(v₁) || b₂ ∈ int-if0-E(v₂) || i ∈ θ(b₁,b₂)⸥⸥ int-I(i)  ⊑ δ⟦⊙⟧(v₁,v₂) 
where ALIGNED< θ( true , true ) || θ( true , false ) || θ( false , true ) || θ( false , false ) ALIGNED>  ALIGNED< & := {0} || & := {i | i ∈ ℤ ; i ≠ 0 } || & := {i | i ∈ ℤ ; i ≠ 0} || & := ℤ ALIGNED>
``````````````````````````````````````````````````

Supporting additional primitive types like booleans, lists, or arbitrary
inductive datatypes is analogous. Introduction functions inject the type into
`Val` and elimination functions project a finite set of discrete observations.
Introduction, elimination and `δ` operators must all be sound and complete
following a Galois connection discipline.

## Abstract Time 

The interface for abstract time is familiar from
\citet{davdar:van-horn:2010:aam} (AAM), which introduces abstract time as a
single parameter to control various forms of context sensitivity, and
\citet{dvanhorn:Smaragdakis2011Pick}, which instantiates the parameter to
achieve both call-site and object sensitivity. We only demonstrate call-site
sensitivity in this presentation, but our language-independent library supports
object sensitivity, the implementation of which is a straightforward
application of \citet{dvanhorn:Smaragdakis2011Pick}.
`````align````````````````````````````````````````
Time : Type ␣␣ tick : Exp × KAddr × Time → Time
``````````````````````````````````````````````````
Remarkably, we need not state laws for `tick`. The interpreter will merge
values which reside at the same address to preserve soundness. Therefore, any
supplied implementations of `tick` is valid from a soundness perspective.
However, different choices in `tick` will yield different tradoffs in precision
and performance of the abstract interpreter.

# The Interpreter

We now present a monadic interpreter for `λIF` parameterized over `M`, `Val`
and `Time` from Section \ref{analysis-parameters}. We instantiate these
parameters to obtain an analysis in Section \ref{recovering-analyses}.

First we implement `A⟦_⟧` as a _monadic_ denotation for atomic expressions. The
monadic `A⟦_⟧` is a straightforward translation of the `A⟦_⟧` shown in Figure
\ref{ConcreteSemantics} from a pure function to a monadic function with state
effects.
`````indent```````````````````````````````````````
A⟦_⟧ ∈ Atom → M(Val)
A⟦i⟧ := return(int-I(i))
A⟦x⟧ := do
  ρ ← get-Env
  σ ← get-Store
  if x ∈ ρ then return(σ(ρ(x))) else return(⊥)
A⟦[λ](x).e⟧ := do
  ρ ← get-Env
  return(clo-I(⟨[λ](x).e,ρ⟩))
``````````````````````````````````````````````````
`get-Env` and `get-Store` are primitive operations for monadic state. `clo-I`
comes from the interface for `Val`.

Next we implement `step`, a _monadic_ small-step _function_ for compound
expressions, shown in Figure \ref{InterpreterStep}. The monadic `step` is a
straightforward translation of the `step` shown in Figure
\ref{ConcreteSemantics} from a relation to a monadic function with state and
nondeterminism effects.

`\begin{figure}`{.raw}
-- \vspace{-1em}
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
    ⟨v' [@] □⟩ → do
      ⟨[λ](x).e,ρ'⟩ ← ↑ₚ(clo-E(v'))
      τ ← get-Time
      σ ← get-Store
      put-Env(ρ'[x ↦ (x,τ)])
      put-Store(σ ⊔ [(x,τ) ↦ {v}])
      return(e)
    ⟨v' ⊕ □⟩ → do
      return(δ⟦⊕⟧(v',v))
    ⟨[if0](□){e₁}{e₂}⟩ → do
      b ← ↑ₚ(int-if0-E(v))
      if(b) then return(e₁) else return(e₂)
``````````````````````````````````````````````````
\caption{Monadic step function and garbage collection}
\label{InterpreterStep} 
-- \vspace{-1em}
`\end{figure}`{.raw}

`step` uses helper functions `push` and `pop` for manipulating stack frames,
`↑ₚ` for lifting values from `𝒫` into `M`, and a monadic version of `tick`
called `tickM`, each of which are shown in Figure \ref{InterpreterHelpers}. The
interpreter looks deterministic, however the nondeterminism is abstracted away
behind `↑ₚ` and monadic bind `x ← e₁ ; e₂`.

We also implement abstract garbage collection in a general away using the
monadic effect interface:
`````indent```````````````````````````````````````
gc : Exp → M(1)
gc(e) := do
  ρ ← get-Env
  σ ← get-Store
  κσ ← get-KStore
  put-Store({l ↦ σ(l) | l ∈ R(σ,ρ,e))
  put-KStore({κl ↦ κσ(κl) | κl ∈ KR(κσ,κl)})
``````````````````````````````````````````````````
where `R` and `KR` are as defined in Section \ref{semantics}. Again, this is a
straightforward translation from a pure function to a monadic function with
state effects.

\paragraph{Preserving Soundness}
In generalizing the semantics to account for nondeterminism, updates to both
the data-store and stack-store must merge values rather than performing a
strong update. This is because we place no restriction on the semantics for
`Time` and therefore must preserve soundness in the presence of reused
addresses.

To support `⊔` for stores (in observation of soundness) we modify our
definitions of `Store` and `KStore`.
`````indent```````````````````````````````````````
σ  ∈ Store  : Addr → Val
κσ ∈ KStore : KAddr → 𝒫(Frame × KAddr)
``````````````````````````````````````````````````

`\begin{figure}`{.raw}
-- \vspace{-1em}
`````indent```````````````````````````````````````
↑ₚ : ∀ α, 𝒫(α) → M(α)
↑ₚ({a₁ .. aₙ}) := return(a₁) ⟨+⟩ .. ⟨+⟩ return(aₙ)
push : Frame → M(1)
push(fr) := do
  κl ← get-KAddr
  κσ ← get-KStore
  κl' ← get-Time
  put-KStore(κσ ⊔ [κl' ↦ {fr∷κl}])
  put-KAddr(κl')
pop : M(Frame)
pop := do
  κl ← get-KAddr
  κσ ← get-KStore
  fr∷κl' ← ↑ₚ(κσ(κl))
  put-KAddr(κl')
  return(fr)
tickM : Exp → M(1)
tickM(e) = do
  τ ← get-Time
  κl ← get-KAddr
  put-Time(tick(e,κl,τ))
``````````````````````````````````````````````````
\caption{Monadic step function and garbage collection}
\label{InterpreterHelpers} 
-- \vspace{-1em}
`\end{figure}`{.raw}

\paragraph{Execution}
In the concrete semantics, execution takes the form of a least-fixed-point
computation over a collecting semantics. This in general requires a
join-semilattice structure for some `Σ` and a transition function `Σ → Σ`.
However, we no longer have a function `Σ → Σ`; we have a monadic function `Exp
→ M(Exp)` which does not immediately admit a least-fixed-point iteration to
execute the analysis.

To solve this we require that monadic actions `Exp → M(Exp)` form a Galois
connection with a transition system `Σ → Σ`. This Galois connection serves two
purposes. First, it allows us to implement the analysis by converting our
interpreter to the transition system `Σ → Σ` through `γ`. Second, this Galois
connection serves to _transport other Galois connections_ as part of our
correctness framework. This will allow us to construct Galois connections
between monads `m₁ α⇄γ m₂` and derive Galois connections between transition
systems `Σ₁ α⇄γ Σ₂` for free.

A collecting-semantics execution of our interpreter is then defined as the
least-fixed-point iteration of `step` transported through the Galois
connection:
`````indent```````````````````````````````````````
Analysis := μ(X). X ⊔ ς₀ ⊔ γ(step)(X)
``````````````````````````````````````````````````
where `ς₀` is the injection of the initial program `e₀` into `Σ` and `γ` has
type `(Exp → M(Exp)) → (Σ → Σ)`.

# Recovering Analyses

In Section \ref{the-interpreter} we defined a monadic interpreter with the
uninstantiated parameters from Section \ref{analysis-parameters}: `M`, `Val`
and `Time`. To recover a concrete interpreter we instantiate these parameters
to concrete components `CM`, `CVal` and `CTime`, and to recover an abstract
interpreter we instantiate them to abstract components `AM`, `AVal` and
`ATime`. The soundness of the final implementation is thus factored into two
steps:

1. Proving the parameterized monadic interpreter correct for any instantiation
   of `M`, `Val` and `Time`.
2. Constructing Galois connections `CM α⇄γ AM`, `CVal α⇄γ AVal` and `CTime α⇄γ
   ATime` piecewise.

The key benefit of our approach is that (1) can be proved once against _all_
instantiations of `M`, `Val` and `Time` using the reasoning principles
established in Section \ref{analysis-parameters}, greatly simplifying the proof
burden when choosing different abstract components in (2).

## Recovering a Concrete Interpreter

For the concrete value space we instantiate `Val` to `CVal`:
`````indent```````````````````````````````````````
v ∈ CVal := 𝒫(CClo + ℤ)
``````````````````````````````````````````````````
The concrete value space `CVal` has straightforward introduction and
elimination rules:
`````indent```````````````````````````````````````
int-I : ℤ → CVal
int-I(i) := {i}
int-if0-E : CVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | ∃ i ∈ v s.t. i ≠ 0 }
``````````````````````````````````````````````````
and a straightforward concrete `δ`:
`````indent```````````````````````````````````````
δ⟦_⟧ : IOp → CVal × CVal → CVal
δ⟦[+]⟧(v₁,v₂) := { i₁ + i₂ | i₁ ∈ v₁ ; i₂ ∈ v₂ }
δ⟦[-]⟧(v₁,v₂) := { i₁ - i₂ | i₁ ∈ v₁ ; i₂ ∈ v₂ }
``````````````````````````````````````````````````
`\begin{proposition}`{.raw}
`CVal` satisfies the abstract domain laws shown in Section
\ref{the-abstract-domain}.
`\end{proposition}`{.raw}

Concrete time `CTime` captures program contours as a product of `Exp` and
`CKAddr`:
`````indent```````````````````````````````````````
τ ∈ CTime := (Exp × KAddr)⸢*⸣
``````````````````````````````````````````````````
and `tick` is just a cons operator:
`````indent```````````````````````````````````````
tick : Exp × CKAddr × CTime → CTime
tick (e,κl,τ) := (e,κl)∷τ
``````````````````````````````````````````````````

For the concrete monad we instantiate `M` to a path-sensitive `CM` which
contains a powerset of concrete state space components.
`````indent```````````````````````````````````````
ψ ∈ Ψ := CEnv × CStore × CKAddr × CKStore × CTime
m ∈ CM(α) := Ψ → 𝒫(α × Ψ)
``````````````````````````````````````````````````
Monadic operators `bind` and `return` encapsulate both state-passing and
set-flattening:
`````indent```````````````````````````````````````
bind : ∀ α, CM(α) → (α → CM(β)) → CM(β)
bind(m)(f)(ψ) := 
  {(y,ψ'') | (y,ψ'') ∈ f(a)(ψ') ; (a,ψ') ∈ m(ψ)}
return : ∀ α, α → CM(α)
return(a)(ψ) := {(a,ψ)}
``````````````````````````````````````````````````
State effects return singleton sets:
`````indent```````````````````````````````````````
get-Env : CM(CEnv)
get-Env(⟨ρ,σ,κ,τ⟩) := {(ρ,⟨ρ,σ,κ,τ⟩)}
put-Env : CEnv → 𝒫(1)
put-Env(ρ')(⟨ρ,σ,κ,τ⟩) := {(1,⟨ρ',σ,κ,τ⟩)}
``````````````````````````````````````````````````
Nondeterminism effects are implemented with set union:
`````indent```````````````````````````````````````
mzero : ∀ α, CM(α)
mzero(ψ) := {}
_[⟨+⟩]_ : ∀ α, CM(α) × CM(α) → CM(α)
(m₁ ⟨+⟩ m₂)(ψ) := m₁(ψ) ∪ m₂(ψ)
``````````````````````````````````````````````````
`\begin{proposition}`{.raw}
`CM` satisfies monad, state, and nondeterminism laws shown in Section
\ref{the-analysis-monad}.
`\end{proposition}`{.raw}

Finally, we must establish a Galois connection between `Exp → CM(Exp)` and `CΣ
→ CΣ` for some choice of `CΣ`. For the path-sensitive monad `CM`, `CΣ` is
defined:
`````indent```````````````````````````````````````
CΣ := 𝒫(Exp × Ψ)
``````````````````````````````````````````````````
The Galois connection between `CM` and `CΣ` is similar to the definition of
`bind`:
`````indent```````````````````````````````````````
γ : (Exp → CM(Exp)) → (CΣ → CΣ)
γ(f)(eψ⸢*⸣) := {(e,ψ') | (e,ψ') ∈ f(e)(ψ) ; (e,ψ) ∈ eψ⸢*⸣}
α : (CΣ → CΣ) → (Exp → CM(Exp))
α(f)(e)(ψ) := f({(e,ψ)})
``````````````````````````````````````````````````
The injection `ς₀` for a program `e₀` is `ς₀ := {⟨e,⊥,⊥,∙,⊥,∙⟩}`.
`\begin{proposition}`{.raw}
`γ` and `α` form a Galois connection.
`\end{proposition}`{.raw}

## Recovering an Abstract Interpreter

We pick a simple abstraction for integers, `{[-],0,[+]}`, although our
technique scales seamlessly to other abstract value domains.
`````indent```````````````````````````````````````
AVal := 𝒫(AClo + {[-],0,[+]})
``````````````````````````````````````````````````
Introduction and elimination for `AVal` are defined:
`````indent```````````````````````````````````````
int-I : ℤ → AVal
int-I(i) := {[-]} if i < 0
int-I(i) := {0}   if i = 0
int-I(i) := {[+]} if i > 0
int-if0-E : AVal → 𝒫(Bool)
int-if0-E(v) := { true | 0 ∈ v } ∪ { false | [-] ∈ v ∨ [+] ∈ v }
``````````````````````````````````````````````````
Introduction and elimination for `AClo` is identical to the concrete domain.

The abstract `δ` operator is defined:
`````indent```````````````````````````````````````
δ : IOp → AVal × AVal → AVal 
δ⟦[+]⟧(v₁,v₂) := 
   { i         | 0 ∈ v₁ ∧ i ∈ v₂ }
  ∪ { i         | i ∈ v₁ ∧ 0 ∈ v₂ }
  ∪ { [+]       | [+] ∈ v₁ ∧ [+] ∈ v₂ } 
  ∪ { [-]       | [-] ∈ v₁ ∧ [-] ∈ v₂ } 
  ∪ { [-],0,[+] | [+] ∈ v₁ ∧ [-] ∈ v₂ }
  ∪ { [-],0,[+] | [-] ∈ v₁ ∧ [+] ∈ v₂ }
``````````````````````````````````````````````````
The definition for `δ⟦[-]⟧(v₁,v₂)` is analogous.
`\begin{proposition}`{.raw}
`AVal` satisfies the abstract domain laws shown in
Section`~\ref{the-abstract-domain}`{.raw}.
`\end{proposition}`{.raw}
`\begin{proposition}`{.raw}
`CVal α⇄γ AVal` and both concrete and abstract definitions for `int-I`,
`int-if0-E` and `δ` are ordered `⊑` respectively through the Galois connection.
`\end{proposition}`{.raw}

Next we abstract `Time` to `ATime` as the finite domain of k-truncated lists of
execution contexts:
`````indent```````````````````````````````````````
ATime := (Exp × AKAddr)⋆ₖ
``````````````````````````````````````````````````
The `tick` operator becomes cons followed by k-truncation, which restricts the
list to the first-k elements:
`````indent```````````````````````````````````````
tick : Exp × AKAddr × ATime → ATime
tick(e,κl,τ) = ⌊(e,κl)∷τ⌋ₖ
``````````````````````````````````````````````````
This abstraction for time yields k-call-site sensitivity, or a kCFA analysis.
`\begin{proposition}`{.raw}
`CTime α⇄γ ATime`, and both concrete and abstract definitions for `tick` are
ordered `⊑` through the Galois connection.
`\end{proposition}`{.raw}

The monad `AM` need not change in implementation from `CM`; they are identical
up the choice of `Ψ`.
`````indent```````````````````````````````````````
ψ ∈ Ψ := AEnv × AStore × AKAddr × AKStore × ATime
``````````````````````````````````````````````````
The resulting state space `AΣ` is finite and its least-fixed-point iteration
will give a sound and computable analysis.

# Varying Path and Flow Sensitivity

Sections \ref{the-interpreter} and \ref{recovering-analyses} describe the
construction of a path-sensitive analysis using our framework. In this section
we show an alternate definition for `AM` which yields a flow-insensitive
analysis. Section \ref{a-compositional-monadic-framework} will generalize the
definitions from this section into compositional components (monad
transformers) in addition to introducing another definition for `AM` which
yields a flow-sensitive analysis.

Before going into the details of the flow-insensitive monad, we wish to build
intuition regarding what one would expect from such a development. 

Recall the path-sensitive monad `AM` and its state space `AΣ` from section
\ref{recovering-analyses}:
`````indent```````````````````````````````````````
AM(Exp) := Ψ × AStore → 𝒫(Exp × Ψ × AStore)
AΣ(Exp) := 𝒫(Exp × Ψ × AStore)
``````````````````````````````````````````````````
where `Ψ := AEnv × AKAddr × AKStore × ATime`. This is path-sensitive because
`AΣ(Exp)` can represent arbirary _relations_ between `(Exp × Ψ)` and `AStore`.

As discussed in Section \ref{path-and-flow-sensitivity-in-analysis}, a flow-sensitive
analysis will give a single set of facts per program point. This results in the
following monad `AM⸢fs⸣` and state space `AΣ⸢fs⸣` which encode _finite maps_ to
`AStore` rather than relations:
`````indent```````````````````````````````````````
AM⸢fs⸣(Exp) := Ψ × AStore → [(Exp × Ψ) ↦ AStore]
AΣ⸢fs⸣(Exp) := [(Exp × Ψ) ↦ AStore]
``````````````````````````````````````````````````
where `[α ↦ s]` is notation for a finite map from `α` to `s`.

Finally, a flow-insensitive analysis contains a single global set of facts,
which is represented by pulling `AStore` out of the powerset:
`````indent```````````````````````````````````````
AM⸢fi⸣(Exp) := Ψ × AStore → 𝒫(Exp × Ψ) × AStore
AΣ⸢fi⸣(Exp) := 𝒫(Exp × Ψ) × AStore
``````````````````````````````````````````````````

These three resulting structures, `AΣ`, `AΣ⸢fs⸣` and `AΣ⸢fi⸣`, capture the
essence of path-sensitive, flow-sensitive and flow-insensitive iteration, and
arise naturally from `AM`, `AM⸢fs⸣` and `AM⸢fi⸣`, which each have monadic
structure. We only describe `AM⸢fi⸣` directly in this section; more
compositional versions of each of these monads are described in Section
\ref{a-compositional-monadic-framework}, from which `AΣ⸢fs⸣` and `AΣ⸢fi⸣` can
be recovered.

## Flow Insensitive Monad

For `AM⸢fi⸣` the monad operator `bind` performs the store merging needed to
capture a flow-insensitive analysis.
`````indent```````````````````````````````````````
bind : ∀ α β, AM⸢fi⸣(α) → (α → AM⸢fi⸣(β)) → AM⸢fi⸣(β)
bind(m)(f)(ψ,σ) := 
  ({bs⸤11⸥ .. bs⸤1m₁⸥ .. bs⸤n1⸥ .. bs⸤nmₙ⸥},σ₁ ⊔ .. ⊔ σₙ) where
    ({(a₁,ψ₁) .. (aₙ,ψₙ)},σ') := m(ψ,σ)
    ({bψ⸤i1⸥ .. bψ⸤imᵢ⸥},σᵢ) := f(aᵢ)(ψᵢ,σ')
``````````````````````````````````````````````````
The unit for `bind` returns one nondeterminism branch and a single global
store:
`````indent```````````````````````````````````````
return : ∀ α, α → AM⸢fi⸣(α)
return(a)(ψ,σ) := ({a,ψ},σ)
``````````````````````````````````````````````````

State effects `get-Env` and `put-Env` are also straightforward, returning one
branch of nondeterminism:
`````indent```````````````````````````````````````
get-Env : AM⸢fi⸣(AEnv)
get-Env(⟨ρ,κ,τ⟩,σ) := ({(ρ,⟨ρ,κ,τ⟩)},σ)
put-Env : AEnv → AM⸢fi⸣(1)
put-Env(ρ')(⟨ρ,κ,τ⟩,σ) := ({(1,⟨ρ',κ,τ⟩)},σ)
``````````````````````````````````````````````````
State effects `get-Store` and `put-Store` are analogous to `get-Env` and
`put-Env`.

Nondeterminism operations will union the powerset and join the store pairwise:
`````indent```````````````````````````````````````
mzero : ∀ α, M(α)
mzero(ψ,σ) := ({}, ⊥)
_[⟨+⟩]_ : ∀ α, M(α) × M(α) → M α 
(m₁ ⟨+⟩ m₂)(ψ,σ) := (aψ⸢*⸣₁ ∪ aψ⸢*⸣₂,σ₁ ⊔ σ₂) where 
  (aψ⸢*⸣ᵢ,σᵢ) := mᵢ(ψ,σ)
``````````````````````````````````````````````````

Finally, the Galois connection relating `AM⸢fi⸣` to a state space transition over
`AΣ⸢fi⸣` must also compute set unions and store joins pairwise:
`````indent```````````````````````````````````````
AΣ⸢fi⸣ := 𝒫(Exp × Ψ) × AStore
γ : (Exp → AM⸢fi⸣(Exp)) → (AΣ⸢fi⸣ → AΣ⸢fi⸣)
γ(f)(eψ⸢*⸣,σ) := 
  ({eψ⸤11⸥ .. eψ⸤n1⸥ .. eψ⸤nmₙ⸥}, σ₁ ⊔ .. ⊔ σₙ) where 
    {(e₁,ψ₁) .. (eₙ,ψₙ)} := eψ⸢*⸣
    ({eψ⸤i1⸥ .. eψ⸤imᵢ⸥},σᵢ) := f(eᵢ)(ψᵢ,σ)
α  : (AΣ⸢fi⸣ → AΣ⸢fi⸣) → (Exp → AM⸢fi⸣(Exp))
α(f)(e)(ψ,σ) := f({(e,ψ)},σ)
``````````````````````````````````````````````````
`\begin{proposition}`{.raw}
`γ` and `α` form a Galois connection.
`\end{proposition}`{.raw}
`\begin{proposition}`{.raw}
There exists Galois connections:
`````align````````````````````````````````````````
CM α₁⇄γ₁ AM α₂⇄γ₂ AM⸢fi⸣
``````````````````````````````````````````````````
`\end{proposition}`{.raw}
The first Galois connection `CM α₁⇄γ₁ AM` is justified piecewise by the Galois
connections between `CVal α⇄γ AVal` and `CTime α⇄γ ATime`. The second Galois
connection `AM α₂⇄γ₂ AM⸢fi⸣` is justified by calculation over their
definitions. We aim to recover this proof more easily through compositional
components in Section \ref{a-compositional-monadic-framework}.
`\begin{corollary}`{.raw}
`````align````````````````````````````````````````
CΣ α₁⇄γ₁ AΣ α₂⇄γ₂ AΣ⸢fi⸣
``````````````````````````````````````````````````
`\end{corollary}`{.raw}
This property is derived by transporting each Galois connection between monads
through their respective Galois connections to `Σ`.
`\begin{proposition}`{.raw}
The following orderings hold between the three induced transition relations:
`````align````````````````````````````````````````
α₁ ∘ Cγ(step) ∘ γ₁ ⊑ Aγ(step) ⊑ γ₂ ∘ Aγ⸢fi⸣(step) ∘ α₂
``````````````````````````````````````````````````
`\end{proposition}`{.raw}
This is an application of the monotonicity of `step` and the Galois connections
between monads, each transported through the Galois connection to their
corrosponding transition systems. This is also a direct corollary of Theorem
\ref{galois-theorem} in Section \ref{galois-transformers-1} when cast in the
compositional framework of Galois transformers.

We note that the implementation for our interpreter and abstract garbage
collector remain the same for each instantiation; they scale seamlessly to
variatiosn in path and flow sensitivity when instantiated with the appropriate
monad. 

# A Compositional Monadic Framework

In our development thus far, any modification to the interpreter requires
redesigning the monad `AM` and constructing new proofs relating `AM` to `CM`.
We want to avoid reconstructing complicated monads for our interpreters,
especially as languages and analyses grow and change. Even more, we want to
avoid reconstructing complicated _proofs_ that such changes require. Toward
this goal we introduce a compositional framework for constructing monads which
are correct-by-construction--we extend the well-known structure of monad
transformer to that of _Galois transformer_.

There are two monadic effects used in our monadic interpreter: state and
nondeterminism. For state we will review the state monad transformer `Sₜ[s]`,
which is standard (See \citet{dvanhorn:Liang1995Monad} for more details). For
nondeterminism we develop two monad transformers, `𝒫ₜ` and `FSₜ[s]`. These
transformers are fully general purpose, even outside the context of program
analysis, and are novel in this work.

To create a monad with various state and nondeterminism effects, one must
merely summon some composition of these three monads. _Implementations and
proofs for monadic sequencing, state effects, nondeterminism effects, and
mappings to an executable transition system will come entirely for free._
This means that for a language which has a different state space than the
example in this paper, no added effort is required to construct a monad stack
for that language.

Path and flow senstivity properties arise from the _order of composition_ of
monad transformers. Placing state after nondeterminism (`Sₜ[s] ∘ 𝒫ₜ` or `Sₜ[s]
∘ FSₜ[s']`) will result in `s` being path-sensitive. Placing state before
nondeterminism (`𝒫ₜ ∘ Sₜ[s]` or `FSₜ[s'] ∘ Sₜ[s]`) will result in `s` being
flow-insensitive. Finally, when `FSₜ[s]` is used in place of `Sₜ[s] ∘ 𝒫ₜ` or
`𝒫ₜ ∘ Sₜ[s]`, `s` will be flow-sensitive. The combination of all three
sensitivities looks like (`M := Sₜ[s₁] ∘ FSₜ[s₂] ∘ Sₜ[s₃]`), which will induce
state space transition system `Σ(Exp) := [(Exp × s₁) ↦ s₂] × s₃`, which is
path-sensitive in `s₁`, flow-sensitive in `s₂` and flow-insensitive in `s₃`.
Using `Sₜ[s]`, `𝒫ₜ` and `FSₜ[s]`, one can easily choose which components of the
anlysis are path-sensitive, flow-sensitive or flow-insensitive.

In the following definitions we must necessarily use `bind`, `return` and other
operations from the underlying monad, and we notate these `bindₘ`, `returnₘ`,
`doₘ`, `←ₘ`,  etc.

## State Monad Transformer

Briefly we review the state monad transformer, `Sₜ[s]`:
`````indent```````````````````````````````````````
Sₜ[_] : (Type → Type) → (Type → Type)
Sₜ[s](m)(α) := s → m(α × s)
``````````````````````````````````````````````````
`Sₜ[s]` transports monad operations from `m` to `Sₜ[s](m)`:
`````indent```````````````````````````````````````
bind : ∀ α β, 
  Sₜ[s](m)(α) → (α → Sₜ[s](m)(β)) → Sₜ[s](m)(β)
bind(m)(f)(s) := (x,s') ←ₘ m(s) ; f(x)(s')
return : ∀ α, α → Sₜ[s](m)(α)
return(x)(s) := returnₘ(x,s)
``````````````````````````````````````````````````
`Sₜ[s]` supports state effects:
`\small\begin{alignat*}{4}`{.raw}
`````rawmacro``````````````````````````````````````
get & : Sₜ[s](m)(s)     & ␣␣get(s)     & := returnₘ(s,s)  \\
put & : s → Sₜ[s](m)(1) & ␣␣put(s')(s) & := returnₘ(1,s')
`````````````````````````````````````````````````
`\end{alignat*}\normalsize`{.raw}
Finally, `Sₜ[s]` transports nondeterminism effects from `m`
to `Sₜ[s](m)`:
`````indent```````````````````````````````````````
mzero : ∀ α, Sₜ[s](m)(α)
mzero(s) := mzeroₘ 
_[⟨+⟩]_ : ∀ α, Sₜ[s](m)(α) × Sₜ[s](m)(α) → Sₜ[s](m)(α)
(m₁ ⟨+⟩ m₂)(s) := m₁(s) ⟨+⟩ₘ m₂(s) 
``````````````````````````````````````````````````

## Nondeterminism Monad Transformer

We have developed a new monad transformer for nondeterminism which composes
with state in both directions. Previous attempts to define a monad transformer
for nondeterminism have resulted in monad operations which do not respect
either monad laws or nondeterminism effect laws--ours does.

The nondeterminism monad transformer is defined with the expected type,
embedding `𝒫` inside `m`:
`````indent```````````````````````````````````````
𝒫ₜ : (Type → Type) → (Type → Type)
𝒫ₜ(m)(α) := m(𝒫(α))
``````````````````````````````````````````````````
`𝒫ₜ` transports monad operations from `m` to `𝒫ₜ(m)` _provided that `m` is a
join-semilattice functor_. The join-lattice functorality of `m` will be
instantiated with `𝒫(β)`.
`````indent```````````````````````````````````````
bind : ∀ α β, 𝒫ₜ(m)(α) → (α → 𝒫ₜ(m)(β)) → 𝒫ₜ(m)(β)
bind(m)(f) := doₘ
  {x₁ .. xₙ} ←ₘ m
  f(x₁) ⊔ₘ .. ⊔ₘ f(xₙ)
return : ∀ α, α → 𝒫ₜ(m)(α)
return(x) := returnₘ({x})
``````````````````````````````````````````````````
`𝒫ₜ` transports state effects from `m` to `𝒫ₜ(m)`:
`````indent```````````````````````````````````````
get : 𝒫ₜ(m)(s)
get = mapₘ(λ(s).{s})(getₘ)
put : s → 𝒫ₜ(m)(1)
put(s) = mapₘ(λ(1).{1})(putₘ(s))
``````````````````````````````````````````````````
Finally, `𝒫ₜ` supports nondeterminism effects through a straightforward
application of the underlying monad's join-semilattice functorality:
`````indent```````````````````````````````````````
mzero : ∀ α, 𝒫ₜ(m)(α)
mzero := ⊥ₘ
_[⟨+⟩]_ : ∀ α, 𝒫ₜ(m)(α) x 𝒫ₜ(m)(α) → 𝒫ₜ(m)(α)
m₁ ⟨+⟩ m₂ := m₁ ⊔ₘ m₂
``````````````````````````````````````````````````

`\begin{proposition}`{.raw}
1. `bind` and `return` satisfy monad laws.
2. `get` and `put` satisfy the state monad laws.
3. `mzero` and `⟨+⟩` satisfy the nondeterminism monad laws.
`\end{proposition}`{.raw}
The key lemma in (1) is the functorality of `m`, namely that:
`````align````````````````````````````````````````
returnₘ(x ⊔ y) = returnₘ(x) ⊔ₘ returnₘ(y)
``````````````````````````````````````````````````
(2) is by simple calculation and (3) is trivial as a consequence of the
underlying monad being a join-semilattice functor.

## Flow Sensitivity Monad Transformer

The flow sensitivity monad transformer is a unique monad transformer that
combines state and nondeterminism effects, and does not arise naturally from
composing vanilla nondeterminism and state transformers. The flow sensitivity
monad transformer is defined:
`````indent```````````````````````````````````````
FSₜ[_] : (Type → Type) → (Type → Type)
FSₜ[s](m)(α) := s → m([α ↦ s])
``````````````````````````````````````````````````
where `[α ↦ s]` is notation for a finite map from `α` to `s`.

`FSₜ[s]` transports monad operations provided that `s` is a join-semilattice
and `m` is a join-semilattice functor. The functorality of `m` will be
instantiated with `[β → s]`, which forms a lattice when `s` also does.
`````indent```````````````````````````````````````
bind : ∀ α β, 
 FSₜ[s](m)(α) → (α → FSₜ[s](m)(β)) → FSₜ[s](m)(β)
bind(m)(f)(s) := doₘ
  {x₁ ↦ s₁,..,xₙ ↦ sₙ} ←ₘ m(s)
  f(x₁)(s₁) ⊔ₘ .. ⊔ₘ f(xₙ)(sₙ)
return : ∀ α, α → FSₜ[s](m)(α)
return(x)(s) := returnₘ {x ↦ s}
``````````````````````````````````````````````````
`FSₜ[s]` transports state effects from `m` to `FSₜ[s](m)`:
`````indent```````````````````````````````````````
get : FSₜ[s](m)(s)
get(s) := returnₘ {s ↦ s}
put : s → FSₜ[s](m)(1)
put(s')(s) := returnₘ {1 ↦ s'}
``````````````````````````````````````````````````
Finally, `FSₜ[s]` supports nondeterminism effects provided `s` is a
join-semilattice and `m` is a join-semilattice functor:
`````indent```````````````````````````````````````
mzero : ∀ α, FSₜ[s](m)(α)
mzero(s) := ⊥ₘ
_[⟨+⟩]_ : ∀ α, FSₜ[s](m)(α) x FSₜ[s](m)(α) → FSₜ[s](m)(α)
(m₁ ⟨+⟩ m₂)(s) := m₁(s) ⊔ₘ m₂(s)
``````````````````````````````````````````````````
`\begin{proposition}`{.raw}
`get` and `put` satisfy the state monad laws, `mzero` and `⟨+⟩` satisfy the
nondeterminism monad laws, and `Sₜ[s] ∘ 𝒫ₜ α₁⇄γ₁ FSₜ[s] α₂⇄γ₂ 𝒫ₜ ∘ Sₜ[s]`.
`\end{proposition}`{.raw}
These proofs are analagous to those for state and nondeterminism monad
transformers.

## Mapping to State Spaces

Both our execution and correctness frameworks requires that monadic actions in
`m` map to state space transitions in `Σ`. We extend the earlier statement of
Galois connection to the transformer setting, mapping monad _transformer_
actions in `T` to state space _functor_ transitions in `Π`.
`````indent```````````````````````````````````````
T : (Type → Type) → (Type → Type)
Π : (Type → Type) → (Type → Type)
mstep : ∀ α β, 
  (α → T(m)(β)) α⇄γ (Π(Σₘ)(α) → Π(Σₘ)(β))
``````````````````````````````````````````````````
In the type of `mstep`, `m` is an arbitrary monad whose monadic actions map to
state space `Σₘ`. The monad transformer `T` must induce a state space
transformer `Π` for which `mstep` can be defined. We only show the `γ` sides of
the mappings in this section, which allow one to execute the analyses.

For the state monad transformer `Sₜ[s]` mstep is defined:
`````indent```````````````````````````````````````
mstep-γ : ∀ α β, 
  (α → Sₜ[s](m)(β)) → (Σₘ(α × s) → Σₘ(β × s))
mstep-γ(f) := mstepₘ-γ(λ(a,s). f(a)(s))
``````````````````````````````````````````````````
For the nondeterminism transformer `𝒫ₜ` mstep is defined:
`````indent```````````````````````````````````````
mstep-γ : ∀ α β, 
  (α → 𝒫ₜ(m)(β)) → (Σₘ(𝒫(α)) → Σₘ(𝒫(β)))
mstep-γ(f) := mstepₘ-γ(F) where 
  F({x₁ .. xₙ}) = f(x₁) ⊔ₘ .. ⊔ₘ f(xₙ))
``````````````````````````````````````````````````
For the flow sensitivity monad transformer `FSₜ[s]` mstep is defined:
`````indent```````````````````````````````````````
mstep-γ : ∀ α β, 
  (α → FSₜ[s](m)(β)) → (Σₘ([α ↦ s]) → Σₘ([β × s]))
mstep-γ(f) := mstepₘ-γ(F) where 
  F({x₁ ↦ s₁},..,{xₙ ↦ sₙ}) := 
    f(x₁)(s₁) ⊔ₘ .. ⊔ₘ f(xₙ)(sₙ)
``````````````````````````````````````````````````
The Galois connections for `mstep` for `Sₜ[s]`, `Pₜ` and `FSₜ[s]` crucially
require that `mstepₘ-γ` and `mstepₘ-α` be homomorphic, i.e. that:
`````indent```````````````````````````````````````
α(id) ⊑ return and α(f ∘ g) ⊑ α(f) ⟨∘⟩ α(g)
``````````````````````````````````````````````````
and likewise for `γ`, where `⟨∘⟩ ` is composition in the Kleisli category for
the monad `M`.

## Galois Transformers

The capstone of our framework is the fact that monad transformers `Sₜ[s]`,
`FSₜ[s]` and `𝒫ₜ` are also _Galois transformers_.

`\begin{definition}`{.raw}
A monad transformer `T` is a Galois transformer if:
`\begin{enumerate}`{.raw}
\item It transport Galois connections, that is for all monads `m₁` and `m₂`,
      `m₁ α⇄γ m₂` implies `T(m₁) α⇄γ T(m₂)`.
`````raw``````````````````````````````````````````
\begin{center}
\begin{tikzpicture}
  \matrix (m) [matrix of math nodes,row sep=3em,column sep=4em,minimum width=2em]
  {
     m_1 & T(m_1) \\
     m_2 & T(m_2) \\
  };
  \path[-stealth]
    (m-1-1) edge [bend left=40] node [right] {$\alpha$}   (m-2-1)
            edge                node [below] {$T$}        (m-1-2)
    (m-2-1) edge [bend left=40] node [left]  {$\gamma$}   (m-1-1)
            edge                node [below] {$T$}        (m-2-2)
    (m-1-2) edge [bend left=40] node [right] {$\alpha_T$} (m-2-2)
    (m-2-2) edge [bend left=40] node [left]  {$\gamma_T$} (m-1-2)
  ;
\end{tikzpicture}
\end{center}
``````````````````````````````````````````````````
\item It transports mappings to an executable transition system, that is there
      exists `Π` s.t. for all monads `m` and functors `Σ`, `(α → m(β)) α⇄γ (Σ(α) →
      Σ(β))` implies `(α → T(m)(β)) α⇄γ (Π(Σ)(α) → Π(Σ)(β))`.
`````raw``````````````````````````````````````````
\begin{center}
\begin{tikzpicture}
  \matrix (m) [matrix of math nodes,row sep=3em,column sep=4em,minimum width=2em]
  {
             \alpha \rightarrow m(\beta)      & \alpha              \rightarrow T(m)(\beta)        \\
     \Sigma(\alpha) \rightarrow \Sigma(\beta) & \Pi(\Sigma)(\alpha) \rightarrow \Pi(\Sigma)(\beta) \\
  };
  \path[-stealth]
    (m-1-1) edge [bend left=40] node [right] {$\alpha$}   (m-2-1)
            edge                node [below] {$T$}        (m-1-2)
    (m-2-1) edge [bend left=40] node [left]  {$\gamma$}   (m-1-1)
            edge                node [below] {$\Pi$}      (m-2-2)
    (m-1-2) edge [bend left=40] node [right] {$\alpha_T$} (m-2-2)
    (m-2-2) edge [bend left=40] node [left]  {$\gamma_T$} (m-1-2)
  ;
\end{tikzpicture}
\end{center}
``````````````````````````````````````````````````
`\end{enumerate}`{.raw}
`\end{definition}`{.raw}
Property (1) transports Galois connections between monads, and property (2)
transports Galois connections between transition systems. By composing the
2-dimensional diagrams (1) and (2) into a 3-dimensional diagram (which we do
not show) we establish the following theorem: 
`\begin{theorem}`{.raw} 
If `T` is a Galois transformer, then it is sufficient to prove that underlying
monads `m₁` and `m₂` form a Galois connection `m₁ α⇄γ m₂` in order to establish
`Π(Σ₁) α⇄γ Π(Σ₂)`. 
\label{galois-theorem}
`\end{theorem}`{.raw} 
This is the workhorse of our entire proof framework, allowing us to reason
about monadic actions, like the monadic interpreter `step` from section
\ref{the-interpreter}, and derive properties about the induced transition
system, which is how the analysis is executed, for free. 
`\begin{proposition}`{.raw}
`Sₜ[s]`, `FSₜ[s]` and `𝒫ₜ` are Galois transformers.
`\end{proposition}`{.raw}
The proofs are sketched earlier in Section
\ref{a-compositional-monadic-framework}.

## Building Transformer Stacks

We can now build monad transformer stacks from combinations of `Sₜ[s]`,
`FS[s]ₜ` and `𝒫ₜ` which automatically construct the following properties:

- The resulting monad has the combined effects of all pieces of the transformer
  stack.
- Actions in the resulting monad map to a state space transition system `Σ → Σ`
  for some `Σ`, allowing one to execute the analysis.
- Galois connections between `CΣ` and `AΣ` are established piecewise from monad
  transformer components.

We instantiate our interpreter to the following monad stacks in decreasing
order of precision:

\vspace{4pt}
`\small\begin{tabular}{ >{$}l<{$} | >{$}l<{$} | >{$}l<{$} }`{.raw}
`````rawmacro````````````````````````````````````
Sₜ[AEnv]     & Sₜ[AEnv]      & Sₜ[AEnv]    \\
Sₜ[AKAddr]   & Sₜ[AKAddr]    & Sₜ[AKAddr]  \\
Sₜ[AKStore]  & Sₜ[AKStore]   & Sₜ[AKStore] \\
Sₜ[ATime]    & Sₜ[ATime]     & Sₜ[ATime]   \\
Sₜ[AStore]   &               & 𝒫ₜ          \\
𝒫ₜ           & FSₜ[AStore]   & Sₜ[AStore]  \\
``````````````````````````````````````````````````
`\end{tabular}\normalsize`{.raw}
\vspace{4pt}

\noindent
From left to right these give path-sensitive, flow-sensitive and
flow-insensitive analyses for the data-store.

Another benefit of our approach is that we can easily select different path and
flow sensitivity properties for the data-store and stack-store independent of
each other, merely by rearranging the order of composition.

\vspace{8pt}
`\small\begin{tabular}{ >{$}l<{$} | >{$}l<{$} | >{$}l<{$} }`{.raw}
`````rawmacro``````````````````````````````````````
Sₜ[AEnv]     & Sₜ[AEnv]      & Sₜ[AEnv]    \\
Sₜ[AKAddr]   & Sₜ[AKAddr]    & Sₜ[AKAddr]  \\
Sₜ[ATime]    & Sₜ[ATime]     & Sₜ[ATime]   \\
Sₜ[AKStore]  &               & 𝒫ₜ          \\
𝒫ₜ           & FSₜ[AKStore]  & Sₜ[AKStore] \\
Sₜ[AStore]   & Sₜ[AStore]    & Sₜ[AStore]  \\
`````````````````````````````````````````````````
`\end{tabular}\normalsize`{.raw}
\vspace{8pt}

\noindent
From left to right these give analysis which are all flow-insensitive in the
data-store, but path-sensitive, flow-sensitive and flow-insensitive in the
stack-store.

# Implementation

We have implemented our framework in Haskell and applied it to compute analyses
for `λIF`. Our implementation provides path sensitivity, flow sensitivity, and
flow insensitivity as a semantics-independent monad library. The code shares a
striking resemblance with the math.

Our implementation is suitable for prototyping and exploring the design space
of static analyzers. Our analyzer supports exponentially more compositions of
analysis features than any current analyzer. For example, our implementation is
the first which can combine arbitrary choices in call-site, object, path and
flow sensitivities. Furthermore, the user can choose different path and flow
sensitivities for each component of the state space.

Our implementation `{\tt maam}`{.raw} supports command-line flags for garbage
collection, mCFA, call-site sensitivity, object sensitivity, and path and flow
sensitivity.
`````raw``````````````````````````````````````````
-- \vspace{1em}
{\small\tt
\par \noindent ./maam prog.lam --gc --mcfa --kcfa=1 --ocfa=2
\par \noindent \hspace{2em} --data-store=flow-sen --stack-store=path-sen
}
-- \vspace{1em}
\par \noindent
`````````````````````````````````````````````````
These flags are implemented completely independently of one another and their
combination is applied to a single parameterized monadic interpreter.
Furthermore, using Galois transformers allows us to prove each combination
correct in one fell swoop.

A developer wishing to use our library to develop analyzers for their language
of choice inherits as much of the analysis infrastructure as possible. We
provide call-site, object, path and flow sensitivities as language-independent
libraries. To support analysis for a new language a developer need only
implement:

- A monadic semantics for their language, using state and nondeterminism
  effects.
- The abstract value domain, and optionally the concrete value domain if they
  wish to recover concrete execution.
- Intentional optimizations for their semantics like garbage collection and
  mcfa.

The developer then receives the following for free through our analysis
library:

- A family of monads which implement their effect interface and give different
  path and flow sensitivities.
- An execution engine for each monad to drive the analysis.
- Mechanisms for call-site and object sensitivities.

Not only is a developer able to reuse our implementation of call-site, object,
path and flow sensitivities, they need not understand the execution machinery
or soundness proofs for them either. They need only verify that their monadic
semantics is monotonic w.r.t. the analysis parameters, and that their abstract
value domain forms a Galois connection. The execution and correctness of the
final analyzer is constructed for free given these two properties.

Our implementation is publicly available and can be installed as a cabal
package: `{\small\tt`{.raw} cabal install maam`}`{.raw}.

# Related Work

\paragraph{Overview}

Program analysis comes in many forms such as points-to
\cite{dvanhorn:Andersen1994Program}, flow
\cite{dvanhorn:Jones:1981:LambdaFlow}, or shape analysis
\cite{dvanhorn:Chase1990Analysis}, and the literature is vast. (See
\citet{dvanhorn:hind-paste01,dvanhorn:Midtgaard2012Controlflow} for surveys.)
Much of the research has focused on developing families or frameworks of
analyses that endow the abstraction with a number of knobs, levers, and dials
to tune precision and compute efficiently (some examples include
\citet{dvanhorn:Shivers:1991:CFA, dvanhorn:nielson-nielson-popl97,
dvanhorn:Milanova2005Parameterized, davdar:van-horn:2010:aam}; there are many
more).  These parameters come in various forms with overloaded meanings such as
object \cite{dvanhorn:Milanova2005Parameterized,
dvanhorn:Smaragdakis2011Pick}, context \cite{dvanhorn:Sharir:Interprocedural,
dvanhorn:Shivers:1991:CFA}, path \cite{davdar:das:2002:esp}, and heap
\cite{davdar:van-horn:2010:aam} sensitivities, or some combination thereof
\cite{dvanhorn:Kastrinis2013Hybrid}.

These various forms can all be cast in the theory of abstraction
interpretation of \citet{dvanhorn:Cousot:1977:AI,
dvanhorn:Cousot1979Systematic} and understood as computable
approximations of an underlying concrete interpreter.  Our work
demonstrates that if this underlying concrete interpreter is written
in monadic style, monad transformers are a useful way to organize and
compose these various kinds of program abstractions in a modular and
language-independent way.

This work is inspired by the trifecta combination of
\citeauthor{dvanhorn:Cousot:1977:AI}'s theory of abstract interpretation based
on Galois connections \cite{dvanhorn:Cousot:1977:AI,
dvanhorn:Cousot1979Systematic, dvanhorn:Cousot98-5},
\citeauthor{davdar:Moggi:1989:Monads}'s original monad transformers
\cite{davdar:Moggi:1989:Monads} which were later popularized in
\citeauthor{dvanhorn:Liang1995Monad}'s _Monad Transformers and Modular
Interpreters_ \cite{dvanhorn:Liang1995Monad}, and
\citeauthor{dvanhorn:Sergey2013Monadic}'s _Monadic Abstract Interpreters_
\cite{dvanhorn:Sergey2013Monadic}.

-- , and continues in the tradition of
-- applying monads to programming language semantics pioneered by
-- \citet{davdar:Moggi:1989:Monads}.

\citet{dvanhorn:Liang1995Monad} first demonstrated how monad transformers could
be used to define building blocks for constructing (concrete) interpreters.
Their interpreter monad \mbox{\(\mathit{InterpM}\)} bears a strong resemblance
to ours.  We show this "building blocks" approach to interpreter construction
also extends to \emph{abstract} interpreter construction using Galois
transfomers.  Moreover, we show that these monad transformers can be proved
sound via a Galois connection to their concrete counterparts, ensuring the
soundness of any stack built from sound blocks of Galois transformers.
Soundness proofs of various forms of analysis are notoriously brittle with
respect to language and analysis features.  A reusable framework of Galois
transformers offers a potential way forward for a modular metatheory of program
analysis.

\citet{dvanhorn:Cousot98-5} develops a "calculational approach" to analysis
design whereby analyses are not designed and then verified \emph{post facto},
but rather derived by positing an abstraction and calculating it from the
concrete interpreter using Galois connections. These calculations are done by
hand. Our approach offers a limited ability to automate the calculation process
by relying on monad transformers to combine different abstractions.

We build directly on the work of Abstracting Abstract Machines (AAM) by
\citet{davdar:van-horn:2010:aam} and \citet{dvanhorn:Smaragdakis2011Pick} in
our parameterization of abstract time to achieve call-site and object
sensitivity. More notably, we follow the AAM philosophy of instrumenting a
concrete semantics _first_ and performing a systematic abstraction _second_.
This greatly simplifies the Galois connection arguments during systematic
abstraction. However, this is at the added cost of proving that the
instrumented semantics simulate the original concrete semantics.

\paragraph{Monadic Abstract Interpreters}

\citeauthor{dvanhorn:Sergey2013Monadic} first introduced the concept of writing
abstract interpreters in monadic style in _Monadic Abstract Interpreters_
(MAI)\cite{dvanhornn:Sergey2013Monadic}, in which variations in analysis are
also recovered through new monad implementations. However, our approach is
considerably different from MAI.

In MAI, the framework's interface is based on _denotation functions_ for every
syntactic form of the language (See "CPSInterface", Figure 2 in MAI). This
design decision has far reaching consequences for the entire approach. The
denotation functions in MAI are language-specific and specialized to their
example language. MAI uses a single monad stack fixed to the denotation
function interface: state on top of list (Section 5.3.1 in MAI). New analyses
are achieved through multiple denotation functions into this single monad.
Analyses in MAI are all fixed to be path-sensitive, and the methodology for
incorporating other path or flow properties is to surgically instrument the
execution of the analysis with a custom Galois connection (Section 6.5 in MAI).
Lastly, the framework provides no reasoning principles or proofs of soundness
for the denotation function interface. _A user of MAI must inline the
definitions of each analysis and prove their implementation correct from
scratch each time._

By contrast, our framework's interface is based on state and nondeterminism
_monadic effects_ (Section \ref{the-analysis-monad}). This interface comes
equipped with reasoning principles, allowing one to verify the correctness of
a monadic interpreter _independent of a particular monad_, which is not
possible in MAI. State and nondeterminism monadic effects capture the essence
of _small-step relational semantics_, and are therefore truly language
independent. Our tools are reusable for any semanatics described as a
small-step state machine relation. Because we place the monadic interpreter
behind an interface of effects rather than denotation functions, we are able to
introduce language-independent monads which capture flow-sensitivity and
flow-insensitivity (Sections \ref{varying-path-and-flow-sensitivity} and
\ref{a-compositional-monadic-framework}), and we show how to compose these
features with other analysis design choices (Sections \ref{analysis-parameters}
and \ref{a-compositional-monadic-framework}). The monadic effect interface also
allows us to separate the monad from the abstract domain, both of which are
tightly coupled in MAI. Finally, our framework is compositional through the use
of monad transformers (Section \ref{a-compositional-monadic-framework}) which
construct execution engines and proofs of soundness for free. 

We do not achieve correctness and compositionality _in addition_ to our
transition from denotation functions to monadic effects; rather we achieve
correctness and compositionality _through it_; such a transition essential,
primary and novel to our work. 

\paragraph{Widening for Control-Flow}

\citeauthor{dvanhorn:Hardekopf2014Widening} also introduces a unifying account
of control flow properties in _Widening for Control-Flow_
(WCF)\cite{dvanhorn:Hardekopf2014Widening}, accounting for path, flow and
call-site sensitivities . WCF achieves this through an instrumentation of the
abstract machine's state space which is allowed to track arbitrary contextual
information, up to the path-history of the entire execution. WCF also develops
a modular proof framework, proving the bulk of soundness proofs for each
instantiation of the instrumentation at once.

Our work achieves similar goals, although isolating path and flow sensitivity
is not our primary objective. While WCF is based on a language-dependent
instrumentation of the semantics, we achieve variations in flow sensitivity by
modifying language-independent control properties of the interpreter--through a
monad.

Particular strengths of WCF are the wide range of choices for control-flow
sensitivity which are shown to be implementable within the design, and the
modular proof framework. For example, WCF is able to also account for call-site
sensitivity through their design; we must account for call-site sensitivity
through a different mechanism.

Particular strengths of our work is the understanding of path and flow
sensitivity not through instrumentation but through control properties of the
interpreter, and also a modular proof framework, although modular in a
different sense from WCF. We also show how to compose different path and flow
sensitivity choices for independent components of the state space, like a
flow-sensitive data-store and path-sensitive stack-store, for example.

# Conclusion

We have shown that \emph{Galois transfomers}, monad transfomers that transport
(1) Galois connections and (2) mappings to an executable transition system, are
effective, language-independent building blocks for constructing program
analyzers and form the basis of a modular, reusable, and composable metatheory
for program analysis.

In the end, we hope language independent characterizations of analysis
ingredients will both facilate the systematic construction of program analyses
and bridge the gap between various communities which often work in isolation.
