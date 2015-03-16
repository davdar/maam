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

