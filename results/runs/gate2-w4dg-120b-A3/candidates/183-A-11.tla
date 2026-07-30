---- MODULE TLAPS ----
EXTENDS Integers

\* This module supplies the set of backend provers and tactics that TLAPS
\* dispatches to, along with the basic toolchain theorem and three
\* standard invariants about the value universe.  It is a configuration
\* module, not an algorithm, so it has no state, action, or liveness
\* concerns at all.

CONSTANTS
  Backends
  Tactics
  MaxTimeout

\* Backends: the set of theorem provers and SMT solvers that the proof
\* system may invoke.
Backends == {"zenon", "isabelle", "cvc3", "yices", "verit", "z3", "spass"}

\* Tactics: the set of heuristics that backends may use.
Tactics == {"default", "minimal"}

\* MaxTimeout: the timeout ceiling for any backend call.
MaxTimeout == 2

\* The one-line specification names the backing operators, so that TLC
\* and the prover driver agree on the set of symbols that exist.
SPECIFICATION == Init /\ Next

Init == TRUE
Next == TRUE

\* The toolchain theorem: the set of values reachable through a proof
\* step is exactly the set of values already reachable.
ToolchainTheorem == \A x \in (UNION {Backends} \cup {Tactics} \cup {MaxTimeout}) : x \in (Backends \cup Tactics \cup {MaxTimeout})

\* The two invariants are the ones the .cfg file expects.
Extensionality == \A X \in SUBSET Backends, Y \in SUBSET Backends : (\A x \in X : x \in Y) => X \subseteq Y
NoSetContainsAll == \A X \in SUBSET Backends : X # Backends

INVARIANTS == Extensionality

PROPERTIES == NoSetContainsAll

====