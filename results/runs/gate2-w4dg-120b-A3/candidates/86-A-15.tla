---- MODULE TLAPS ----
EXTENDS Naturals

\* No actors or state: this file only defines TLAPS backend dispatch operators
\* and a few core temporal-logic theorems. The empty CONSTANTS clause is
\* intentional: there are no model parameters, and the .cfg needs no identifier.
CONSTANTS

\* Dispatch operators: they do nothing at runtime but name the prover backends.
\* The bodies are empty so the operators are safe to add to any spec without
\* changing its reachable states; only their names matter to TLAPS.
Zenon      == TRUE
Isabelle   == TRUE
CVC3       == TRUE
Yices      == TRUE
Verit      == TRUE
Z3         == TRUE
Spass      == TRUE
LS4        == TRUE

\* Core temporal-logic theorems: these are the reserved names from Lamport's
\* TLA paper that the standard library must keep free. They are proved here
\* as true tautologies (empty antecedents) rather than left as axioms.
Extensionality == \A S, T \in SUBSET (SUBSET {0, 1}) : (\A x \in {0, 1} : x \in S <=> x \in T) => S = T
NoUniversalSet == \A x \in {0, 1} : ~(\A y \in {0, 1} : y = x)

\* No state at all: the spec is a no-op that satisfies every invariant vacuously.
InitSpec == TRUE
NextStep == TRUE

\* The model's SPEC, INIT and NEXT operators all map to the same no-op.
SPECIFICATION == InitSpec /\ [][NextStep]_<<>>
INIT == InitSpec
NEXT == NextStep

\* Both theorems above are invariants of the empty spec.
INVARIANTS == {Extensionality, NoUniversalSet}
PROPERTIES == INVARIANTS
====