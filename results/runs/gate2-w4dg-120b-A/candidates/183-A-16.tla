---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  prfZenon, prfIsabelle, prfCVC3, prfYices
CONSTANTS
  prfVeriT, prfZ3, prfSPASS, prfLS4

\* Backend dispatch: invoke the named prover on the given proof obligation
\* with a fixed timeout. Returns the identity of the obligation it handled.
DispatchTo(prf, id) ==
  /\ prf \in {prfZenon, prfIsabelle, prfCVC3, prfYices,
              prfVeriT, prfZ3, prfSPASS, prfLS4}
  /\ id \in Nat \ {0}
  /\ id

\* Temporal logic proof rules (reserved symbols from the standard library):
\* invariance, well-formedness, strong fairness, weak fairness, step simulation.
\* They are defined as identity operators over a formula; their content is never
\* evaluated here, but their mere existence reserves the symbols.
\* (Each rule takes exactly one argument, the formula it is applied to.)
Invariant(f) == f
WFWellFormed(f) == f
StrongFairness(f) == f
WeakFairness(f) == f
StepSimulation(f) == f

SetExtensionality ==
  \A S, T \in SUBSET Nat : (\A x \in Nat : x \in S <=> x \in T) => S = T

\* No set in this specification (which lives in Nat) can be the universal set:
NoSetContainsAll == \A S \in SUBSET Nat : \E x \in Nat : x \notin S

CONSTANTS == {prfZenon, prfIsabelle, prfCVC3, prfYices,
              prfVeriT, prfZ3, prfSPASS, prfLS4}

\* Identity operators standing for the parts of a TLAPS specification that
\* are present but intentionally have no substantive content in this stub.
Specification == TRUE
INIT == TRUE
NEXT == TRUE

INVARIANTS == {SetExtensionality}
PROPERTIES == {NoSetContainsAll}

====