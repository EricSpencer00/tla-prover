---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The .cfg file overrides the natural numbers with a finite bound; we re-interpret
\* Nat as a finite set rather than an infinite one, keeping the same name for
\* readability. Nat itself is NOT declared here; it comes from the standard
\* module. NatOverride is a re-export of the bounded version that the config
\* expects model checking to use.

NatOverride == 0..MaxNat

\* SPECIFICATION: the model's full behaviour, brought in from the base proof.
SPECIFICATION == Spec

\* INIT: the base specification's initial predicate.
INIT == Init

\* NEXT: the base specification's next-relation predicate.
NEXT == Next

\* INVARIANTS: the base proof's invariant that the double of any natural number is even.
INVARIANTS == DoubleIsEven

\* PROPERTIES: the base proof's liveness property, an eventuality the model must satisfy.
PROPERTIES == EventualParity

====