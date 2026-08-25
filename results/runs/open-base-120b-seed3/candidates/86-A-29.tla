---- MODULE TLAPS ----
EXTENDS Naturals, FiniteSets, Sequences

\* ----------------------------------------------------------------------
\* Backend provers for TLAPS.  The arguments are proof obligations that
\* will be dispatched to the corresponding automated theorem prover.
\* ----------------------------------------------------------------------
Zenon(p)    == p
Isabelle(p) == p
CVC3(p)     == p
Yices(p)   == p
VeriT(p)    == p
Z3(p)       == p
SPASS(p)    == p
LS4(p)      == p

\* ----------------------------------------------------------------------
\* Temporal‑logic proof‑rule placeholders.  Their definitions are
\* intentionally trivial; their names are reserved for use by TLAPS.
\* ----------------------------------------------------------------------
Invariance(p)       == p
WellFormedness(p)  == p
StrongFairness(p)  == p
WeakFairness(p)    == p
StepSimulation(p)  == p

\* ----------------------------------------------------------------------
\* Fundamental theorems required by the description.
\* ----------------------------------------------------------------------
\* Set extensionality: two sets are equal iff they have the same
\* elements.
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x : (x \in S) <=> (x \in T)) => S = T

\* No set contains every possible value.
THEOREM NoUniversalSet ==
  \A S : \E x : x \notin S

====