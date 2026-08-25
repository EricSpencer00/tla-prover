---- MODULE TLAPS ----
\*=====================================================================
\* TLAPS: Backend pragmas and temporal logic proof rules for TLAPS
\*=====================================================================

\*-------------------------
\* Constants
\*-------------------------
CONSTANT UNIV \* Universe of all values (to be instantiated by the model)

\*-------------------------
\* Backend prover operators
\* Each operator is a placeholder that can be used in TLAPS proofs to
\* indicate which backend should be invoked.  The arguments are
\* arbitrary expressions representing the proof obligation.
\*-------------------------
Zenon(p)      == TRUE
Isabelle(p)   == TRUE
CVC3(p)       == TRUE
Yices(p)      == TRUE
VeriT(p)      == TRUE
Z3(p)         == TRUE
SPASS(p)      == TRUE
LS4(p)        == TRUE

\*-------------------------
\* Temporal‑logic proof‑rule operators
\* These operators are provided so that their names are reserved.
\* They do not implement the rules; they merely serve as markers.
\*-------------------------
InvarianceRule(p)        == TRUE
WellFormednessRule(p)    == TRUE
StrongFairnessRule(p)    == TRUE
WeakFairnessRule(p)      == TRUE
StepSimulationRule(p)    == TRUE

\*-------------------------
\* Fundamental theorems
\*-------------------------

\* Set extensionality: two sets are equal iff they have the same elements.
THEOREM SetExtensionality ==
  \A S, T \in SUBSET UNIV :
    (\A x \in UNIV : (x \in S) <=> (x \in T)) => S = T

\* No set contains every possible value (i.e., there is no universal set).
THEOREM NoSetContainsAll ==
  \A S \in SUBSET UNIV : \E x \in UNIV : x \notin S

====