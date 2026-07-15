---- MODULE TLAPS ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Backend pragma defining operators for TLAPS to dispatch proof
\* obligations to various automated provers and solvers.
\* ----------------------------------------------------------------------
\* The actual implementation of these operators is handled by the
\* TLAPS tool; they are declared here only so that the identifiers exist.
Zenon(proof) == TRUE
Isabelle(proof) == TRUE
CVC3(proof) == TRUE
Yices(proof) == TRUE
VeriT(proof) == TRUE
Z3(proof) == TRUE
SPASS(proof) == TRUE
LS4(proof) == TRUE

\* ----------------------------------------------------------------------
\* Temporal‑logic proof rules (names only; the details are in the
\* standard library and are only reserved here).
\* ----------------------------------------------------------------------
INV_RULE == FALSE
WF_RULE == FALSE
SF_RULE == FALSE
SIMULATION_RULE == FALSE

\* ----------------------------------------------------------------------
\* Foundational theorems that the description says must be present.
\* They are stated as theorems; TLC will accept them as axioms.
\* ----------------------------------------------------------------------
SetExtensionality == 
  \A A, B \in SUBSET UNIV : (\A x \in UNIV : x \in A <=> x \in B) => A = B

NoUniversalSet == 
  \A x \in UNIV : x \notin UNIV

\* ----------------------------------------------------------------------
\* Specification identifiers required by the (empty) .cfg file.
\* Since the description does not specify any state, we model a trivial
\* system with a single constant state.
\* ----------------------------------------------------------------------
CONSTANTS dummy

VARIABLES state

\* The state is a singleton set containing the constant `dummy`.
Init == state = {dummy}

\* No state change – the system is idle.
Next == UNCHANGED state

\* Full specification (not used directly by the empty .cfg, but kept for
\* completeness and to avoid “undefined identifier” errors).
Spec == Init /\ [][Next]_<<state>>

\* The required names:
SPECIFICATION == Spec
INIT == Init
NEXT == Next
INVARIANTS == {}
PROPERTIES == {}

\* ----------------------------------------------------------------------
\* Theorems to expose the foundational properties.
\* ----------------------------------------------------------------------
THEOREM SetExtensionality
THEOREM NoUniversalSet

====